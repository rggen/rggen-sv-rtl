module rggen_register_common
  import  rggen_rtl_pkg::*;
#(
  parameter bit                     READABLE              = 1,
  parameter bit                     WRITABLE              = 1,
  parameter int                     ADDRESS_WIDTH         = 8,
  parameter bit [ADDRESS_WIDTH-1:0] OFFSET_ADDRESS        = '0,
  parameter int                     BUS_WIDTH             = 32,
  parameter int                     DATA_WIDTH            = BUS_WIDTH,
  parameter int                     VALUE_WIDTH           = BUS_WIDTH,
  parameter bit                     USE_ADDITIONAL_MATCH  = '0
)(
  input logic                 i_clk,
  input logic                 i_rst_n,
  rggen_register_if.register  register_if,
  input logic                 i_additional_match,
  rggen_bit_field_if.register bit_field_if
);
  localparam  int WORDS             = DATA_WIDTH / BUS_WIDTH;
  localparam  int BUS_BYTE_WIDTH    = BUS_WIDTH / 8;
  localparam  int DATA_BYTE_WIDTH   = DATA_WIDTH / 8;
  localparam  int WORD_INDEX_WIDTH  = (WORDS >= 2) ? $clog2(WORDS) : 1;

  genvar  g;

  //  Decode address
  logic [WORDS-1:0] match;
  logic             active;

  always_comb begin
    if (WORDS == 1) begin
      active  = match[0];
    end
    else begin
      active  = |match;
    end
  end

  generate
    for (g = 0;g < WORDS;++g) begin : g_decoder
      localparam  bit [ADDRESS_WIDTH-1:0] START_ADDRESS = OFFSET_ADDRESS
                                                        + ADDRESS_WIDTH'(BUS_BYTE_WIDTH * g);

      rggen_address_decoder #(
        .READABLE             (READABLE             ),
        .WRITABLE             (WRITABLE             ),
        .WIDTH                (ADDRESS_WIDTH        ),
        .BUS_WIDTH            (BUS_WIDTH            ),
        .START_ADDRESS        (START_ADDRESS        ),
        .BYTE_SIZE            (BUS_BYTE_WIDTH       ),
        .USE_ADDITIONAL_MATCH (USE_ADDITIONAL_MATCH )
      ) u_decoder (
        .i_address          (register_if.address  ),
        .i_access           (register_if.access   ),
        .i_additional_match (i_additional_match   ),
        .o_match            (match[g]             )
      );
    end
  endgenerate

  //  Request
  logic                   frontdoor_valid;
  logic                   backdoor_valid;
  logic                   pending_valid;
  logic [DATA_WIDTH-1:0]  mask[2];
  logic                   write[2];
  logic [DATA_WIDTH-1:0]  write_data[2];

  always_comb begin
    if (backdoor_valid) begin
      if (write[1]) begin
        bit_field_if.write_valid  = '1;
        bit_field_if.read_valid   = '0;
      end
      else begin
        bit_field_if.write_valid  = '0;
        bit_field_if.read_valid   = '1;
      end
      bit_field_if.mask         = mask[1];
      bit_field_if.write_data   = write_data[1];
    end
    else begin
      if (write[0]) begin
        bit_field_if.write_valid  = (frontdoor_valid || pending_valid);
        bit_field_if.read_valid   = '0;
      end
      else begin
        bit_field_if.write_valid  = '0;
        bit_field_if.read_valid   = (frontdoor_valid || pending_valid);
      end
      bit_field_if.mask         = mask[0];
      bit_field_if.write_data   = write_data[0];
    end
  end

  always_comb begin
    frontdoor_valid = active && register_if.valid;
    mask[0]         = get_mask(match, register_if.strobe);
    if (WRITABLE) begin
      write[0]      = register_if.access[RGGEN_ACCESS_DATA_BIT];
      write_data[0] = {WORDS{register_if.write_data}};
    end
    else begin
      write[0]      = '0;
      write_data[0] = '0;
    end
  end

  function automatic logic [DATA_WIDTH-1:0] get_mask(
    logic [WORDS-1:0]     match,
    logic [BUS_WIDTH-1:0] strobe
  );
    if (BUS_WIDTH == DATA_WIDTH) begin
      return strobe;
    end
    else begin
      logic [DATA_WIDTH-1:0]  mask;
      for (int i = 0;i < WORDS;++i) begin
        if (match[i]) begin
          mask[BUS_WIDTH*i+:BUS_WIDTH]  = strobe;
        end
        else begin
          mask[BUS_WIDTH*i+:BUS_WIDTH]  = '0;
        end
      end

      return mask;
    end
  endfunction

  //  Response
  logic [BUS_WIDTH-1:0] read_data;

  rggen_mux #(
    .WIDTH    (BUS_WIDTH  ),
    .ENTRIES  (WORDS      )
  ) u_read_data_mux (
    .i_select (match                  ),
    .i_data   (bit_field_if.read_data ),
    .o_data   (read_data              )
  );

  always_comb begin
    register_if.active    = active;
    register_if.ready     = !backdoor_valid;
    register_if.status    = RGGEN_OKAY;
    register_if.read_data = read_data;
    register_if.value     = VALUE_WIDTH'(bit_field_if.value);
  end

`ifdef RGGEN_ENABLE_BACKDOOR
  //  Backdoor access
  rggen_backdoor #(
    .DATA_WIDTH (DATA_WIDTH )
  ) u_backdoor (
    .i_clk              (i_clk                  ),
    .i_rst_n            (i_rst_n                ),
    .i_frontdoor_valid  (frontdoor_valid        ),
    .i_frontdoor_ready  (register_if.ready      ),
    .o_backdoor_valid   (backdoor_valid         ),
    .o_pending_valid    (pending_valid          ),
    .o_write            (write[1]               ),
    .o_mask             (mask[1]                ),
    .o_write_data       (write_data[1]          ),
    .i_read_data        (bit_field_if.read_data ),
    .i_value            (bit_field_if.value     )
  );
`else
  always_comb begin
    backdoor_valid  = '0;
    pending_valid   = '0;
    mask[1]         = '0;
    write[1]        = '0;
  end
`endif

`ifdef RGGEN_ENABLE_SVA
  ast_only_one_word_is_selected:
  assert property (
    @(posedge i_clk)
    (register_if.valid && (match != '0)) |-> $onehot(match)
  );
`endif
endmodule
