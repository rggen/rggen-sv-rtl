module rggen_register_common
  import  rggen_rtl_pkg::*;
#(
  parameter bit                     READABLE        = 1,
  parameter bit                     WRITABLE        = 1,
  parameter int                     ADDRESS_WIDTH   = 8,
  parameter bit [ADDRESS_WIDTH-1:0] OFFSET_ADDRESS  = '0,
  parameter int                     BUS_WIDTH       = 32,
  parameter int                     DATA_WIDTH      = BUS_WIDTH,
  parameter bit [DATA_WIDTH-1:0]    VALID_BITS      = '1,
  parameter int                     REGISTER_INDEX  = 0
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
  localparam  int ADDRESS_LSB       = $clog2(BUS_BYTE_WIDTH);
  localparam  int WORD_INDEX_WIDTH  = (WORDS >= 2) ? $clog2(WORDS) : 1;

  genvar  g;

  //  Decode address
  logic [WORDS-1:0] match;
  logic             active;

  assign  active  = |{1'b0, match};

  generate for (g = 0;g < WORDS;++g) begin : g_decoder
    localparam  bit [ADDRESS_WIDTH-1:0]
      START_ADDRESS = OFFSET_ADDRESS
                    + DATA_BYTE_WIDTH * REGISTER_INDEX
                    + BUS_BYTE_WIDTH  * g;
    localparam  bit [ADDRESS_WIDTH-1:0]
      END_ADDRESS = START_ADDRESS + BUS_BYTE_WIDTH - 1;

    rggen_address_decoder #(
      .READABLE       (READABLE       ),
      .WRITABLE       (WRITABLE       ),
      .WIDTH          (ADDRESS_WIDTH  ),
      .LSB            (ADDRESS_LSB    ),
      .START_ADDRESS  (START_ADDRESS  ),
      .END_ADDRESS    (END_ADDRESS    )
    ) u_decoder (
      .i_address          (register_if.address  ),
      .i_access           (register_if.access   ),
      .i_additional_match (i_additional_match   ),
      .o_match            (match[g]             )
    );
  end endgenerate

  //  Request
  logic                   frontdoor_valid;
  logic                   backdoor_valid;
  logic                   pending_valid;
  logic [DATA_WIDTH-1:0]  read_mask[2];
  logic [DATA_WIDTH-1:0]  write_mask[2];
  logic [DATA_WIDTH-1:0]  write_data[2];

  assign  bit_field_if.valid      = (frontdoor_valid || backdoor_valid || pending_valid) ? '1 : '0;
  assign  bit_field_if.read_mask  = (backdoor_valid) ? read_mask[1]  : read_mask[0];
  assign  bit_field_if.write_mask = (backdoor_valid) ? write_mask[1] : write_mask[0];
  assign  bit_field_if.write_data = (backdoor_valid) ? write_data[1] : write_data[0];

  assign  frontdoor_valid = (active) ? register_if.valid : '0;
  assign  read_mask[0]    = get_mask(1'b0, READABLE, match, register_if.access, {BUS_BYTE_WIDTH{1'b1}});
  assign  write_mask[0]   = get_mask(1'b1, WRITABLE, match, register_if.access, register_if.strobe    );
  assign  write_data[0]   = (WRITABLE) ? {WORDS{register_if.write_data}} : '0;

  function automatic logic [DATA_WIDTH-1:0] get_mask(
    logic                       write_access,
    logic                       accessible,
    logic [WORDS-1:0]           match,
    rggen_access                access,
    logic [BUS_BYTE_WIDTH-1:0]  strobe
  );
    logic [DATA_WIDTH-1:0]  mask;

    for (int i = 0;i < WORDS;++i) begin
      for (int j = 0;j < BUS_BYTE_WIDTH;++j) begin
        mask[i*BUS_WIDTH+8*j+:8] = (
          accessible && (access[RGGEN_ACCESS_DATA_BIT] == write_access) && match[i]
        ) ? {8{strobe[j]}} : '0;
      end
    end

    return mask;
  endfunction

  //  Response
  logic [WORD_INDEX_WIDTH-1:0]  word_index;

  assign  register_if.active    = active;
  assign  register_if.ready     = (!backdoor_valid) ? active : '0;
  assign  register_if.status    = RGGEN_OKAY;
  assign  register_if.read_data = get_read_data(word_index, bit_field_if.read_data);
  assign  register_if.value     = get_valid_value(bit_field_if.value);

  rggen_onehot #(WORDS) u_onehot();
  assign  word_index  = u_onehot.to_binary(match);

  function automatic logic [BUS_WIDTH-1:0] get_read_data(
    logic [WORD_INDEX_WIDTH-1:0]  word_index,
    logic [DATA_WIDTH-1:0]        read_data
  );
    if (READABLE) begin
      logic [BUS_WIDTH-1:0] data[WORDS];

      for (int i = 0;i < WORDS;++i) begin
        for (int j = 0;j < BUS_WIDTH;++j) begin
          data[i][j]  = (
            VALID_BITS[BUS_WIDTH*i+j]
          ) ? read_data[BUS_WIDTH*i+j] : '0;
        end
      end

      return data[word_index];
    end
    else begin
      return '0;
    end
  endfunction

  function automatic logic [DATA_WIDTH-1:0] get_valid_value(
    logic [DATA_WIDTH-1:0]  raw_value
  );
    logic [DATA_WIDTH-1:0]  value;
    for (int i = 0;i < DATA_WIDTH;++i) begin
      value[i]  = (VALID_BITS[i]) ? raw_value[i] : 1'b0;
    end
    return value;
  endfunction

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
    .o_read_mask        (read_mask[1]           ),
    .o_write_mask       (write_mask[1]          ),
    .o_write_data       (write_data[1]          ),
    .i_read_data        (bit_field_if.read_data ),
    .i_value            (bit_field_if.value     )
  );
`else
  assign  backdoor_valid  = '0;
  assign  pending_valid   = '0;
  assign  read_mask[1]    = '0;
  assign  write_mask[1]   = '0;
  assign  write_data[1]   = '0;
`endif

`ifdef RGGEN_ENABLE_SVA
  ast_only_one_word_is_selected:
  assert property (
    @(posedge i_clk)
    (register_if.valid && (match != '0)) |-> $onehot(match)
  );
`endif
endmodule
