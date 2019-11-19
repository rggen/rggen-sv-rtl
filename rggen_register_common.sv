module rggen_register_common #(
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
  localparam  int WORDS           = DATA_WIDTH / BUS_WIDTH;
  localparam  int BUS_BYTE_WIDTH  = BUS_WIDTH / 8;
  localparam  int DATA_BYTE_WIDTH = DATA_WIDTH / 8;
  localparam  int ADDRESS_LSB     = $clog2(BUS_BYTE_WIDTH);

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
      .i_write            (register_if.write    ),
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
  assign  read_mask[0]    = get_read_mask(match, register_if.write);
  assign  write_mask[0]   = get_write_mask(match, register_if.write, register_if.strobe);
  assign  write_data[0]   = (WRITABLE) ? {WORDS{register_if.write_data}} : '0;

  function automatic logic [DATA_WIDTH-1:0] get_read_mask(
    logic [WORDS-1:0] match,
    logic             write
  );
    logic [DATA_WIDTH-1:0]  mask;

    if (READABLE) begin
      for (int i = 0;i < WORDS;++i) begin
        mask[BUS_WIDTH*i+:BUS_WIDTH]  = (match[i] && (!write)) ? {BUS_WIDTH{1'b1}} : {BUS_WIDTH{1'b0}};
      end
    end
    else begin
      mask  = '0;
    end

    return mask;
  endfunction

  function automatic logic [DATA_WIDTH-1:0] get_write_mask(
    logic [WORDS-1:0]           match,
    logic                       write,
    logic [BUS_BYTE_WIDTH-1:0]  strobe
  );
    logic [DATA_WIDTH-1:0]  mask;

    if (WRITABLE) begin
      for (int i = 0;i < WORDS;++i) begin
        mask[BUS_WIDTH*i+:BUS_WIDTH]  = (match[i] && write) ? expand_strobe(strobe) : {BUS_WIDTH{1'b0}};
      end
    end
    else begin
      mask  = '0;
    end

    return mask;
  endfunction

  function automatic logic [BUS_WIDTH-1:0] expand_strobe(logic [BUS_BYTE_WIDTH-1:0] strobe);
    logic [BUS_WIDTH-1:0] mask;
    for (int i = 0;i < BUS_BYTE_WIDTH;++i) begin
      mask[8*i+:8]  = {8{strobe[i]}};
    end
    return mask;
  endfunction

  //  Response
  typedef logic [BUS_WIDTH-1:0] read_data_array[WORDS];

  read_data_array               read_data;
  rggen_mux #(BUS_WIDTH, WORDS) u_read_data_mux();

  assign  read_data             = collect_valid_read_data_bits(bit_field_if.read_data);
  assign  register_if.active    = active;
  assign  register_if.ready     = (!backdoor_valid) ? active : '0;
  assign  register_if.status    = rggen_rtl_pkg::RGGEN_OKAY;
  assign  register_if.read_data = (READABLE) ? u_read_data_mux.mux(match, read_data) : '0;
  assign  register_if.value     = collect_valid_value_bits(bit_field_if.value);

  function automatic logic [DATA_WIDTH-1:0] collect_valid_value_bits(
    logic [DATA_WIDTH-1:0]  raw_value
  );
    logic [DATA_WIDTH-1:0]  value;
    for (int i = 0;i < DATA_WIDTH;++i) begin
      value[i]  = (VALID_BITS[i]) ? raw_value[i] : 1'b0;
    end
    return value;
  endfunction

  function automatic read_data_array collect_valid_read_data_bits(
    logic [DATA_WIDTH-1:0]  raw_read_data
  );
    read_data_array read_data;

    if (READABLE) begin
      for (int i = 0;i < WORDS;++i) begin
        for (int j = 0;j < BUS_WIDTH;++j) begin
          read_data[i][j] = (VALID_BITS[BUS_WIDTH*i+j]) ? raw_read_data[BUS_WIDTH*i+j] : 1'b0;
        end
      end
    end
    else begin
      read_data = '{ default: {BUS_WIDTH{1'b0}} };
    end

    return read_data;
  endfunction

`ifdef RGGEN_ENABLE_BACKDOOR
  //  Backdoor access
  rggen_backdoor_if backdoor_if (i_clk, i_rst_n);
  assign  backdoor_valid        = backdoor_if.valid;
  assign  read_mask[1]          = backdoor_if.read_mask;
  assign  write_mask[1]         = backdoor_if.write_mask;
  assign  write_data[1]         = backdoor_if.write_data;
  assign  backdoor_if.read_data = bit_field_if.read_data;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      pending_valid <= '0;
    end
    else if (register_if.ready) begin
      pending_valid <= '0;
    end
    else if (backdoor_valid && frontdoor_valid) begin
      pending_valid <= '1;
    end
  end
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
    (match != '0) |-> $onehot(match)
  );
`endif
endmodule
