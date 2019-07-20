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

  genvar  i;
  genvar  j;

  //  Decode address
  logic [WORDS-1:0] match;

  generate for (i = 0;i < WORDS;++i) begin : g_decoder
    localparam  bit [ADDRESS_WIDTH-1:0]
      START_ADDRESS = OFFSET_ADDRESS
                    + DATA_BYTE_WIDTH * REGISTER_INDEX
                    + BUS_BYTE_WIDTH  * i;
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
      .o_match            (match[i]             )
    );
  end endgenerate

  //  Request
  logic                   backdoor_valid;
  logic [DATA_WIDTH-1:0]  read_mask[2];
  logic [DATA_WIDTH-1:0]  write_mask[2];
  logic [DATA_WIDTH-1:0]  write_data[2];

  assign  bit_field_if.valid      = (backdoor_valid || register_if.valid) ? '1 : '0;
  assign  bit_field_if.read_mask  = (backdoor_valid) ? read_mask[1]  : read_mask[0];
  assign  bit_field_if.write_mask = (backdoor_valid) ? write_mask[1] : write_mask[0];
  assign  bit_field_if.write_data = (backdoor_valid) ? write_data[1] : write_data[0];

  generate for (i = 0;i < WORDS;++i) begin : g_data_mask_expansion
    assign  read_mask[0][BUS_WIDTH*i+:BUS_WIDTH]  = (match[i] && (!register_if.write)) ? '1                           : '0;
    assign  write_mask[0][BUS_WIDTH*i+:BUS_WIDTH] = (match[i] &&   register_if.write ) ? get_mask(register_if.strobe) : '0;
    assign  write_data[0][BUS_WIDTH*i+:BUS_WIDTH] = register_if.write_data;
  end endgenerate

  function automatic logic [BUS_WIDTH-1:0] get_mask(logic [BUS_BYTE_WIDTH-1:0] strobe);
    logic [BUS_WIDTH-1:0] mask;
    for (int i = 0;i < BUS_BYTE_WIDTH;++i) begin
      mask[8*i+:8]  = {8{strobe[i]}};
    end
  endfunction

  //  Response
  logic                 active;
  logic [BUS_WIDTH-1:0] read_data[WORDS];

  assign  active              = (WORDS > 1) ? |match : match[0];
  assign  register_if.active  = active;
  assign  register_if.ready   = active;
  assign  register_if.status  = rggen_rtl_pkg::RGGEN_OKAY;

  generate for (i = 0;i < WORDS;++i) begin : g_data_collection
    for (j = 0;j < BUS_WIDTH;++j) begin : g
      localparam  int BIT = BUS_WIDTH * i + j;
      assign  read_data[i][j]         = (VALID_BITS[BIT]) ? bit_field_if.read_data[BIT] : '0;
      assign  register_if.value[BIT]  = (VALID_BITS[BIT]) ? bit_field_if.value[BIT]     : '0;
    end
  end endgenerate

  rggen_mux #(BUS_WIDTH, WORDS) u_read_data_mux();
  assign  register_if.read_data = u_read_data_mux.mux(match, read_data);

`ifdef RGGEN_ENABLE_BACKDOOR
  rggen_backdoor_if backdoor_if (i_clk, i_rst_n);
  assign  backdoor_valid  = backdoor_if.valid;
  assign  read_mask[1]    = backdoor_if.read_mask;
  assign  write_mask[1]   = backdoor_if.write_mask;
  assign  write_data[1]   = backdoor_if.write_data;
`else
  assign  backdoor_valid  = '0;
  assign  read_mask[1]    = '0;
  assign  write_mask[1]   = '0;
  assign  write_data[1]   = '0;
`endif
endmodule
