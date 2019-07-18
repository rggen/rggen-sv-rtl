module rggen_indirect_register #(
  parameter bit                             READABLE              = 1,
  parameter bit                             WRITABLE              = 1,
  parameter int                             ADDRESS_WIDTH         = 8,
  parameter bit [ADDRESS_WIDTH-1:0]         OFFSET_ADDRESS        = '0,
  parameter int                             BUS_WIDTH             = 32,
  parameter int                             DATA_WIDTH            = BUS_WIDTH,
  parameter bit [DATA_WIDTH-1:0]            VALID_BITS            = '1,
  parameter int                             INDIRECT_INDEX_WIDTH  = 1,
  parameter bit [INDIRECT_INDEX_WIDTH-1:0]  INDIRECT_INDEX_VALUE  = '0
)(
  input logic                         i_clk,
  input logic                         i_rst_n,
  rggen_register_if.register          register_if,
  input logic [INDIRECT_INDEX_WIDTH]  i_indirect_index,
  rggen_bit_field_if.register         bit_field_if
);
endmodule
