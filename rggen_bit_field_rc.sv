module rggen_bit_field_rc #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic [WIDTH-1:0]     i_set,
  input   logic [WIDTH-1:0]     i_mask,
  output  logic [WIDTH-1:0]     o_value,
  output  logic [WIDTH-1:0]     o_value_unmasked
);
endmodule
