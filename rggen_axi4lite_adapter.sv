module rggen_axi4lite_adapter #(
  parameter int ADDRESS_WIDTH = 8,
  parameter int BUS_WIDTH     = 32,
  parameter int REGISTERS     = 1,
  parameter bit WRITE_FIRST   = 1
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_axi4lite_if.slave axi4lite_if,
  rggen_register_if.host  register_if[REGISTERS]
);

endmodule
