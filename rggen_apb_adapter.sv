module rggen_apb_adapter #(
  parameter int ADDRESS_WIDTH = 8,
  parameter int BUS_WIDTH     = 32,
  parameter int REGISTERS     = 1
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_apb_if.slave      apb_if,
  rggen_register_if.host  register_if[REGISTERS]
);

endmodule
