module rggen_external_register #(
  parameter int ADDRESS_WIDTH                     = 8,
  parameter int BUS_WIDTH                         = 32,
  parameter bit [ADDRESS_WIDTH-1:0] START_ADDRESS = '0,
  parameter bit [ADDRESS_WIDTH-1:0] END_ADDRESS   = '0
)(
  input logic                 i_clk,
  input logic                 i_rst_n,
  rggen_register_if.register  register_if,
  rggen_bus_if.master         bus_if
);
endmodule
