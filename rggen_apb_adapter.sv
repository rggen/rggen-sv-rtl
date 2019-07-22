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
  rggen_bus_if #(ADDRESS_WIDTH, BUS_WIDTH)  bus_if();
  logic                                     valid_pready;

  assign  bus_if.valid      = (apb_if.psel && (!valid_pready)) ? '1 : '0;
  assign  bus_if.address    = apb_if.paddr;
  assign  bus_if.write      = apb_if.pwrite;
  assign  bus_if.write_data = apb_if.pwdata;
  assign  bus_if.strobe     = apb_if.pstrb;

  assign  valid_pready  = (apb_if.penable) ? apb_if.pready : '0;
  always_ff @(posedge i_clk , negedge i_rst_n) begin
    if (!i_rst_n) begin
      apb_if.pready <= '0;
    end
    else begin
      apb_if.pready <= bus_if.ready;
    end
  end

  always_ff @(posedge i_clk) begin
    if (bus_if.ready) begin
      apb_if.prdata   <= bus_if.read_data;
      apb_if.pslverr  <= bus_if.status[1];
    end
  end

  rggen_adapter_common #(
    .BUS_WIDTH  (BUS_WIDTH  ),
    .REGISTERS  (REGISTERS  )
  ) u_adapter_common (
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .bus_if       (bus_if       ),
    .register_if  (register_if  )
  );
endmodule
