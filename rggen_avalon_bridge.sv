module rggen_avalon_bridge
  import  rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 16,
  parameter bit READ_STROBE   = 1
)(
  rggen_bus_if.slave    bus_if,
  rggen_avalon_if.host  avalon_if
);
`ifndef SYNTHESIS
  initial begin
    assume (ADDRESS_WIDTH == avalon_if.ADDRESS_WIDTH);
  end
`endif

  always_comb begin
    avalon_if.read        = bus_if.valid && (bus_if.access == RGGEN_READ);
    avalon_if.write       = bus_if.valid && (bus_if.access != RGGEN_READ);
    avalon_if.address     = ADDRESS_WIDTH'(bus_if.address);
    avalon_if.byteenable  = ((bus_if.access != RGGEN_READ) || READ_STROBE) ? bus_if.strobe : '1;
    avalon_if.writedata   = bus_if.write_data;
  end

  always_comb begin
    bus_if.ready      = bus_if.valid && (!avalon_if.waitrequest);
    bus_if.status     = rggen_status'(avalon_if.response);
    bus_if.read_data  = avalon_if.readdata;
  end
endmodule
