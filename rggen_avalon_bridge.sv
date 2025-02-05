module rggen_avalon_bridge
  import  rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 16,
  parameter bit READ_STROBE   = 1
)(
  input var             i_clk,
  input var             i_rst_n,
  rggen_bus_if.slave    bus_if,
  rggen_avalon_if.host  avalon_if
);
`ifndef SYNTHESIS
  initial begin
    assume (ADDRESS_WIDTH == avalon_if.ADDRESS_WIDTH);
  end
`endif

  logic request_done;

  always_comb begin
    if (bus_if.access == RGGEN_READ) begin
      avalon_if.read        = bus_if.valid && (!request_done);
      avalon_if.write       = '0;
      avalon_if.byteenable  = (READ_STROBE) ? bus_if.strobe : '1;
    end
    else begin
      avalon_if.read        = '0;
      avalon_if.write       = bus_if.valid && (!request_done);
      avalon_if.byteenable  = bus_if.strobe;
    end
    avalon_if.address   = ADDRESS_WIDTH'(bus_if.address);
    avalon_if.writedata = bus_if.write_data;
  end

  always_comb begin
    bus_if.ready      = avalon_if.readdatavalid || avalon_if.writeresponsevalid;
    bus_if.status     = rggen_status'(avalon_if.response);
    bus_if.read_data  = avalon_if.readdata;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      request_done  <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      request_done  <= '0;
    end
    else if (avalon_if.read || avalon_if.write) begin
      request_done  <= !avalon_if.waitrequest;
    end
  end
endmodule
