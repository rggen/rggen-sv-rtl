module rggen_external_register #(
  parameter int 　　　　　　　　　　　ADDRESS_WIDTH = 8,
  parameter int 　　　　　　　　　　　BUS_WIDTH     = 32,
  parameter bit [ADDRESS_WIDTH-1:0] START_ADDRESS = '0,
  parameter bit [ADDRESS_WIDTH-1:0] END_ADDRESS   = '0
)(
  input logic                 i_clk,
  input logic                 i_rst_n,
  rggen_register_if.register  register_if,
  rggen_bus_if.master         bus_if
);
  //  Decode address
  localparam  int ADDRESS_LSB = $clog2(BUS_WIDTH) - 3;

  logic match;
  rggen_address_decoder #(
    .READABLE       (1'b1           ),
    .WRITABLE       (1'b1           ),
    .WIDTH          (ADDRESS_WIDTH  ),
    .LSB            (ADDRESS_LSB    ),
    .START_ADDRESS  (START_ADDRESS  ),
    .END_ADDRESS    (END_ADDRESS    )
  ) u_decoder (
    .i_address          (register_if.address  ),
    .i_write            (register_if.write    ),
    .i_additional_match (1'b1                 ),
    .o_match            (match                )
  );

  //  Request
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      bus_if.valid  <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      bus_if.valid  <= '0;
    end
    else if (register_if.valid && match) begin
      bus_if.valid  <= '1;
    end
  end

  always_ff @(posedge i_clk) begin
    if (register_if.valid && match) begin
      bus_if.address    <= register_if.address;
      bus_if.write      <= register_if.write;
      bus_if.write_data <= register_if.write_data;
      bus_if.strobe     <= register_if.strobe;
    end
  end

  //  Response
  assign  register_if.active    = match;
  assign  register_if.ready     = (bus_if.valid) ? bus_if.ready : '0;
  assign  register_if.status    = bus_if.status;
  assign  register_if.read_data = bus_if.read_data;
  assign  register_if.value     = bus_if.read_data;
endmodule
