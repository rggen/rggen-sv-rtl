module rggen_maskable_register #(
  parameter bit                     READABLE        = 1,
  parameter bit                     WRITABLE        = 1,
  parameter int                     ADDRESS_WIDTH   = 8,
  parameter bit [ADDRESS_WIDTH-1:0] OFFSET_ADDRESS  = '0,
  parameter int                     BUS_WIDTH       = 32,
  parameter int                     DATA_WIDTH      = BUS_WIDTH,
  parameter int                     VALUE_WIDTH     = BUS_WIDTH
)(
  input logic                 i_clk,
  input logic                 i_rst_n,
  rggen_register_if.register  register_if,
  rggen_bit_field_if.register bit_field_if
);
  import rggen_rtl_pkg::RGGEN_ACCESS_DATA_BIT;

  localparam  int HALF_WIDTH  = BUS_WIDTH / 2;

  logic [HALF_WIDTH-1:0]  write_data;
  logic [HALF_WIDTH-1:0]  strobe;
  logic [HALF_WIDTH-1:0]  write_data_mask;
  logic [BUS_WIDTH-1:0]   mask;

  always_comb begin
    write_data  = register_if.write_data[1*HALF_WIDTH+:HALF_WIDTH];
    strobe      = register_if.strobe[1*HALF_WIDTH+:HALF_WIDTH];
    if (register_if.access[RGGEN_ACCESS_DATA_BIT]) begin
      write_data_mask = write_data & strobe;
    end
    else begin
      write_data_mask = '1;
    end

    mask  = {HALF_WIDTH'(0), write_data_mask};
  end

  rggen_register_common #(
    .READABLE             (READABLE       ),
    .WRITABLE             (WRITABLE       ),
    .ADDRESS_WIDTH        (ADDRESS_WIDTH  ),
    .OFFSET_ADDRESS       (OFFSET_ADDRESS ),
    .BUS_WIDTH            (BUS_WIDTH      ),
    .DATA_WIDTH           (DATA_WIDTH     ),
    .VALUE_WIDTH          (VALUE_WIDTH    ),
    .USE_ADDITIONAL_MASK  (1'b1           )
  ) u_register_common (
    .i_clk              (i_clk        ),
    .i_rst_n            (i_rst_n      ),
    .register_if        (register_if  ),
    .i_additional_match (1'b1         ),
    .i_additional_mask  (mask         ),
    .bit_field_if       (bit_field_if )
  );
endmodule
