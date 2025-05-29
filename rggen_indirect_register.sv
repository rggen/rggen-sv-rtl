module rggen_indirect_register #(
  parameter bit                     READABLE              = 1,
  parameter bit                     WRITABLE              = 1,
  parameter int                     ADDRESS_WIDTH         = 8,
  parameter bit [ADDRESS_WIDTH-1:0] OFFSET_ADDRESS        = '0,
  parameter int                     BUS_WIDTH             = 32,
  parameter int                     DATA_WIDTH            = BUS_WIDTH,
  parameter int                     VALUE_WIDTH           = BUS_WIDTH,
  parameter int                     INDIRECT_MATCH_WIDTH  = 1
)(
  input logic                             i_clk,
  input logic                             i_rst_n,
  rggen_register_if.register              register_if,
  input logic [INDIRECT_MATCH_WIDTH-1:0]  i_indirect_match,
  rggen_bit_field_if.register             bit_field_if
);
  logic index_matched;

  always_comb begin
    index_matched = i_indirect_match == '1;
  end

  rggen_register_common #(
    .READABLE             (READABLE       ),
    .WRITABLE             (WRITABLE       ),
    .ADDRESS_WIDTH        (ADDRESS_WIDTH  ),
    .OFFSET_ADDRESS       (OFFSET_ADDRESS ),
    .BUS_WIDTH            (BUS_WIDTH      ),
    .DATA_WIDTH           (DATA_WIDTH     ),
    .VALUE_WIDTH          (VALUE_WIDTH    ),
    .USE_ADDITIONAL_MATCH (1              )
  ) u_register_common (
    .i_clk              (i_clk          ),
    .i_rst_n            (i_rst_n        ),
    .register_if        (register_if    ),
    .i_additional_match (index_matched  ),
    .bit_field_if       (bit_field_if   )
  );
endmodule
