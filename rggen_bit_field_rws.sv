module rggen_bit_field_rws #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic                 i_set,
  input   logic [WIDTH-1:0]     i_value,
  output  logic [WIDTH-1:0]     o_value
);
  logic [WIDTH-1:0] value;

  assign  bit_field_if.read_data  = value;
  assign  bit_field_if.value      = value;
  assign  o_value                 = value;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      value <= INITIAL_VALUE;
    end
    else if (i_set) begin
      value <= i_value;
    end
    else if (bit_field_if.valid) begin
      value <=
        (bit_field_if.write_data &   bit_field_if.write_mask ) |
        (value                   & (~bit_field_if.write_mask));
    end
  end
endmodule
