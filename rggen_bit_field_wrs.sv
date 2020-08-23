module rggen_bit_field_wrs #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  output  logic [WIDTH-1:0]     o_value
);
  logic [WIDTH-1:0] value;

  assign  bit_field_if.value      = value;
  assign  bit_field_if.read_data  = value;
  assign  o_value                 = value;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      value <= INITIAL_VALUE;
    end
    else if (bit_field_if.valid) begin
      if (bit_field_if.read_mask != '0) begin
        value <= '1;
      end
      else begin
        value <=
          (bit_field_if.write_data &   bit_field_if.write_mask ) |
          (value                   & (~bit_field_if.write_mask));
      end
    end
  end
endmodule
