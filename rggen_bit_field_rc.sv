module rggen_bit_field_rc #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic [WIDTH-1:0]     i_set,
  input   logic [WIDTH-1:0]     i_mask,
  output  logic [WIDTH-1:0]     o_value,
  output  logic [WIDTH-1:0]     o_value_unmasked
);
  logic [WIDTH-1:0] value;

  assign  bit_field_if.read_data  = value & i_mask;
  assign  bit_field_if.value      = value;
  assign  o_value                 = value & i_mask;
  assign  o_value_unmasked        = value;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      value <= INITIAL_VALUE;
    end
    else if ((i_set != '0) || bit_field_if.valid) begin
      value <= get_next_value();
    end
  end

  function automatic logic [WIDTH-1:0] get_next_value();
    logic [WIDTH-1:0] read_mask;
    logic [WIDTH-1:0] clear;
    read_mask = bit_field_if.read_mask;
    clear     = (bit_field_if.valid) ? ~read_mask : '1;
    return (value & clear) | i_set;
  endfunction
endmodule
