module rggen_bit_field_rs #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic [WIDTH-1:0]     i_clear,
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
    else if ((i_clear != '0) || bit_field_if.valid) begin
      value <= get_next_value();
    end
  end

  function automatic logic [WIDTH-1:0] get_next_value();
    logic [WIDTH-1:0] read_mask;
    logic [WIDTH-1:0] set;
    read_mask = bit_field_if.read_mask;
    set       = (bit_field_if.valid) ? read_mask : '0;
    return (value & (~i_clear)) | set;
  endfunction
endmodule
