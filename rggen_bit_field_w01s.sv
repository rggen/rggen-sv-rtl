module rggen_bit_field_w01s #(
  parameter bit             SET_VALUE     = 0,
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
    logic [WIDTH-1:0] write_data;
    logic [WIDTH-1:0] write_mask;
    logic [WIDTH-1:0] set;

    write_data  = bit_field_if.write_data;
    write_mask  = bit_field_if.write_mask;
    if (bit_field_if.valid) begin
      set = write_mask & ((SET_VALUE) ? write_mask : ~write_mask);
    end
    else begin
      set = '0;
    end

    return (value & (~i_clear)) | set;
  endfunction
endmodule
