module rggen_bit_field_rwc #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0,
  parameter bit             WRITE_FIRST   = 1
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic                 i_clear,
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
    else begin
      value <= get_next_value();
    end
  end

  function automatic logic [WIDTH-1:0] get_next_value();
    logic [WIDTH-1:0] write_data;
    logic [WIDTH-1:0] write_mask;
    logic             write_access;
    logic [1:0]       source_select;

    write_data    = bit_field_if.write_data;
    write_mask    = bit_field_if.write_mask;
    write_access  = (bit_field_if.valid) ? |write_mask : '0;

    if (WRITE_FIRST && write_access) begin
      source_select = {1'b0, 1'b1};
    end
    else if ((!WRITE_FIRST) && i_clear) begin
      source_select = {1'b1, 1'b0};
    end
    else begin
      source_select = {i_clear, write_access};
    end

    if (source_select[0]) begin
      return (write_data & write_mask) | (value & (~write_mask));
    end
    else if (source_select[1]) begin
      return INITIAL_VALUE;
    end
    else begin
      return value;
    end
  endfunction
endmodule
