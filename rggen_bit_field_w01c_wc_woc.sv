module rggen_bit_field_w01c_wc_woc #(
  parameter bit [1:0]       CLEAR_VALUE   = 2'b00,
  parameter bit             WRITE_ONLY    = 0,
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
  logic [WIDTH-1:0] value_masked;

  assign  bit_field_if.read_data  = (!WRITE_ONLY) ? value_masked : '0;
  assign  bit_field_if.value      = value;
  assign  o_value                 = value_masked;
  assign  o_value_unmasked        = value;

  assign  value_masked  = value & i_mask;
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      value <= INITIAL_VALUE;
    end
    else if ((i_set != '0) || bit_field_if.valid) begin
      value <= get_next_value();
    end
  end

  function automatic logic [WIDTH-1:0] get_next_value();
    logic             valid;
    logic [WIDTH-1:0] write_data;
    logic [WIDTH-1:0] write_mask;
    logic [WIDTH-1:0] clear;

    valid         = bit_field_if.valid;
    write_data    = bit_field_if.write_data;
    write_mask    = bit_field_if.write_mask;

    clear = '0;
    if (valid && (write_mask != '0)) begin
      case (CLEAR_VALUE)
        2'b00:    clear = write_mask & (~write_data);
        2'b01:    clear = write_mask &   write_data;
        default:  clear = '1;
      endcase
    end

    return (value & (~clear)) | i_set;
  endfunction
endmodule
