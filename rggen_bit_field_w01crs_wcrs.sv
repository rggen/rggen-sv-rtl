module rggen_bit_field_w01crs_wcrs #(
  parameter bit [1:0]       CLEAR_VALUE   = 2'b00,
  parameter int             WIDTH         = 1,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
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
    else if (bit_field_if.valid) begin
      value <= get_next_value();
    end
  end

  function automatic logic [WIDTH-1:0] get_next_value();
    logic [WIDTH-1:0] read_mask;
    logic [WIDTH-1:0] write_mask;
    logic [WIDTH-1:0] write_data;
    logic [WIDTH-1:0] clear;
    logic [WIDTH-1:0] set;

    read_mask   = bit_field_if.read_mask;
    write_mask  = bit_field_if.write_mask;
    write_data  = bit_field_if.write_data;

    clear = '0;
    set   = '0;
    if (read_mask != '0) begin
      set   = '1;
    end
    else if (write_mask != '0) begin
      case (CLEAR_VALUE)
        2'b00:    clear = write_mask & (~write_data);
        2'b01:    clear = write_mask &   write_data;
        default:  clear = '1;
      endcase
    end

    return (value & (~clear)) | set;
  endfunction
endmodule
