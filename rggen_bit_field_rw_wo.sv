module rggen_bit_field_rw_wo #(
  parameter int             WIDTH         = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0,
  parameter bit             WRITE_ONLY    = 0,
  parameter bit             WRITE_ONCE    = 0
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  output  logic [WIDTH-1:0]     o_value
);
  logic [WIDTH-1:0] value;
  logic             written;

  assign  bit_field_if.value  = value;
  assign  o_value             = value;
  generate if (!WRITE_ONLY) begin : g_readable
    assign  bit_field_if.read_data  = value;
  end
  else begin : g_write_only
    assign  bit_field_if.read_data  = '0;
  end endgenerate

  generate if (WRITE_ONCE) begin : g_write_once
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        written <= '0;
      end
      else if (bit_field_if.valid) begin
        if (bit_field_if.write_mask != '0) begin
          written <= '1;
        end
      end
    end
  end
  else begin : g_write_any_times
    assign  written = '0;
  end endgenerate

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      value <= INITIAL_VALUE;
    end
    else if (bit_field_if.valid && (!written)) begin
      value <=
        (bit_field_if.write_data &   bit_field_if.write_mask ) |
        (value                   & (~bit_field_if.write_mask));
    end
  end
endmodule
