module rggen_bit_field_w01trg #(
  parameter bit TRIGGER_VALUE = '0,
  parameter int WIDTH         = 1
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic [WIDTH-1:0]     i_value,
  output  logic [WIDTH-1:0]     o_trigger
);
  logic [WIDTH-1:0] trigger;
  logic [WIDTH-1:0] assert_trigger;

  always_comb begin
    bit_field_if.read_data  = i_value;
    bit_field_if.value      = trigger;
    o_trigger               = trigger;
  end

  always_comb begin
    for (int i = 0;i < WIDTH;++i) begin
      assert_trigger[i] =
        bit_field_if.write_valid && bit_field_if.mask[i] &&
          (bit_field_if.write_data[i] == TRIGGER_VALUE);
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      trigger <= '0;
    end
    else begin
      for (int i = 0;i < WIDTH;++i) begin
        if (assert_trigger[i]) begin
          trigger[i]  <= '1;
        end
        else if (trigger[i]) begin
          trigger[i]  <= '0;
        end
      end
    end
  end
endmodule
