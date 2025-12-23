module rggen_bit_field_counter
  import  rggen_rtl_pkg::*;
#(
  parameter int             WIDTH           = 8,
  parameter bit [WIDTH-1:0] INITIAL_VALUE   = '0,
  parameter int             UP_WIDTH        = 1,
  parameter int             DOWN_WIDTH      = 1,
  parameter bit             WRAP_AROUND     = 0,
  parameter bit             USE_CLEAR       = 1,
  parameter int             UP_PORT_WIDTH   = rggen_clip_width(UP_WIDTH),
  parameter int             DOWN_PORT_WIDTH = rggen_clip_width(DOWN_WIDTH)
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  rggen_bit_field_if.bit_field      bit_field_if,
  input   var                       i_clear,
  input   var [UP_PORT_WIDTH-1:0]   i_up,
  input   var [DOWN_PORT_WIDTH-1:0] i_down,
  output  var [WIDTH-1:0]           o_count
);
  logic [WIDTH-1:0]           count;
  logic [UP_PORT_WIDTH-1:0]   up;
  logic [DOWN_PORT_WIDTH-1:0] down;

  always_comb begin
    bit_field_if.value      = count;
    bit_field_if.read_data  = count;
    o_count                 = count;
  end

  always_comb begin
    if (UP_WIDTH > 0) begin
      up  = i_up;
    end
    else begin
      up  = '0;
    end

    if (DOWN_WIDTH > 0) begin
      down  = i_down;
    end
    else begin
      down  = '0;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      count <= INITIAL_VALUE;
    end
    else if (USE_CLEAR && i_clear) begin
      count <= INITIAL_VALUE;
    end
    else if (bit_field_if.write_valid) begin
      for (int i = 0;i < WIDTH;++i) begin
        if (bit_field_if.mask[i]) begin
          count[i]  <= bit_field_if.write_data[i];
        end
      end
    end
    else if ((up != '0) || (down != '0)) begin
      if (WRAP_AROUND) begin
        count <= calc_count_next_simple(count, up, down);
      end
      else begin
        count <= calc_count_next(count, up, down);
      end
    end
  end

  function automatic logic [WIDTH-1:0] calc_count_next_simple(
    logic [WIDTH-1:0]           count,
    logic [UP_PORT_WIDTH-1:0]   up,
    logic [DOWN_PORT_WIDTH-1:0] down
  );
    localparam  int UP_VALUE_WIDTH    = rggen_clip_width($clog2(UP_WIDTH + 1));
    localparam  int DOWN_VALUE_WIDTH  = rggen_clip_width($clog2(DOWN_WIDTH + 1));

    logic [UP_VALUE_WIDTH-1:0]    up_value;
    logic [DOWN_VALUE_WIDTH-1:0]  down_value;

    up_value  = UP_VALUE_WIDTH'(0);
    for (int i = 0;i < UP_WIDTH;++i) begin
      if (up[i]) begin
        up_value  = up_value + UP_VALUE_WIDTH'(1);
      end
    end

    down_value  = DOWN_VALUE_WIDTH'(0);
    for (int i = 0;i < DOWN_WIDTH;++i) begin
      down_value  = down_value + DOWN_VALUE_WIDTH'(1);
    end

    return count + WIDTH'(up_value) - WIDTH'(down_value);
  endfunction

  function automatic logic [WIDTH-1:0] calc_count_next(
    logic [WIDTH-1:0]           count,
    logic [UP_PORT_WIDTH-1:0]   up,
    logic [DOWN_PORT_WIDTH-1:0] down
  );
    localparam  int             UP_DOWN_WIDTH       = (UP_WIDTH > DOWN_WIDTH) ? UP_WIDTH : DOWN_WIDTH;
    localparam  int             UP_DOWN_VALUE_WIDTH = rggen_clip_width($clog2(UP_DOWN_WIDTH + 1)) + 1;
    localparam  int             COUNT_NEXT_WIDTH    = WIDTH + 1;
    localparam  bit [WIDTH-1:0] MAX_VALUE           = '1;
    localparam  bit [WIDTH-1:0] MIN_VALUE           = '0;

    logic [UP_DOWN_VALUE_WIDTH-1:0] up_down_value;
    logic [COUNT_NEXT_WIDTH-1:0]    count_next;

    up_down_value = UP_DOWN_VALUE_WIDTH'(0);
    for (int i = 0;i < UP_DOWN_WIDTH;++i) begin
      logic [1:0] up_down;

      up_down[1]  = (i < UP_WIDTH  ) && up[i];
      up_down[0]  = (i < DOWN_WIDTH) && down[i];

      case (up_down)
        2'b10:    up_down_value = up_down_value + UP_DOWN_VALUE_WIDTH'(1);
        2'b01:    up_down_value = up_down_value - UP_DOWN_VALUE_WIDTH'(1);
        default:  up_down_value = up_down_value;
      endcase
    end

    count_next  =
      COUNT_NEXT_WIDTH'(count) +
      {{(COUNT_NEXT_WIDTH-UP_DOWN_VALUE_WIDTH){up_down_value[UP_DOWN_VALUE_WIDTH-1]}}, up_down_value};
    if (!count_next[COUNT_NEXT_WIDTH-1]) begin
      return count_next[0+:WIDTH];
    end
    else if (up_down_value[UP_DOWN_VALUE_WIDTH-1]) begin
      //  underflow
      return MIN_VALUE;
    end
    else begin
      // overflow
      return MAX_VALUE;
    end
  endfunction
endmodule
