module rggen_bit_field
  import  rggen_rtl_pkg::*;
#(
  parameter int                 WIDTH                     = 8,
  parameter bit [WIDTH-1:0]     INITIAL_VALUE             = '0,
  parameter rggen_sw_hw_access  PRECEDENCE_ACCESS         = RGGEN_SW_ACCESS,
  parameter rggen_sw_action     SW_READ_ACTION            = RGGEN_READ_DEFAULT,
  parameter rggen_sw_action     SW_WRITE_ACTION           = RGGEN_WRITE_DEFAULT,
  parameter bit                 SW_WRITE_ONCE             = '0,
  parameter rggen_polarity      SW_WRITE_ENABLE_POLARITY  = RGGEN_ACTIVE_HIGH,
  parameter rggen_polarity      HW_WRITE_ENABLE_POLARITY  = RGGEN_ACTIVE_HIGH,
  parameter int                 HW_SET_WIDTH              = WIDTH,
  parameter int                 HW_CLEAR_WIDTH            = WIDTH,
  parameter bit                 STORAGE                   = '1
)(
  input   logic                       i_clk,
  input   logic                       i_rst_n,
  rggen_bit_field_if.bit_field        bit_field_if,
  input   logic                       i_sw_write_enable,
  input   logic                       i_hw_write_enable,
  input   logic [WIDTH-1:0]           i_hw_write_data,
  input   logic [HW_SET_WIDTH-1:0]    i_hw_set,
  input   logic [HW_CLEAR_WIDTH-1:0]  i_hw_clear,
  input   logic [WIDTH-1:0]           i_value,
  input   logic [WIDTH-1:0]           i_mask,
  output  logic [WIDTH-1:0]           o_value,
  output  logic [WIDTH-1:0]           o_value_unmasked
);
//--------------------------------------------------------------
//  Utility functions
//--------------------------------------------------------------
  function automatic logic [1:0] get_sw_update(
    logic             valid,
    logic [WIDTH-1:0] read_mask,
    logic             write_enable,
    logic [WIDTH-1:0] write_mask,
    logic             write_done
  );
    logic [1:0] action;
    logic [1:0] access;
    logic [1:0] update;

    action[0] = (SW_READ_ACTION  == RGGEN_READ_CLEAR) ||
                (SW_READ_ACTION  == RGGEN_READ_SET  );
    action[1] = (SW_WRITE_ACTION != RGGEN_WRITE_NONE);

    access[0] = (read_mask  != '0);
    access[1] = (write_mask != '0)  && write_enable && (!write_done);

    update[0] = valid && action[0] && access[0];
    update[1] = valid && action[1] && access[1];
    return update;
  endfunction

  function automatic logic get_hw_update(
    logic                       write_enable,
    logic [HW_SET_WIDTH-1:0]    set,
    logic [HW_CLEAR_WIDTH-1:0]  clear
  );
    logic update;
    update  = write_enable || (set != '0) || (clear != '0);
    return update;
  endfunction

  function automatic logic [WIDTH-1:0] get_next_value(
    logic [WIDTH-1:0]           current_value,
    logic [1:0]                 sw_update,
    logic [WIDTH-1:0]           sw_write_mask,
    logic [WIDTH-1:0]           sw_write_data,
    logic                       hw_write_enable,
    logic [WIDTH-1:0]           hw_write_data,
    logic [HW_SET_WIDTH-1:0]    hw_set,
    logic [HW_CLEAR_WIDTH-1:0]  hw_clear
  );
    logic [WIDTH-1:0] value;

    if (PRECEDENCE_ACCESS == RGGEN_SW_ACCESS) begin
      value =
        get_hw_next_value(
          current_value, hw_write_enable, hw_write_data,
          hw_set, hw_clear
        );
      value =
        get_sw_next_value(
          value, sw_update, sw_write_mask, sw_write_data
        );
    end
    else begin
      value =
        get_sw_next_value(
          current_value, sw_update, sw_write_mask, sw_write_data
        );
      value =
        get_hw_next_value(
          value, hw_write_enable, hw_write_data,
          hw_set, hw_clear
        );
    end

    return value;
  endfunction

  function automatic logic [WIDTH-1:0] get_sw_next_value(
    logic [WIDTH-1:0] current_value,
    logic [1:0]       update,
    logic [WIDTH-1:0] write_mask,
    logic [WIDTH-1:0] write_data
  );
    logic [WIDTH-1:0] value[2];
    logic [WIDTH-1:0] masked_data[2];

    case (SW_READ_ACTION)
      RGGEN_READ_CLEAR: value[0]  = '0;
      RGGEN_READ_SET:   value[0]  = '1;
      default:          value[0]  = current_value;
    endcase

    masked_data[0]  = write_mask & (~write_data);
    masked_data[1]  = write_mask & ( write_data);
    case (SW_WRITE_ACTION)
      RGGEN_WRITE_DEFAULT:  value[1]  = (current_value & (~write_mask)) | masked_data[1];
      RGGEN_WRITE_0_CLEAR:  value[1]  = current_value & (~masked_data[0]);
      RGGEN_WRITE_1_CLEAR:  value[1]  = current_value & (~masked_data[1]);
      RGGEN_WRITE_CLEAR:    value[1]  = '0;
      RGGEN_WRITE_0_SET:    value[1]  = current_value | masked_data[0];
      RGGEN_WRITE_1_SET:    value[1]  = current_value | masked_data[1];
      RGGEN_WRITE_SET:      value[1]  = '1;
      RGGEN_WRITE_0_TOGGLE: value[1]  = current_value ^ masked_data[0];
      RGGEN_WRITE_1_TOGGLE: value[1]  = current_value ^ masked_data[1];
      default:              value[1]  = current_value;
    endcase

    if (update[0]) begin
      return value[0];
    end
    else if (update[1]) begin
      return value[1];
    end
    else begin
      return current_value;
    end
  endfunction

  function automatic logic [WIDTH-1:0] get_hw_next_value(
    logic [WIDTH-1:0]           current_value,
    logic                       write_enable,
    logic [WIDTH-1:0]           write_data,
    logic [HW_SET_WIDTH-1:0]    set,
    logic [HW_CLEAR_WIDTH-1:0]  clear
  );
    logic [WIDTH-1:0] set_clear[2];
    logic [WIDTH-1:0] value;

    if (HW_SET_WIDTH == WIDTH) begin
      set_clear[0][HW_SET_WIDTH-1:0]  = set;
    end
    else begin
      set_clear[0]  = {WIDTH{set[0]}};
    end

    if (HW_CLEAR_WIDTH == WIDTH) begin
      set_clear[1][HW_CLEAR_WIDTH-1:0]  = clear;
    end
    else begin
      set_clear[1]  = {WIDTH{clear[0]}};
    end

    value = (write_enable) ? write_data : current_value;
    value = (value & (~set_clear[1])) | set_clear[0];

    return value;
  endfunction

//--------------------------------------------------------------
//  Body
//--------------------------------------------------------------
  localparam  bit SW_READABLE = SW_READ_ACTION != RGGEN_READ_NONE;

  logic [WIDTH-1:0] value;
  logic [WIDTH-1:0] value_masked;
  logic [WIDTH-1:0] read_data;

  assign  bit_field_if.read_data  = read_data;
  assign  bit_field_if.value      = value;
  assign  o_value                 = value_masked;
  assign  o_value_unmasked        = value;

  assign  value_masked  = value & i_mask;
  assign  read_data     = (SW_READABLE) ? value_masked : '0;

  generate if (STORAGE) begin : g
    logic             sw_write_enable;
    logic [1:0]       sw_update;
    logic             sw_write_done;
    logic             hw_write_enable;
    logic             hw_update;
    logic [WIDTH-1:0] value_next;

    assign  sw_write_enable = i_sw_write_enable == SW_WRITE_ENABLE_POLARITY;
    assign  hw_write_enable = i_hw_write_enable == HW_WRITE_ENABLE_POLARITY;

    assign  sw_update =
      get_sw_update(
        bit_field_if.valid, bit_field_if.read_mask,
        sw_write_enable, bit_field_if.write_mask, sw_write_done
      );
    assign  hw_update =
      get_hw_update(hw_write_enable, i_hw_set, i_hw_clear);

    if (SW_WRITE_ONCE) begin : g_sw_write_done
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          sw_write_done <= '0;
        end
        else if (sw_update[1]) begin
          sw_write_done <= '1;
        end
      end
    end
    else begin : g_sw_write_done
      assign  sw_write_done = '0;
    end

    assign  value_next  =
      get_next_value(
        value, sw_update, bit_field_if.write_mask, bit_field_if.write_data,
        hw_write_enable, i_hw_write_data, i_hw_set, i_hw_clear
      );
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        value <= INITIAL_VALUE;
      end
      else if (sw_update[0] || sw_update[1] || hw_update) begin
        value <= value_next;
      end
    end
  end
  else begin : g
    assign  value = i_value;
  end endgenerate
endmodule
