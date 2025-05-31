module rggen_bit_field
  import  rggen_rtl_pkg::*;
#(
  parameter int                 WIDTH                     = 8,
  parameter bit [WIDTH-1:0]     INITIAL_VALUE             = '0,
  parameter rggen_sw_hw_access  PRECEDENCE_ACCESS         = RGGEN_HW_ACCESS,
  parameter rggen_sw_action     SW_READ_ACTION            = RGGEN_READ_DEFAULT,
  parameter rggen_sw_action     SW_WRITE_ACTION           = RGGEN_WRITE_DEFAULT,
  parameter bit                 SW_WRITE_CONTROL          = '0,
  parameter bit                 SW_WRITE_ONCE             = '0,
  parameter rggen_polarity      SW_WRITE_ENABLE_POLARITY  = RGGEN_ACTIVE_HIGH,
  parameter rggen_polarity      HW_WRITE_ENABLE_POLARITY  = RGGEN_ACTIVE_HIGH,
  parameter bit [2:0]           HW_ACCESS                 = '0,
  parameter int                 HW_SET_WIDTH              = WIDTH,
  parameter int                 HW_CLEAR_WIDTH            = WIDTH,
  parameter bit                 STORAGE                   = '1,
  parameter bit                 EXTERNAL_READ_DATA        = '0,
  parameter bit                 EXTERNAL_MASK             = '0,
  parameter bit                 TRIGGER                   = '0
)(
  input   logic                       i_clk,
  input   logic                       i_rst_n,
  rggen_bit_field_if.bit_field        bit_field_if,
  output  logic                       o_write_trigger,
  output  logic                       o_read_trigger,
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
  localparam  bit SW_WRITABLE     = SW_READ_ACTION != RGGEN_WRITE_NONE;
  localparam  bit SW_READABLE     = SW_READ_ACTION != RGGEN_READ_NONE;
  localparam  bit SW_READ_UPDATE  = SW_READABLE && (SW_READ_ACTION != RGGEN_READ_DEFAULT);

//--------------------------------------------------------------
//  Utility functions
//--------------------------------------------------------------
  function automatic logic get_sw_write_update(
    logic write_valid,
    logic write_enable,
    logic write_done
  );
    logic [2:0] update;

    update[0] = write_valid;
    if (SW_WRITE_CONTROL) begin
      update[1] = write_enable == SW_WRITE_ENABLE_POLARITY;
    end
    else begin
      update[1] = '1;
    end
    if (SW_WRITE_ONCE) begin
      update[2] = !write_done;
    end
    else begin
      update[2] = '1;
    end

    return update[0] && update[1] && update[2];
  endfunction

  function automatic logic get_hw_update(
    logic                       write_enable,
    logic [HW_SET_WIDTH-1:0]    set,
    logic [HW_CLEAR_WIDTH-1:0]  clear
  );
    logic [2:0] update;
    update[0] = HW_ACCESS[0] && (write_enable == HW_WRITE_ENABLE_POLARITY);
    update[1] = HW_ACCESS[1] && (set          != '0                      );
    update[2] = HW_ACCESS[2] && (clear        != '0                      );
    return update[0] || update[1] || update[2];
  endfunction

  function automatic logic [WIDTH-1:0] get_sw_read_next_value(
    logic [WIDTH-1:0] current_value,
    logic [WIDTH-1:0] mask
  );
    case (SW_READ_ACTION)
      RGGEN_READ_CLEAR: return (mask != '0) ? '0 : current_value;
      RGGEN_READ_SET:   return (mask != '0) ? '1 : current_value;
      default:          return current_value;
    endcase
  endfunction

  function automatic logic [WIDTH-1:0] get_sw_write_next_value(
    logic [WIDTH-1:0] current_value,
    logic [WIDTH-1:0] mask,
    logic [WIDTH-1:0] write_data
  );
    logic [WIDTH-1:0] data;

    data  = current_value;
    case (SW_WRITE_ACTION)
      RGGEN_WRITE_DEFAULT: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i]) begin
            data[i] = write_data[i];
          end
        end
      end
      RGGEN_WRITE_0_CLEAR: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i] && (!write_data[i])) begin
            data[i] = '0;
          end
        end
      end
      RGGEN_WRITE_1_CLEAR: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i] && write_data[i]) begin
            data[i] = '0;
          end
        end
      end
      RGGEN_WRITE_CLEAR: begin
        if (mask != '0) begin
          data  = '0;
        end
      end
      RGGEN_WRITE_0_SET: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i] && (!write_data[i])) begin
            data[i] = '1;
          end
        end
      end
      RGGEN_WRITE_1_SET: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i] && write_data[i]) begin
            data[i] = '1;
          end
        end
      end
      RGGEN_WRITE_SET: begin
        if (mask != '0) begin
          data  = '1;
        end
      end
      RGGEN_WRITE_0_TOGGLE: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i] && (!write_data[i])) begin
            data[i] = ~current_value[i];
          end
        end
      end
      RGGEN_WRITE_1_TOGGLE: begin
        for (int i = 0;i < WIDTH;++i) begin
          if (mask[i] && write_data[i]) begin
            data[i] = ~current_value[i];
          end
        end
      end
      default: ; // nothing to do
    endcase

    return data;
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

    if (!HW_ACCESS[1]) begin
      set_clear[0]  = '0;
    end
    else if (HW_SET_WIDTH == WIDTH) begin
      set_clear[0][HW_SET_WIDTH-1:0]  = set;
    end
    else begin
      set_clear[0]  = {WIDTH{set[0]}};
    end

    if (!HW_ACCESS[2]) begin
      set_clear[1]  = '0;
    end
    else if (HW_CLEAR_WIDTH == WIDTH) begin
      set_clear[1][HW_CLEAR_WIDTH-1:0]  = clear;
    end
    else begin
      set_clear[1]  = {WIDTH{clear[0]}};
    end

    for (int i = 0;i < WIDTH;++i) begin
      if (set_clear[0][i]) begin
        value[i]  = '1;
      end
      else if (set_clear[1][i]) begin
        value[i]  = '0;
      end
      else if (HW_ACCESS[0] && (write_enable == HW_WRITE_ENABLE_POLARITY)) begin
        value[i]  = write_data[i];
      end
      else begin
        value[i]  = current_value[i];
      end
    end

    return value;
  endfunction

//--------------------------------------------------------------
//  Body
//--------------------------------------------------------------
  logic [1:0]       sw_update;
  logic             sw_write_done;
  logic             hw_update;
  logic [1:0]       trigger;
  logic [WIDTH-1:0] value;
  logic [WIDTH-1:0] read_data;

  always_comb begin
    bit_field_if.value  = value;
    if (EXTERNAL_MASK) begin
      bit_field_if.read_data  = read_data & i_mask;
    end
    else begin
      bit_field_if.read_data  = read_data;
    end
  end

  always_comb begin
    o_write_trigger   = trigger[0];
    o_read_trigger    = trigger[1];
    o_value_unmasked  = value;
    if (EXTERNAL_MASK) begin
      o_value = value & i_mask;
    end
    else begin
      o_value = value;
    end
  end

  always_comb begin
    if (SW_READ_UPDATE) begin
      sw_update[0] = bit_field_if.read_valid;
    end
    else begin
      sw_update[0] = '0;
    end

    if (SW_WRITABLE) begin
      sw_update[1] = get_sw_write_update(bit_field_if.write_valid, i_sw_write_enable, sw_write_done);
    end
    else begin
      sw_update[1]  = '0;
    end

    if (HW_ACCESS != '0) begin
      hw_update = get_hw_update(i_hw_write_enable, i_hw_set, i_hw_clear);
    end
    else begin
      hw_update = '0;
    end
  end

  generate
    if (STORAGE && SW_WRITABLE && SW_WRITE_ONCE) begin : g_sw_write_done
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          sw_write_done <= '0;
        end
        else if (sw_update[1] && (bit_field_if.mask != '0)) begin
          sw_write_done <= '1;
        end
      end
    end
    else begin : g_sw_write_done
      assign  sw_write_done = '0;
    end
  endgenerate

  generate
    if (TRIGGER && SW_WRITABLE) begin : g_write_trigger
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          trigger[0]  <= '0;
        end
        else begin
          trigger[0]  <= sw_update[1] && (bit_field_if.mask != '0);
        end
      end
    end
    else begin : g_write_trigger
      assign  trigger[0]  = '0;
    end

    if (TRIGGER && SW_READABLE) begin : g_read_trigger
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          trigger[1]  <= '0;
        end
        else begin
          trigger[1]  <= sw_update[0] && (bit_field_if.mask != '0);
        end
      end
    end
    else begin : g_read_trigger
      assign  trigger[1]  = '0;
    end
  endgenerate

  generate
    if (!STORAGE) begin : g_value
      always_comb begin
        value = i_value;
      end
    end
    else if (PRECEDENCE_ACCESS == RGGEN_SW_ACCESS) begin : g_value
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          value <= INITIAL_VALUE;
        end
        else if (sw_update[0]) begin
          value <=
            get_sw_read_next_value(
              value, bit_field_if.mask
            );
        end
        else if (sw_update[1]) begin
          value <=
            get_sw_write_next_value(
              value, bit_field_if.mask, bit_field_if.write_data
            );
        end
        else if (hw_update) begin
          value <=
            get_hw_next_value(
              value, i_hw_write_enable, i_hw_write_data,
              i_hw_set, i_hw_clear
            );
        end
      end
    end
    else begin : g_value
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          value <= INITIAL_VALUE;
        end
        else if (hw_update) begin
          value <=
            get_hw_next_value(
              value, i_hw_write_enable, i_hw_write_data,
              i_hw_set, i_hw_clear
            );
        end
        else if (sw_update[0]) begin
          value <=
            get_sw_read_next_value(
              value, bit_field_if.mask
            );
        end
        else if (sw_update[1]) begin
          value <=
            get_sw_write_next_value(
              value, bit_field_if.mask, bit_field_if.write_data
            );
        end
      end
    end
  endgenerate

  always_comb begin
    if (!SW_READABLE) begin
      read_data = '0;
    end
    else if (EXTERNAL_READ_DATA) begin
      read_data = i_value;
    end
    else begin
      read_data = value;
    end
  end
endmodule
