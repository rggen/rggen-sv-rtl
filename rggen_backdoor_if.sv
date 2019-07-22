`ifndef RGGEN_BACKDOOR_IF_SV
`define RGGEN_BACKDOOR_IF_SV

`ifdef RGGEN_ENABLE_BACKDOOR
interface rggen_backdoor_if(
  input logic i_clk,
  input logic i_rst_n
);
  import  uvm_pkg::uvm_reg_data_logic_t;

  typedef struct {
    uvm_reg_data_logic_t  read_mask;
    uvm_reg_data_logic_t  write_mask;
    uvm_reg_data_logic_t  write_data;
  } rggen_backdoor_access;

  logic                 valid;
  uvm_reg_data_logic_t  read_mask;
  uvm_reg_data_logic_t  write_mask;
  uvm_reg_data_logic_t  write_data;
  uvm_reg_data_logic_t  read_data;

  mailbox backdoor_access_mailbox;
  initial begin
    backdoor_access_mailbox = new(1);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      valid <= '0;
    end
    else if (backdoor_access_mailbox.num() > 0) begin
      rggen_backdoor_access backdoor_access;
      backdoor_access_mailbox.get(backdoor_access);
      valid       <= '1;
      read_mask   <= backdoor_access.read_mask;
      write_mask  <= backdoor_access.write_mask;
      write_data  <= backdoor_access.write_data;
    end
    else begin
      valid <= '0;
    end
  end

  clocking monitor_cb @(posedge i_clk);
    input valid;
    input read_mask;
    input write_mask;
    input write_data;
    input read_data;
  endclocking

  task automatic backdoor_read(
    input uvm_reg_data_logic_t  mask,
    ref   uvm_reg_data_logic_t  data
  );
    rggen_backdoor_access backdoor_access;
    backdoor_access.read_mask   = mask;
    backdoor_access.write_mask  = '0;
    backdoor_access.write_data  = '0;
    backdoor_access_mailbox.put(backdoor_access);
    data  = get_read_data();
  endtask

  task automatic backdoor_write(
    uvm_reg_data_logic_t  mask,
    uvm_reg_data_logic_t  data
  );
    rggen_backdoor_access backdoor_access;
    backdoor_access.read_mask   = '0;
    backdoor_access.write_mask  = mask;
    backdoor_access.write_data  = data;
    backdoor_access_mailbox.put(backdoor_access);
  endtask

  function automatic uvm_reg_data_logic_t get_read_data();
    return monitor_cb.read_data;
  endfunction

  task automatic wait_for_change();
    @(monitor_cb.read_data);
  endtask
endinterface
`endif

`endif
