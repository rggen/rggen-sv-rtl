`ifndef RGGEN_BACKDOOR_IF_SV
`define RGGEN_BACKDOOR_IF_SV

`ifdef RGGEN_ENABLE_BACKDOOR
interface rggen_backdoor_if(
  input logic i_clk,
  input logic i_rst_n
);
  import  uvm_pkg::uvm_reg_data_t;

  bit             valid;
  uvm_reg_data_t  read_mask;
  uvm_reg_data_t  write_mask;
  uvm_reg_data_t  write_data;
  uvm_reg_data_t  read_data;

  clocking backdoor_cb @(posedge i_clk);
    output  valid;
    output  read_mask;
    output  write_mask;
    output  write_data;
    input   read_data;
  endclocking

  event at_clock_edge;
  always @(backdoor_cb) begin
    ->at_clock_edge;
  end

  semaphore backdoor_access_lock;
  initial begin
    backdoor_access_lock  = new(1);
  end

  task automatic backdoor_read(
    input uvm_reg_data_t  mask,
    ref   uvm_reg_data_t  data
  );
    backdoor_access(0, mask, data);
  endtask

  task automatic backdoor_write(
    uvm_reg_data_t  mask,
    uvm_reg_data_t  data
  );
    backdoor_access(1, mask, data);
  endtask

  task automatic backdoor_access(
    input bit                   write,
    input uvm_reg_data_t  mask,
    ref   uvm_reg_data_t  data
  );
    backdoor_access_lock.get(1);

    if (!at_clock_edge.triggered) begin
      @(backdoor_cb);
    end

    backdoor_cb.valid <= '1;
    if (write) begin
      backdoor_cb.read_mask   <= '0;
      backdoor_cb.write_mask  <= mask;
      backdoor_cb.write_data  <= data;
    end
    else begin
      data  = get_read_data();
      backdoor_cb.read_mask   <= mask;
      backdoor_cb.write_mask  <= '0;
    end

    @(backdoor_cb);
    backdoor_cb.valid <= '0;

    backdoor_access_lock.put(1);
  endtask

  function automatic uvm_reg_data_t get_read_data();
    return backdoor_cb.read_data;
  endfunction

  task automatic wait_for_change();
    @(backdoor_cb.read_data);
  endtask
endinterface
`endif

`endif
