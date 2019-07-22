`ifndef RGGEN_BACKDOOR_PKG_SV
`define RGGEN_BACKDOOR_PKG_SV

`ifdef RGGEN_ENABLE_BACKDOOR
package rggen_backdoor_pkg;
  import  uvm_pkg::*;
  `include  "uvm_macros.svh"

  typedef virtual rggen_backdoor_if rggen_backdoor_vif;

  class rggen_backdoor extends uvm_reg_backdoor;
    protected rggen_backdoor_vif  vif;

    function new(string name, rggen_backdoor_vif vif);
      super.new(name);
      this.vif  = vif;
    endfunction

    function bit is_auto_updated(uvm_reg_field field);
      return 1;
    endfunction

    task wait_for_change(uvm_object element);
      vif.wait_for_change();
    endtask

    task write(uvm_reg_item rw);
      int unsigned          width;
      int unsigned          lsb;
      uvm_reg_data_logic_t  mask;
      uvm_reg_data_logic_t  data;

      get_location_info(rw, width, lsb);
      mask  = ((1 << width) - 1) << lsb;
      data  = rw.value[0] << lsb;

      vif.backdoor_write(mask, data);
    endtask

    function void read_func(uvm_reg_item rw);
      int unsigned          width;
      int unsigned          lsb;
      uvm_reg_data_logic_t  mask;
      uvm_reg_data_logic_t  data;

      get_location_info(rw, width, lsb);
      mask  = ((1 << width) - 1);

      data  = vif.get_read_data();
      rw.value[0] = (data >> lsb) & mask;
    endfunction

    protected function void get_location_info(
      input uvm_reg_item  rw,
      ref   int unsigned  width,
      ref   int unsigned  lsb
    );
      case (rw.element_kind)
        UVM_REG: begin
          uvm_reg element;
          $cast(element, rw.element);
          width = element.get_n_bits();
          lsb   = 0;
        end
        UVM_FIELD: begin
          uvm_reg_field element;
          $cast(element, rw.element);
          width = element.get_n_bits();
          lsb   = element.get_lsb_pos();
        end
      endcase
    endfunction
  endclass

  rggen_backdoor_vif  backdoor_vif[string];

  function automatic void set_backdoor_vif(
    string              hdl_path,
    rggen_backdoor_vif  vif
  );
    backdoor_vif[hdl_path]  = vif;
  endfunction

  function automatic uvm_reg_backdoor get_backdoor(
    string  hdl_path
  );
    rggen_backdoor  backdoor;
    backdoor  = new("backdoor", backdoor_vif[hdl_path]);
    return backdoor;
  endfunction
endpackage
`endif

`endif
