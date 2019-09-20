`ifndef RGGEN_BACKDOOR_PKG_SV
`define RGGEN_BACKDOOR_PKG_SV

`ifdef RGGEN_ENABLE_BACKDOOR
package rggen_backdoor_pkg;
  typedef virtual rggen_backdoor_if rggen_backdoor_vif;
  rggen_backdoor_vif  backdoor_vif[string];

  function automatic void set_backdoor_vif(
    string              hdl_path,
    rggen_backdoor_vif  vif
  );
    backdoor_vif[hdl_path]  = vif;
  endfunction

  function automatic rggen_backdoor_vif get_backdoor_vif(
    string  hdl_path
  );
    return backdoor_vif[hdl_path];
  endfunction
endpackage
`endif

`endif
