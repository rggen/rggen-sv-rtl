`ifndef RGGEN_BACKDOOR_PKG_SV
`define RGGEN_BACKDOOR_PKG_SV

`ifdef RGGEN_ENABLE_BACKDOOR
package rggen_backdoor_pkg;
  typedef virtual rggen_backdoor_if rggen_backdoor_vif;
  rggen_backdoor_vif  backdoor_vif[string];

  function automatic void set_backdoor_vif(
    string              hdl_path,
    bit                 inside_vhdl_design,
    rggen_backdoor_vif  vif
  );
    string  path;

    if (inside_vhdl_design) begin
      path  = normalize_hdl_path(hdl_path);
    end
    else begin
      path  = hdl_path;
    end

    backdoor_vif[path]  = vif;
  endfunction

  function automatic string normalize_hdl_path(
    string  original_path
  );
    string  path;
    path  = original_path;
    if (path[0] == "\\") begin
      path  = path.substr(1, path.len() - 1);
    end
    if (path[path.len()-1] == " ") begin
      path  = path.substr(0, path.len() - 2);
    end
    return path.tolower();
  endfunction

  function automatic rggen_backdoor_vif get_backdoor_vif(
    string  hdl_path
  );
    return backdoor_vif[hdl_path];
  endfunction
endpackage
`endif

`endif
