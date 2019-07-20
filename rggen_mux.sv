interface rggen_mux #(
  parameter int WIDTH   = 8,
  parameter int ENTRIES = 2
)();
  function automatic logic [WIDTH-1:0] mux(
    logic [ENTRIES-1:0] select,
    logic [WIDTH-1:0]   value_in[ENTRIES]
  );
    logic [WIDTH-1:0] out;

    if (ENTRIES > 1) begin
      out = '0;
      for (int i = 0;i < ENTRIES;++i) begin
        out = out | ({WIDTH{select[i]}} & value_in[i]);
      end
    end
    else begin
      out = value_in[0];
    end

    return out;
  endfunction
endinterface
