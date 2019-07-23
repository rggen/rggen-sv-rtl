interface rggen_mux #(
  parameter int WIDTH   = 8,
  parameter int ENTRIES = 2
)();
  localparam  int INDEX_WIDTH = (ENTRIES >= 2) ? $clog2(ENTRIES) : 1;

  function automatic logic [WIDTH-1:0] mux(
    logic [ENTRIES-1:0] select,
    logic [WIDTH-1:0]   value_in[ENTRIES]
  );
    if (ENTRIES >= 2) begin
      return value_in[get_index(select)];
    end
    else begin
      return value_in[0];
    end
  endfunction

  function automatic logic [INDEX_WIDTH-1:0] get_index(
    logic [ENTRIES-1:0] select
  );
    logic [INDEX_WIDTH-1:0] index;
    for (int i = 0;i < INDEX_WIDTH;++i) begin
      logic [ENTRIES-1:0] temp;
      for (int j = 0;j < ENTRIES;++j) begin
        temp[j] = select[j] & j[i];
      end
      index[i]  = |temp;
    end
    return index;
  endfunction
endinterface
