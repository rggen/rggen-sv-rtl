interface rggen_mux #(
  parameter int WIDTH   = 2,
  parameter int ENTRIES = 2
);
  function automatic logic [WIDTH-1:0] mux(
    logic [ENTRIES-1:0]             select,
    logic [ENTRIES-1:0][WIDTH-1:0]  data
  );
    if (ENTRIES > 1) begin
      logic [WIDTH-1:0] out;

      for (int i = 0;i < WIDTH;++i) begin
        logic [ENTRIES-1:0] temp;
        for (int j = 0;j < ENTRIES;++j) begin
          temp[j] = select[j] & data[j][i];
        end
        out[i]  = |temp;
      end

      return out;
    end
    else begin
      return data[0];
    end
  endfunction
endinterface
