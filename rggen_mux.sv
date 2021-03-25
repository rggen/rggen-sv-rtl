interface rggen_mux #(
  parameter int WIDTH   = 2,
  parameter int ENTRIES = 2
);
  function automatic logic [WIDTH-1:0] mux(
    logic [ENTRIES-1:0]             select,
    logic [ENTRIES-1:0][WIDTH-1:0]  data
  );
    logic [WIDTH-1:0] out;

    if (ENTRIES > 1) begin
      for (int i = 0;i < ENTRIES;++i) begin
        if (i == 0) begin
          out = ({WIDTH{select[i]}} & data[i]);
        end
        else begin
          out = ({WIDTH{select[i]}} & data[i]) | out;
        end
      end
    end
    else begin
      out = data[0];
    end

    return out;
  endfunction
endinterface
