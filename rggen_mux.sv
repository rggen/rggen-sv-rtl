interface rggen_mux #(
  parameter int WIDTH   = 2,
  parameter int ENTRIES = 2
);
  function automatic logic [WIDTH-1:0] __reduce_or(
    int                             n,
    int                             offset,
    logic [ENTRIES-1:0][WIDTH-1:0]  data
  );
    if (n > 4) begin
      int               next_n;
      int               next_offset;
      logic [WIDTH-1:0] result[2];

      next_n      = n / 2;
      next_offset = offset;
      result[0]   = __reduce_or(next_n, next_offset, data);

      next_n      = (n / 2) + (n % 2);
      next_offset = (n / 2) + offset;
      result[1]   = __reduce_or(next_n, next_offset, data);

      return result[0] | result[1];
    end
    else if (n == 4) begin
      return data[0+offset] | data[1+offset] | data[2+offset] | data[3+offset];
    end
    else if (n == 3) begin
      return data[0+offset] | data[1+offset] | data[2+offset];
    end
    else if (n == 2) begin
      return data[0+offset] | data[1+offset];
    end
    else begin
      return data[0+offset];
    end
  endfunction

  function automatic logic [WIDTH-1:0] mux(
    logic [ENTRIES-1:0]             select,
    logic [ENTRIES-1:0][WIDTH-1:0]  data
  );
    if (ENTRIES > 1) begin
      logic [ENTRIES-1:0][WIDTH-1:0]  masked_data;

      for (int i = 0;i < ENTRIES;++i) begin
        masked_data[i]  = {WIDTH{select[i]}} & data[i];
      end

      return __reduce_or(ENTRIES, 0, masked_data);
    end
    else begin
      return data[0];
    end
  endfunction
endinterface
