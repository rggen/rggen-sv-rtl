interface rggen_onehot #(
  parameter int N = 2
)();
  localparam  int BINARY_WIDTH  = (N >= 2) ? $clog2(N) : 1;

  function automatic logic [BINARY_WIDTH-1:0] to_binary(
    logic [N-1:0] onehot
  );
    logic [BINARY_WIDTH-1:0]  binary;

    if (N >= 2) begin
      for (int i = 0;i < BINARY_WIDTH;++i) begin
        logic [N-1:0] temp;
        for (int j = 0;j < N;++j) begin
          temp[j] = onehot[j] & j[i];
        end
        binary[i] = |temp;
      end
    end
    else begin
      binary  = '0;
    end

    return binary;
  endfunction
endinterface
