module rggen_adapter_common
  import  rggen_rtl_pkg::*;
#(
  parameter int                     ADDRESS_WIDTH       = 8,
  parameter int                     LOCAL_ADDRESS_WIDTH = 8,
  parameter int                     BUS_WIDTH           = 32,
  parameter int                     REGISTERS           = 1,
  parameter bit                     PRE_DECODE          = 0,
  parameter bit [ADDRESS_WIDTH-1:0] BASE_ADDRESS        = '0,
  parameter int                     BYTE_SIZE           = 256,
  parameter bit                     ERROR_STATUS        = 0,
  parameter bit [BUS_WIDTH-1:0]     DEFAULT_READ_DATA   = '0
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_bus_if.slave      bus_if,
  rggen_register_if.host  register_if[REGISTERS]
);
  genvar  i;

  //  State
  logic busy;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      busy  <= '0;
    end
    else if (bus_if.ready) begin
      busy  <= '0;
    end
    else if (bus_if.valid) begin
      busy  <= '1;
    end
  end

  //  Pre-decode
  localparam  bit [ADDRESS_WIDTH-1:0] END_ADDRESS = BASE_ADDRESS + BYTE_SIZE - 1;

  logic in_valid_range;

  generate if (PRE_DECODE) begin : g_pre_decode
    assign  in_valid_range  =
      ((bus_if.address >= BASE_ADDRESS) && (bus_if.address <= END_ADDRESS)) ? '1 : '0;
  end
  else begin : g_no_pre_decode
    assign  in_valid_range  = '1;
  end endgenerate

  //  Request
  generate for (i = 0;i < REGISTERS;++i) begin : g_request
    assign  register_if[i].valid      = (bus_if.valid && in_valid_range && (!busy)) ? '1 : '0;
    assign  register_if[i].access     = bus_if.access;
    assign  register_if[i].address    = bus_if.address[LOCAL_ADDRESS_WIDTH-1:0];
    assign  register_if[i].write_data = bus_if.write_data;
    assign  register_if[i].strobe     = bus_if.strobe;
  end endgenerate

  //  Response
  localparam  rggen_status  DEFAULT_STATUS        = (ERROR_STATUS) ? RGGEN_SLAVE_ERROR : RGGEN_OKAY;
  localparam  int           RESPONSES             = REGISTERS + 1;
  localparam  int           RESPONSES_INDEX_WIDTH = $clog2(RESPONSES);

  logic [REGISTERS-0:0]             ready;
  logic [REGISTERS-1:0]             active;
  rggen_status                      status[RESPONSES];
  logic [BUS_WIDTH-1:0]             read_data[RESPONSES];
  logic [RESPONSES_INDEX_WIDTH-1:0] response_index;

  assign  ready[REGISTERS]      = ~|{1'b0, active};
  assign  status[REGISTERS]     = DEFAULT_STATUS;
  assign  read_data[REGISTERS]  = DEFAULT_READ_DATA;

  generate for (i = 0;i < REGISTERS;++i) begin : g_response
    assign  ready[i]      = (in_valid_range) ? register_if[i].ready  : '0;
    assign  active[i]     = (in_valid_range) ? register_if[i].active : '0;
    assign  status[i]     = register_if[i].status;
    assign  read_data[i]  = register_if[i].read_data;
  end endgenerate

  assign  bus_if.ready      = |ready;
  assign  bus_if.status     = status[response_index];
  assign  bus_if.read_data  = read_data[response_index];

  rggen_onehot #(RESPONSES) u_onehot();
  assign  response_index  = u_onehot.to_binary(ready);

`ifdef RGGEN_ENABLE_SVA
  ast_hold_request_until_ready_is_high:
  assert property (
    @(posedge i_clk)
    (bus_if.valid && (!bus_if.ready)) |=>
      (
        $stable(bus_if.valid) && $stable(bus_if.access) &&
        $stable(bus_if.address) && $stable(bus_if.write_data)
      )
  );

  ast_only_one_register_is_active:
  assert property (
    @(posedge i_clk)
    (bus_if.valid && (active != '0)) |-> $onehot(active)
  );

  ast_assert_ready_of_active_register_only:
  assert property (
    @(posedge i_clk)
    (bus_if.valid && (ready != '0)) |-> (active == ready[REGISTERS-1:0])
  );
`endif
endmodule
