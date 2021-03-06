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
  logic inside_range;

  assign  inside_range  = pre_decode(bus_if.address);

  function automatic logic pre_decode(
    logic [ADDRESS_WIDTH-1:0] address
  );
    if (PRE_DECODE) begin
      logic [ADDRESS_WIDTH-1:0] begin_addrss;
      logic [ADDRESS_WIDTH-1:0] end_address;

      begin_addrss  = ADDRESS_WIDTH'(BASE_ADDRESS);
      end_address   = ADDRESS_WIDTH'(BASE_ADDRESS + BYTE_SIZE - 1);

      return (address >= begin_addrss) && (address <= end_address);
    end
    else begin
      return '1;
    end
  endfunction

  //  Request
  generate for (i = 0;i < REGISTERS;++i) begin : g_request
    assign  register_if[i].valid      = bus_if.valid && inside_range && (!busy);
    assign  register_if[i].access     = bus_if.access;
    assign  register_if[i].address    = bus_if.address[LOCAL_ADDRESS_WIDTH-1:0];
    assign  register_if[i].write_data = bus_if.write_data;
    assign  register_if[i].strobe     = bus_if.strobe;
  end endgenerate

  //  Response
  localparam  rggen_status  DEFAULT_STATUS  = (ERROR_STATUS) ? RGGEN_SLAVE_ERROR : RGGEN_OKAY;

  rggen_mux #($bits(rggen_status), REGISTERS) u_status_mux();
  rggen_mux #(BUS_WIDTH          , REGISTERS) u_read_data_mux();

  logic [REGISTERS-1:0]                           ready;
  logic [REGISTERS-1:0]                           active;
  logic [REGISTERS-1:0][$bits(rggen_status)-1:0]  status;
  logic [REGISTERS-1:0][BUS_WIDTH-1:0]            read_data;
  logic                                           register_inactive;
  rggen_status                                    register_status;
  logic [BUS_WIDTH-1:0]                           register_read_data;

  generate for (i = 0;i < REGISTERS;++i) begin : g_response
    assign  active[i]     = register_if[i].active;
    assign  ready[i]      = register_if[i].ready;
    assign  status[i]     = register_if[i].status;
    assign  read_data[i]  = register_if[i].read_data;
  end endgenerate

  assign  register_inactive   = (!inside_range) || (active == '0);
  assign  register_status     = rggen_status'(u_status_mux.mux(active, status));
  assign  register_read_data  = u_read_data_mux.mux(active, read_data);

  assign  bus_if.ready      = (ready != '0) || register_inactive;
  assign  bus_if.status     = (register_inactive) ? DEFAULT_STATUS    : register_status;
  assign  bus_if.read_data  = (register_inactive) ? DEFAULT_READ_DATA : register_read_data;

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
    (bus_if.valid && (ready != '0)) |-> (active == ready)
  );
`endif
endmodule
