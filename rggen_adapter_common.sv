module rggen_adapter_common
  import  rggen_rtl_pkg::*;
#(
  parameter int                     ADDRESS_WIDTH       = 8,
  parameter int                     LOCAL_ADDRESS_WIDTH = 8,
  parameter int                     BUS_WIDTH           = 32,
  parameter int                     STROBE_WIDTH        = BUS_WIDTH / 8,
  parameter int                     REGISTERS           = 1,
  parameter bit                     PRE_DECODE          = 0,
  parameter bit [ADDRESS_WIDTH-1:0] BASE_ADDRESS        = '0,
  parameter int                     BYTE_SIZE           = 256,
  parameter bit                     USE_READ_STROBE     = 0,
  parameter bit                     ERROR_STATUS        = 0,
  parameter bit [BUS_WIDTH-1:0]     DEFAULT_READ_DATA   = '0,
  parameter bit                     INSERT_SLICER       = 0
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

  always_comb begin
    inside_range  = pre_decode(bus_if.address);
  end

  function automatic logic pre_decode(
    logic [ADDRESS_WIDTH-1:0] address
  );
    if (PRE_DECODE) begin
      logic [ADDRESS_WIDTH-1:0] begin_addrss;
      logic [ADDRESS_WIDTH-1:0] end_address;

      begin_addrss  = BASE_ADDRESS;
      end_address   = BASE_ADDRESS + ADDRESS_WIDTH'(BYTE_SIZE - 1);

      return (address >= begin_addrss) && (address <= end_address);
    end
    else begin
      return '1;
    end
  endfunction

  //  Request
  logic                           bus_valid;
  rggen_access                    bus_access;
  logic [LOCAL_ADDRESS_WIDTH-1:0] bus_address;
  logic [BUS_WIDTH-1:0]           bus_write_data;
  logic [STROBE_WIDTH-1:0]        bus_strobe;

  generate
    if (INSERT_SLICER) begin : g_request_slicer
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          bus_valid <= '0;
        end
        else if (!busy) begin
          bus_valid <= bus_if.valid && inside_range;
        end
        else begin
          bus_valid <= '0;
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          bus_access      <= rggen_access'(0);
          bus_address     <= '0;
          bus_write_data  <= '0;
          bus_strobe      <= '0;
        end
        else if (bus_if.valid && (!busy)) begin
          bus_access      <= bus_if.access;
          bus_address     <= get_local_address(bus_if.address);
          bus_write_data  <= bus_if.write_data;
          bus_strobe      <= bus_if.strobe;
        end
      end
    end
    else begin : g_no_request_slicer
      always_comb begin
        bus_valid       = bus_if.valid && inside_range && (!busy);
        bus_access      = bus_if.access;
        bus_address     = get_local_address(bus_if.address);
        bus_write_data  = bus_if.write_data;
        bus_strobe      = bus_if.strobe;
      end
    end

    for (i = 0;i < REGISTERS;++i) begin : g_request
      always_comb begin
        register_if[i].valid      = bus_valid;
        register_if[i].access     = bus_access;
        register_if[i].address    = bus_address;
        register_if[i].write_data = bus_write_data;
        register_if[i].strobe     = get_regiser_strobe(bus_access, bus_strobe);
      end
    end
  endgenerate

  function automatic logic [LOCAL_ADDRESS_WIDTH-1:0] get_local_address(
    logic [ADDRESS_WIDTH-1:0] address
  );
    logic [ADDRESS_WIDTH-1:0] local_address;

    if (BASE_ADDRESS[0+:LOCAL_ADDRESS_WIDTH] == '0) begin
      local_address = address;
    end
    else begin
      local_address = address - BASE_ADDRESS;
    end

    return local_address[0+:LOCAL_ADDRESS_WIDTH];
  endfunction

  function automatic logic [BUS_WIDTH-1:0] get_regiser_strobe(
    rggen_access              bus_access,
    logic [STROBE_WIDTH-1:0]  bus_strobe
  );
    logic [BUS_WIDTH-1:0] strobe;

    if ((!USE_READ_STROBE) && (bus_access == RGGEN_READ)) begin
      strobe  = '1;
    end
    else if (STROBE_WIDTH == BUS_WIDTH) begin
      strobe  = BUS_WIDTH'(bus_strobe);
    end
    else begin
      for (int i = 0;i < STROBE_WIDTH;++i) begin
        strobe[8*i+:8]  = {8{bus_strobe[i]}};
      end
    end

    return strobe;
  endfunction

  //  Response
  localparam  int STATUS_WIDTH    = $bits(rggen_status);
  localparam  int RESPONSE_WIDTH  = 1 + 1 + BUS_WIDTH + ((ERROR_STATUS) ? STATUS_WIDTH : 0);

  logic [REGISTERS-1:0]                     active;
  logic [REGISTERS-1:0][RESPONSE_WIDTH-1:0] response;
  logic [RESPONSE_WIDTH-1:0]                selected_response;
  logic                                     register_active;
  logic                                     register_ready;
  rggen_status                              register_status;
  logic [BUS_WIDTH-1:0]                     register_read_data;
  logic                                     register_inactive;

  generate
    if (ERROR_STATUS) begin : g_response
      for (i = 0;i < REGISTERS;++i) begin : g
        always_comb begin
          active[i]   = register_if[i].active;
          response[i] = {register_if[i].status, register_if[i].read_data, register_if[i].ready, 1'b1};
        end
      end

      always_comb begin
        register_active     = selected_response[0];
        register_ready      = selected_response[1];
        register_read_data  = selected_response[2+:BUS_WIDTH];
        register_status     = rggen_status'(selected_response[2+BUS_WIDTH+:STATUS_WIDTH]);
      end
    end
    else begin : g_response
      for (i = 0;i < REGISTERS;++i) begin : g
        always_comb begin
          active[i]   = register_if[i].active;
          response[i] = {register_if[i].read_data, register_if[i].ready, 1'b1};
        end
      end

      always_comb begin
        register_active     = selected_response[0];
        register_ready      = selected_response[1];
        register_read_data  = selected_response[2+:BUS_WIDTH];
        register_status     = RGGEN_OKAY;
      end
    end
  endgenerate

  rggen_mux #(
    .WIDTH    (RESPONSE_WIDTH ),
    .ENTRIES  (REGISTERS      )
  ) u_mux (
    .i_select (active             ),
    .i_data   (response           ),
    .o_data   (selected_response  )
  );

  always_comb begin
    register_inactive = (!inside_range) || (!register_active);
  end

  always_comb begin
    bus_if.ready  = ((!INSERT_SLICER) || busy) && (register_ready || register_inactive);
    if ((!ERROR_STATUS) || (!register_inactive)) begin
      bus_if.status     = register_status;
      bus_if.read_data  = register_read_data;
    end
    else begin
      bus_if.status     = RGGEN_SLAVE_ERROR;
      bus_if.read_data  = DEFAULT_READ_DATA;
    end
  end

`ifdef RGGEN_ENABLE_SVA
  ast_hold_request_command_until_ready_is_high:
  assert property (
    @(posedge i_clk)
    (bus_if.valid && (!bus_if.ready)) |=>
      ($stable(bus_if.valid) && $stable(bus_if.access) && $stable(bus_if.address))
  );

  ast_hold_request_data_until_ready_is_high:
  assert property (
    @(posedge i_clk)
    (bus_if.valid && (!bus_if.ready) && (bus_if.access != RGGEN_READ)) |=>
      ($stable(bus_if.write_data) && $stable(bus_if.strobe))
  );

  ast_only_one_register_is_active:
  assert property (
    @(posedge i_clk)
    (bus_if.valid && (active != '0)) |-> $onehot(active)
  );
`endif
endmodule
