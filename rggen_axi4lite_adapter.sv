module rggen_axi4lite_adapter
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
  parameter bit [BUS_WIDTH-1:0]     DEFAULT_READ_DATA   = '0,
  parameter bit                     WRITE_FIRST         = 1
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_axi4lite_if.slave axi4lite_if,
  rggen_register_if.host  register_if[REGISTERS]
);
  typedef enum logic [1:0] {
    IDLE,
    BUS_ACCESS_BUSY,
    WAIT_FOR_RESPONSE_READY
  } rggen_axi4lite_adapter_state;

  rggen_bus_if #(ADDRESS_WIDTH, BUS_WIDTH)  bus_if();
  rggen_axi4lite_adapter_state              state;

  logic [1:0]               request_valid;
  logic [2:0]               request_ready;
  rggen_access              access;
  logic [ADDRESS_WIDTH-1:0] address;
  logic [BUS_WIDTH-1:0]     write_data;
  logic [BUS_WIDTH/8-1:0]   strobe;

  //  Request
  assign  axi4lite_if.awready = request_ready[0];
  assign  axi4lite_if.wready  = request_ready[1];
  assign  axi4lite_if.arready = request_ready[2];

  assign  bus_if.valid
    = (state == BUS_ACCESS_BUSY) ? '1
    : (state == IDLE           ) ? |request_valid : '0;
  assign  bus_if.access
    = ((state == IDLE) && request_valid[0]) ? RGGEN_WRITE
    : ((state == IDLE) && request_valid[1]) ? RGGEN_READ  : access;
  assign  bus_if.address
    = ((state == IDLE) && request_valid[0]) ? axi4lite_if.awaddr
    : ((state == IDLE) && request_valid[1]) ? axi4lite_if.araddr : address;
  assign  bus_if.write_data
    = ((state == IDLE) && request_valid[0]) ? axi4lite_if.wdata : write_data;
  assign  bus_if.strobe
    = ((state == IDLE) && request_valid[0]) ? axi4lite_if.wstrb : strobe;

  assign  request_valid =
    get_request_valid(axi4lite_if.awvalid, axi4lite_if.wvalid, axi4lite_if.arvalid);
  assign  request_ready =
    get_request_ready(state, axi4lite_if.awvalid, axi4lite_if.wvalid, axi4lite_if.arvalid);

  always_ff @(posedge i_clk) begin
    if ((state == IDLE) && (request_valid != '0)) begin
      access      <= bus_if.access;
      address     <= bus_if.address;
      write_data  <= bus_if.write_data;
      strobe      <= bus_if.strobe;
    end
  end

  function automatic logic [1:0] get_request_valid(
    logic awvalid,
    logic wvalid,
    logic arvalid
  );
    logic write_valid;
    logic read_valid;

    if (WRITE_FIRST) begin
      write_valid = (awvalid && wvalid) ? '1 : '0;
      read_valid  = (!write_valid) ? arvalid : '0;
    end
    else begin
      read_valid  = arvalid;
      write_valid = (awvalid && wvalid && (!read_valid)) ? '1 : '0;
    end

    return {read_valid, write_valid};
  endfunction

  function automatic logic [2:0] get_request_ready(
    rggen_axi4lite_adapter_state  state,
    logic                         awvalid,
    logic                         wvalid,
    logic                         arvalid
  );
    if (state == IDLE) begin
      logic awready;
      logic wready;
      logic arready;

      if (WRITE_FIRST) begin
        awready = wvalid;
        wready  = awvalid;
        arready = (awvalid && wvalid) ? '0 : '1;
      end
      else begin
        arready = '1;
        awready = (!arvalid) ? wvalid  : '0;
        wvalid  = (!arvalid) ? awvalid : '0;
      end

      return {arready, wready, awready};
    end
    else begin
      return 3'b000;
    end
  endfunction

  //  Response
  logic [1:0]           response_valid;
  logic                 response_ack;
  logic [BUS_WIDTH-1:0] read_data;
  logic [1:0]           status;

  assign  axi4lite_if.bvalid  = response_valid[0];
  assign  axi4lite_if.bresp   = status;
  assign  axi4lite_if.rvalid  = response_valid[1];
  assign  axi4lite_if.rdata   = read_data;
  assign  axi4lite_if.rresp   = status;

  assign  response_ack  = (
    (axi4lite_if.bvalid && axi4lite_if.bready) ||
    (axi4lite_if.rvalid && axi4lite_if.rready)
  ) ? '1 : '0;
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_valid  <= 2'b00;
    end
    else if (response_ack) begin
      response_valid  <= 2'b00;
    end
    else if (bus_if.valid && bus_if.ready) begin
      response_valid  <= (
        bus_if.access[RGGEN_ACCESS_DATA_BIT]
      ) ? 2'b01 : 2'b10;
    end
  end

  always_ff @(posedge i_clk) begin
    if (bus_if.valid && bus_if.ready) begin
      status    <= bus_if.status;
      read_data <= bus_if.read_data;
    end
  end

  //  State machine
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      state <= IDLE;
    end
    else begin
      case (state)
        IDLE: begin
          if (request_valid != '0) begin
            if (bus_if.ready) begin
              state <= WAIT_FOR_RESPONSE_READY;
            end
            else begin
              state <= BUS_ACCESS_BUSY;
            end
          end
        end
        BUS_ACCESS_BUSY: begin
          if (bus_if.ready) begin
            state <= WAIT_FOR_RESPONSE_READY;
          end
        end
        WAIT_FOR_RESPONSE_READY: begin
          if (response_ack) begin
            state <= IDLE;
          end
        end
      endcase
    end
  end

  //  Adapter common
  rggen_adapter_common #(
    .ADDRESS_WIDTH        (ADDRESS_WIDTH        ),
    .LOCAL_ADDRESS_WIDTH  (LOCAL_ADDRESS_WIDTH  ),
    .BUS_WIDTH            (BUS_WIDTH            ),
    .REGISTERS            (REGISTERS            ),
    .PRE_DECODE           (PRE_DECODE           ),
    .BASE_ADDRESS         (BASE_ADDRESS         ),
    .BYTE_SIZE            (BYTE_SIZE            ),
    .ERROR_STATUS         (ERROR_STATUS         ),
    .DEFAULT_READ_DATA    (DEFAULT_READ_DATA    )
  ) u_adapter_common (
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .bus_if       (bus_if       ),
    .register_if  (register_if  )
  );
endmodule
