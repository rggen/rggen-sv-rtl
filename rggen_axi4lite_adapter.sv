module rggen_axi4lite_adapter
  import  rggen_rtl_pkg::*;
#(
  parameter int                     ID_WIDTH            = 0,
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

  rggen_axi4lite_if #(ID_WIDTH, ADDRESS_WIDTH, BUS_WIDTH) buffer_if();
  rggen_bus_if #(ADDRESS_WIDTH, BUS_WIDTH)                bus_if();
  rggen_axi4lite_adapter_state                            state;

  //  Input buffer
  rggen_axi4lite_skid_buffer #(
    .ID_WIDTH       (ID_WIDTH       ),
    .ADDRESS_WIDTH  (ADDRESS_WIDTH  ),
    .BUS_WIDTH      (BUS_WIDTH      )
  ) u_buffer (
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .slave_if   (axi4lite_if  ),
    .master_if  (buffer_if    )
  );

  logic [1:0]               request_valid;
  logic [2:0]               request_ready;
  rggen_access              access;
  logic [ADDRESS_WIDTH-1:0] address;
  logic [BUS_WIDTH-1:0]     write_data;
  logic [BUS_WIDTH/8-1:0]   strobe;

  //  Request
  always_comb begin
    buffer_if.awready = request_ready[0];
    buffer_if.wready  = request_ready[1];
    buffer_if.arready = request_ready[2];
  end

  always_comb begin
    bus_if.valid  =
      ((state == IDLE) && (request_valid != '0)) ||
      ((state == BUS_ACCESS_BUSY));
  end

  always_comb begin
    if (state != IDLE) begin
      bus_if.access     = access;
      bus_if.address    = address;
      bus_if.write_data = write_data;
      bus_if.strobe     = strobe;
    end
    else if (request_valid[0]) begin
      bus_if.access     = RGGEN_WRITE;
      bus_if.address    = buffer_if.awaddr;
      bus_if.write_data = buffer_if.wdata;
      bus_if.strobe     = buffer_if.wstrb;
    end
    else begin
      bus_if.access     = RGGEN_READ;
      bus_if.address    = buffer_if.araddr;
      bus_if.write_data = buffer_if.wdata;
      bus_if.strobe     = buffer_if.wstrb;
    end
  end

  always_comb begin
    request_valid =
      get_request_valid(buffer_if.awvalid, buffer_if.wvalid, buffer_if.arvalid);
    request_ready =
      get_request_ready(state, buffer_if.awvalid, buffer_if.wvalid, buffer_if.arvalid);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      access  <= rggen_access'(0);
      address <= '0;
    end
    else if ((state == IDLE) && (request_valid != '0)) begin
      access  <= bus_if.access;
      address <= bus_if.address;
    end
  end

  always_ff @(posedge i_clk) begin
    if ((state == IDLE) && (request_valid != '0)) begin
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
      write_valid = awvalid && wvalid;
      read_valid  = arvalid && (!write_valid);
    end
    else begin
      read_valid  = arvalid;
      write_valid = awvalid && wvalid && (!read_valid);
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
        arready = !(awvalid && wvalid);
      end
      else begin
        arready = '1;
        awready = (!arvalid) && wvalid;
        wvalid  = (!arvalid) && awvalid;
      end

      return {arready, wready, awready};
    end
    else begin
      return 3'b000;
    end
  endfunction

  //  Response
  logic [1:0]                             response_valid;
  logic                                   response_ack;
  logic [rggen_clip_width(ID_WIDTH)-1:0]  id;
  logic [BUS_WIDTH-1:0]                   read_data;
  logic [1:0]                             status;

  always_comb begin
    buffer_if.bvalid  = response_valid[0];
    buffer_if.bid     = id;
    buffer_if.bresp   = status;
  end

  always_comb begin
    buffer_if.rvalid  = response_valid[1];
    buffer_if.rid     = id;
    buffer_if.rresp   = status;
    buffer_if.rdata   = read_data;
  end

  always_comb begin
    response_ack  =
      (buffer_if.bvalid && buffer_if.bready) ||
      (buffer_if.rvalid && buffer_if.rready);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_valid  <= 2'b00;
    end
    else if (response_ack) begin
      response_valid  <= 2'b00;
    end
    else if (bus_if.valid && bus_if.ready) begin
      if (bus_if.access[RGGEN_ACCESS_DATA_BIT]) begin
        response_valid  <= 2'b01;
      end
      else begin
        response_valid  <= 2'b10;
      end
    end
  end

  generate if (ID_WIDTH > 0) begin : g_id
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        id  <= '0;
      end
      else if (buffer_if.awvalid && buffer_if.awready) begin
        id  <= buffer_if.awid;
      end
      else if (buffer_if.arvalid && buffer_if.arready) begin
        id  <= buffer_if.arid;
      end
    end
  end
  else begin : g_no_id
    always_comb begin
      id  = '0;
    end
  end endgenerate

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
