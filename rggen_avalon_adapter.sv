module rggen_avalon_adapter
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
  parameter bit                     INSERT_SLICER       = 0
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_avalon_if.agent   avalon_if,
  rggen_register_if.host  register_if[REGISTERS]
);
  rggen_bus_if #(ADDRESS_WIDTH, BUS_WIDTH)  bus_if();

  logic [1:0]               request_valid;
  logic                     read;
  logic [ADDRESS_WIDTH-1:0] address;
  logic [BUS_WIDTH/8-1:0]   byteenable;
  logic [BUS_WIDTH-1:0]     writedata;
  logic [1:0]               response_valid;
  logic [1:0]               response;
  logic [BUS_WIDTH-1:0]     readdata;

  always_comb begin
    avalon_if.waitrequest         = request_valid[1];
    avalon_if.readdatavalid       = response_valid[0];
    avalon_if.writeresponsevalid  = response_valid[1];
    avalon_if.response            = response;
    avalon_if.readdata            = readdata;
  end

  always_comb begin
    bus_if.valid  = request_valid != '0;
    if (request_valid[1]) begin
      bus_if.access     = (read) ? RGGEN_READ : RGGEN_WRITE;
      bus_if.address    = address;
      bus_if.write_data = writedata;
      bus_if.strobe     = byteenable;
    end
    else begin
      bus_if.access     = (avalon_if.read) ? RGGEN_READ : RGGEN_WRITE;
      bus_if.address    = avalon_if.address;
      bus_if.write_data = avalon_if.writedata;
      bus_if.strobe     = avalon_if.byteenable;
    end
  end

  always_comb begin
    request_valid[0]  = avalon_if.read || avalon_if.write;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      request_valid[1]  <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      request_valid[1]  <= '0;
    end
    else if (request_valid == 2'b01) begin
      request_valid[1]  <= '1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      read        <= '0;
      address     <= '0;
      byteenable  <= '0;
      writedata   <= '0;
    end
    else if (request_valid == 2'b01) begin
      read        <= avalon_if.read;
      address     <= avalon_if.address;
      byteenable  <= avalon_if.byteenable;
      writedata   <= avalon_if.writedata;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_valid  <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      if (bus_if.access == RGGEN_READ) begin
        response_valid  <= 2'b01;
      end
      else begin
        response_valid  <= 2'b10;
      end
    end
    else begin
      response_valid  <= '0;
    end
  end

  always_ff @(posedge i_clk) begin
    if (bus_if.valid && bus_if.ready) begin
      response  <= bus_if.status;
      readdata  <= bus_if.read_data;
    end
  end

  rggen_adapter_common #(
    .ADDRESS_WIDTH        (ADDRESS_WIDTH        ),
    .LOCAL_ADDRESS_WIDTH  (LOCAL_ADDRESS_WIDTH  ),
    .BUS_WIDTH            (BUS_WIDTH            ),
    .REGISTERS            (REGISTERS            ),
    .PRE_DECODE           (PRE_DECODE           ),
    .BASE_ADDRESS         (BASE_ADDRESS         ),
    .BYTE_SIZE            (BYTE_SIZE            ),
    .USE_READ_STROBE      (1                    ),
    .ERROR_STATUS         (ERROR_STATUS         ),
    .DEFAULT_READ_DATA    (DEFAULT_READ_DATA    ),
    .INSERT_SLICER        (INSERT_SLICER        )
  ) u_adapter_common (
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .bus_if       (bus_if       ),
    .register_if  (register_if  )
  );
endmodule
