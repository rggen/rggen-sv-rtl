interface rggen_axi4lite_if #(
  parameter int ADDRESS_WIDTH = 16,
  parameter int BUS_WIDTH     = 32
);
  logic                     awvalid;
  logic                     awready;
  logic [ADDRESS_WIDTH-1:0] awaddr;
  logic [2:0]               awprot;
  logic                     wvalid;
  logic                     wready;
  logic [BUS_WIDTH-1:0]     wdata;
  logic [BUS_WIDTH/8-1:0]   wstrb;
  logic                     bvalid;
  logic                     bready;
  logic [1:0]               bresp;
  logic                     arvalid;
  logic                     arready;
  logic [ADDRESS_WIDTH-1:0] araddr;
  logic [2:0]               arprot;
  logic                     rvalid;
  logic                     rready;
  logic [1:0]               rresp;
  logic [BUS_WIDTH-1:0]     rdata;

  modport master (
    output  awvalid,
    input   awready,
    output  awaddr,
    output  awprot,
    output  wvalid,
    input   wready,
    output  wdata,
    output  wstrb,
    input   bvalid,
    output  bready,
    input   bresp,
    output  arvalid,
    input   arready,
    output  araddr,
    output  arprot,
    input   rvalid,
    output  rready,
    input   rresp,
    input   rdata
  );

  modport slave (
    input   awvalid,
    output  awready,
    input   awaddr,
    input   awprot,
    input   wvalid,
    output  wready,
    input   wdata,
    input   wstrb,
    output  bvalid,
    input   bready,
    output  bresp,
    input   arvalid,
    output  arready,
    input   araddr,
    input   arprot,
    output  rvalid,
    input   rready,
    output  rresp,
    output  rdata
  );

  modport monitor (
    input awvalid,
    input awready,
    input awaddr,
    input awprot,
    input wvalid,
    input wready,
    input wdata,
    input wstrb,
    input bvalid,
    input bready,
    input bresp,
    input arvalid,
    input arready,
    input araddr,
    input arprot,
    input rvalid,
    input rready,
    input rresp,
    input rdata
  );
endinterface
