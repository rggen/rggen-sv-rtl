interface rggen_avalon_if #(
  parameter int ADDRESS_WIDTH = 16,
  parameter int BUS_WIDTH     = 32
);
  logic                     read;
  logic                     write;
  logic [ADDRESS_WIDTH-1:0] address;
  logic [BUS_WIDTH/8-1:0]   byteenable;
  logic [BUS_WIDTH-1:0]     writedata;
  logic                     waitrequest;
  logic [1:0]               response;
  logic [BUS_WIDTH-1:0]     readdata;

  modport host (
    output  read,
    output  write,
    output  address,
    output  byteenable,
    output  writedata,
    input   waitrequest,
    input   response,
    input   readdata
  );

  modport agent (
    input   read,
    input   write,
    input   address,
    input   byteenable,
    input   writedata,
    output  waitrequest,
    output  response,
    output  readdata
  );

  modport monitor (
    input read,
    input write,
    input address,
    input byteenable,
    input writedata,
    input waitrequest,
    input response,
    input readdata
  );
endinterface
