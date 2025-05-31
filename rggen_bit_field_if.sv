interface rggen_bit_field_if #(
  parameter int WIDTH = 32
);
  logic             write_valid;
  logic             read_valid;
  logic [WIDTH-1:0] mask;
  logic [WIDTH-1:0] write_data;
  logic [WIDTH-1:0] read_data;
  logic [WIDTH-1:0] value;

  modport register (
    output  write_valid,
    output  read_valid,
    output  mask,
    output  write_data,
    input   read_data,
    input   value
  );

  modport bit_field (
    input   write_valid,
    input   read_valid,
    input   mask,
    input   write_data,
    output  read_data,
    output  value
  );

  modport monitor (
    input write_valid,
    input read_valid,
    input mask,
    input write_data,
    input read_data,
    input value
  );
endinterface
