module rggen_address_decoder
  import  rggen_rtl_pkg::*;
#(
  parameter bit             READABLE      = 1,
  parameter bit             WRITABLE      = 1,
  parameter int             WIDTH         = 8,
  parameter int             LSB           = 0,
  parameter bit [WIDTH-1:0] START_ADDRESS = '0,
  parameter bit [WIDTH-1:0] END_ADDRESS   = '0
)(
  input   logic [WIDTH-1:0] i_address,
  input   rggen_access      i_access,
  input   logic             i_additional_match,
  output  logic             o_match
);
  logic address_match;
  logic access_match;

  generate
    if (START_ADDRESS[WIDTH-1:LSB] == END_ADDRESS[WIDTH-1:LSB]) begin : g_address_matcher
      assign  address_match =
        (i_address[WIDTH-1:LSB] == START_ADDRESS[WIDTH-1:LSB]) ? '1 : '0;
    end
    else begin : g_address_matcher
      assign  address_match = (
        (i_address[WIDTH-1:LSB] >= START_ADDRESS[WIDTH-1:LSB]) &&
        (i_address[WIDTH-1:LSB] <= END_ADDRESS[WIDTH-1:LSB]  )
      ) ? '1 : '0;
    end

    if (READABLE && WRITABLE) begin : g_access_matcher
      assign  access_match  = '1;
    end
    else if (READABLE) begin : g_access_matcher
      assign  access_match  = (!i_access[RGGEN_ACCESS_DATA_BIT]);
    end
    else begin : g_access_matcher
      assign  access_match  = i_access[RGGEN_ACCESS_DATA_BIT];
    end
  endgenerate

  assign  o_match = (
    address_match && access_match && i_additional_match
  ) ? '1 : '0;
endmodule
