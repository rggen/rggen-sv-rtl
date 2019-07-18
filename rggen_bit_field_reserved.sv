module rggen_bit_field_reserved (
  rggen_bit_field_if.bit_field  bit_field_if
);
  assign  bit_field_if.read_data  = '0;
  assign  bit_field_if.value      = '0;
endmodule
