package rggen_rtl_pkg;
  typedef enum logic [1:0] {
    RGGEN_OKAY          = 2'b00,
    RGGEN_EXOKAY        = 2'b01,
    RGGEN_SLAVE_ERROR   = 2'b10,
    RGGEN_DECODE_ERROR  = 2'b11
  } rggen_status;
endpackage
