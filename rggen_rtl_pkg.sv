package rggen_rtl_pkg;
  typedef enum logic [1:0] {
    RGGEN_READ          = 2'b10,
    RGGEN_POSTED_WRITE  = 2'b01,
    RGGEN_WRITE         = 2'b11
  } rggen_access;

  localparam  int RGGEN_ACCESS_DATA_BIT       = 0;
  localparam  int RGGEN_ACCESS_NON_POSTED_BIT = 1;

  typedef enum logic [1:0] {
    RGGEN_OKAY          = 2'b00,
    RGGEN_EXOKAY        = 2'b01,
    RGGEN_SLAVE_ERROR   = 2'b10,
    RGGEN_DECODE_ERROR  = 2'b11
  } rggen_status;
endpackage
