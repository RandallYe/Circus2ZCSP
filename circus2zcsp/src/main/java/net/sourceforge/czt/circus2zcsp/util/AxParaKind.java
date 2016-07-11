package net.sourceforge.czt.circus2zcsp.util;

public enum AxParaKind {
  AXDEF, 
  GEN_AXDEF, 
  ABBR, 
  GEN_ABBR, 
  BOXED_SCHEMA, 
  GEN_BOXED_SCHEMA, 
  HORIZON_SCHEMA, 
  GEN_HORIZON_SCHEMA,
  ;
  
  @Override
  public String toString()
  {
    String ret = "Unknown";
    switch(this) {
      case AXDEF:
        ret = "Axdef";
        break;
      case GEN_AXDEF:
        ret = "Generic Axdef";
        break;
      case ABBR:
        ret = "Abbreviation";
        break;
      case GEN_ABBR:
        ret = "Generic Axdef";
        break;
      case BOXED_SCHEMA:
      case HORIZON_SCHEMA:
        ret = "Schema";
        break;
      case GEN_BOXED_SCHEMA:
      case GEN_HORIZON_SCHEMA:
        ret = "Generic Schema";
        break;
      default:
        break;
    }
    return ret;
  }
}
