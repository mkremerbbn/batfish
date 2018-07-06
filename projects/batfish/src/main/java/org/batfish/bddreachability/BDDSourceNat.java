package org.batfish.bddreachability;

import net.sf.javabdd.BDD;

final class BDDSourceNat {
  final BDD _condition;
  final BDD _updateSrcIp;

  public BDDSourceNat(BDD condition, BDD updateSrcIp) {
    _condition = condition;
    _updateSrcIp = updateSrcIp;
  }
}
