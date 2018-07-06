package org.batfish.bddreachability;

import java.util.List;
import javax.annotation.Nullable;
import net.sf.javabdd.BDD;
import org.batfish.z3.expr.StateExpr;

final class Edge {
  final BDD _constraint;
  final StateExpr _postState;
  final StateExpr _preState;
  final @Nullable List<BDDSourceNat> _sourceNats;

  Edge(StateExpr preState, StateExpr postState, BDD constraint) {
    _constraint = constraint;
    _postState = postState;
    _preState = preState;
    _sourceNats = null;
  }

  Edge(StateExpr preState, StateExpr postState, BDD constraint, List<BDDSourceNat> sourceNats) {
    _constraint = constraint;
    _postState = postState;
    _preState = preState;
    _sourceNats = sourceNats;
  }

  public BDD getConstraint() {
    return _constraint;
  }

  public List<BDDSourceNat> getSourceNats() {
    return _sourceNats;
  }
}
