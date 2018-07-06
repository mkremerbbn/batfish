package org.batfish.bddreachability;

import static org.batfish.bddreachability.TestNetwork.DST_PREFIX_1;
import static org.batfish.bddreachability.TestNetwork.DST_PREFIX_2;
import static org.batfish.bddreachability.TestNetwork.LINK_1_NETWORK;
import static org.batfish.bddreachability.TestNetwork.LINK_2_NETWORK;
import static org.batfish.bddreachability.TestNetwork.SOURCE_NAT_ACL_IP;
import static org.batfish.bddreachability.TestNetwork.SOURCE_NAT_POOL_IP;
import static org.batfish.datamodel.Configuration.DEFAULT_VRF_NAME;
import static org.batfish.symbolic.bdd.BDDMatchers.intersects;
import static org.batfish.symbolic.bdd.BDDMatchers.isEquivalentTo;
import static org.batfish.symbolic.bdd.BDDMatchers.isOne;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.hasKey;
import static org.hamcrest.Matchers.hasSize;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;

import com.google.common.collect.ImmutableSet;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import net.sf.javabdd.BDD;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.DataPlane;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.UniverseIpSpace;
import org.batfish.specifier.InterfaceLocation;
import org.batfish.specifier.IpSpaceAssignment;
import org.batfish.symbolic.bdd.BDDAcl;
import org.batfish.symbolic.bdd.BDDInteger;
import org.batfish.symbolic.bdd.BDDOps;
import org.batfish.symbolic.bdd.BDDPacket;
import org.batfish.symbolic.bdd.IpSpaceToBDD;
import org.batfish.z3.expr.StateExpr;
import org.batfish.z3.state.Accept;
import org.batfish.z3.state.Drop;
import org.batfish.z3.state.NeighborUnreachable;
import org.batfish.z3.state.NodeAccept;
import org.batfish.z3.state.NodeDropAclIn;
import org.batfish.z3.state.NodeDropAclOut;
import org.batfish.z3.state.NodeDropNoRoute;
import org.batfish.z3.state.NodeDropNullRoute;
import org.batfish.z3.state.NodeInterfaceNeighborUnreachable;
import org.batfish.z3.state.OriginateVrf;
import org.batfish.z3.state.PostInVrf;
import org.batfish.z3.state.PreInInterface;
import org.batfish.z3.state.PreOutEdge;
import org.batfish.z3.state.PreOutEdgePostNat;
import org.batfish.z3.state.PreOutVrf;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

public final class BDDReachabilityAnalysisTest {
  private static BDDReachabilityAnalysis GRAPH;
  private static BDDReachabilityAnalysisFactory GRAPH_FACTORY;
  private static TestNetwork NET;

  private BDDOps _bddOps;

  private Ip _dstIface1Ip;
  private BDD _dstIface1IpBDD;
  private Ip _dstIface2Ip;
  private BDD _dstIface2IpBDD;
  private String _dstIface1Name;
  private String _dstIface2Name;
  private String _dstName;
  private NodeAccept _dstNodeAccept;
  private PostInVrf _dstPostInVrf;
  private PreInInterface _dstPreInInterface1;
  private PreInInterface _dstPreInInterface2;
  private PreOutEdge _dstPreOutEdge1;
  private PreOutEdge _dstPreOutEdge2;
  private PreOutEdgePostNat _dstPreOutEdgePostNat1;
  private PreOutEdgePostNat _dstPreOutEdgePostNat2;
  private PreOutVrf _dstPreOutVrf;

  private Ip _link1DstIp;
  private BDD _link1DstIpBDD;
  private String _link1DstName;

  private BDD _link1SrcIpBDD;
  private String _link1SrcName;

  private Ip _link2DstIp;
  private BDD _link2DstIpBDD;
  private String _link2DstName;

  private BDD _link2SrcIpBDD;
  private String _link2SrcName;

  private String _srcName;
  private NodeAccept _srcNodeAccept;
  private PostInVrf _srcPostInVrf;
  private PreInInterface _srcPreInInterface1;
  private PreInInterface _srcPreInInterface2;
  private PreOutEdge _srcPreOutEdge1;
  private PreOutEdge _srcPreOutEdge2;
  private PreOutEdgePostNat _srcPreOutEdgePostNat1;
  private PreOutEdgePostNat _srcPreOutEdgePostNat2;
  private PreOutVrf _srcPreOutVrf;

  @BeforeClass
  public static void initFactory() throws IOException {
    NET = new TestNetwork();
    NET._batfish.computeDataPlane(false);
    DataPlane dataPlane = NET._batfish.loadDataPlane();
    GRAPH_FACTORY =
        new BDDReachabilityAnalysisFactory(NET._configs, dataPlane.getForwardingAnalysis(), false);

    IpSpaceAssignment assignment =
        IpSpaceAssignment.builder()
            .assign(
                new InterfaceLocation(NET._srcNode.getName(), NET._link1Src.getName()),
                UniverseIpSpace.INSTANCE)
            .build();
    GRAPH = GRAPH_FACTORY.bddNetworkGraph(assignment);
  }

  @Before
  public void setup() {
    _bddOps = new BDDOps(BDDPacket.factory);
    _dstIface1Ip = DST_PREFIX_1.getStartIp();
    _dstIface1IpBDD = dstIpBDD(_dstIface1Ip);
    _dstIface2Ip = DST_PREFIX_2.getStartIp();
    _dstIface2IpBDD = dstIpBDD(_dstIface2Ip);
    _dstIface1Name = NET._dstIface1.getName();
    _dstIface2Name = NET._dstIface2.getName();
    _dstName = NET._dstNode.getHostname();
    _dstNodeAccept = new NodeAccept(_dstName);
    _dstPostInVrf = new PostInVrf(_dstName, DEFAULT_VRF_NAME);
    _dstPreOutVrf = new PreOutVrf(_dstName, DEFAULT_VRF_NAME);

    _link1DstIp = LINK_1_NETWORK.getEndIp();
    _link1DstIpBDD = dstIpBDD(_link1DstIp);
    _link1DstName = NET._link1Dst.getName();

    _link1SrcName = NET._link1Src.getName();
    _link1SrcIpBDD = dstIpBDD(LINK_1_NETWORK.getStartIp());

    _link2DstIp = LINK_2_NETWORK.getEndIp();
    _link2DstIpBDD = dstIpBDD(_link2DstIp);
    _link2DstName = NET._link2Dst.getName();

    _link2SrcIpBDD = dstIpBDD(LINK_2_NETWORK.getStartIp());
    _link2SrcName = NET._link2Src.getName();

    _srcName = NET._srcNode.getHostname();
    _srcNodeAccept = new NodeAccept(_srcName);
    _srcPostInVrf = new PostInVrf(_srcName, DEFAULT_VRF_NAME);

    _dstPreInInterface1 = new PreInInterface(_dstName, _link1DstName);
    _dstPreInInterface2 = new PreInInterface(_dstName, _link2DstName);

    _srcPreInInterface1 = new PreInInterface(_srcName, _link1SrcName);
    _srcPreInInterface2 = new PreInInterface(_srcName, _link2SrcName);

    _dstPreOutEdge1 = new PreOutEdge(_dstName, _link1DstName, _srcName, _link1SrcName);
    _dstPreOutEdge2 = new PreOutEdge(_dstName, _link2DstName, _srcName, _link2SrcName);
    _dstPreOutEdgePostNat1 =
        new PreOutEdgePostNat(_dstName, _link1DstName, _srcName, _link1SrcName);
    _dstPreOutEdgePostNat2 =
        new PreOutEdgePostNat(_dstName, _link2DstName, _srcName, _link2SrcName);
    _srcPreOutEdge1 = new PreOutEdge(_srcName, _link1SrcName, _dstName, _link1DstName);
    _srcPreOutEdge2 = new PreOutEdge(_srcName, _link2SrcName, _dstName, _link2DstName);
    _srcPreOutEdgePostNat1 =
        new PreOutEdgePostNat(_srcName, _link1SrcName, _dstName, _link1DstName);
    _srcPreOutEdgePostNat2 =
        new PreOutEdgePostNat(_srcName, _link2SrcName, _dstName, _link2DstName);
    _srcPreOutVrf = new PreOutVrf(_srcName, DEFAULT_VRF_NAME);
  }

  private static List<Ip> bddIps(BDD bdd) {
    BDDInteger bddInteger = GRAPH_FACTORY.getIpSpaceToBDD().getBDDInteger();

    return bddInteger
        .getValuesSatisfying(bdd, 10)
        .stream()
        .map(Ip::new)
        .collect(Collectors.toList());
  }

  private static BDD bddTransition(StateExpr preState, StateExpr postState) {
    return GRAPH_FACTORY.getBDDTransitions().get(preState).get(postState);
  }

  private static BDD dstIpBDD(Ip ip) {
    return new IpSpaceToBDD(BDDPacket.factory, new BDDPacket().getDstIp()).toBDD(ip);
  }

  private static BDD srcIpBDD(Ip ip) {
    return new IpSpaceToBDD(BDDPacket.factory, new BDDPacket().getSrcIp()).toBDD(ip);
  }

  private BDD or(BDD... bdds) {
    return _bddOps.or(bdds);
  }

  private static BDD vrfAcceptBDD(String node) {
    return GRAPH_FACTORY.getVrfAcceptBDDs().get(node).get(DEFAULT_VRF_NAME);
  }

  @Test
  public void testVrfAcceptBDDs() {
    assertThat(
        vrfAcceptBDD(_dstName),
        isEquivalentTo(or(_link1DstIpBDD, _link2DstIpBDD, _dstIface1IpBDD, _dstIface2IpBDD)));
    assertThat(vrfAcceptBDD(_srcName), isEquivalentTo(or(_link1SrcIpBDD, _link2SrcIpBDD)));
  }

  @Test
  public void testBDDTransitions_NodeAccept_Accept() {
    assertThat(bddTransition(_srcNodeAccept, Accept.INSTANCE), isOne());
    assertThat(bddTransition(_dstNodeAccept, Accept.INSTANCE), isOne());
  }

  @Test
  public void testBDDTransitions_PostInVrf_outEdges() {
    BDD nodeAccept = bddTransition(_srcPostInVrf, _srcNodeAccept);
    BDD nodeDropNoRoute = bddTransition(_srcPostInVrf, new NodeDropNoRoute(_srcName));
    BDD preOutVrf = bddTransition(_srcPostInVrf, _srcPreOutVrf);

    // test that out edges are mutually exclusive
    assertThat(nodeAccept, not(intersects(nodeDropNoRoute)));
    assertThat(nodeAccept, not(intersects(preOutVrf)));
    assertThat(nodeDropNoRoute, not(intersects(preOutVrf)));
  }

  @Test
  public void testBDDTransitions_PostInVrf_NodeAccept() {
    assertThat(
        bddTransition(_srcPostInVrf, new NodeAccept(_srcName)),
        isEquivalentTo(or(_link1SrcIpBDD, _link2SrcIpBDD)));
    assertThat(
        bddTransition(_dstPostInVrf, new NodeAccept(_dstName)),
        isEquivalentTo(or(_link1DstIpBDD, _link2DstIpBDD, _dstIface1IpBDD, _dstIface2IpBDD)));
  }

  @Test
  public void testBDDTransitions_PostInVrf_PreOutVrf() {
    assertThat(
        bddTransition(_dstPostInVrf, _dstPreOutVrf),
        isEquivalentTo(or(_link1SrcIpBDD, _link2SrcIpBDD)));

    assertThat(
        bddTransition(_srcPostInVrf, _srcPreOutVrf),
        isEquivalentTo(or(_link1DstIpBDD, _link2DstIpBDD, _dstIface1IpBDD, _dstIface2IpBDD)));
  }

  @Test
  public void testBDDTransitions_PreInInterface_NodeDropAclIn() {
    NodeDropAclIn dstDropAclIn = new NodeDropAclIn(_dstName);
    assertThat(
        bddTransition(_dstPreInInterface1, dstDropAclIn), isEquivalentTo(dstIpBDD(_dstIface2Ip)));
    assertThat(bddTransition(_dstPreInInterface2, dstDropAclIn), nullValue());
  }

  @Test
  public void testBDDTransitions_PreInInterface_PostInVrf() {
    // link1: not(_dstIface2Ip)
    assertThat(
        bddTransition(_dstPreInInterface1, _dstPostInVrf),
        isEquivalentTo(dstIpBDD(_dstIface2Ip).not()));
    // link2: universe
    assertThat(bddTransition(_dstPreInInterface2, _dstPostInVrf), isOne());
  }

  @Test
  public void testBDDTransitions_PreOutVrf_outEdges() {
    String link1SrcName = NET._link1Src.getName();
    String link2SrcName = NET._link2Src.getName();
    PreOutEdgePostNat link1PreOutEdgePostNat =
        new PreOutEdgePostNat(_srcName, link1SrcName, _dstName, _link1DstName);
    PreOutEdgePostNat link2PreOutEdgePostNat =
        new PreOutEdgePostNat(_srcName, link2SrcName, _dstName, _link2DstName);
    BDD nodeDropNullRoute = bddTransition(_srcPreOutVrf, new NodeDropNullRoute(_srcName));
    BDD nodeInterfaceNeighborUnreachable1 =
        bddTransition(_srcPreOutVrf, new NodeInterfaceNeighborUnreachable(_srcName, link1SrcName));
    BDD nodeInterfaceNeighborUnreachable2 =
        bddTransition(_srcPreOutVrf, new NodeInterfaceNeighborUnreachable(_srcName, link2SrcName));
    BDD preOutEdge1 = bddTransition(_srcPreOutVrf, _srcPreOutEdge1);
    BDD preOutEdge2 = bddTransition(_srcPreOutVrf, _srcPreOutEdge2);

    assertThat(nodeDropNullRoute, nullValue());

    assertThat(nodeInterfaceNeighborUnreachable1, isEquivalentTo(_link1SrcIpBDD));
    assertThat(nodeInterfaceNeighborUnreachable2, isEquivalentTo(_link2SrcIpBDD));

    assertThat(
        bddIps(preOutEdge1),
        containsInAnyOrder(_dstIface1Ip, _dstIface2Ip, NET._link1Dst.getAddress().getIp()));
    assertThat(
        bddIps(preOutEdge2), containsInAnyOrder(_dstIface2Ip, NET._link2Dst.getAddress().getIp()));

    // ECMP: _dstIface1Ip is routed out both edges
    assertThat(preOutEdge1.and(preOutEdge2), isEquivalentTo(dstIpBDD(_dstIface2Ip)));
  }

  @Test
  public void testBDDTransitions_PreOutVrf_NodeInterfaceNeighborUnreachable() {
    /*
     * These predicates include the IP address of the interface, which is technically wrong.
     * It doesn't matter because those addresses can't get to PreOutVrf from PostInVrf.
     */
    assertThat(
        bddTransition(
            _dstPreOutVrf, new NodeInterfaceNeighborUnreachable(_dstName, _dstIface1Name)),
        isEquivalentTo(_dstIface1IpBDD));
    assertThat(
        bddTransition(
            _dstPreOutVrf, new NodeInterfaceNeighborUnreachable(_dstName, _dstIface2Name)),
        isEquivalentTo(_dstIface2IpBDD));
    assertThat(
        bddTransition(_dstPreOutVrf, new NodeInterfaceNeighborUnreachable(_dstName, _link1DstName)),
        isEquivalentTo(_link1DstIpBDD));
    assertThat(
        bddTransition(_dstPreOutVrf, new NodeInterfaceNeighborUnreachable(_dstName, _link2DstName)),
        isEquivalentTo(_link2DstIpBDD));
  }

  @Test
  public void testBDDTransitions_PreOutVrf_PreOutEdge() {
    assertThat(
        bddTransition(_srcPreOutVrf, _srcPreOutEdge1),
        isEquivalentTo(or(_link1DstIpBDD, _dstIface1IpBDD, _dstIface2IpBDD)));
    assertThat(
        bddTransition(_srcPreOutVrf, _srcPreOutEdge2),
        isEquivalentTo(or(_link2DstIpBDD, _dstIface2IpBDD)));

    assertThat(bddTransition(_dstPreOutVrf, _dstPreOutEdge1), isEquivalentTo(_link1SrcIpBDD));
    assertThat(bddTransition(_dstPreOutVrf, _dstPreOutEdge2), isEquivalentTo(_link2SrcIpBDD));
  }

  @Test
  public void testBDDTransitions_PreOutEdgePostNat_NodeDropAclOut() {
    assertThat(bddTransition(_dstPreOutEdgePostNat1, new NodeDropAclOut(_dstName)), nullValue());
    assertThat(bddTransition(_dstPreOutEdgePostNat2, new NodeDropAclOut(_dstName)), nullValue());
    assertThat(bddTransition(_srcPreOutEdgePostNat1, new NodeDropAclOut(_srcName)), nullValue());
    assertThat(bddTransition(_srcPreOutEdgePostNat2, new NodeDropAclOut(_srcName)), nullValue());
  }

  @Test
  public void testBDDTransitions_PreOutEdgePostNat_PreInInterface() {
    assertThat(bddTransition(_dstPreOutEdgePostNat1, _srcPreInInterface1), isOne());
    assertThat(bddTransition(_dstPreOutEdgePostNat2, _srcPreInInterface2), isOne());
    assertThat(bddTransition(_srcPreOutEdgePostNat1, _dstPreInInterface1), isOne());
    assertThat(bddTransition(_srcPreOutEdgePostNat2, _dstPreInInterface2), isOne());
  }

  @Test
  public void testGraph_terminalStates() {
    Set<StateExpr> terminalStates = GRAPH.getLeafStates();
    assertThat(
        terminalStates,
        equalTo(ImmutableSet.of(Accept.INSTANCE, Drop.INSTANCE, NeighborUnreachable.INSTANCE)));
  }

  @Test
  public void testBDDNetworkGraph_sourceNat_match() {
    IpSpaceAssignment assignment =
        IpSpaceAssignment.builder()
            .assign(
                new InterfaceLocation(NET._srcNode.getName(), NET._link1Src.getName()),
                SOURCE_NAT_ACL_IP.toIpSpace())
            .build();

    BDDReachabilityAnalysis graph =
        GRAPH_FACTORY.bddNetworkGraph(assignment, _dstIface2Ip.toIpSpace());
    graph.computeReachability();

    BDD dstIpBDD = GRAPH_FACTORY.getIpSpaceToBDD().toBDD(_dstIface2Ip);
    BDD natPoolIpBDD = srcIpBDD(SOURCE_NAT_POOL_IP);
    BDD natAclIpBDD = srcIpBDD(SOURCE_NAT_ACL_IP);

    BDD srcNatAclBDD = BDDAcl.create(NET._link2SrcSourceNatAcl).getBdd();
    assertThat(srcNatAclBDD, isEquivalentTo(natAclIpBDD));

    OriginateVrf originateVrf = new OriginateVrf(_srcName, Configuration.DEFAULT_VRF_NAME);
    PreOutEdgePostNat preOutEdge2PostNat =
        new PreOutEdgePostNat(_srcName, _link2SrcName, _dstName, _link2DstName);

    assertThat(graph.getNatRoots(), hasKey(preOutEdge2PostNat));
    Map<StateExpr, StateExpr> natRoots = graph.getNatRoots().get(preOutEdge2PostNat);
    assertThat(natRoots, hasKey(originateVrf));
    StateExpr logicalRoot = natRoots.get(originateVrf);

    BDD preOutEdgePostNatLink2 = graph._reachableStates.get(preOutEdge2PostNat).get(logicalRoot);

    assertThat(preOutEdgePostNatLink2, isEquivalentTo(dstIpBDD.and(natPoolIpBDD)));

    List<BDDReachabilityAnalysis.MultipathConsistencyViolation> violations =
        graph.detectMultipathInconsistency();

    /*
     * TODO: we should get a violation here, but it's masked because NAT only occurs along one path.
     * The solution is to map back to the original headerspaces, and report violations based on
     * those.
     */
    assertThat(violations, hasSize(0));
  }

  @Test
  public void testBDDNetworkGraph_sourceNat_noMatch() {
    IpSpaceAssignment assignment =
        IpSpaceAssignment.builder()
            .assign(
                new InterfaceLocation(NET._srcNode.getName(), NET._link1Src.getName()),
                Ip.MAX.toIpSpace())
            .build();

    BDDReachabilityAnalysis graph =
        GRAPH_FACTORY.bddNetworkGraph(assignment, _dstIface2Ip.toIpSpace());
    graph.computeReachability();

    BDD dstIpBDD = GRAPH_FACTORY.getIpSpaceToBDD().toBDD(_dstIface2Ip);
    BDD srcIpBDD = srcIpBDD(Ip.MAX);

    OriginateVrf originateVrf = new OriginateVrf(_srcName, Configuration.DEFAULT_VRF_NAME);
    BDD preOutEdgePostNatLink2 =
        graph
            ._reachableStates
            .get(new PreOutEdgePostNat(_srcName, _link2SrcName, _dstName, _link2DstName))
            .get(originateVrf);

    assertThat(preOutEdgePostNatLink2, isEquivalentTo(dstIpBDD.and(srcIpBDD)));
    List<BDDReachabilityAnalysis.MultipathConsistencyViolation> violations =
        graph.detectMultipathInconsistency();
    assertThat(violations, hasSize(1));
    BDDReachabilityAnalysis.MultipathConsistencyViolation violation = violations.get(0);
    assertThat(violation.finalStates, equalTo(ImmutableSet.of(Accept.INSTANCE, Drop.INSTANCE)));
    assertThat(violation.predicate, isEquivalentTo(dstIpBDD.and(srcIpBDD)));
  }
}
