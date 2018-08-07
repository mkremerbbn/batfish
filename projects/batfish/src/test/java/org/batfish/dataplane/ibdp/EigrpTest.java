package org.batfish.dataplane.ibdp;

import static java.util.Objects.requireNonNull;
import static org.batfish.datamodel.RoutingProtocol.EIGRP;
import static org.batfish.datamodel.RoutingProtocol.EIGRP_EX;
import static org.batfish.datamodel.RoutingProtocol.OSPF;
import static org.batfish.dataplane.ibdp.TestUtils.assertNoRoute;
import static org.batfish.dataplane.ibdp.TestUtils.assertRoute;
import static org.batfish.representation.cisco.Interface.getDefaultBandwidth;
import static org.batfish.representation.cisco.Interface.getDefaultDelay;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSortedMap;
import java.util.Collections;
import java.util.List;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.concurrent.atomic.AtomicInteger;
import javax.annotation.Nullable;
import org.batfish.common.BatfishLogger;
import org.batfish.common.util.CommonUtil;
import org.batfish.datamodel.AbstractRoute;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.InterfaceAddress;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.Topology;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.eigrp.EigrpInterfaceSettings;
import org.batfish.datamodel.eigrp.EigrpMetric;
import org.batfish.datamodel.eigrp.EigrpProcess;
import org.batfish.datamodel.eigrp.EigrpProcessMode;
import org.batfish.datamodel.ospf.OspfArea;
import org.batfish.datamodel.ospf.OspfProcess;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.LiteralEigrpMetric;
import org.batfish.datamodel.routing_policy.expr.MatchProtocol;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.SetEigrpMetric;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements;
import org.junit.Ignore;
import org.junit.Test;

public class EigrpTest {

  private static final InterfaceAddress R1_E1_2_ADDR = new InterfaceAddress("10.12.0.1/24");
  private static final InterfaceAddress R1_L0_ADDR = new InterfaceAddress("1.1.1.1/32");
  private static final InterfaceAddress R1_E1_4_ADDR = new InterfaceAddress("10.14.0.1/24");
  private static final String R1 = "R1";

  private static final InterfaceAddress R2_E2_1_ADDR = new InterfaceAddress("10.12.0.2/24");
  private static final InterfaceAddress R2_E2_3_ADDR = new InterfaceAddress("10.23.0.2/24");
  private static final InterfaceAddress R2_L0_ADDR = new InterfaceAddress("2.2.2.2/32");
  private static final String R2 = "R2";

  private static final InterfaceAddress R3_E3_2_ADDR = new InterfaceAddress("10.23.0.3/24");
  private static final InterfaceAddress R3_E3_4_ADDR = new InterfaceAddress("10.34.0.3/24");
  private static final InterfaceAddress R3_L0_ADDR = new InterfaceAddress("3.3.3.3/32");
  private static final String R3 = "R3";

  private static final InterfaceAddress R4_E4_1_ADDR = new InterfaceAddress("10.14.0.4/24");
  private static final InterfaceAddress R4_E4_3_ADDR = new InterfaceAddress("10.34.0.4/24");
  private static final InterfaceAddress R4_L0_ADDR = new InterfaceAddress("4.4.4.4/32");
  private static final String R4 = "R4";

  private static final double externalBandwidth = 1E8;
  private static final double externalDelay = 1E9;

  /*
   * Int:1/2   2/1      2/3   3/2      3/4   4/3
   * R1 <=========> R2 <=========> R3 <=========> R4
   */
  private static IncrementalDataPlane computeLinearDataPlane(
      EigrpProcessMode mode1,
      EigrpProcessMode mode2,
      EigrpProcessMode mode3,
      EigrpProcessMode mode4,
      String interfacePrefix) {

    long asn = 1L;
    String c1E1To2Name = interfacePrefix + "1/2";
    String c2E2To1Name = interfacePrefix + "2/1";
    String c2E2To3Name = interfacePrefix + "2/3";
    String c3E3To2Name = interfacePrefix + "3/2";
    String c3E3To4Name = interfacePrefix + "3/4";
    String c4E4To3Name = interfacePrefix + "4/3";

    NetworkFactory nf = new NetworkFactory();

    EigrpProcess.Builder epb =
        EigrpProcess.builder().setAsNumber(asn).setRouterId(new Ip("100.100.100.100"));
    Interface.Builder eib = nf.interfaceBuilder().setActive(true).setOspfCost(1);

    /* Configuration 1 */
    Configuration c1 = buildConfiguration(R1, eib, epb, null, null, null);
    // Build EIGRP
    epb.setMode(mode1).build();
    buildEigrpLoopbackInterface(eib, asn, mode1, R1_L0_ADDR);
    buildEigrpExternalInterface(eib, asn, mode1, R1_E1_2_ADDR, c1E1To2Name, 1.0);

    /* Configuration 2 */
    Configuration c2 = buildConfiguration(R2, eib, epb, null, null, null);
    // Build EIGRP
    epb.setMode(mode2).build();
    buildEigrpLoopbackInterface(eib, asn, mode2, R2_L0_ADDR);
    buildEigrpExternalInterface(eib, asn, mode2, R2_E2_1_ADDR, c2E2To1Name, 1.0);
    buildEigrpExternalInterface(eib, asn, mode2, R2_E2_3_ADDR, c2E2To3Name, 1.0);

    /* Configuration 3 */
    Configuration c3 = buildConfiguration(R3, eib, epb, null, null, null);
    // Build EIGRP
    epb.setMode(mode3).build();
    buildEigrpLoopbackInterface(eib, asn, mode3, R3_L0_ADDR);
    buildEigrpExternalInterface(eib, asn, mode3, R3_E3_2_ADDR, c3E3To2Name, 1.0);
    buildEigrpExternalInterface(eib, asn, mode3, R3_E3_4_ADDR, c3E3To4Name, 1.0);

    /* Configuration 4 */
    Configuration c4 = buildConfiguration(R4, eib, epb, null, null, null);
    // Build EIGRP
    epb.setMode(mode4).build();
    buildEigrpLoopbackInterface(eib, asn, mode4, R4_L0_ADDR);
    buildEigrpExternalInterface(eib, asn, mode4, R4_E4_3_ADDR, c4E4To3Name, 1.0);

    return buildDataPlane(c1, c2, c3, c4);
  }

  private static List<Statement> getExportPolicyStatements(RoutingProtocol protocol) {
    EigrpMetric metric =
        requireNonNull(
            EigrpMetric.builder()
                .setBandwidth(externalBandwidth)
                .setDelay(externalDelay)
                .setMode(EigrpProcessMode.CLASSIC)
                .build());

    If exportIfMatchProtocol = new If();
    exportIfMatchProtocol.setGuard(new MatchProtocol(protocol));
    exportIfMatchProtocol.setTrueStatements(
        ImmutableList.of(
            new SetEigrpMetric(new LiteralEigrpMetric(metric)),
            Statements.ExitAccept.toStaticStatement()));
    exportIfMatchProtocol.setFalseStatements(
        ImmutableList.of(Statements.ExitReject.toStaticStatement()));
    return ImmutableList.of(exportIfMatchProtocol);
  }

  /*
   * Four routers, configured in a square. Each router has external interfaces as depicted and a
   * single loopback interface. The names of the external interface between router RA and router RB is
   * <interfacePrefix><A>/<B>. R1 is running OSPF, R3 is running EIGRP, and R2/R4 are running both
   * EIGRP and OSPF with redistribution of OSPF routes into EIGRP.
   *
   *
   *           2/3   3/2
   *   R2.O,E <=========> R3.E
   *    2/1|              | 3/4
   *       |              |
   *       |              |
   *    1/2|   1/4   4/1  | 4/3
   *     R1.O <=========> R4.O,E
   */
  private static IncrementalDataPlane computeMultipathDataPlaneWithRedistribution(
      EigrpProcessMode mode1,
      EigrpProcessMode mode2,
      EigrpProcessMode mode3,
      EigrpProcessMode mode4,
      String interfacePrefix,
      RoutingProtocol otherProcess) {

    long asn = 1L;
    long otherAsn = 2L;
    long area = 1L;
    String c1E1To2Name = interfacePrefix + "1/2";
    double c1E1To2DelayMult = 10.0;
    String c1E1To4Name = interfacePrefix + "1/4";
    double c1E1To4DelayMult = 200.0;
    String c2E2To1Name = interfacePrefix + "2/1";
    double c2E2To1DelayMult = 3000.0;
    String c2E2To3Name = interfacePrefix + "2/3";
    double c2E2To3DelayMult = 40000.0;
    String c3E3To2Name = interfacePrefix + "3/2";
    double c3E3To2DelayMult = 500000.0;
    String c3E3To4Name = interfacePrefix + "3/4";
    double c3E3To4DelayMult = 6000000.0;
    String c4E4To1Name = interfacePrefix + "4/1";
    double c4E4To1DelayMult = 70000000.0;
    String c4E4To3Name = interfacePrefix + "4/3";
    double c4E4To3DelayMult = 800000000.0;

    NetworkFactory nf = new NetworkFactory();
    RoutingPolicy.Builder exportOspf =
        nf.routingPolicyBuilder().setStatements(getExportPolicyStatements(RoutingProtocol.OSPF));
    RoutingPolicy.Builder exportConnected =
        nf.routingPolicyBuilder()
            .setStatements(getExportPolicyStatements(RoutingProtocol.CONNECTED));

    EigrpProcess.Builder epb =
        EigrpProcess.builder().setAsNumber(asn).setRouterId(new Ip("100.100.100.100"));
    Interface.Builder eib = nf.interfaceBuilder().setActive(true).setOspfCost(1);

    Interface.Builder nib = nf.interfaceBuilder().setActive(true).setOspfCost(1);

    OspfProcess.Builder opb = nf.ospfProcessBuilder();
    OspfArea.Builder oab = nf.ospfAreaBuilder().setNumber(area);
    Interface.Builder oib =
        nf.interfaceBuilder().setActive(true).setOspfCost(1).setOspfEnabled(true);

    /* Configuration 1 */
    Configuration c1 = buildConfiguration(R1, eib, epb, oib, opb, nib);
    if (otherProcess == OSPF) {
      // Build OSPF
      oib.setOspfArea(oab.setOspfProcess(opb.build()).build());
      buildOspfLoopbackInterface(oib, R1_L0_ADDR);
      buildOspfExternalInterface(oib, c1E1To2Name, R1_E1_2_ADDR);
      buildOspfExternalInterface(oib, c1E1To4Name, R1_E1_4_ADDR);
    } else if (otherProcess == EIGRP) {
      // Build other EIGRP
      epb.setAsNumber(otherAsn).setRouterId(new Ip("200.200.200.200")).build();
      epb.setMode(mode1).build();
      buildEigrpLoopbackInterface(eib, otherAsn, mode1, R1_L0_ADDR);
      buildEigrpExternalInterface(
          eib, otherAsn, mode1, R1_E1_2_ADDR, c1E1To2Name, c1E1To2DelayMult);
      buildEigrpExternalInterface(
          eib, otherAsn, mode1, R1_E1_4_ADDR, c1E1To4Name, c1E1To4DelayMult);
      // reset builder
      epb.setAsNumber(asn).setRouterId(new Ip("100.100.100.100"));
    }

    /* Configuration 2 */
    Configuration c2 = buildConfiguration(R2, eib, epb, oib, opb, nib);
    // Build EIGRP (with redistribute other process only for OSPF)
    if (otherProcess == OSPF) {
      epb.setExportPolicy(exportOspf.setOwner(c2).build().getName());
    }
    epb.setMode(mode2).build();
    buildEigrpExternalInterface(eib, asn, mode2, R2_E2_3_ADDR, c2E2To3Name, c2E2To3DelayMult);
    if (otherProcess == OSPF) {
      // Build OSPF
      oib.setOspfArea(oab.setOspfProcess(opb.build()).build());
      buildOspfLoopbackInterface(oib, R2_L0_ADDR);
      buildOspfExternalInterface(oib, c2E2To1Name, R2_E2_1_ADDR);
    } else if (otherProcess == EIGRP) {
      // Build other EIGRP
      epb.setAsNumber(otherAsn).setRouterId(new Ip("200.200.200.200")).build();
      buildEigrpLoopbackInterface(eib, otherAsn, mode2, R2_L0_ADDR);
      buildEigrpExternalInterface(
          eib, otherAsn, mode2, R2_E2_1_ADDR, c2E2To1Name, c2E2To1DelayMult);
      // reset builder
      epb.setAsNumber(asn).setRouterId(new Ip("100.100.100.100"));
    }

    /* Configuration 3 */
    Configuration c3 = buildConfiguration(R3, eib, epb, oib, opb, nib);
    // No process
    buildNoneInterface(nib, R3_L0_ADDR);
    // Build EIGRP with redistribute connected
    epb.setExportPolicy(exportConnected.setOwner(c3).build().getName());
    epb.setMode(mode3).build();
    buildEigrpExternalInterface(eib, asn, mode3, R3_E3_2_ADDR, c3E3To2Name, c3E3To2DelayMult);
    buildEigrpExternalInterface(eib, asn, mode3, R3_E3_4_ADDR, c3E3To4Name, c3E3To4DelayMult);

    /* Configuration 4 */
    Configuration c4 = buildConfiguration(R4, eib, epb, oib, opb, nib);
    // Build EIGRP with redistribute OSPF
    epb.setExportPolicy(exportOspf.setOwner(c4).build().getName());
    epb.setMode(mode4).build();
    buildEigrpLoopbackInterface(eib, asn, mode4, R4_L0_ADDR);
    buildEigrpExternalInterface(eib, asn, mode4, R4_E4_3_ADDR, c4E4To3Name, c4E4To3DelayMult);
    if (otherProcess == OSPF) {
      // Build OSPF
      oib.setOspfArea(oab.setOspfProcess(opb.build()).build());
      buildOspfExternalInterface(oib, c4E4To1Name, R4_E4_1_ADDR);
    } else if (otherProcess == EIGRP) {
      // Build other EIGRP
      epb.setAsNumber(otherAsn).setRouterId(new Ip("200.200.200.200")).build();
      buildEigrpExternalInterface(
          eib, otherAsn, mode4, R4_E4_1_ADDR, c4E4To1Name, c4E4To1DelayMult);
      // reset builder
      epb.setAsNumber(asn).setRouterId(new Ip("100.100.100.100"));
    }

    return buildDataPlane(c1, c2, c3, c4);
  }

  private static Configuration buildConfiguration(
      String hostname,
      Interface.Builder eib,
      EigrpProcess.Builder epb,
      @Nullable Interface.Builder oib,
      @Nullable OspfProcess.Builder opb,
      @Nullable Interface.Builder nib) {
    ConfigurationFormat format = ConfigurationFormat.CISCO_IOS;
    NetworkFactory nf = new NetworkFactory();
    Vrf.Builder vb = nf.vrfBuilder().setName(Configuration.DEFAULT_VRF_NAME);
    Configuration.Builder cb = nf.configurationBuilder().setConfigurationFormat(format);
    Configuration c = cb.setHostname(hostname).build();
    Vrf v = vb.setOwner(c).build();
    if (epb != null && eib != null) {
      epb.setExportPolicy(null).setVrf(v);
      eib.setOwner(c).setVrf(v);
    }
    if (nib != null) {
      nib.setOwner(c).setVrf(v);
    }
    if (opb != null && oib != null) {
      opb.setVrf(v);
      oib.setOwner(c).setVrf(v);
    }
    return c;
  }

  private static IncrementalDataPlane buildDataPlane(
      Configuration c1, Configuration c2, Configuration c3, Configuration c4) {
    SortedMap<String, Configuration> configurations =
        new ImmutableSortedMap.Builder<String, Configuration>(String::compareTo)
            .put(c1.getHostname(), c1)
            .put(c2.getHostname(), c2)
            .put(c3.getHostname(), c3)
            .put(c4.getHostname(), c4)
            .build();
    IncrementalBdpEngine engine =
        new IncrementalBdpEngine(
            new IncrementalDataPlaneSettings(),
            new BatfishLogger(BatfishLogger.LEVELSTR_OUTPUT, false),
            (s, i) -> new AtomicInteger());
    Topology topology = CommonUtil.synthesizeTopology(configurations);
    return (IncrementalDataPlane)
        engine.computeDataPlane(false, configurations, topology, Collections.emptySet())._dataPlane;
  }

  private static void buildEigrpExternalInterface(
      Interface.Builder eib,
      long asn,
      EigrpProcessMode mode,
      InterfaceAddress addr,
      String name,
      double delayMult) {
    ConfigurationFormat format = ConfigurationFormat.CISCO_IOS;
    EigrpInterfaceSettings.Builder esb =
        EigrpInterfaceSettings.builder().setAsn(asn).setEnabled(true);
    EigrpMetric.Builder emb = EigrpMetric.builder();
    emb.setBandwidth(null)
        .setDefaultBandwidth(getDefaultBandwidth(name, format))
        .setDefaultDelay(getDefaultDelay(name, format))
        .setDelay(getDefaultDelay(name, format) * delayMult)
        .setMode(mode);
    esb.setPassive(false).setMetric(emb.build());
    eib.setName(name).setAddress(addr).setEigrp(esb.build()).build();
  }

  private static void buildEigrpLoopbackInterface(
      Interface.Builder eib, long asn, EigrpProcessMode mode, InterfaceAddress addr) {
    ConfigurationFormat format = ConfigurationFormat.CISCO_IOS;
    EigrpInterfaceSettings.Builder esb =
        EigrpInterfaceSettings.builder().setAsn(asn).setEnabled(true);
    EigrpMetric.Builder emb = EigrpMetric.builder();
    emb.setBandwidth(null)
        .setDefaultBandwidth(getDefaultBandwidth("Loopback0", format))
        .setDefaultDelay(getDefaultDelay("Loopback0", format))
        .setDelay(null)
        .setMode(mode);
    esb.setPassive(true).setMetric(emb.build());
    eib.setName("Loopback0").setAddress(addr).setEigrp(esb.build()).build();
  }

  private static void buildNoneInterface(Interface.Builder nib, InterfaceAddress addr) {
    nib.setName("Loopback0").setAddress(addr).build();
  }

  private static void buildOspfExternalInterface(
      Interface.Builder oib, String name, InterfaceAddress addr) {
    oib.setAddress(addr).setName(name).setOspfPassive(false).build();
  }

  private static void buildOspfLoopbackInterface(Interface.Builder oib, InterfaceAddress addr) {
    String name = "Loopback0";
    oib.setAddress(addr).setName(name).setOspfPassive(true).build();
  }

  /** Test route computation and propagation for EIGRP in classic mode */
  @Test
  public void testEigrpClassicLinearRoutes() {
    IncrementalDataPlane dp =
        computeLinearDataPlane(
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.CLASSIC,
            "GigabitEthernet");
    SortedMap<String, SortedMap<String, SortedSet<AbstractRoute>>> routes =
        IncrementalBdpEngine.getRoutes(dp);

    long scale = 256L;
    // GigabitEthernet values
    long bandwidth = 10L;
    long delay = 1L;
    // Loopback values
    long lDelay = 500L;

    bandwidth *= scale;
    delay *= scale;
    lDelay *= scale;

    // r1
    assertNoRoute(routes, R1, Prefix.ZERO);
    assertRoute(routes, EIGRP, R1, R2_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R1, R3_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R1, R4_L0_ADDR, bandwidth + delay * 3 + lDelay);
    assertRoute(routes, EIGRP, R1, R2_E2_3_ADDR, bandwidth + delay * 2);
    assertRoute(routes, EIGRP, R1, R3_E3_4_ADDR, bandwidth + delay * 3);

    // r2
    assertNoRoute(routes, R2, Prefix.ZERO);
    assertRoute(routes, EIGRP, R2, R1_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R2, R3_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R2, R4_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R2, R3_E3_4_ADDR, bandwidth + delay * 2);

    // r3
    assertNoRoute(routes, R3, Prefix.ZERO);
    assertRoute(routes, EIGRP, R3, R1_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R3, R2_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R3, R4_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R3, R1_E1_2_ADDR, bandwidth + delay * 2);

    // r4
    assertNoRoute(routes, R4, Prefix.ZERO);
    assertRoute(routes, EIGRP, R4, R1_L0_ADDR, bandwidth + delay * 3 + lDelay);
    assertRoute(routes, EIGRP, R4, R2_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R4, R3_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R4, R1_E1_2_ADDR, bandwidth + delay * 3);
    assertRoute(routes, EIGRP, R4, R2_E2_3_ADDR, bandwidth + delay * 2);
  }

  /** Test route computation, propagation, and one-way redistribution for EIGRP in classic mode */
  @Test
  public void testEigrpClassicMultipathRoutes() {
    IncrementalDataPlane dp =
        computeMultipathDataPlaneWithRedistribution(
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.CLASSIC,
            "GigabitEthernet",
            RoutingProtocol.OSPF);
    SortedMap<String, SortedMap<String, SortedSet<AbstractRoute>>> routes =
        IncrementalBdpEngine.getRoutes(dp);

    long scale = 256L;
    // GigabitEthernet values
    long bandwidth = 10L;
    // Loopback values
    long lDelay = 500L;
    long exMetric =
        EigrpMetric.namedToClassicBandwidth((long) (externalBandwidth / 1000.0))
            + EigrpMetric.namedToClassicDelay((long) externalDelay);

    bandwidth *= scale;
    lDelay *= scale;
    exMetric *= scale;

    // r1
    assertNoRoute(routes, R1, Prefix.ZERO);
    assertRoute(routes, OSPF, R1, R2_L0_ADDR, 2L);

    // r2
    assertNoRoute(routes, R2, Prefix.ZERO);
    assertRoute(routes, OSPF, R2, R1_L0_ADDR, 2L);
    assertRoute(routes, EIGRP_EX, R2, R3_L0_ADDR, exMetric + 40000L * scale);
    assertRoute(routes, EIGRP, R2, R4_L0_ADDR, bandwidth + (6000000L + 40000L) * scale + lDelay);

    // r3
    assertNoRoute(routes, R3, Prefix.ZERO);
    assertRoute(routes, EIGRP_EX, R3, R1_L0_ADDR, exMetric + 500000L * scale);
    assertRoute(routes, EIGRP_EX, R3, R2_L0_ADDR, exMetric + 6000000L * scale);
    assertRoute(routes, EIGRP, R3, R4_L0_ADDR, bandwidth + 6000000L * scale + lDelay);

    // r4
    assertNoRoute(routes, R4, Prefix.ZERO);
    assertRoute(routes, OSPF, R4, R1_L0_ADDR, 2L);
    assertRoute(routes, OSPF, R4, R2_L0_ADDR, 3L);
    assertRoute(routes, EIGRP_EX, R4, R3_L0_ADDR, exMetric + 800000000L * scale);
  }

  /** Test route computation and propagation for EIGRP in named mode */
  @Test
  public void testEigrpNamedRoutes() {
    IncrementalDataPlane dp =
        computeLinearDataPlane(
            EigrpProcessMode.NAMED,
            EigrpProcessMode.NAMED,
            EigrpProcessMode.NAMED,
            EigrpProcessMode.NAMED,
            "GigabitEthernet");
    SortedMap<String, SortedMap<String, SortedSet<AbstractRoute>>> routes =
        IncrementalBdpEngine.getRoutes(dp);

    // named scale / rib scale
    long scale = 65536L / 128L;
    // GigabitEthernet values
    long bandwidth = 10L;
    long delay = 10L;
    // Loopback values
    long lDelay = 5000L;

    bandwidth *= scale;
    delay *= scale;
    lDelay *= scale;

    // r1
    assertNoRoute(routes, R1, Prefix.ZERO);
    assertRoute(routes, EIGRP, R1, R2_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R1, R3_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R1, R4_L0_ADDR, bandwidth + delay * 3 + lDelay);
    assertRoute(routes, EIGRP, R1, R2_E2_3_ADDR, bandwidth + delay * 2);
    assertRoute(routes, EIGRP, R1, R3_E3_4_ADDR, bandwidth + delay * 3);

    // r2
    assertNoRoute(routes, R2, Prefix.ZERO);
    assertRoute(routes, EIGRP, R2, R1_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R2, R3_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R2, R4_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R2, R3_E3_4_ADDR, bandwidth + delay * 2);

    // r3
    assertNoRoute(routes, R3, Prefix.ZERO);
    assertRoute(routes, EIGRP, R3, R1_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R3, R2_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R3, R4_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R3, R1_E1_2_ADDR, bandwidth + delay * 2);

    // r4
    assertNoRoute(routes, R4, Prefix.ZERO);
    assertRoute(routes, EIGRP, R4, R1_L0_ADDR, bandwidth + delay * 3 + lDelay);
    assertRoute(routes, EIGRP, R4, R2_L0_ADDR, bandwidth + delay * 2 + lDelay);
    assertRoute(routes, EIGRP, R4, R3_L0_ADDR, bandwidth + delay + lDelay);
    assertRoute(routes, EIGRP, R4, R1_E1_2_ADDR, bandwidth + delay * 3);
    assertRoute(routes, EIGRP, R4, R2_E2_3_ADDR, bandwidth + delay * 2);
  }

  /**
   * Test route computation and propagation for EIGRP with a mixture of named and classic routers
   *
   * <p>{@link Ignore Ignored} because further testing is necessary in GNS3 to determine the correct
   * costs
   */
  @Ignore
  @Test
  public void testEigrpMixedRoutes() {
    IncrementalDataPlane dp =
        computeLinearDataPlane(
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.NAMED,
            EigrpProcessMode.CLASSIC,
            EigrpProcessMode.NAMED,
            "GigabitEthernet");
    SortedMap<String, SortedMap<String, SortedSet<AbstractRoute>>> routes =
        IncrementalBdpEngine.getRoutes(dp);

    // r1
    assertNoRoute(routes, R1, Prefix.ZERO);
    assertRoute(routes, EIGRP, R1, R2_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R1, R2_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R1, R3_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R1, R4_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R1, R2_E2_3_ADDR, 0L);
    assertRoute(routes, EIGRP, R1, R3_E3_4_ADDR, 0L);

    // r2
    assertNoRoute(routes, R2, Prefix.ZERO);
    assertRoute(routes, EIGRP, R2, R1_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R2, R3_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R2, R4_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R2, R3_E3_4_ADDR, 0L);

    // r3
    assertNoRoute(routes, R3, Prefix.ZERO);
    assertRoute(routes, EIGRP, R3, R1_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R3, R2_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R3, R4_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R3, R1_E1_2_ADDR, 0L);

    // r4
    assertNoRoute(routes, R4, Prefix.ZERO);
    assertRoute(routes, EIGRP, R4, R1_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R4, R2_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R4, R3_L0_ADDR, 0L);
    assertRoute(routes, EIGRP, R4, R1_E1_2_ADDR, 0L);
    assertRoute(routes, EIGRP, R4, R2_E2_3_ADDR, 0L);
  }
}
