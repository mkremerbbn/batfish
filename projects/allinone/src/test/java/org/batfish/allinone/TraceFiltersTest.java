package org.batfish.allinone;

import static org.batfish.datamodel.IpAccessListLine.acceptingHeaderSpace;
import static org.batfish.datamodel.matchers.ConfigurationMatchers.hasIpAccessLists;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.hasEntry;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSortedMap;
import java.io.IOException;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Flow;
import org.batfish.datamodel.HeaderSpace;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.IpAccessList;
import org.batfish.datamodel.IpAccessListLine;
import org.batfish.datamodel.LineAction;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.acl.AclTrace;
import org.batfish.datamodel.acl.PermittedByAcl;
import org.batfish.datamodel.questions.FiltersSpecifier;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.main.Batfish;
import org.batfish.main.BatfishTestUtils;
import org.batfish.question.tracefilters.TraceFiltersAnswerElement;
import org.batfish.question.tracefilters.TraceFiltersAnswerer;
import org.batfish.question.tracefilters.TraceFiltersQuestion;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

public class TraceFiltersTest {

  @Rule public TemporaryFolder _folder = new TemporaryFolder();

  private NetworkFactory _nf;

  private Configuration.Builder _cb;

  private Configuration _c;

  @Before
  public void setup() {
    _nf = new NetworkFactory();
    _cb = _nf.configurationBuilder().setConfigurationFormat(ConfigurationFormat.CISCO_IOS);
    _c = _cb.build();
  }

  @Test
  public void testIndirection() throws IOException {
    IpAccessList.Builder aclb = _nf.aclBuilder().setOwner(_c);

    /*
    Reference ACL contains 1 line: Permit 1.0.0.0/24
    Main ACL contains 2 lines:
    0. Permit anything that reference ACL permits
    1. Permit 1.0.0.0/24
     */

    IpAccessList referencedAcl =
        aclb.setLines(
                ImmutableList.of(
                    acceptingHeaderSpace(
                        HeaderSpace.builder()
                            .setSrcIps(Prefix.parse("1.0.0.0/32").toIpSpace())
                            .build())))
            .setName("acl1")
            .build();
    IpAccessList acl =
        aclb.setLines(
                ImmutableList.of(
                    IpAccessListLine.accepting()
                        .setMatchCondition(new PermittedByAcl(referencedAcl.getName()))
                        .build(),
                    acceptingHeaderSpace(
                        HeaderSpace.builder()
                            .setSrcIps(Prefix.parse("1.0.0.0/24").toIpSpace())
                            .build())))
            .setName("acl2")
            .build();

    Batfish batfish = BatfishTestUtils.getBatfish(ImmutableSortedMap.of(_c.getName(), _c), _folder);

    assertThat(_c, hasIpAccessLists(hasEntry(referencedAcl.getName(), referencedAcl)));
    assertThat(_c, hasIpAccessLists(hasEntry(acl.getName(), acl)));

    TraceFiltersQuestion question =
        new TraceFiltersQuestion(NodesSpecifier.ALL, FiltersSpecifier.ALL);
    question.setSrcIp(new Ip("1.0.0.4"));
    TraceFiltersAnswerer answerer = new TraceFiltersAnswerer(question, batfish);
    TraceFiltersAnswerElement answer = answerer.answer();
    Flow flow =
        question.createBaseFlowBuilder().setIngressNode(_c.getName()).setTag("BASE").build();
    assertThat(
        answer
            .getRows()
            .contains(
                TraceFiltersAnswerElement.createRow(
                    _c.getName(),
                    acl.getName(),
                    flow,
                    LineAction.ACCEPT,
                    0,
                    "",
                    new AclTrace(ImmutableList.of()))),
        equalTo(true));

    // Tests for general ACL reachability answer
    System.out.print(answer.prettyPrint());
  }

}
