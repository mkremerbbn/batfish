package org.batfish.question.bgpsessionstatus;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;

import org.batfish.datamodel.questions.NodesSpecifier;
import org.junit.Test;

public class BgpSessionStatusQuestionTest {
  @Test
  public void testDefaultParameters() {
    BgpSessionStatusQuestion question = new BgpSessionStatusQuestion();

    assertThat(question.getDataPlane(), equalTo(false));
    assertThat(question.getIncludeEstablishedCount(), equalTo(false));
    assertThat(question.getNode1Regex(), equalTo(NodesSpecifier.ALL));
    assertThat(question.getNode2Regex(), equalTo(NodesSpecifier.ALL));
    assertThat(question.getName(), equalTo("bgpsessionstatusnew"));
  }

  @Test
  public void testDoesNotMatchNullStatus() {
    BgpSessionStatusQuestion question = new BgpSessionStatusQuestion();
    assertThat(question.matchesStatus(null), equalTo(false));
  }
}
