import go
import DataFlow

class TestConfig extends Configuration {
  TestConfig() { this = "TaintGetter" }

  override predicate isSource(Node nd) { nd.(CallNode).getCalleeName() = "taint" }

  override predicate isSink(Node nd) {
    exists(CallNode sink | sink.getAnArgument() = nd and sink.getCalleeName() = "sink")
  }

  override predicate isAdditionalFlowStep(Node pred, Node succ) {
    pred = StringConcatenation::getAnOperand(succ)
  }
}

from Configuration cfg, Node source, Node sink
where cfg.hasFlow(source, sink)
select source, sink
