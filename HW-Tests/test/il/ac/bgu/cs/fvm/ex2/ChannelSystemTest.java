package il.ac.bgu.cs.fvm.ex2;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Map;

import org.junit.Test;

import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.examples.AlternatingBitProtocolBuilder;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

public class ChannelSystemTest {


	@SuppressWarnings("unchecked")
	@Test
    public void debug() throws Exception {

        FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

        TransitionSystem<Pair<List<String>, Map<String, Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromChannelSystem(AlternatingBitProtocolBuilder.build());

		assertTrue(fvmFacadeImpl.isInitialExecutionFragment(ts, 
				AlternatingSequence.of(
						p(seq("snd_msg(0)", "off", "wait(0)"), map()),
						"C!0",
						p(seq("set_tmr(0)", "off", "wait(0)"), map(p("C",seq(0)))),
						"_tmr_on!|_tmr_on?",
						p(seq("wait(0)", "on", "wait(0)"), map(p("C",seq(0)))),
						"_timeout?|_timeout!",
						p(seq("snd_msg(0)", "off", "wait(0)"), map(p("C",seq(0)))),
						"C!0",
						p(seq("set_tmr(0)", "off", "wait(0)"), map(p("C",seq(0,0)))),
						"C?y",
						p(seq("set_tmr(0)", "off", "pr_msg(0)"), map(p("y",0),p("C",seq(0)))),
						"",
						p(seq("set_tmr(0)", "off", "snd_ack(0)"), map(p("y",0),p("C",seq(0)))),
						"D!0",
						p(seq("set_tmr(0)", "off", "wait(1)"), map(p("y",0),p("C",seq(0)),p("D",seq(0)))),
						"C?y",
						p(seq("set_tmr(0)", "off", "pr_msg(1)"), map(p("y",0),p("C",seq()),p("D",seq(0)))),
						"",
						p(seq("set_tmr(0)", "off", "wait(1)"), map(p("y",0),p("C",seq()),p("D",seq(0))))

				)));
        
    }

	@Test
    public void different_pg_order() throws Exception {

        FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

        ChannelSystem<String, String> cs = AlternatingBitProtocolBuilder.build();

		TransitionSystem<Pair<List<String>, Map<String, Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromChannelSystem(cs);
	
        @SuppressWarnings("unchecked")
		AlternatingSequence<Pair<List<String>, Map<String, Object>>, String> seq = AlternatingSequence.of(
                p(seq("snd_msg(0)", "off", "wait(0)"), map()),
                "C!0",
                p(seq("set_tmr(0)", "off", "wait(0)"), map(p("C", seq(0)))),
                "_tmr_on!|_tmr_on?",
                p(seq("wait(0)", "on", "wait(0)"), map(p("C", seq(0)))),
                "_timeout?|_timeout!",
                p(seq("snd_msg(0)", "off", "wait(0)"), map(p("C", seq(0)))),
                "C!0",
                p(seq("set_tmr(0)", "off", "wait(0)"), map(p("C", seq(0,0)))),
                "C?y",
                p(seq("set_tmr(0)", "off", "pr_msg(0)"), map(p("C", seq(0)),p("y",0))),
                "",
                p(seq("set_tmr(0)", "off", "snd_ack(0)"), map(p("C", seq(0)),p("y",0))),
                "D!0",
                p(seq("set_tmr(0)", "off", "wait(1)"), map(p("C", seq(0)),p("D", seq(0)),p("y",0))),
                "C?y",
                p(seq("set_tmr(0)", "off", "pr_msg(1)"), map(p("C", seq()),p("D", seq(0)),p("y",0))),
                "",
                p(seq("set_tmr(0)", "off", "wait(1)"), map(p("C", seq()),p("D", seq(0)),p("y",0)))
        );

        assertTrue(fvmFacadeImpl.isInitialExecutionFragment(ts, seq));

    }

}
