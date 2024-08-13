# Collect a JFR trace with async-profiler (can be analyzed in JDK Mission
# Control or IntelliJ):

# 1. start your process
# 2. get its PID
# 3. collect trace:
async-profiler -e cpu,alloc,lock -d 60 -f out.jfr 'PID'
# 4. open 'out.jfr' in your favorite tool

# Available events (-e flag):
#  > Basic events:
#  >   cpu
#  >   alloc
#  >   lock
#  >   wall
#  >   itimer
#  > Java method calls:
#  >   pack.age.ClassName.methodName

# Java has some absolutely incredible industrial-strength tools for COLLECTING
# statistics about running processes:
#
#   - Java Flight Recorder (JFR)
#   - VisualVM
#   - async-profiler
#
# ... but the tools for EXPLORING and INTERPRETING those traces are garbage.
# Or at least, I haven't found one I like yet.
#
#    | FEATURES THAT          |          |                     |          |
#    | CALVIN WANTS           | VISUALVM | JDK MISSION CONTROL | INTELLIJ |
#    ----------------------------------------------------------------------
#    | Focus [1]              | no       | yes [2]             | yes      |
#    | Ignore [3]             | no       | no                  | no       |
#    | Blame-caller [4]       | no       | no                  | no       |
#    | Collapse-recursion [5] | no       | no                  | no       |
#    | Total-time [6]         | yes      | no [7]              | yes      |
#    | Self-time [6]          | yes      | no [7]              | no       |
#    | Callee-breakdown [6]   | no       | yes [7]             | yes      |
#    | Search [8]             | no       | no                  | yes      |
#
# NOTES:
#    [1]: I want to be able to restrict my view to a particular method; I don't
#         care that my server spent 99.3% of its time waiting on epoll()!  I
#         want to focus on handleRequest(), where it spends the 0.7% of its
#         time where the work happens.  I want to be able to make this choice
#         while EXPLORING the trace, not while COLLECTING the trace.
#    [2]: This feature is technically available, but the inferface for using it
#         is garbage.  In particular, it's virtually impossible to search for a
#         method to focus on, and once you find one, the interface for focusing
#         is shoddy and confusing.  JFR Mission Control also often forgets what
#         you tried to focus on.
#    [3]: I want to be able to ignore a particular call.  For instance, I might
#         not care that a method spent 30% of its time in lock.acquire(); the
#         cost of that call is blamed on someone else (the lock-holding
#         thread).
#    [4]: I want to be able to attribute a particular method to its caller's
#         self-time or a callee's self-time.  For instance, if I have 8
#         overloads of the same method, I want to treat them all as calls to
#         the one overload that does the work.  Or, if I call a standard sort()
#         method, I might want to blame its CPU usage on the caller, not the
#         standard library.
#    [5]: I hate seeing traces like
#           Repl.eval(...)
#             doWork()
#             Repl.eval(...)
#               doWork()
#               Repl.eval(...)
#                 Repl.eval(...)
#                 doWork()
#         I want to be able to collapse all the recursive eval() calls to see
#         how much all those calls to doWork() contribute to the overall CPU
#         usage of the evaluator.
#    [6]: I want to be able to see a breakdown of each method's total time,
#         self time, and a breakdown of what percent of the total time was
#         spent in each callee.
#    [7]: How is this not present in the display???  JDK Mission Control
#         has enough information to show me this, but there is no panel that
#         does.  It only cares about "samples" and "sample weight".  The latter
#         is not defined anywhere, and I have no reason to think it has
#         anything to do with time.  Similarly, while it has a callee
#         breakdown, the percentages are in terms of samples, not time.
#    [8]: This one drives me up the wall.  I want to be able to Cmd+F for a
#         name to find relevant heavy stack traces.  How is this not supported
#         in any tool???
