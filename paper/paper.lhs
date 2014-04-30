\documentclass[preprint]{sigplanconf}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%format <*> = "<\!\!\!*\!\!\!>"
%format newline = "\\[-1.5em]"
%format interpP = "\interp{P}"

\usepackage{enumerate}
\usepackage{subfigure}
\usepackage{fancyvrb}
\usepackage{stmaryrd}
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{xypic}
\usepackage{multirow}
\usepackage{hyperref}
\usepackage{url}
\usepackage{color}

\ifdefined\nolhs
\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\else
\fi

\bibliographystyle{amsalpha}

\newcommand{\note}[1]{{\color{blue}{#1}}}

\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}

\makeatletter
\newtheorem*{rep@@lemma}{\rep@@title}
\newcommand{\newreplemma}[2]{%
\newenvironment{rep#1}[1]{%
 \def\rep@@title{#2 \ref{##1} (recap)}%
 \begin{rep@@lemma}}%
 {\end{rep@@lemma}}}
\makeatother

\newreplemma{lemma}{Lemma}

\theoremstyle{definition}
\newtheorem{definition}{Definition}

\newreplemma{definition}{Definition}


\newcommand{\play}{\mathsf{play}\;}
\newcommand{\playOp}{\textsf{play}}

\newcommand{\sleep}{\mathsf{sleep}\;}
\newcommand{\sleepOp}{\textsf{sleep}}

\newcommand{\ksleep}{\mathsf{kernelSleep}\;}
\newcommand{\ksleepOp}{\textsf{kernelSleep}}

\newcommand{\lang}{SonicPi}

\newcommand{\vtime}[1]{[#1]_{\mathsf{v}}}
\newcommand{\etime}[1]{[#1]_{\mathsf{t}}}

\newcommand{\interp}[1]{\llbracket{#1}\rrbracket}

\newcommand{\ie}{\emph{i.e.}}
\newcommand{\eg}{\emph{e.g.}}

\authorinfo{Sam Aaron}{}{}
\authorinfo{Dominic Orchard}{}{}
\title{A programming model for temporal coordination (in music)}

\begin{document}
\maketitle

\section{Introduction}
\label{sec:introduction}

\note{Introduction to SonicPi}

The underlying programming model of SonicPi provides a way to separate
the ordering of effects from the timing of
effects. Figure~\ref{three-chord-example} shows an example program
where three chords are played in sequence, combining simple notions of 
parallel, timed, and ordered effects. The first three statements play
the notes of a C major chord in parallel. A \sleepOp{} statement then 
provides a \emph{barrier}




Thus ``$\sleep{} t$'' communicates that, after it has been evaluated, at least 
$t$ seconds has elapsed since the last \sleepOp{}. This provides a minimum
time. In between calls to \sleepOp{}, any other statements can (with some limits)
be considered task parallel. 

In \lang{}, it is possible that a computation proceeding a \sleepOp{}
can overrun; that is, run longer than the sleep time.  Thus, the
programming model is not suitable for realtime systems requiring hard
deadlines but \sleepOp{} instead provides a \emph{soft deadline} (using
the terminology of Hansson and Jonsson~\cite{hansson1994logic}).


\begin{itemize}
\item A computational model of virtual and real time 
      structured by an \emph{applicative functor} abstraction.

\item We show that the applicative approach extends
      to a monadic approach, which can be composed with additional
      monads to capture other useful notions of effect in \lang{} programs,
      such as random numbers (Section~\ref{}).
\end{itemize}

Previously reported on the language~\cite{aaron2013sonic}

\begin{figure}[t]
\subfigure[Three chord program in \lang{}]{
\begin{minipage}{0.46\linewidth}
\[
\hspace{-6em}
\begin{array}{l}
\play C \\
\play E \\ 
\play G \\
\sleep 1 \\
\play F \\
\play A \\
\play C \\
\sleep 0.5 \\
\play G \\
\play B \\
\play D \\
\end{array}
\]
\end{minipage}
\label{three-chord-example}
}
\subfigure[Timing of the three chord program]{
\begin{minipage}{0.46\linewidth}
\note{insert nice diagram that shows when the notes
occur over the 1.5s duration} \\
\end{minipage}
\label{three-chord-timing}
}
\caption{Playing three chords (C major, F major, G major) 
in \lang{} with the second two chords played
closer together by $0.5s$.}
\end{figure}

\subsection{Examples}
\label{sec:examples}

\note{Show a few more example programs here that
demonstrate the programming model.}

Figure~\ref{sleep-examples} shows four similar programs which each
have different internal behaviours for \sleepOp, illustrating the
semantics of \sleepOp{}. The first three take 3s to execute and the
last takes 4s to execute, with the behaviours:
%
\begin{enumerate}[(a)]
\item{3s -- sleeps for 1s then sleeps for 2s (two sleeps performed);}
\item{3s -- performs a computation lasting 1s, ignores
the first \sleepOp{} since its minimum deadline has been reached, 
and then sleeps for 2s (one sleep performed);}
\item{3s -- performs a computation lasting 2s, which means that
the first \sleepOp{} is ignored, and the second \sleepOp{} waits
for only 1s to reach its minimum deadline (half a sleep performed);}
\item{4s -- performs a computation lasting 2s, thus 
the first \sleepOp{} is ignored, then performs a computation lasting
2s, thus the second \sleepOp{} is ignored (no sleeps performed).}
\end{enumerate}


\begin{figure}[t]
\subfigure[Two sleeps]{
\begin{minipage}{0.18\linewidth}
\[
\hspace{-1em}
\begin{array}{l}
\sleep 1 \\
\sleep 2 \\ \\ \\ \\
\end{array}
\]
\end{minipage}
\label{sleep-examples:a}
}
\rule[-2em]{0.3pt}{5em}
%\hspace{1em}
% takes 3
\subfigure[One sleep]{
\begin{minipage}{0.23\linewidth}
\begin{center}
\[
\hspace{-0.5em}
\begin{array}{l}
\ldots \; \textit{\# lasts 1s} \\
\sleep 1 \\
\sleep 2 \\ \\  \\
\end{array}
\]
\end{center}
\end{minipage}
\label{sleep-examples:b}
}
\rule[-2em]{0.3pt}{5em}
%\hspace{1em}
% takes 3s
\subfigure[Half a sleep]{
\begin{minipage}{0.23\linewidth}
\begin{center}
\[
\hspace{-0.5em}
\begin{array}{l}
\ldots \; \textit{\# lasts 2s} \\
\sleep 1 \\
\sleep 2 \\ \\ \\
\end{array}
\]
\end{center}
\end{minipage}
\label{sleep-examples:c}
% takes 6
}
\rule[-2em]{0.3pt}{5em}
\subfigure[No sleeps]{
\begin{minipage}{0.23\linewidth}
\begin{center}
\[
\hspace{-0.5em}
\begin{array}{l}
\ldots \; \textit{\# lasts 2s} \\
\sleep 1 \\
\ldots \; \textit{\# lasts 2s} \\
\sleep 2 \\  \\
\end{array}
\]
\end{center}
\end{minipage}
}

\caption{Example programs with different \sleepOp{} behaviours}
\label{sleep-examples}
\end{figure}

\section{Model}

\paragraph{Terminology and notation}
We refer to closed sequences of statements (\ie{}, without free
variables) as \emph{programs}. Throughout, $P$, $Q$ range over programs,
and $s, t$ range over times (usually in seconds).

\subsection{Virtual time and real time}

The programming model of \lang{} distinguishes between the
\emph{actual time} elapsed since the start of a program $P$ which we
write as $\etime{P}$ and the \emph{virtual time} which is advanced by
\sleepOp{} statements which we write as $\vtime{P}$.

Since \sleepOp{} is the only operation that changes the virtual
time, we can easily specify the definition of $\vtime{-}$ over all programs:
%
\begin{definition}
Virtual time is specified for statements of \lang{} programs 
by the following (ordered) cases:
%
\begin{align*}
\vtime{\sleep t} & = t \\ 
\vtime{P; Q} & = \vtime{P} + \vtime{Q} \\
\vtime{-} & = 0
\end{align*}
%
\ie{}, the virtual time is $0$ 
for any statment other than \sleepOp{} or sequential composition.
\label{sleep-spec}
\end{definition}

Providing exact deadlines in real-time system is difficult due 
to noise and overhead caused by execution. We do not wish to sweep
this under the carpet in \lang{} or in our models. We therefore define
a relation $\approx$ on actual time (non virtual times), where:
%%
\begin{equation}
s \approx t
\equiv
t - \varepsilon \leq s \leq t + \varepsilon 
\end{equation}
%
for some value of $\varepsilon$ which is the maximum negligible 
time value with respect to the application at hand. In the case of
\lang{}, this is equal to the scheduling delay for the SuperCollider
engine (and is machine dependent), which is roughly \note{X}.

\note{Discuss this further, may be
  able to say later that in some cases $\epsilon$ is the scheduling
  time for play statments?} 

The virtual time and actual time of a single sleep statement (in
isolation) are roughly the same, \ie{}, $\vtime{\sleep t} \approx
\etime{\sleep t}$ and thus $\etime{\sleep t} \approx t$ (by the
specification in Definition~\ref{sleep-spec}). Note that this holds
only when \sleepOp{} is used in isolation, that is, when it is the
only statement in a program. As shown by the examples of
Section~\ref{sec:examples}, the use of $\sleep t$ in a program does
not mean that a program necessarily waits for $t$ seconds-- depending
on the context, it may wait for anywhere between $0$ and $t$ seconds.
 
%For convenience, and to contrast with \sleepOp{}, we'll use an additional
%statement \ksleepOp{} here (which is not available in the actual language)
% which always sleeps for the number of seconds specified by its parameter.

\begin{lemma}
For some program $P$ and time $t$: 
%%
\begin{align*}
\etime{P; \sleep{} t} \approx
 \begin{cases}
   \etime{P} & (\vtime{P} + t) < \etime{P} \\
   \vtime{P} + t  & \textit{otherwise}
 \end{cases}
\end{align*}
%\begin{align*}
%\etime{P; \sleep{} t} = 
% \begin{cases}
%   \etime{P} & t < \etime{P} \\
%   \vtime{P} + t & t \geq \etime{P}
% \end{cases}
%\end{align*}
\label{lem:sleep-R}
\end{lemma}

\begin{lemma}
For some program $P$ and time $t$:
%%
\begin{align*}
\etime{\sleep{} t; P} \approx t + \etime{P}
\end{align*}
\label{lem:sleep-L}
\end{lemma}

\begin{lemma}
For all programs $P$ then $\etime{P} \geq \vtime{P}$. 
\label{lemma-rel-etime-vtime}
\end{lemma}

\begin{theorem}
For all programs $P$ and $Q$ then:
%%
\begin{equation}
\vtime{P} + \vtime{Q} \leq \etime{P; Q} \lesssim \etime{P} + \etime{Q}
\end{equation}
\label{theorem:main}
\end{theorem}


From these lemmas we can reason about the evaluation time of programs.
For example, consider subprograms $A$, $B$, $C$ where 
$\etime{A} = t_1$, $\etime{B} = t_2$, $\etime{C} = t_3$ and
$\vtime{A} = \vtime{B} \vtime{C} = 0$, interposed with two
sleep statements of duration $s_1$ and $s_2$:
%
\begin{equation}
\begin{array}{l}
A \\
\sleep s_1 \\
B  \\
\sleep s_2 \\
C
\end{array}
\label{example:time1}
\end{equation}
%%
Then by the above lemmas, we see that $\etime{eq. \eqref{example:time1}} = 
s_1 + s_2 + t_3$, iff $t_1 \leq 1$ and $t_2 \leq 2$.

%\begin{equation*}
%\begin{array}{lllll}
%A & \multirow{2}{*}{\rule[1em]{0.6pt}{1.2em}} & \multirow{2}{*}{$t_1$} & 
%\multirow{4}{*}{\rule[1em]{0.6pt}{4em}} & \multirow{4}{*}{$t_1 + t_2 + 3$}
%\\
%\emph{sleep} \; 1 \qquad \\
%B &  \multirow{2}{*}{\rule[1em]{0.6pt}{1.2em}} & \multirow{2}{*}{$t_2$} \\
%\emph{sleep} \; 2
%\end{array}
%\end{equation*}


\newcommand{\TM}{\mathsf{TM}}

\subsection{Monadic structure on computation}

In the following, we use Haskell as our meta language for the
semantics (since it provides convenient syntax for working with
monads)\footnote{The source code for the model is avilable at
  \url{https://github.com/dorchard/time-monad}}.
\lang{} computations are modelled by the \emph{Temporal} data type, defined:
%%
\begin{code}
data Temporal a =
    T ((Time, Time) -> (VTime -> IO (a, VTime)))
\end{code}
%
Thus, temporal computations map a pair of two times, which will be
the start time of the computation and current time, to a stateful
computation with a single location storing a virtual time, over the
\emph{IO} type.  The \emph{IO} computation provides underlying access
to the actual time from kernel.

The \emph{Monad} instance for \emph{Temporal} is then as follows:
%
\begin{code}
instance Monad Temporal where
  return a     = T ( \_ -> \vT -> return (a, vT))

  newline
  (T p) >>= q  = T (\(startT, nowT) -> \vT -> 
                    do  (x, vT')    <- p (startT, nowT) vT
                        let (T q')  = q x
                        thenT       <- getCurrentTime
                        q' (startT, thenT) vT')
\end{code} 
%
To ease understanding, we recall the types of \emph{return}
and |(>>=)| along with some intuition for their behaviour for
\emph{Temporal}:
%
\begin{itemize}
\item |return :: a -> Temporal a| lifts a pure value into a trivially
effectful computation by ignoring the time parameters and 
providing the usual pure state behaviour: passing the state unchanged.

\item |(>>=) :: Temporal a -> (a -> Temporal b) -> Temporal b| 
  composes two computations together.  The result of composing two
  temporal computations, with start time \emph{startT}, current time
  \emph{nowT}, and virtual time \emph{vT}, is the result of evaluating
  first the left-hand side at time \emph{nowT} and then 

right hand side, and then the left hand side.  Note that
  |getCurrentTime :: IO Time| retrieves the time from the operation
  system.
\end{itemize}

The |runTime| operation executes a temporal computation
inside of the \emph{IO} monad by providing the start time of the
computation, and with virtual time 0:
%%
\begin{code}
runTime :: Temporal a -> IO a
runTime (T c) = do  startT <- getCurrentTime
                    (x, _) <- c (startT, startT) 0
                    return x
\end{code}
%%
To illustrate the evalution of temporal computation and the
ordering and interleaving of calls to the operation system for the
current time, we consider a program:
%%
\begin{code}
runTime (do { f; g; h; })
\end{code}
(where |f = T f', g = T g', h = T h'|) which 
desugars to the following \emph{IO} computation, 
after some simplification: 
%%
\begin{code}
do  startT    <- getCurrentTime
    (_, vT')  <- f' (startT, startT) 0
    thenT     <- getCurrentTime
    (_, vT'') <- g' (startT, thenT) vT'
    thenT'    <- getCurrentTime
    (y, _)    <- h' (startT, thenT') vT'')
    return y
\end{code}
%
The above illustrates the repeated calls to |getCurrentTime|, the
constant start time parameter, and the threading of virtual time state
throughout the computation. 

Figure~\ref{core-functions} provides a number of effectul operations
for \emph{Temporal} that access the current time, the start time, get
and set the virtual time, and cause a kernel sleep. These
are used in the next part of the model. 

\begin{figure}[t]
\begin{code}
time :: Temporal Time
time  = T (\(_, nowT) -> \vT -> return (nowT, vT))


start :: Temporal Time
start = T (\(startT, _) -> \vT -> return (startT, vT))


getVirtualTime :: Temporal VTime
getVirtualTime = T (\(_, _) -> \vT -> return (vT, vT))


setVirtualTime :: VTime -> Temporal ()
setVirtualTime vT = T (\_ -> \_ -> return ((), vT))


kernelSleep :: RealFrac a => a -> Temporal ()
kernelSleep t =  T (\(_, _) -> \vT -> 
                       do  threadDelay (round (t * 1000000))
                           return ((), vT))
\end{code}
\caption{Simple \emph{Temporal} computations, used  by the model}
\label{core-functions}
\end{figure}

\paragraph{Interpreting \lang{} statements}

The following interpretation function $\interp{-}$ on \lang{} 
programs shows the mapping to the operations of the \emph{Temporal}
monad:
%%
\begin{align*}
\interp{\emph{statement}} & : \emph{Temporal} \, () \\
\interp{x = P; Q} & = \interp{P} |>>= (\x ->| \interp{Q}) \\
\interp{P; Q} & = \interp{P} |>>= (\_ ->| \interp{Q}) \\
\interp{\sleep e} & = \emph{sleep} \, \interp{e}
\end{align*}
%%
Note that $\interp{-}$ is overloaded in the rule for \sleepOp{} for (pure) expressions. 
The concrete interpreation of other statements in the language, such as \playOp, is
elided here since it does not relate directly to the temporal semantics. 

The key primitive \emph{sleep} provides the semantics for \sleepOp{} as:
%%
\begin{code}
sleep :: VTime -> Temporal ()
sleep delayT = do  nowT      <- time
                   vT        <- getVirtualTime
                   let vT'   = vT + delayT
                   setVirtualTime vT'
                   startT    <- start
                   let diffT = diffTime nowT startT
                   if (vT' < diffT) then return () 
                                    else kernelSleep (vT' - diffT)
\end{code}
%
Thus, \emph{sleep} proceeds by getting the current time, calculating
the new virtual time \emph{vT'} and updating the virtual time
state. If the new virtual time is less than the elapsed time
\emph{diffT} then no actual (kernel) sleeping happens. However, if the
new virtual time is ahead of the elapsed time, then the process sleeps
for the difference.

\subsection{Soundness}

We replay the previous lemmas on the temporal behaviour of \lang{} programs,
and show that the monadic model is sound with respect to these, \ie{},
that the lemmas hold of the model. 

\noindent
\begin{repdefinition}{sleep-spec}
\begin{align*}
\vtime{\sleep t} & = t \\ 
\vtime{P; Q} & = \vtime{P} + \vtime{Q} \\
\vtime{-} & = 0
\end{align*}
\end{repdefinition}

\begin{proof}
For our model, the proof is straightforward. For the case of
$P; Q$, we rely on the monotonicity of virtual time: virtual
time is only ever increasing, and can only ever be incremented by sleep. 
\note{Could put more here}
\end{proof}

\begin{replemma}{lem:sleep-R}
For some program $P$ and time $t$: 
%%
\begin{align*}
\etime{P; \sleep{} t} \approx
 \begin{cases}
   \etime{P} & (\vtime{P} + t) < \etime{P} \\
   \vtime{P} + t  & \textit{otherwise}
 \end{cases}
\end{align*}
\end{replemma}

\begin{proof}
Our model interprets $(P; \sleep t)$ as:
%%
\begin{code}
runTime (do {interpP; sleep t})
\end{code}
%%
which desugars and simplifies to the following \emph{IO} computation:
%
\begin{code}
do  startT     <- getCurrentTime
    (x, vT')   <- interpP (startT, startT) 0
    nowT       <- getCurrentTime
    let vT''   = vT' + t
    setVirtualTime vT''
    let diffT  = diffTime nowT startT
    if (vT'' < diffT)
      then return ()
      else kernelSleep' (vT'' - diffT)

\end{code}
%%
where |kernelSleep' x = threadDelay (round (x * 1000000))| is used
as an alias here (as per the definition of \emph{kernelSleep} in
Figure~\ref{core-functions}.

From this we see that $\emph{diffT} = \etime{P}$ and $\emph{vT'} = \vtime{P}$ and 
 $\emph{vT''} = \vtime{P} + t$. Therefore, the guard of the 
\emph{if} expression is $(\vtime{P} + t) < \etime{P}$.
If the updating of the virtual time state and the computing of 
the guard takes $e$ then the overall time taken is:
%%
\begin{align*}
\etime{P; \sleep{} t} = 
 \begin{cases}
   \etime{P} + e & (\vtime{P} + t) < \etime{P}  \\
   \etime{P} + e + (\vtime{P} + t) - \etime{P}  & \textit{otherwise}
 \end{cases}
\end{align*}
%%
which is equivalent to the statment of the lemma if $e \leq \epsilon$
and if the reduction to the interpretation to get to the above code 
takes less than $\epsilon$:
\begin{align*}
\etime{P; \sleep{} t} \approx 
 \begin{cases}
   \etime{P} & (\vtime{P} + t) < \etime{P} \\
   \vtime{P} + t  &  \textit{otherwise}
 \end{cases}
\end{align*}
\end{proof}

\begin{replemma}{lem:sleep-L}
For some program $P$ and time $t$:
%%
\begin{align*}
\etime{\sleep{} t; P} \approx t + \etime{P}
\end{align*}
\end{replemma}

\begin{proof}
Our models interprets $(\sleep t; P)$ as:
%
\begin{code}
runTime (do { sleep t; interpP })
\end{code}
%
which desugars and simplifies to the following \emph{IO} computation:
%
%\begin{code}
%do  setVirtualTime delayT
%    kernelSleep delayT 
%    interpP
%\end{code}
\begin{code}
do  startT <- getCurrentTime
    kernelSleep delayT 
    let (T p) = interpP ()
    thenT <- getCurrentTime 
    p (startT, thenT) delayT
\end{code}
%
The code does a |kernelSleep| for $t$ and then continues with $P$ at
virtual time $t$, \ie{}, the time taken is $t + \interp{P}_t$.  In
desugaring and simplifying we have certainly elided some intermediate
steps in the computation (such as the guard test in sleep), which we
account for as part of the error $\epsilon$.
\end{proof}

\begin{replemma}{lemma-rel-etime-vtime}
For all programs $P$ then $\etime{P} \geq \vtime{P}$. 
\end{replemma}

\begin{proof}
By induction % possibly by strong induction?

$\interp{sleep t} = $
|runTime (sleep t)| $\leadsto$ |kernelSleep' delayT|

$\etime{P;Q} = $
Inductive hypothesis: $\etime{P} \geq \vtime{P}$
              $\etime{Q} \geq \vtime{Q}$


\begin{itemize}
\item case $P = sleep t$ 

$\etime{sleep t; Q} = t + \etime{Q}$ 
$\vtime{sleep t; Q} = t + \vtime{Q}$
by inductive hypothesis $t + \etime{Q} \geq t + \vtime{Q}$.

\item case $Q = sleep t$

$\vtime{P; sleep t} = \vtime{P} + t$
By inductive hypothesis ($\etime{P} \geq \vtime{P}$) then


\begin{itemize}
\item case $\vtime{P} + t \leq \etime{P}$ then

$\etime{P; sleep t} = \etime{P}$ 
therefore $\etime{P; sleep t} \geq \vtime{P; sleep t}$
since $\etime{P} \geq \vtime{P} + t$ by the case.

\item case $\vtime{P} + t \geq \etime{P}$ then
 $\etime{P; sleep t} = \vtime{P} + t$
then $\etime{P; sleep t} \geq \vtime{P; sleep t}$
since $\etime{P; sleep t} = \vtime{P; sleep t}$. 
\end{itemize}

\item case $P = P';P''$, $Q = Q';Q''$

reassociate 

case P' = sleep t, 

$\etime{P';Q'} = t + \etime{Q'}$
\end{itemize}

\end{proof}

\subsubsection{Monad laws}

\paragraph{Quotienting by non-time dependent functions}

\note{This section is more of a marker for myself (Dom), I need
to think about this later, but basically it is about showing
that the monad laws hold for our semantics (but not in general)}

In L, there is no expression which returns the current time; 
 \emph{getTime} belongs only to the model, not to the language.
That is, for all expressions $e$, then the denotation 
$\interp{e}$ factors through 

\subsection{Subsets of the semantics}

For the examples of Section~\ref{sec:introduction}, the full structure
of monad is not needed to give their semantics as there is no using of
binding between statements (and thus no dataflow). In these case just
an \emph{applicative functor}~\cite{mcbride2008functional} or even a
monoid would suffice. These can be derived from the monad structure
on \emph{Temporal} since all monads are applicative functors and all 
monads define monoid over $m ()$.

\paragraph{Applicative subset}

Applicative functors are described by the following interface in
Haskell:
%%
\begin{code}
class Functor f => Applicative f where
   pure  :: a -> f a
   (<*>) :: f (a -> b) -> f a -> f b
\end{code}
%
The \emph{Applicative} class describes how to compose effectul
computations encoded as values of type $f\ a$ (the effectful
computation of a pure value of type $a$). Thus, \emph{pure} constructs
a trivially effectful computation from a pure value and |<*>| (akin to
application) takes an effectful computation of a function and an
effectful computation of an argument and evaluates the two effects.

Our \emph{Temporal} denotations have the applicative functor
structure with the following derivation in terms of the monad:
%
\begin{code}
instance Functor Temporal where
    fmap f x = do { x' <- x; return (f x') }

instance Applicative Temporal where
    pure a          = return a
    f <*> x         = do { f' <- f; x' <- x; return (f' x') }
\end{code}
%
Note that the definition of |<*>| here orders the effects left-to-right.

The interpretation of sequential composition for statements (with no
dataflow) is then $\interp{P; Q} = (\lambda() \rightarrow
\interp{P}) <\!\!\!*\!\!\!> \interp{Q}$.

\paragraph{Monoid subset}

Alternatively, the full structure of an applicative functor is
not even needed in this restricted case. Instead, a monoid
over \emph{Temporal ()} would suffice:
%
\begin{code}
class Monoid m where
   mempty :: m
   mappend :: m -> m -> m

instance Monoid (Temporal ()) where
    mempty        = return ()
    a `mappend` b = do { a; b; return () }
\end{code}
%% 
with the interpretation $\interp{P; Q} = \interp{P} |`mappend`| Q$ and
where |mempty| provides a \emph{no-op}. 

\subsection{Alternate definition of \emph{sleep}}

\begin{code}
sleep' :: VTime -> Temporal ()
sleep' delayT = do  vT        <- getVirtualTime
                    let vT'   = vT + delayT
                    setVirtualTime vT'
                    startT    <- start
                    nowT      <- time
                    let diffT = diffTime nowT startT
                    if (vT' < diffT) 
                        then return () 
                        else kernelSleep (vT' - diffT)
\end{code}
%
This alternate definition should reduce any oversleeping by minimising 
noise in the timing. For example, the virtual time is calculated 
and updated before the current time is retrieved in case the additional
time taken in updating the virtual time means that the elapsed time
catches up with the virtual time. 

To see the difference, consider Lemma~\ref{lem:sleep-R}:

\begin{replemma}{lem:sleep-R}
For some program $P$ and time $t$: 
%%
\begin{align*}
\etime{P; \sleep{} t} = 
 \begin{cases}
   \etime{P} & (\vtime{P} + t) < \etime{P} \\
   \vtime{P} + t  & \textit{otherwise}
 \end{cases}
\end{align*}
\end{replemma}
%
\noindent
If the above alternate definition \emph{sleep'} is used, then
the interpreation of $(P; \sleep t)$  
desugars and simplifies to the following:
%
\begin{code}
do  startT     <- getCurrentTime
    (x, vT')   <- interpP (startT, startT) 0
    let vT''   = vT' + t
    setVirtualTime vT''
    nowT       <- getCurrentTime
    let diffT  = diffTime nowT startT
    if (vT'' < diffT)
      then return ()
      else kernelSleep (vT'' - diffT)
\end{code}
%%
which exhibits the temporal behaviour:
%% 
\begin{align*}
\etime{P; \sleep{} t} = 
 \begin{cases}
   \etime{P} + e_1 + e_2 & (\vtime{P} + t) < (\etime{P} + e_1) \\
   \vtime{P} + t + e_2 &  \textit{otherwise}
 \end{cases}
\end{align*}
%
where $e_1$ is the time taken by updating the virtual time and
$e_2$ is the time taken by the guard. This gives
a tighter bound on sleep behaviour that previously where the behaviour was:
%
\begin{align*}
\etime{P; \sleep{} t} = 
 \begin{cases}
   \etime{P} + e_1 + e_2 & (\vtime{P} + t) < \etime{P} \\
   \vtime{P} + t + e_1 + e_2 &  \textit{otherwise}
 \end{cases}
\end{align*}
%

\subsection{Emitting overrun exceptions}

\paragraph{Overrun}

\paragraph{Overrun schedule}


\section{Related work}

There has been various work on reasoning about time in logic. For
example, modal CTL (Computational Tree Logic) has been extended with
time bounds for deadlines~\cite{emerson1991quantitative} (RCTL,
Real-Time Computational Tree Logic) and for soft deadlines with
probabilities on time bounds~\cite{hansson1994logic}. In these logics,
temporal modalities are indexed with time bounds, \eg{}, $AF^{\leq 50}
p$ means $p$ is true after at least $50$ ``time units'' (where $A$ is
the CTL connective for \emph{along all paths} and $F$ for
\emph{finally} (or \emph{eventually})). Our approach is less
prescriptive and explicit, but has some resemblance in the use of
\sleepOp{}. For example, the program $\sleep t ; P$ roughly
corresponds to $AF^{\leq t} \interp{P}$, \ie{}, after at leat $t$ then
whatever $P$ does will have happend. Our framework is not motivated by
logic and we do not have a model checking process for answering
questions such as, at time $t$ what formula hold (what statements have
been evluated).  The properties of Lemmas 1 to 5 however provide some
basis for programmers to reason about time in their programs. In
practice, we find that such reasoning can be done by children in a
completely informal but highly useful way.



\section{Epilogue}


\paragraph{Acknowledgements}

\bibliography{references}

\appendix

\paragraph{Proof} (of Theorem~\ref{theorem:main})
Since sequential composition is associative, we can reassociate
$P; Q$ such that $P = P_1; P'$ where $P_1$ is a single statement

\begin{itemize}
\item $P = \sleep t$

\begin{align*}
\begin{array}{ll}
       & \etime{\sleep t; Q} \\[0.5em]
\equiv & \; \{\textit{Lemma}~\ref{lem:sleep-L}\} \\[0.1em]
       & s + \etime{Q} \\[0.5em]
\equiv & \; \{\textit{Definition}~\ref{}\} \\[0.1em]
       & \etime{\sleep t} + \etime{Q}
\end{array}
\end{align*}

\item $Q = \sleep t$ by Lemma~\ref{lem:sleep-R} then 
there are two cases:

\begin{itemize}
\item $\etime{P} \leq t$ then:

\begin{align*}
\begin{array}{ll}
       & \etime{P; \sleep t} \\[0.5em]
\equiv & \; \{\textit{Lemma}~\ref{lem:sleep-R}\} \\[0.1em]
       & \vtime{P} + t \\[0.5em]
\equiv & \; \{\textit{Definition}~\ref{sleep-spec}\} \\[0.1em]
       & \vtime{P} + \vtime{\sleep t}
\end{array}
\end{align*}

\item $\etime{P} > t$ then:

\begin{align*}
\begin{array}{ll}
       & \etime{P; \sleep t} \\[0.5em]
\equiv & \; \{\textit{Lemma}~\ref{lem:sleep-R}\} \\[0.1em]
       & \etime{P} \\[0.5em]
\leq   & \etime{P} + \etime{\sleep t}
\end{array}
\end{align*}

\end{itemize}

\item $P = P';P'', Q = Q';Q''$

Ressociate so that $P'; (P''; (Q'; Q''))$ then

By induction:
%%
\begin{align}
\vtime{P'} + \vtime{P''} \leq \etime{P'; P''} \leq \vtime{P'} + \vtime{P''} \\
\vtime{Q'} + \vtime{Q''} \leq \etime{Q'; Q''} \leq \vtime{Q'} + \vtime{Q''} \\
\end{align}

and
\note{STUCK!}
\end{itemize}


\end{document}
