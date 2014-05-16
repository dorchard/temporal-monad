\documentclass[preprint]{sigplanconf}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%format <*> = "<\!\!\!*\!\!\!>"
%format newline = "\\[-1.5em]"
%format interpP = "\interp{P}"
%format lamWild = "{\backslash}{\anonymous}"


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
\usepackage[pdftex]{graphicx}

\DeclareGraphicsExtensions{.png,.jpg,.pdf} % used graphic file format for pdflatex

\bibliographystyle{amsalpha}

\newcommand{\note}[1]{{\color{blue}{#1}}}

\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}


\CustomVerbatimEnvironment{SVerbatim}{Verbatim}{fontsize=\footnotesize,xleftmargin=0.5cm,xrightmargin=0.5cm,framesep=3mm,commandchars=\\\{\}}

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
\newtheorem{example}{Example}

\newreplemma{definition}{Definition}


\newcommand{\play}{\mathsf{play}\;}
\newcommand{\playOp}{\textsf{play}}

\newcommand{\sleep}{\textnormal{\texttt{sleep}}\;}
\newcommand{\sleepOp}{\texttt{sleep}}

\newcommand{\ksleep}{\textnormal{\texttt{kernelSleep}}\;}
\newcommand{\ksleepOp}{\texttt{kernelSleep}}

\newcommand{\schedAheadT}{\textnormal{\texttt{scheduleAheadTime}}\;}
\newcommand{\schedAheadTOp}{\texttt{scheduleAheadTime}}

\newcommand{\lang}{Sonic Pi}

\newcommand{\vtime}[1]{[#1]_{\mathsf{v}}}
\newcommand{\etime}[1]{[#1]_{\mathsf{t}}}

\newcommand{\synVar}{\mathit{v}}

\newcommand{\interp}[1]{\llbracket{#1}\rrbracket}

\newcommand{\ie}{\emph{i.e.}}
\newcommand{\eg}{\emph{e.g.}}

\authorinfo{Samuel Aaron}
           {Computer Laboratory, University of Cambridge, UK}
           {sam.aaron|@|cl.cam.ac.uk}
\authorinfo{Dominic Orchard}
           {Computer Laboratory, University of Cambridge, UK}
           {dominic.orchard|@|cl.cam.ac.uk}
\authorinfo{Alan F. Blackwell}
           {Computer Laboratory, University of Cambridge, UK}
           {alan.blackwell|@|cl.cam.ac.uk}

\title{Temporal semantics for a live coding language}
% A programming model for temporal coordination (in music)}

\begin{document}
\maketitle

\begin{abstract}
Sonic Pi is a music live coding language that has been designed for
educational use, as a first programming language. However, it is
not straightforward to achieve the necessary simplicity of a first language
in a music live coding setting, for reasons largely related to the
manipulation of time. The original version of Sonic Pi used a `sleep'
function for managing time, blocking computation 
for a specified time period. However, whilst this approach was conceptually
simple, it resulted in badly timed music, especially when multiple musical
threads were executing concurrently. This paper describes an alternative
programming approach for timing (implemented in Sonic Pi v2.0) which
maintains syntactic compatibility with version 1.0, yet provides accurate
timing via interaction between real time and a ``virtual time''.
We provide a formal specification of the temporal behaviour of Sonic Pi,
motivated in relation to other recent approaches to the semantics of time in
live coding and general computation. We then define a monadic model of the
Sonic Pi temporal semantics which is sound with respect to this
specification, using Haskell as a metalanguage.
\end{abstract}

\section{Introduction}
\label{sec:introduction}

Timing is a critical component of music. Therefore any language for
describing music must have a method for describing the precise timing
of sounds, such as individual notes. Performing a piece of music
correctly then amounts to a computation, evaluating the musical
description to emit correct notes at correct times.  This kind of
timing contrasts with many notions in computing.  For example,
``real-time computing'' approaches often focus on computing within a
certain time limit (a deadline), thus high-performance is important.
But in music, being early is just as bad as being late. A similar
situation in mechanical coordination tasks, such as coordinating
robotic limbs for walking. For these kinds of applications, a robust
programming model for timing is required.  We argue that our Sonic Pi
language provides a suitable, robust temporal model for music in the
context of live programming and education.

Sonic Pi is a domain specific language for manipulating synthesisers
through time~\cite{Aaron2013}. It was designed for teaching core
computing concepts to school students using creative programming,
specically live-coding music, as a means for engaging students.  The
precise timing of effects, which do not occur too early or too late,
is core to the programming approach of Sonic Pi. 

Sonic Pi is a mostly pure language, with first-class functions. Its
impurity arises from timing and output effects (for producing sounds).
Primarily, this paper introduces the temporal programming model of
Sonic Pi. We give a monadic description of its effects, showing
that the impure part of the language can be embedded in a pure
language.

As well as the need for programming approaches to time, there is a
well-recognised need for models of temporal behaviour coupled with
reasoning systems for time. This has been explored particularly in
logic, with modal logics such as the Real-Time Computation Tree
Logic~\cite{emerson1991quantitative}. In the literature, Lee makes a
powerful argument for the development of a semantics of time in
computation, or as he describes it, a properly formalised class of
``time system'' that can be applied alongside the type systems (which
is already understood to be an essential software engineering
tool)~\cite{Lee2009}.  It is in this spirit that we develop two kinds
of model for the temporal semantics of Sonic Pi: a time system
and a denotational model
%: an axiomatic specification 
% that provides a ``time system'' (a system with which to statically
%analysis timing) and a denotational model.

The core contributions of this paper are three-fold:
%%
\begin{itemize}
\item We present a new programming approach for precisely timing
  effects, which is implemented as part of the Sonic Pi language for
  music live coding. We explain how this programming approach has
  evolved to replace the previous version of the Sonic Pi language
  (Section~\ref{sec:sp-1}), providing a syntactically identical
  language but with an improved approach to timing (Section~\ref{sec:new-sleep}).

\item We formalise the temporal semantics of this approach,
  introducing a specification of the temporal behaviour of Sonic Pi
  programs: a \emph{time system}, which provides a static
analysis of timing in programs (Section~\ref{sec:axiomatic}).
The style is axiomatic, and can be considered an abstract model of
timing. 

\item We give a denotational semantics to a core subset of the
  language, using monads, (Section~\ref{sec:time-monad}) and prove it
  sound with respect to the time system, \ie{}, the language is
  \emph{time safe}. We later extend this model to include temporal
  warnings (Section~\ref{sec:temporal-warnings}). The style of this
  model is denotational, complementing the more abstract time system. 
\end{itemize}

\noindent
We begin with a discussion of the research context surroduning first
programming languages and live coding (particularly for music), as
both these aspects motivate the language design.  Those readers who are 
keen to get to the language design may skip this discussion and move
to Section~\ref{sec:sp-1}.

\subsection{The first language and live conding contexts}
\label{sec:context}

A first programming language should be conceptually straightforward
and syntactically uncluttered. However, it is not straightforward to
achieve this simplicity in a music live coding language, for reasons
largely related to the representation of time. Representing musical
time in a programming language is often problematic, firstly because
natural ways of describing and organising musical events are
multi-threaded (scores, chords, resonance, reverb), and secondly
because so many standard computational formalisms treat execution time
as a non-functional requirement~\cite{Lee2009}. Time can be even more
problematic in live coding, because the creation of the code, as a
performance, is interleaved with the sound events resulting from its
execution. Yet for users of Sonic Pi, the creative experience they
have, like all experience, arises through time -- as media theorist
Mieke Bal says, ``\emph{time is where subjectivity is
  produced}''~\cite{bal2002travelling}.

As noted by Julian Rorhruber~\cite{blackwell_et_al:DR:2014:4420}, there
have been many publications discussing alternative approaches to the
representation of time in live coding, many having to choose between
explicit or implicit representation of time, and between description of
time with reference to internal or external state. These many
interesting strategies include McLean's formalism of cyclic time in the
Tidal language~\cite{mclean2013textural}, and Sorensen's temporal
recursion in Impromptu/Extempore~\cite{sorensen2010programming}. In this
paper, we present a formalism that is designed to achieve
production-quality sound (via the SuperCollider synthesis server) while
allowing inexperienced programmers in an educational setting (typically
11-12 year-old children) to express the temporal structure in terms that
have an intuitive correspondence to the experience and production of
musical sounds. The semantics of our formalism can be seen to be similar
to the interaction of time and the massively overloaded \texttt{=>}
operator in the live coding language ChucK~\cite{Wang2003}.

In music, it is clear that we must be able to speak about the precise
location of events in time, and hence that any music programming
language must of necessity provide some kind of time semantics, even if
these are only informal. In the case of live coding languages, an
additional consideration is that the time at which the program is edited
may coincide or overlap with the time at which it is executed. This
overlap between execution and creation time is of broader value in
software engineering, as noted for example by
McDirmid~\cite{MSR-TR-2014-42}, whose Glitch system allows the user to
adjust the notional execution time relative to a point in the source
code editing environment. Tools of this kind can also benefit from a
formal semantics in which to define the relationship between changes or
navigation within the code, and changes or navigation within the
cause-effect sequence of execution time.

\section{Problems with timing in Sonic Pi 1.0}
\label{sec:sp-1}

\begin{SaveVerbatim}{example0}
play 52
play 55
play 59
\end{SaveVerbatim}

\begin{SaveVerbatim}{example0b}
play 52
sleep 1
play 55
sleep 1
play 59
\end{SaveVerbatim}

\begin{figure}[t]
\subfigure[Chord; notes together]{
\hspace{2.5em}
\begin{minipage}{0.34\linewidth}
\BUseVerbatim[fontsize=\footnotesize,baselinestretch=0.97]{example0}
\vspace{0.5em}
\end{minipage}
\label{eminor-chord}
}
\subfigure[Arpeggio; notes in succession]{
\hspace{1.5em}
\begin{minipage}{0.4\linewidth}
\BUseVerbatim[fontsize=\footnotesize,baselinestretch=0.97]{example0b}
\vspace{0.5em}
\end{minipage}
\label{eminor-chord-spaced}
}
\caption{Playing MIDI notes of the E minor chord in Sonic Pi 1.0}
\end{figure}


One of the core computing concepts that Sonic Pi has been used to teach is the
sequential ordering of effects in imperative programs, such as playing
successive notes see Figure~\ref{eminor-chord} (which is considered
her to be a Sonic Pi version 1.0 program). 

However, given the clockspeeds of modern processors, the instructions
of Figure~\ref{eminor-chord} are likely to be executed so quickly in
succession that they will be perceived as a chord \ie{}, all the note
being played simultaneously, rather than as succesive notes in an
\emph{arpeggio} form. It is therefore necessary to separate the
triggering of these notes in time. This can be achieved by
``sleeping'' the current thread, see Figure~\ref{eminor-chord-spaced}.
This notion of sleep is similar to that of the standard POSIX sleep
operation that suspends execution for the specified time~\cite{posix}. 

\begin{SaveVerbatim}{example-drums}
loop do
  play 30                  #A
  sample :drum_heavy_kick  #B
  sleep 0.5                #C
end
\end{SaveVerbatim}

\begin{figure}[t]
\begin{minipage}{0.46\linewidth}
\BUseVerbatim[fontsize=\footnotesize,baselinestretch=0.97]{example-drums}
\end{minipage}
\caption{A continuously repeating bass and drum hit.)}
\label{example-drum-loop}
\end{figure}


Whilst these temporal semantics worked well in a computing education
context for demonstrating effect execution order, they didn't translate
well to music contexts due to a mismatch with user expectations; they did
not allow correct timing of musical notes. This mismatch was particularly 
emphasised when Sonic Pi gained the ability to play drum samples. Consider the example 
in Figure~\ref{example-drum-loop}. Here we are attempting to regularly play
MIDI note 30 at the same time as the drum sample \texttt{:drum\_heavy\_kick} 
with half a second between each onset.

Unfortunately the execution will not produce the desired
behaviour and the rhythm will drift in time due to the addition of the
execution time itself to the sleep time. For example, after line A in
Figure~\ref{example-drum-loop} has completed execution, the clock time
will have moved on by the amount of time it took to execute the
line. Similarly for line B. Line C introduces two extra sources of time,
the sleep time and the time spent waiting for the scheduler to pick up
and continue executing the thread. Therefore, instead of each iteration
taking precisely 0.5s, the actual time is the summation of the
computation time of A, the computation time of B, 0.5 and the scheduler
pick-up time. Depending on load and processor speed, these extra times
can produce dramatically noticeable results. This is profoundly apparent
when the user requests two threads to work in synchronisation such as in
Figure~\ref{example-threaded-drum-loop}. The threads may start out in
synchronisation, but because the extra computation time will differ
across the threads, they will drift at varying rates and move out of
synchronisation.

\begin{SaveVerbatim}{example-t-drums}
in_thread
  loop do
    play 30
    sleep 0.5
  end
end

in_thread
  loop do
    sample :drum_heavy_kick
    sleep 1
  end
end
\end{SaveVerbatim}

\begin{figure}[t]
\vspace{-1.4em}
\begin{minipage}{0.46\linewidth}
\BUseVerbatim[fontsize=\footnotesize,baselinestretch=0.97]{example-t-drums}
\end{minipage}
\caption{Two concurrent threads playing in synchronisation)}
\label{example-threaded-drum-loop}
\end{figure}


Sonic Pi's timing issues are further compounded by the fact that calls
to \texttt{play} and \texttt{sample} are asynchronous messages, and there is an
additional time cost for these messages to be sent and interpreted by
the external synth process. This then adds additional varying time
(jitter) to each sound trigger.


\begin{figure}[htbp!]
        \centering
                \includegraphics[width=1\columnwidth]{assets/timing-version1-diagram.pdf}
        \caption{The timing behaviour in Sonic Pi 1.0}
        \label{fig:sp-timing1.0}
\end{figure}

The temporal issues described in this section are summarised in
Figure~\ref{fig:sp-timing1.0}, which describes the timing behaviour of
Sonic Pi v 1.0 code triggering three successive chords. Each of the $\Delta$
times in the far left column represents the real computation time of
each statement. Notice how they are all unique. The precise duration is
related to aspects such as the amount of processing required for the
computation, the current load of the system and the processor speed. The
duration of deltas is therefore nondeterministic and will not be
consistent across runs of the same program. As
Figure~\ref{fig:sp-timing1.0} illustrates, the actual run time of the
program is a summation of all these $\Delta$ times in addition to the
requested sleep durations:
%%
\begin{equation*}
\Delta_a + \Delta_b + \Delta_c + 1 + \Delta_d + \Delta_e + \Delta_f 
+ 0.5 + \Delta_g + \Delta_h + \Delta_i
\end{equation*}
%%
This results in both drift and jitter of the
timing of the sounds produced by the program.

\subsection{Temporal expectations}

When users create programs in Sonic Pi, the ease with which they can
produce the musical effects they intend is dependent on their
expectations of codes behaviour. As described by Honing (~\cite{Honing1993}, see
Section~\ref{sec:related-work}), music systems may represent temporal
structure either explicitly (describing time intervals and relations)
or implicitly (in an ordered sequence of notes having different
durations). Musical scores provide an implicit time representation,
while most music programming systems rely on explicit time
representation. Unfortunately, in the case of general purpose
programming languages, the typical implementation of the sleep
operator supports an explicit representation of rhythm that is
guaranteed to be accurate only in the ordering of the notes, not in
the elapsed time between them. In teaching programming, the usual
focus is on correctness of this explicitly specified behaviour. When
teaching programming through the medium of music, as in Sonic Pi, the
musical expectations that are usually associated with implicit
representation of rhythm mean that non-expert musicians are likely to
hear that something is wrong, while not being able to express
precisely what the problem is.

%The temporal semantics of initial version of Sonic Pi (as
%described above) did not meet user expectations.% in
%ways specially related to the nature of these expectations.
% From a functional-requirements perspective, the explicit representation of rhythm provided
%computationally accurate semantics. All expressed computation happens
%(\ie{}, all notes are played, and all sleeps are honoured) and the
%execution happens in the defined order. However, when we consider the
%implicit representation from the experience of rhythm, the addition of
%implicit computation time to the explicit timing statements produces
%sporadic timing of the musical events which reduces the quality of the
%musical experience.

Less expert musicians might be able to identify more explicit problems
(such as extra beats), but find it harder to say precisely what the
problem is when that problem is related to their implicit
expectations. %This is something that they expect to happen, but unless
%they are experienced musicians, may not be able to explain that they
%want it to happen.
%In this second case,
Even if the user can perceive
the timing mistakes, they language provides no means to fix them. One of
the goals of Sonic Pi is to to create a system that is useful to
experienced musicians (with clear musical goals) and acceptable to
inexperienced musicians that may not be able to clearly articulate what
they want to achieve, but know when it is wrong.

It is therefore important to maintain the conceptual simplicity of the
original approach, while providing an improved time semantics that
satisfies not only explicit expectations of the musical listener, but
also these implicit expectations.


%% *** Sam will possibly write a section comparing the new Sonic Pi time
%% semantics to the time semantics of ChucK

\section{Reinventing sleep}
\label{sec:new-sleep}

Sonic Pi 2.0 introduces a new implementation and semantics of the sleep command which
maintains syntactic and conceptual compatibility with the previous
implementation yet modifies the temporal semantics to match the implicit
rhythmical expectations previously described. The semantics is no longer
similar to that of the POSIX sleep command.
The underlying programming
model of Sonic Pi 2.0 provides a way to separate the ordering of effects
from the timing of effects. Figure~\ref{three-chord-example} shows the
program that was used in Figure~\ref{fig:sp-timing1.0}, but we now treat
it as Sonic Pi 2.0 program. This example program (playing three chords in sequence)
 combines simple notions of parallel, timed, and ordered effects.

The first three statements play the notes of a C major chord in
parallel.  A \sleepOp{} statement then provides a ``temporal barrier''
which blocks the computation from continuing until 1 second has elapsed
since the \emph{start} of the program (not since the end of playing the
notes). Once one second has elapsed, the next three statements are
executed which plays an F major chord. The next \sleepOp{} means that
the final chord is not played until 1.5 seconds has elapsed since the
start of the program. Figure~\ref{three-chord-timing} illustrates the
timing.
Thus, $\sleep{} t$ communicates that, after it has been evaluated,
at least $t$ seconds has elapsed since the last \sleepOp{}. This
provides a minimum time. In between calls to \sleepOp{}, any other
statements can (with some limits) be considered task parallel. As
mentioned earlier, ChucK has a similar mechanism as part of its
massively overloaded operator~\cite{Wang2003}.

\begin{SaveVerbatim}{example1}
play :C ; play :E ; play :G
sleep 1
play :F ; play :A ; play :C
sleep 0.5
play :G ; play :B ; play :D
\end{SaveVerbatim}

\begin{figure}[b]
%\subfigure[Three chord program in \lang{} 2.0]{
%\begin{minipage}{0.46\linewidth}
%\[
%\hspace{-6em}
%\begin{array}{l}
%\play C \\
%\play E \\
%\play G \\
%\sleep 1 \\
%\play F \\
%\play A \\
%\play C \\
%\sleep 0.5 \\
%\play G \\
%\play B \\
%\play D \\
%\end{array}
%\]
\BUseVerbatim[fontsize=\footnotesize,baselinestretch=0.97]{example1} \\
%\end{minipage}

%}
\caption{Playing three chords (C major, F major, G major)
in \lang{} 2.0, with the second two played
closer together by $0.5s$.}
\label{three-chord-example}
\end{figure}

These semantics are achieved by introducing a notion of \emph{virtual time}
 as a thread-local variable which is only advanced by the new 
\sleepOp{} operation. Each thread has access to both real time and virtual
time, with the virtual time used to schedule external effects. In order
to keep the execution of the program in synchronisation with the
explicit timing requirements of the program, \sleepOp{} takes into account
the execution time since the last \sleepOp{} and reduces the requested
sleep time appropriately. Therefore if the user issues a \sleepOp{} 1
statement, and the current execution time since the last \sleepOp{}
statement is 0.1 seconds, the implementation only sleeps the current
thread for 0.9s. This ensures that no drifting occurs. 

Figure~\ref{fig:reich} demonstrates the timing of the
Figure~\ref{three-chord-example} program in Sonic Pi 2.0, which
contrasts with the timing diagram in Figure~\ref{fig:sp-timing1.0}. 
The overall elapsed time for the program is now:
%%
\begin{align*}
\hspace{-5.8em} (\emph{v 2.0}) & \hspace{6em} 1.5 + \Delta_g + \Delta_h + \Delta_i
\end{align*}
%%
which contrasts with the Sonic Pi 1.0 timing for the same program:
%%
\begin{equation*}
(\emph{v 1.0})\quad 1.5 + \Delta_a + \Delta_b + \Delta_c + \Delta_d + \Delta_e + \Delta_f +  
 \Delta_g + \Delta_h + \Delta_i
\end{equation*}
%%
This shows that we have eliminated drift in Sonic Pi 2.0 since the
only overhead is now just the overhead of the \texttt{play} statements
following the last \texttt{sleep}. For Sonic Pi 1.0, each block of
\texttt{play} statements adds overhead, leading to timing drift over
the course of a program. In Section~\ref{sec:axiomatic} we will make
precise the behaviour of the new sleep operation. 

In order to deal with relative execution times within a sleep barrier, \eg{},
the \texttt{play :C ; play :E ; play :G} operations in Figure~\ref{three-chord-example},
and also to accomodate the cost of scheduling output effects (to the synthesiser
serve), a constant \schedAheadTOp{} value is added to the current virtual time for all
asynchronously scheduled effects. Provided that the addition of the
jitter time and the execution time between calls to \sleepOp{} never
exceeds this value, the temporal expectations of the system are met.

\begin{figure}[t]
        \centering
                \includegraphics[width=1\columnwidth]{assets/timing-diagram.pdf}
        \caption{Timing behaviour of Sonic Pi 2.0 including virtual and scheduled time with a \schedAheadTOp{} of 0.5.}
        \label{fig:reich}
\end{figure}


It is possible that a computation proceeding a \sleepOp{} can overrun; that is, run longer
than the sleep time.  Thus, the programming model is not suitable for
realtime systems requiring hard deadlines but \sleepOp{} instead
provides a \emph{soft deadline} (in the terminology of Hansson and
Jonsson~\cite{hansson1994logic}).



\subsection{Examples}
\label{sec:examples}

Figure~\ref{sleep-examples} shows four similar programs which each
have different internal behaviours for \sleepOp, illustrating its semantics.
We use the function \ksleepOp{}, which is not a standard part of the Sonic Pi
language, as a placeholder to represent a computation lasting a particular
length of time (as specified by the parameter to \ksleepOp{}). 
The first three example programs take 3s to execute and the
last takes 4s to execute, with the behaviours:
%
\begin{enumerate}[(a)]
\item{3s -- sleeps for 1s then sleeps for 2s (two sleeps performed);}
\item{3s -- performs a computation lasting 1s, ignores
the first \sleepOp{} since its minimum duration has been reached,
and then sleeps for 2s (one sleep performed);}
\item{3s -- performs a computation lasting 2s, which means that
the first \sleepOp{} is ignored, and the second \sleepOp{} waits
for only 1s to reach its minimum duration (half a sleep performed);}
\item{4s -- performs a computation lasting 2s, thus
the first \sleepOp{} is ignored, then performs a computation lasting
2s, thus the second \sleepOp{} is ignored (no sleeps performed).}
\end{enumerate}


\begin{figure}[t]
\subfigure[Two sleeps]{
\begin{minipage}{0.18\linewidth}
{\small{
\[
\hspace{-1em}
\begin{array}{l}
\texttt{sleep 1} \\
\texttt{sleep 2} \\ \\ \\ \\[-0.9em]
\end{array}
\]
}}
\end{minipage}
\label{sleep-examples:a}
}
\rule[-2em]{0.3pt}{5em}
%\hspace{1em}
% takes 3
\subfigure[One sleep]{
\begin{minipage}{0.23\linewidth}
{\small{
\begin{center}
\[
\hspace{-0.5em}
\begin{array}{l}
\texttt{kernelSleep 1} \\
\texttt{sleep 1} \\
\texttt{sleep 2} \\ \\  \\ 
\end{array}
\]
\end{center}
}}
\end{minipage}
\label{sleep-examples:b}
}
\rule[-2em]{0.3pt}{5em}
%\hspace{1em}
% takes 3s
\subfigure[Half a sleep]{
\begin{minipage}{0.23\linewidth}
{\small{
\begin{center}
\[
\hspace{-0.5em}
\begin{array}{l}
\texttt{kernelSleep 2} \\
\texttt{sleep 1} \\
\texttt{sleep 2} \\ \\ \\
\end{array}
\]
\end{center}
}}
\end{minipage}
\label{sleep-examples:c}
% takes 6
}
\rule[-2em]{0.3pt}{5em}
\subfigure[No sleeps]{
\begin{minipage}{0.23\linewidth}
{\small{
\begin{center}
\[
\hspace{-0.5em}
\begin{array}{l}
\texttt{kernelSleep 2} \\
\texttt{sleep 1} \\
\texttt{kernelSleep 2} \\
\texttt{sleep 2} \\  \\
\end{array}
\]
\end{center}
}}
\end{minipage}
}
where \ksleepOp{} is a placeholder to represent a computation lasting a particular length
of time
\caption{Example programs with different \sleepOp{} behaviours}
\label{sleep-examples}
\end{figure}

\section{A ``time system'' for Sonic Pi}
\label{sec:axiomatic}

From our experiences, we've found that the programming model of Sonic
Pi, particularly its temporal model, is easy to understand by even
complete beginners, including children. By a few simple examples it
is easy to demonstrate the temporal semantics, using sounds as output,
without having to appeal to any meta-theory; Sonic Pi attains the goal
of being a good first language.

In this section, we approach the programming model of Sonic Pi from a
more theoretical angle, in order to develop a specification of our
programming model that can be reused for other applications and
languages outside of the Sonic Pi context. From our model we prove a
number of core properties of Sonic Pi as well. It is in no way
necessary for programmers of Sonic Pi to understand this theory, but
the contribution here is useful for future language design and
implementation research.

Firstly, we define an abstract specification of virtual time and
actual elapsed time in a simple core subset of Sonic Pi
(Section~\ref{sec:spec}). This gives an abstract, axiomatic
model of the semantics which we call a \emph{time system}. 
This model is made more concrete by providing a denotational-style, monadic semantics
in the next section 
(Section~\ref{sec:time-monad}), introducing the \emph{temporal
  monad}. We prove the monadic model sound with
respect to the initial axiomatic specification, up to ``small'' permutations
in time delay (Section~\ref{sec:soundness}).

\paragraph{Terminology and notation}
We refer to sequences statements as \emph{programs}. Throughout, $P$,
$Q$ range over programs, and $s, t$ range over times (usually in
seconds).

\paragraph{A core fragment of Sonic Pi}

Throughout the rest of this paper, we model a core subset of
the Sonic Pi 2.0 language with the following grammar, where $P$ are
programs, $S$ statements, and $E$ expressions:
%%
\begin{align*}
P & ::= P; S \mid \emptyset \\
S & ::= E \mid \synVar = E \\
E  & ::= \sleep \mathbb{R}_{\geq 0} \mid A^i \mid \synVar
\end{align*}
%%
where $A^i$ represents operations (actions) in Sonic Pi other than \sleepOp,
\eg{}, some $A^j$ is the \texttt{play} operation. We use this to
abstract over operations in the language which do not modify virtual
time.

By the above definition, programs $P$ are a ``snoc''-list (\ie{},
elements are ``consed'' onto the end, not front as is standard for
inductively-defined lists) where $\emptyset$ is the empty list. This
structure aids later proofs since it allows inductive reasoning on
a statement of a program and its preceding program, which is necessary
for modelling \texttt{sleep}. 

Statements $S$ may be expressions on
their own, or may have (pure) bindings to variables. Throughout we
consider the first case of $S$ as a degenerate case of the second where
the variable is irrelevant \ie{}, $? = E$ where $?$ is a wildcard variable. 

We'll add the previously seen \ksleepOp{} operation to the core subset here, which
blocks the current computation for the time specified by its
parameter, \ie{}, it has the semantics of POSIX \emph{sleep}. 
This operation is not available in the actual language,
but it is usedul for examples and contrasting with \sleepOp{}.

\subsection{Virtual time and real time}
\label{sec:spec}

As described previously, the programming model of \lang{}
distinguishes between the actual time elapsed since the start of a
program $P$ which we write here as $\etime{P}$ and the virtual time
which is advanced by \sleepOp{} statements which we write as
$\vtime{P}$. Both these abstract functions return time values,
thus, $\vtime{-},\etime{-} \in \mathbb{R}_{\geq 0}$, \ie{}, both
return positive, real-number values.

In this section we give specifications on the functions
$[-]_v$ and $[-]_t$ providing an axiomatic model of the temporal behaviour
of Sonic Pi programs. % We'll treat these operations as overloaded for
%programs $P$, statements $S$ and expressions $E$.

Virtual time $\vtime{-}$ can be easily defined over all programs,
statements, and expressions, since the \sleepOp{} operation is the
only expression changing virtual time:
%
\begin{definition}
Virtual time is specified for statements of \lang{} programs
by the following cases:
%
\begin{align*}
\begin{array}{crl}
\vtime{P; \synVar = E} = \vtime{P} + \vtime{E} & \qquad \vtime{\sleep t} & \hspace{-0.8em} = t \\
\vtime{\emptyset } = 0 &  \qquad \vtime{A^i} & \hspace{-0.8em}  = 0
\end{array}
\end{align*}
%
We therefore overload $\vtime{-}$ to programs, statements, and expressions. 
Anything other than \sleepOp{} or sequential composition has 
the virtual time is $0$. Note that the equations on the left define $\vtime{-}$ for
programs (with statements covered by the single case for $P; \synVar = E$),
and on the right for expressions.
\label{def:vtime}
\end{definition}

\paragraph{Equality on time}

Providing exact deadlines in real-time systems is difficult due
to non-determinism combined with execution overheads. We do not ignore
this problem in the programming model of \lang{} and the discussion here.
We define the relation $\approx$ on actual times, where:
%%
\begin{equation}
\forall s, t . \quad
s \approx t
\;
\equiv
\;
{\mid}{(s - t)}{\mid} \leq \epsilon
%\;
%(t - \epsilon) \leq s \leq (t + \epsilon)
\end{equation}
%
for some value of $\epsilon$ which is the maximum negligible
time value with respect to the application at hand.
For example, if $\epsilon = 0.1$ then $3 \approx 3.05 \approx 2.92$.

In the case of \lang{}, we mitigate any $\epsilon$-time differences by
scheduling calls to the synthesise server using the current virtual
time (see the diagram of Figure~\ref{fig:reich}). 
Later in the denotational model (Section~\ref{sec:time-monad}),
we'll demonstrate sources of temporal variations
$\epsilon$, which limited to a very small part of the model. 
Crucially, these $\epsilon$ time differences do not
accumulate-- the \sleepOp{} operation provides a barrier which
prevents this. 

%In the case of
%\lang{}, we set $\epsilon$ equal to the schedule ahead time (\schedAheadTOp{}, in Section~\ref{sec:new-sleep}), which in our earlier examples was 0.5 seconds. 

%\note{Discuss this further, may be
%  able to say later that in some cases $\epsilon$ is the scheduling
%  time for play statements?}

\paragraph{Axioms of actual time}

The virtual time and actual time of a single sleep statement
 are roughly the same, \ie{}, $\vtime{\sleep t} \approx
\etime{\sleep t}$ and thus $\etime{\sleep t} \approx t$ (by the
specification in Definition~\ref{def:vtime}). This holds
only when \sleepOp{} is used in isolation, that is, when it is the
only statement in a program. As shown by the examples of
Section~\ref{sec:examples}, the use of $\sleep t$ in a program does
not mean that a program necessarily waits for $t$ seconds-- depending
on the context, it may wait for anywhere between $0$ and $t$ seconds.

%We outline here some important temporal properties of our \lang{}
%programs that relates the virtual time and actual times. In
%Section~\ref{sec:soundness}, we replay these lemmas and prove a
%soundness result: that these lemmas are true for our model.

\begin{definition}
The actual elapsed time $\etime{-}$ can be specified at the level of programs
by the following equations:
%%
\begin{align*}
\etime{\emptyset} & \, \approx \, 0 \\
\etime{P; \sleep{} t} & \,\approx\,
 (\vtime{P} + t) \;\, \textit{max} \;\, \etime{P} \\
\etime{P; A^i} & \,\approx\,
 \etime{P} + \etime{A^i}
\end{align*}
%
% CASE VERSION
%
%\etime{P; \sleep{} t} \approx
% \begin{cases}
%   \etime{P} & (\vtime{P} + t) < \etime{P} \\
%   \vtime{P} + t  & \textit{otherwise}
% \end{cases}
%\end{align*}
%
In the case of $A^i = \ksleepOp{}$, then $\etime{\ksleep t} = t$.
\label{def:etime}
\end{definition}

\begin{example}
The following two small example programs illustrate this definition, both
of which have actual time 2 but arising from different calls to \sleepOp{}.
%%
\begin{itemize}
\item[--] $\etime{\texttt{kernelSleep 2; sleep 1}} \approx 2$

\begin{itemize}
\item[]
where $P = \texttt{kernelSleep 2}$, 
$\vtime{P} = 0$, $t = 1$, and
$\etime{P} = 2$, thus $(\vtime{P} + t) < \etime{P}$
\end{itemize}
\vspace{0.5em}

\item[--] $\etime{\texttt{kernelSleep 1; sleep 2}} \approx 2$

\begin{itemize}
\item[]
where $P = \texttt{kernelSleep 1}$, 
$\vtime{P} = 0$, $t = 2$, and
$\etime{P} = 1$, thus $(\vtime{P} + t) > \etime{P}$
\end{itemize}
\end{itemize}
\end{example}

%%
%\begin{lemma}
%For some program $P$ and time $t$:
%%%
%\begin{align*}
%\etime{\sleep{} t; P} \approx t + \etime{P}
%\end{align*}
%\label{lem:sleep-L}
%\end{lemma}
%
%The implication of this lemma is that a preceding sleep does not affect

Definition~\ref{def:etime} illuminates the semantics of \sleepOp,
showing the interaction between actual time $\etime{-}$
and virtual time $\vtime{-}$ in the case for \sleepOp{}.
Note that the definition of $\etime{-}$ (in the \sleepOp{} case)
is not a straightforward recursive decomposition on
programs, statements, and expressions as in the
definition of $\vtime{-}$ (Definition~\ref{def:etime}). Instead,
the actual time of a \sleepOp{} depends on its \emph{context}, which
is the pre-composed (preceding) program $P$ and its actual time $\etime{P}$.
This is why we have structured the core subset language here
 in terms of ``snoc''-list since the temporal semantics of an individual
statement can depend on the program that has \emph{come before} it (the tail
of the list ``snoc''-list).

This definition provides us with the following lemma about
the temporal semantics of any Sonic Pi program:
%
\begin{lemma}
For some program $P$ then $\etime{P} \geq \vtime{P}$.
\label{lemma-rel-etime-vtime}
\end{lemma}
%
That is, the actual running time of a program is always at least the
virtual time; a Sonic Pi program never ``under-runs'' its virtual time
specification.

\begin{proof}
By induction on the structure of programs.
%
\begin{itemize}
\item $P = \emptyset$. Trivial since $\vtime{\emptyset} = 0$ by Definition~\ref{def:vtime}.
\item $P = (P'; \synVar = E)$, split on $E$
  \begin{itemize}
    \item $E = \sleep t$

      (a) by Definition~\ref{def:vtime}, $\vtime{P'; \sleep t} = \vtime{P'} + t$.

      (b) by Definition~\ref{def:etime}, $\etime{P'; \sleep t} = (\vtime{P'} + t) \;\, \textit{max} \;\, \etime{P'}$.

      (c) by (b) $(\vtime{P'} + t) \;\, \textit{max} \;\, \etime{P'} \geq \vtime{P'} + t$

      $\therefore$ by (a) and (c) then $\etime{P'; \sleep t} \geq \vtime{P' \sleep t}$

     \item otherwise $E = A^i$

     (a) by Definition~\ref{def:vtime}), $\vtime{P'; \synVar = A^i} = \vtime{P'}$

     (b) by Definition~\ref{def:etime}), $\etime{P'; \synVar = A^i} = \etime{P'} + \etime{A^i}$

     (c) by inductive hypothesis $\etime{P'} \geq \vtime{P'}$.

     (d) since $\etime{-} \in \mathbb{R}_{\geq 0}$, by monotonicity and (c)
      $\etime{P'} + \etime{A^1} \geq \vtime{P'}$.

      $\therefore$ (a), (b) and (d) then $\etime{P'; \synVar = A^i} \geq \vtime{P'; \synVar = A^i}$.
  \end{itemize}
\end{itemize}
\end{proof}
%
\noindent
The abstraction specification of the temporal behaviour here gives us a model
with which we can reason about time in Sonic Pi programs.
%%
\begin{example}
Consider subprograms $A$, $B$, $C$ where
$\vtime{A} = \vtime{B} = \vtime{C} = 0$ which are interposed with two
sleep statements of duration $s_1$ and $s_2$:
%
\[
P = A; \, \sleep s_1; \, B; \, \sleep s_2; \, C
\]
%%
Then by the above definitions, we see that if $\etime{A} \leq s_1$ and
$\etime{B} \leq s_2$ then $\etime{P} = s_1 + s_2 + \etime{C}$.
\end{example}

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

\noindent
We now move on to a denotational model, which provides a semantics for
the core subset of the language described here. We'll prove this sound
semantics with respect to the axiomatic model of this section, linking
the two levels of model.

\newcommand{\TM}{\mathsf{TM}}

\section{A denotational model of Sonic Pi's temporal semantics}
\label{sec:time-monad}

%We use Haskell as a meta language for defining this model
%for ease of understanding. 

In the following, we use Haskell as a meta language for a denotational
model (semantics) since it provides a convenient syntax for working
with monads. This approach also provides an executable semantics that
is useful for experimentation and integrating into other approaches.
The source code is available at
\url{https://github.com/dorchard/temporal-monad}.

We introduce the mode here and prove it sound with respect to the time
system approach of the previous section. We also consider alternate,
simplified models using applicative functors or monoids in Section~\ref{sec:alternate},
along with alternate models for \sleepOp{}. Lastly, we extend the model
to incorporate ``temporal warnings'' to describe temporal
errors that can occur at runtime (Section~\ref{sec:temporal-warnings}).

\paragraph{The \emph{Temporal} monad}

We define an interpretation $\interp{-}$ that maps programs and
statements to a parametric data structure, named \emph{Temporal},
which encapsulates the effects of the Sonic Pi programs.  For closed
programs (those without free variables) the type of this
interpretation is $\interp{\emph{P}} : \emph{Temporal} \,
()$. Temporal computations, encapsulated by |Temporal| are functions
of the form:
%%
\begin{align*}
& (\textit{start time}, \textit{current time}) \\
& \quad \rightarrow (\textit{old vtime} \rightarrow
\textit{kernel-access} \, (\textit{result}, \textit{new vtime}))
\end{align*}
%%
that is, mapping a pair of two times: the start time and current time
of the computation (which are used to compute the time elapsed
since the start of the program), to a stateful computation on virtual times
(mapping from an old virtual time to a new virtual time) which may
access the kernel to get the actual clock time, and produces a result
along with the new virtual time.  Concretely, |Temporal| is defined:
%%
\begin{code}
data Temporal a =
    T ((Time, Time) -> (VTime -> IO (a, VTime)))
\end{code}
%
where |IO| is part of the Haskell implementation and encapsulates access to
the actual clock time from operation system.

|Temporal| has a monad structure, defined by the following instance of the |Monad| class:
%
\begin{code}
instance Monad Temporal where
  return a     = T ( lamWild -> \vT -> return (a, vT))

  newline
  (T p) >>= q  = T (\(startT, nowT) -> \vT ->
                    do  (x, vT')    <- p (startT, nowT) vT
                        let (T q')  = q x
                        thenT       <- getCurrentTime
                        q' (startT, thenT) vT')
\end{code}
%
To ease understanding, we recall the types of \emph{return}
and |(>>=)| and give some intuition for their behaviour for
\emph{Temporal}:
%
\begin{itemize}
\item |return :: a -> Temporal a| lifts a pure value into a trivially
effectful computation by ignoring the time parameters and
providing the usual pure state behaviour of returning the parameter state |vT| unchanged
along with the result. The nested use of |return|, on the right, comes from the |IO| monad,
thus |return :: a -> IO a|.

\item |(>>=) :: Temporal a -> (a -> Temporal b) -> Temporal b|
  composes two computations together.  The result of composing two
  temporal computations, with start time \emph{startT}, current time
  \emph{nowT}, and virtual time \emph{vT}, is the result of evaluating
  first the left-hand side at time \emph{nowT} and then right-hand side
  at the new current time \emph{thenT}.

  The expression |getCurrentTime :: IO Time| retrieves the time from
  the operation system.
\end{itemize}

\noindent
To model the evaluation of a program, the |runTime| operation executes
a temporal computation inside of the \emph{IO} monad by providing the
start time of the computation, from the operating system and the virtual time 0:
%%
\begin{code}
runTime :: Temporal a -> IO a
runTime (T c) = do  startT <- getCurrentTime
                    (x, _) <- c (startT, startT) 0
                    return x
\end{code}
%%
\begin{example}
To illustrate the evaluation of temporal computations and the
ordering and interleaving of calls to the operation system for the
current time, consider the program:
%%
\begin{code}
runTime (do { f; g; h; })
\end{code}
(where |f = (T f'), g = (T g'), h = (T h')|) which
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
This illustrates the repeated calls to |getCurrentTime|, the
constant start time parameter, and the threading of virtual time state
throughout the computation.
\end{example}

Figure~\ref{core-functions} shows a number of effectful operations of
 the \emph{Temporal} monad that access the current time, the start time, get
and set the virtual time, and cause a kernel sleep. These
are used in the next part of the model.

\begin{figure}[t]
\begin{code}
time :: Temporal Time
time  = T (\(_, nowT) -> \vT -> return (nowT, vT))
newline
start :: Temporal Time
start = T (\(startT, _) -> \vT -> return (startT, vT))
newline
getVirtualTime :: Temporal VTime
getVirtualTime = T (\(_, _) -> \vT -> return (vT, vT))
newline
setVirtualTime :: VTime -> Temporal ()
setVirtualTime vT = T (lamWild -> lamWild -> return ((), vT))
newline
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
\interp{\emph{P}} & : \emph{Temporal} \, () \\
\interp{P; \sleep e} & = \interp{P} |>>= (lamWild ->| \emph{sleep} \, \interp{e}) \\
\interp{P; \synVar = E} & = \interp{P} |>>= (\v ->| \interp{E})
\end{align*}
%%
(where $\interp{-}$ is overloaded in the rule for \sleepOp{} for (pure) expressions).
%The concrete interpretation of other statements in the language, such as \playOp, is
%elided here since it does not relate directly to the temporal semantics.
The primitive \emph{sleep} provides the semantics for \sleepOp{} as:
%%
\begin{code}
sleep :: VTime -> Temporal ()
sleep delayT = do  nowT      <- time
                   vT        <- getVirtualTime
                   let vT'   = vT + delayT
                   setVirtualTime vT'
                   startT    <- start
                   let diffT = diffTime nowT startT
                   if (vT' < diffT)
                     then return ()
                     else kernelSleep (vT' - diffT)
\end{code}
%
where \emph{sleep} proceeds first by getting the current time
\emph{nowT}, calculating the new virtual time \emph{vT'} and updating
the virtual time state. If the new virtual time is less than the
elapsed time \emph{diffT} then no actual (kernel)
sleeping happens. However, if the new virtual time is ahead of the
elapsed time, then the process waits for the difference such that the
elapsed time equals the virtual time.

Note that in this definition we have introduced an overhead, an
$\epsilon$ time, arising from the time elapsed between the first
statment |nowT <- time| and the final |kernelSleep| operation.  The
initial |time| operation retrieves the current time and is used to
calculate the duration of the preceding program. Any sleeping that
happens however occurs after we have calculated the amount of time to
sleep and after we have decided whether a sleep is needed (all of
which takes some time to compute).  Therefore a small $\epsilon$ time
is introduced here.  We will account for this in the following
section.



\subsection{Soundness of the temporal monad: time safety}
\label{sec:soundness}

We replay the previous axiomatic specifications on the temporal behaviour of \lang{} programs,
and show that the monadic model is sound with respect to these, \ie{},
that the model meets this specification. We call this a \emph{time safety} property
of the language, with respect to the time system provided by the axiomatic
specification. 

\noindent
\begin{repdefinition}{def:vtime}
Virtual time is specified for statements of \lang{} programs
by the following cases:
%
\begin{align*}
\begin{array}{crl}
\vtime{P; \synVar = E} = \vtime{P} + \vtime{E} & \qquad \vtime{\sleep t} & \hspace{-0.8em} = t \\
\vtime{\emptyset } = 0 &  \qquad \vtime{A^i} & \hspace{-0.8em}  = 0
\end{array}
\end{align*}
\end{repdefinition}

\begin{lemma}
$\vtime{\mathit{runTime} \, \interp{P}} = \vtime{P}$, \ie{},
the virtual time of the evaluated denotational model matches the virtual time calculated
from the axiomatic model.
\end{lemma}

\begin{proof}
For our model, the proof is straightforward. For the case of
$P; S$, we rely on the monotonicity of virtual time: virtual
time is only ever increasing, and is only ever incremented by \emph{sleep}. 
\end{proof}

\begin{repdefinition}{def:etime}
The actual elapsed time $\etime{-}$ can be specified at the level of programs
by the following equations:
%%
\begin{align*}
\etime{\emptyset} & \, \approx \, 0 \\
\etime{P; \sleep{} t} & \,\approx\,
 (\vtime{P} + t) \;\, \textit{max} \;\, \etime{P} \\
\etime{P; A^i} & \,\approx\,
 \etime{P} + \etime{A^i}
\end{align*}
\end{repdefinition}

\begin{lemma}
$\etime{\mathit{runTime} \, \interp{P}} \approx \etime{P}$, \ie{},
the actual time of the evaluated denotational model is approximately equal
to actual time calculated from the axiomatic model.
\end{lemma}

\begin{proof}
The key case is for $(P; \sleep{} t)$, which we show here.
Our model interprets the evaluation of $(P; \sleep t)$ as:
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
    if (vT'' < diffT)  then return ()
                       else kernelSleep' (vT'' - diffT)

\end{code}
%%
where |kernelSleep' x = threadDelay (round (x * 1000000))| is used
to simplify the code here (as per the definition of \emph{kernelSleep} in
Figure~\ref{core-functions}).

From this we see that $\emph{diffT} = \etime{P}$ and $\emph{vT'} = \vtime{P}$ and
 $\emph{vT''} = \vtime{P} + t$. Therefore, the guard of the
|if| expression is $(\vtime{P} + t) < \etime{P}$.
If the updating of the virtual time state and the computing of
the guard takes $e$ then the overall time taken is:
%%
\begin{align*}
\etime{P; \sleep{} t} & =
 \begin{cases}
   \etime{P} + e & (\vtime{P} + t) < \etime{P}  \\
   \etime{P} + e + (\vtime{P} + t) - \etime{P}  & \textit{otherwise}
 \end{cases} \\
 & =
 \begin{cases}
   \etime{P} + e & (\vtime{P} + t) < \etime{P}  \\
   \vtime{P} + t + e & \textit{otherwise}
 \end{cases} \\
& = (\etime{P} + e)  \, \mathit{max} \, (\vtime{P} + t + e) \\
& \approx \etime{P} \, \mathit{max} \, (\vtime{P} + t)
\end{align*}
%%
where the final stage in this simplification holds if $e
\leq \epsilon$ and if the reduction to the interpretation to get to
the above code takes less than $\epsilon$. This
$\epsilon$ is not however a drift, but a single overhead that can be
be masked by a small \texttt{scheduleAheadTime} (see Section~\ref{sec:new-sleep}). 
\end{proof}

%\note{I suppose this is ok- I'm a bit wary about saying the simplification
%takes less than $\epsilon$. It surely does, but I am only hand waving.
%We could time $e$ though in the model and show it is less than the schedule
%time. We could go further and time the analogous parts of the Sonic Pi implementation
%to check that the real $e$ is less than $\epsilon$. This would be good.}


\subsection{Monad laws and equational theory for Sonic Pi programs}

The |Temporal| monad is ``weak'', in the sense that the standard monad
laws do not always hold.  For example, consider the law:
%%
\begin{equation}
%|(return x) >>= (\y -> f y)| \equiv |f x|
|m >>= return| \equiv |m|
\label{law-example}
\end{equation}
%%
where |m :: Temporal a|. In our model this corresponds to the following
equality on programs:
%%
\begin{equation*}
\interp{x = P; y = x} \equiv \interp{y = P}
\end{equation*}
%%
This should seem an intuitive rule to most programmers.  However, for
the |Temporal| monad, this law is violated in cases where |m| depends
on the current time. For example, let |m| be defined:
%
\begin{code}
m = do   kernelSleep 1
         start <- start
         end <- time
         return (diffTime end start) -- duration
\end{code}
%%
Then we can run an experiment in GHCi to see that different results are possible:
%%
\begin{SVerbatim}
*Main> runTime $ m >>= return
1.001113s
*Main> runTime $ m
1.00114s
\end{SVerbatim}
(note, these results are also non-deterministic).  The difference in
results follows from the additional reduction required on |(>>=)| in
the first case (left-hand side of \eqref{law-example}). Note that we
calculate a duration here since using the absolute time produced by
|time| would be disingenuous, since we are evaluating |m >>= return|
and |m| at different start times.

In the above example, we have computed a time-dependent value (the duration). 
Due to variations in timing (and in the $\epsilon$ overheads), this disrupts
the monad laws as seen above with the monad law shown in equation~\ref{law-example}. 
However, in the programming model of Sonic Pi, there are no
operations that expose the actual time (or current) time to the user-- that is,
the above program is not the model of any Sonic Pi program. We can therefore
``quotient'' the model by operations that do not expose the time, \ie{}, we exclude
|start| and |time|, which are not part of the Sonic Pi language. 
From this we regain the monad laws, up to $\approx$ due to
small variations (as seen above). These are then:
%

%\paragraph{Laws with respect to $\epsilon$}

%\paragraph{Quotienting by non-time dependent functions}

%\note{This section is more of a marker for myself (Dom), I need
%to think about this later, but basically it is about showing
%that the monad laws hold for our semantics (but not in general)}

%In L, there is no expression which returns the current time;
% \emph{getTime} belongs only to the model, not to the language.
%That is, for all expressions $e$, then the denotation
%$\interp{e}$ factors through

\begin{align*}
\begin{array}{rll}
        |(return x) >>= f| &
\approx_{} & |f x|  \\[0.5em]
        |m >>= return|     &
\approx & |m|    \\[0.5em]
        |m >>= (\x -> (f x) >>= g)| &
\approx & |(m >>= f) >>= g|
\end{array}
\end{align*}
%
which each provide the following standard equational theory on SonicPi programs respectively:
%%
\begin{align*}
\texttt{$y$ = $x$; $P$} & \; \equiv \; P \{x \mapsto y\} \\
\texttt{$x$ = $P$; $y$ = $x$} & \; \equiv \; \texttt{$y$ = $P$} \\
\texttt{($x$ = $P$; $y$ = $Q$); $z$ = $R$} & \; \equiv \; \texttt{$x$ = $P$; ($y$ = $Q$; $z$ = $R$)}
\end{align*}
%%

\subsection{Alternate definitions}
\label{sec:alternate}

\noindent
We briefly discuss some alternative structuring of the model here
and an alternate model for \sleepOp{}.

\subsubsection{Subsets of the semantics}

For the examples of Section~\ref{sec:introduction}, the full structure
of monad is not needed to give their semantics as there is no using of
binding between statements (and thus no dataflow). In these case just
an \emph{applicative functor}~\cite{mcbride2008functional} or even a
monoid would suffice. These can be derived from the monad structure
on \emph{Temporal} since all monads are applicative functors and all
monads $m$ define a monoid over |m ()|.

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
The \emph{Applicative} class describes how to compose effectful
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

\subsubsection{Alternate definition for \emph{sleep}}

We give an alternate definition for the model of \sleepOp{} here that
reorders the calculation of the sleep delay. This alternate definition
slightly reduces any oversleeping by minimising noise in the timing.
%
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
Thus, the virtual time is calculated
and updated before the current time is retrieved in case the additional
time taken in updating the virtual time means that the elapsed time
catches up with the virtual time. The previous definition of
\emph{sleep} instead calculated the current time immediately, thus
computing the time of the preceding statement more accurately, but then
not accounting for the time elapsed before sleeping in the |kernelSleep| delay.

To see the difference, consider Definition~\ref{def:etime}, with the
case $\etime{P; \sleep{} t} \approx\,
 (\vtime{P} + t) \;\, \textit{max} \;\, \etime{P}$.
If the above alternate definition \emph{sleep'} is used, then
the interpretation of $(P; \sleep t)$
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
\etime{P; \sleep{} t} & =
 \begin{cases}
   \etime{P} + e_1 + e_2 & (\vtime{P} + t) < (\etime{P} + e_1) \\
   \vtime{P} + t + e_2 &  \textit{otherwise}
 \end{cases} \\
& = ((\vtime{P} + t) \, \mathit{max} \, (\etime{P} + e_1)) + e_2
\end{align*}
%
where $e_1$ is the time taken by updating the virtual time and
$e_2$ is the time taken by the guard. This gives
a tighter bound on sleep behaviour that previously where the behaviour is:
%
\begin{align*}
\etime{P; \sleep{} t} = ((\vtime{P} + t) \, \mathit{max} \, \etime{P}) + e_1 + e_2
\end{align*}
%
\ie{}, without resorting to approximate equalities on time with $\approx$

\section{Emitting overrun warnings}
\label{sec:temporal-warnings}

We extend the |Temporal| monad with an additional parameter for the
$\epsilon$ time (maximum allowable overrun) and an output stream for
sending ``warnings'' when overruns occur.

Overrun warnings are either \emph{strong}, when the real time
is more than $\epsilon$ ahead of virtual time, or \emph{weak} when the real
time is less than $\epsilon$ ahead of virtual time. That is:
%%
\begin{itemize}
\item{$\etime{P} > (\vtime{P} + \epsilon) \Rightarrow \interp{P} \leadsto$ \emph{strong warning} }
\item{$(\vtime{P} + \epsilon) \leq \etime{P} > \vtime{P} \Rightarrow \interp{P} \leadsto$ \emph{weak warning}}
\end{itemize}
%%
We redefine the interpretation $\interp{-}$ to produce computations described
by the following type |TemporalE|, thus $\interp{P} : \emph{TemporalE} \, ()$:
%%
\begin{code}
data Warning = Strong VTime | Weak VTime

data TemporalE a =
    TE (VTime -> Temporal (a, [Warning]))
\end{code}
%%
Therefore, |TemporalE| wraps the previous |Temporal| type with a |VTime|
parameter for $\epsilon$ and pairs the result with a list, representing the output
stream of warnings. The |lift| function (shown in Figure~\ref{core-functionsE})
 allows the previous effectful operations on
|Temporal| to be promoted to the |TemporalE| type (by ignoring the new parameter for
$\epsilon$ and producing the empty output stream), of type
|lift :: Temporal a -> TemporalE a|. Figure~\ref{core-functionsE} shows
a number of other simple |TemporalE| computations for raising exceptions
and getting the $\epsilon$ parameter.

\begin{figure}[t]
\begin{code}
weakWarn :: VTime -> TemporalE ()
weakWarn t = TE (lamWild -> return ((), [Weak t])) >>
        (warn $ "warning: overran by " ++ (show t))
newlinee
strongWarn :: VTime -> TemporalE ()
strongWarn t = TE (lamWild -> return ((), [Strong t])) >>
        (warn $ "WARNING: overran by " ++ (show t))
newline
epsilonTime :: TemporalE VTime
epsilonTime = TE (\eps -> return (eps, []))
newline
lift :: Temporal a -> TemporalE a
lift t = TE (lamWild -> fmap (\a -> (a, [])) t)
newline
warn :: String -> TemporalE ()
warn s = lift (T (lamWild -> \vt -> do  putStrLn s
                                        return ((), vt)))
\end{code}
\caption{Simple \emph{TemporalE} computations}
\label{core-functionsE}
\end{figure}

The |TemporalE| encoding has the following instance of |Monad| which
is simply a combination of the usual reader monad behaviour (for the
$\epsilon$ parameter) and the writer monad (for the output stream), but
lifted to the |Temporal| monad:
%%
\begin{code}
instance Monad TemporalE where
    return a = TE (\_ -> return (a, []))
    (TE p) >>= q = TE (\eps -> do  (a, es) <- p eps
                                   let (TE q') = q a
                                   (b, es') <- q' eps
                                   return (b, es++es'))

\end{code}
%%
Therefore, the |do| here is a |Temporal| computation, with the previous
monadic semantics.

Evaluating |TemporalE| computations is much the same as before, with
the $\epsilon$ time passed as a parameter:
%
\begin{code}
runTime :: VTime -> TemporalE a -> IO (a, [Warning])
runTime eps (TE c) = do  startT <- getCurrentTime
                         let (T c') = c eps
                         (y, _) <- c' (startT, startT) 0
                         return y
\end{code}

Finally, the new definition of |sleep| for |TemporalE| is the point at which
exceptions may be raised:
%
\begin{code}
sleep :: VTime -> TemporalE ()
sleep delayT =
     do  nowT      <- time
         vT        <- getVirtualTime
         let vT'   = vT + delayT
         setVirtualTime vT'
         startT    <- start
         eps       <- epsilonTime
         let diffT = diffTime nowT startT
         if (vT' < diffT)
               then  if ((vT' + eps) < diffT)
                     then strongWarn (diffT - vT')
                     else weakWarn (diffT - vT')
               else kernelSleep (vT' - diffT)
\end{code}
%
The definition is similar to \emph{sleep} for |Temporal|, except
that in the true-branch of the conditional there is additional testing to see if
|diffT| is greater than the new virtual time $+ \epsilon$ (in which case
a strong exception is raised), or if |diffT| is between $vT'$ and $vT' + \epsilon$
(in which case a weak exception is raised).

\section{Related work}
\label{sec:related-work}

Section~\ref{sec:context} considered some related live coding languages
and approaches. We highlight a few others here that arise in logic
and artifical intelligence. 


%Lee~\cite{Lee2009} makes a powerful argument for the development of a
%semantics of time in computation, or as he describes it, a properly
%formalised class of "time system" that can be applied alongside the type
%systems already understood to be an essential software engineering
%tool. As he observes, although the passage of time is a key aspect of
%physical processes, it is almost entirely absent in computing. Indeed, a
%key premise of theoretical computer science is that time is irrelevant
%to correctness, and is at most a measure of quality. Lee's argument is
%founded primarily on the need for embedded computing systems that are
%able to interact with the physical world by including time in the domain
%of discourse. Rather than the distinction between functional and
%non-functional requirements that defines "function" as a mathematical
%mapping from inputs to outputs, in this view the correctness of program
%execution incorporates the concept that an event must occur at the
%correct time. It is important to note, as he attributes to Stankovic,
%that the conventional equation of "real-time computing" as equivalent to
%"fast computing" is a misconception. Although there are indeed computing
%applications where computation must be completed as fast as possible
%before some deadline (and where the most effective research priority may
%be simply to create a faster computer), if time is taken seriously as a
%component of system behaviour (as it is in music) then an event that
%occurs too soon may be just as incorrect as one that occurs too late.

\paragraph{Logics}

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
corresponds to $AF^{\leq t} \interp{P}$, \ie{}, after at least $t$
then whatever $P$ does will have happened. Our framework is not
motivated by logic and we do not have a model checking process for
answering questions such as, at time $t$ what formula hold (what
statements have been evaluated).  The time system approach of
Section~\ref{sec:axiomatic} does however provide a basis for
programmers to reason about time in their programs. In practice, we
find that such reasoning can be done by children in a completely
informal but highly useful way; that language has reached a sweet-spot
between expressivity and ease of understanding. 

\paragraph{Artificial intelligence}

Reasoning about the temporal component of events and action is a classic
problem in artificial intelligence (e.g. Shoham 1988,
Shanahan~\cite{Shanahan1995}, Fisher et al.~\cite{Fisher2005}), in which
causal mechanisms and metrical description may be more or less tightly
coupled. Human interaction with systems that employ temporal reasoning
can be considered either from a software engineering perspective (the
usability of formal time notations, for example as in Kutar et al. 2001),
or from a cognitive science standpoint, as in Honing's discussion of
music cognition from a representational
perspective~\cite{Honing1993}. Honing observes that representation of
time in music can be both declarative and procedural, drawing on
propositional and analogical cognitive resources. These representations
may have conflicting implications for efficiency of control and
accessibility of knowledge, for example trills or vibrato can be readily
performed by an expert musician, but use mechanisms that are difficult
to describe. Honing suggests that computer music systems should be
distinguished according to whether they support only tacit time
representation (events are encoded only as occurring "now"), implicit
time representation (events are ordered in a metrical sequence) or
explicit time representation (temporal structure can be described and
manipulated). Bellingham et al.~\cite{Bellingham2014} provide a survey of
32 algorithmic composition systems, in which they apply Honing's
framework to discuss the problem of notating the hierarchical
combinations of cyclical and linear time that result in musical
perception of pattern and tempo.

\section{Conclusion}

In this paper we have described an enhancement to the Sonic Pi language
that improves the quality of musical experience for novice programmers
in a live coding context. This is achieved by modifying the semantics
of the familiar "sleep" operator in a manner that is consistent with
musical expectations, while differing from the conventional
interpretation in many languages. As a result, the enhanced Sonic Pi
is able to retain identical concrete syntax to earlier versions, while
implementing behaviour that is simple and predictable from a
programmer perspective. Other music programming systems often provide
similar mechanisms in order to achieve predictable timing behaviour,
and our solution is comparable to those that have been implemented in
other systems. We therefore introduce a formal semantics that can be
used to prove the desirable properties of this kind of temporal
behaviour. This combination of simple syntax, with formally defined
semantics that correspond to user expectations, promises to be
beneficial beyond the domain of music programming, to other types of
physical world interface.

Further work is to expand the notion of \emph{time safety} and
\emph{time systems}, which we have introduced here, and explore their
use in live coding languages and languages for temporal coordination
(such as in robotics).  We considered the safety property of ``not
being too early'', which is an invariant of the Sonic Pi language.
Further work is to explore language invariants relating to deadlines (similar
to the real-times logics discussed earlier). 

\paragraph{Acknowledgements}

We thank Andrew Rice for helpful discussion about this work.
This work was kindly supported by the Raspberry Pi foundation.

\bibliography{references}

\appendix

\end{document}
