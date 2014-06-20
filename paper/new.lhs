\documentclass[preprint,9pt]{sigplanconf}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%format <*> = "<\!\!\!*\!\!\!>"
%format newline = "\\[-1.5em]"
%format interpP = "\interp{P}"
%format lamWild = "\lambda{\anonymous}"


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

\newcommand{\envE}{\mathit{env}}

\begin{document}

We define an interpretation $\interp{-}$ overloaded on programs,
statements, and expressions where the type of the interpretation
depends on the syntactic category. The interpretation of a closed
program yields a value of type |Temporal ()|. For open syntax, we
model a variable environment mapping variables to values by
the |Env| type, which is threaded through the interpretation. 
For expression, we model the value domain via the data type |Value|
(for which we elide the details of this definition). 

The interpretation reassociates the left-associated program syntax (where the last
statement is at the head of the snoc-list representation) to a right-associated
semantics using a continuation-passing approach, \eg{}, for a three statement program
%
\newcommand{\fcomp}{\,\hat{\circ}\,}
%
\[\interp{((\emptyset;S_1);S_2);S_3} = \interp{S_1} \fcomp (\interp{S_2} \fcomp (\interp{S_3} \fcomp \interp{\emptyset}))\]
%
where $\fcomp$ represents the (forwards, left-to-right) sequential composition of denotations
and as before $\emptyset$ represents the empty program.

The interpretation of statement sequences is defined:
%
\begin{align*}
\interp{P} & |:: (Env -> Temporal ()) -> Temporal ()| \\
\interp{\emptyset} \, k & = k \, \mathit{emptyEnv} \\
\interp{P; S}      \, k & = \interp{P} \, (\lambda \envE{} . \; (\interp{S} \, \envE{}) |>>=| k)
\end{align*}
%
Thus, the parameter $k$ is a continuation (taking an environment |Env|) 
for the tail of the right-associated semantics. The interpretation of
statements is defined:
%%
\begin{align*}
& \interp{S} :: |Env -> Temporal Env| \\
& \interp{\anonymous = E} \envE{} = (\interp{E} \envE{}) |>>= (lamWild -> return env)| \\
& \interp{v = E} \envE{} = (\interp{E} \envE{}) |>>= (\x -> return env|[v \mapsto x])
\end{align*}
%%
For both kinds of statement, with and without variable binding, the expression $E$
is evaluated where $\interp{E} |:: Env -> Temporal Value|$. The result
of evaluting $E$ is then monadically composed (via |>>=| of the |Temporal| monad)
with a computation returning an environment. 
For statements without a binding, the environment |env| is returned unmodified; 
for statements with a binding, the environment |env| is extended with a mapping from $v$ to
the value $x$ of the evaluated expression, written here as $|env|[v \mapsto x]$. 

For expressions, we show just the interpretation of \texttt{sleep} 
and variable expressions (which project from the environment):
\begin{align*}
\interp{E} & |:: Env -> Temporal Value| \\
\interp{\texttt{sleep} \, e} \envE{} & = |(sleep t) >>= (lamWild -> return NoValue)| \\
\interp{v} \envE{} & = |return (env v)|
\end{align*}
where $|NoValue| \in Value$. 


At the top-level, we interpret a closed program to a value
of the |Temoral| monad, \ie{}, $\interp{P}_{\mathsf{top}} :: Temporal ()$, defined:
%%
\begin{align*}
\interp{P}_{\mathsf{top}} = |runTime| (\interp{P} (\lambda \anonymous \; . \; |return ()|))
\end{align*}
%%





\end{document}
