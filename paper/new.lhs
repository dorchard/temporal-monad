\documentclass[preprint]{sigplanconf}

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

The interpretation reassociates the right-associative program syntax (where the last
statement is at the head of the snoc-list representation) to a left-associated
semantics using a continuation-style approach. The interpretation of statement sequences
has type:
\begin{align*}
\interp{P} & |:: (Env -> Temporal ()) -> Temporal ()|
\end{align*}
%
The parameter is a continuation, taking in an environment, which
is the tail of the left-associated semantics:
\begin{align*}
\interp{\emptyset} \, k & = k \, \mathit{emptyEnv} \\
\interp{P; S}      \, k & = \interp{P} \, (\lambda \envE{} . \; (\interp{S} \, \envE{}) |>>=| k) \\
\end{align*}

At the top-level, we interpret a closed program to a value
of the |Temoral| monad, \ie{}, $\interp{P} :: Temporal ()$, defined:
%%

%%



\begin{align*}
& \interp{S} :: |Env -> Temporal Env| \\
& \interp{\anonymous = E} \envE{} = (\interp{E} \envE{}) |>>= (lamWild -> return env)| \\
& \interp{v = E} \envE{} = (\interp{E} \envE{}) |>>= (\x -> return env|[v \mapsto x])
\end{align*}

\begin{align*}
\interp{E} |:: Env -> Temporal Value|
\end{align*}

\begin{align*}
\interp{\texttt{sleep} \, e} \envE{} & = |(sleep t) >>= (lamWild -> return NoValue)|
\end{align*}



\end{document}
