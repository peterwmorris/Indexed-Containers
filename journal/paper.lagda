%if style == newcode

\begin{code}

module paper where

\end{code}

%endif

\documentclass[a4paper]{article}

\usepackage{url}
\usepackage{times}
\usepackage{amsmath}
\usepackage{xypic}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{stmaryrd}
\usepackage{color}

\newcommand{\note}[1]{}
\newcommand{\todo}[1]{\textcolor{red}{\textbf{Todo:~}#1}}

%include lhs2TeX.fmt
%include agda.fmt

%include lib.fmt

%format . = "."
%format $$ = "\!\!" 
%format split = \ ( "\!"
%format tilps = "\!\!" )
%format & = "\!" , "\!"
%format ↦ =  →
%format !* = "\!" 
%format !s = "\!"
%format !m = "\!"

\begin{document}

\newcounter{theorem}

\newtheorem{proposition}[theorem]{Proposition}
\newenvironment{proof}[1][Proof]{\begin{trivlist}
\item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}

\title{Indexed Containers}
\author{Thorsten Altenkirch 
   \and Neil Ghani 
   \and Peter Hancock 
   \and Conor McBride 
   \and Peter Morris}
\date{\today}

\maketitle

\begin{abstract}

  We show that the syntactically rich notion of inductive families can
  be reduced to a core type theory with a fixed number of type
  constructors exploiting the novel notion of indexed containers.
  Indexed containers generalize simple containers, capturing strictly
  positive families instead of just strictly positive types, without
  having to extend the core type theory. Other applications of indexed
  containers include datatype-generic programming and reasoning about
  polymorphic functions. The construction presented here has been
  formalized using the Agda system.

\end{abstract}


%%Introduction
%include introduction.lagda

\section{Background}
\label{sec:background}

 %include tt.lagda
 %include cont.lagda

%%Indexed Functors
%include ifunc.lagda

%%Indexed Containers
%include icont.lagda

%%Init Alg ICont
%include initalg.lagda
 
%%Term Co-Alg ICont
%include termcoalg.lagda

\section{W is still enough}
\label{sec:w-enough}

%include wifromw.lagda
%include mfromw.lagda

%%Strictly Positive Families
%include spf.lagda

\section{Conclusions}


\bibliographystyle{plain}
\bibliography{ic}

\end{document}
