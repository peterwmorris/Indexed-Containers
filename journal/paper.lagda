%if style == newcode

\begin{code}

module paper where

\end{code}

%endif

\documentclass[a4paper]{article}

% \documentclass[12pt]{article}
% \usepackage[paperwidth=9cm, paperheight=12cm, top=0.5cm, bottom=0.5cm, left=0.0cm, right=0.5cm]{geometry}
% \special{papersize=9cm,12cm}

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

  We show that the syntactically rich notion of strictly positive
  families can be reduced to a core type theory with a fixed number of
  type constructors exploiting the novel notion of indexed containers.
  As a result, we show indexed containers capture strictly positive families
  in much the same way that containers capture strictly positive
  types. Interestingly, this step from containers to indexed
  containers is achieved without having to extend the core type
  theory. 
%Other applications of indexed containers include
%  datatype-generic programming and reasoning about polymorphic
%  functions. 
The construction presented here has been formalized using
  the Agda system.

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

We have shown how inductive and coinductive families, a central
feature in dependently typed programming, can be constructed from the
standard infrastructure present in Type Theory, i.e. W-types together
with $\Pi$, $\Sigma$ and equality types. Indeed, we are able to reduce
the syntactically rich notion of families to a small collection of
categorically inspired combinators. This is an alternative to the
complex syntactic schemes present in the \emph{Calculus of Inductive
  Constructions} (CIC), or in the Agda and Epigram systems. We are
able to encode inductively defined families in a small core language
which means that we rely only on a small trusted code base. The
reduction to W-types requires an extensional propositional
equality. Our current approach using an axiom |ext| is sufficent for
proofs but isn't computationally adequate. A more satisfying approach
would built on \emph{Observational Type Theory} (OTT)
\cite{alti:ott-conf}.

\todo{Mention Epigram 2?}

The present paper is an annotated Agda script, i.e. all the proofs are
checked by the Agda system. We have tried hard to integrate the formal
development with the narrative. In some cases we have surpressed
certain details present in the source of the paper to keep the
material readable.

A more serious challenge are mutual inductively (or coinductively)
defined families where one type depends on another
\cite{forsberg2010inductive}. A typical example is the syntax of Type
Theory itself which, to simplify, can be encoded by mutually defining
contexts containing terms, types in a given context and terms in a
given type:
\begin{spec}
Con : Set
Ty : Con → Set
Tm : (Γ : Con) → Ty Γ → Set
\end{spec}
In recent work \cite{txa:catind2} present a categorical semantics for
this kind of definitions based on dialgebras. However, a presentation
of strictly positive definitions in the spirit of contaienrs is not
yet available.

\todo{Discuss the relationship to inductive-recursive definitions.}

\bibliographystyle{plain}
\bibliography{ic}

\end{document}
