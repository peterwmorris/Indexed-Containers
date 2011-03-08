%if style == newcode

module paper where

%endif

\documentclass[a4paper]{article}

\usepackage{url}
\usepackage{times}
\usepackage{amsmath}
\usepackage{xypic}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{stmaryrd}

\newcommand{\note}[1]{}

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

Blah

\end{abstract}


\section{Introduction}

\section{Background}

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

%include wifromw.lagda
%include mfromw.lagda

\section{Strictly Positive Types}

\section{Conclusions}


\bibliographystyle{plain}
\bibliography{paper}

\end{document}
