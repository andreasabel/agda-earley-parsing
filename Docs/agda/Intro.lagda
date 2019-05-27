\newcommand{\agdaNat}{
\begin{code}
data ℕ : Set where
  zero  :  ℕ
  suc   :  ℕ → ℕ
\end{code}
}

\newcommand{\agdaPlus}{
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero   +  b  =  b
suc a  +  b  =  suc (a + b)
\end{code}
}
