import VerboseDemo.Lib

/-!
# Some levels from the Real analysis game

Compare with
https://github.com/AlexKontorovich/RealAnalysisGame/blob/main/Game/Levels/L3Levels/L01_ArchProp.lean
https://github.com/AlexKontorovich/RealAnalysisGame/blob/main/Game/Levels/L3Levels/L02_OneOverN.lean
https://github.com/AlexKontorovich/RealAnalysisGame/blob/main/Game/Levels/L4Levels/L01_NonConverge.lean
https://github.com/AlexKontorovich/RealAnalysisGame/blob/main/Game/Levels/L5Levels/L01_DoubleSeqConv.lean
https://github.com/AlexKontorovich/RealAnalysisGame/blob/main/Game/Levels/L9Levels/L05_BddOfConv.lean
(but note the last one uses a completely different strategy to prove that convergent sequences are
bounded.
-/

open Verbose.NameLess

Exercise-lemma arch "Weak archimedian property"
Given: {A : ℝ}
Assume:
Conclusion: ∃ (N : ℕ), A < N
Proof:
  Let's prove that ⌈A⌉₊ + 1 works
  Calc
    A ≤ ⌈A⌉₊           by computation
    _ < ⌈A⌉₊ + 1       by computation
QED

Exercise "n ↦ 1/n converges to zero"
Given:
Assume:
Conclusion: (seq n ↦ 1/n) converges to 0
Proof:
  Fix ε > 0
  We obtain N : ℕ such that N > 1/ε
  Let's prove that N works
  Since ε > 0 we get that 1/ε > 0
  Since N ≥ 1/ε and 1/ε > 0 we get that N > 0

  Fix n ≥ N
  Calc
    |(seq n ↦ 1 / n) n - 0| = 1/n by computation
    _                       ≤ 1/N since n ≥ N and N > 0
    _                       < ε   since N > 1/ε and ε > 0
QED


Exercise "n ↦ (-1)^n does not converge"
  Given:
  Assume:
  Conclusion: ¬ ∃ l, (seq n ↦ (-1)^n) converges to l
Proof:
  Assume that ∃ l, (seq n ↦ (-1)^n) converges to l
  Since ∃ l, (seq n ↦ (-1)^n) converges to l we get l such that
    (seq n ↦ (-1)^n) converges to l
  Since 1/2 > 0 and (seq n ↦ (-1)^n) converges to l we get N such that
    ∀ n ≥ N, |(-1)^n - l| < 1/2

  Since ∀ n ≥ N, |(-1)^n - l| < 1/2 and 2*N ≥ N we get that |(-1)^(2*N) - l| < 1/2
  Since |(-1)^(2*N) - l| < 1/2 and (-1)^(2*N) = (1 : ℝ) we get that |1 - l| < 1/2
    hence 1 - l < 1/2 hence 1/2 < l

  Since ∀ n ≥ N, |(-1)^n - l| < 1/2 and 2*N + 1 ≥ N we get that |(-1)^(2*N+1) - l| < 1/2
  Since |(-1)^(2*N+1) - l| < 1/2 and (-1)^(2*N+1) = (-1 : ℝ) we get that |-1 - l| < 1/2
    hence -1/2 < -1 - l hence l < -1/2

  Since 1/2 < l and l < -1/2 we get that 1/2 < -1/2
    finally we conclude that False
QED

Exercise "double of convergent sequence"
  Given: (a : ℕ → ℝ) (l : ℝ)
  Assume: (ha : a converges to l)
  Conclusion: (2*a) converges to 2*l
Proof:
  Fix ε > 0
  Since a converges to l and ε/2 > 0 we get N such that ∀ n ≥ N, |a n - l| < ε/2
  Let's prove that N works
  Fix n ≥ N
  Since (∀ n ≥ N, |a n - l| < ε/2) and n ≥ N we get that |a n - l| < ε/2
  Calc
    |(2 * a) n - 2 * l| = |2*(a n - l)| by computation
      _                 = 2 * |a n - l| by computation
      _                 < 2*ε/2 since |a n - l| < ε/2
      _                 = ε by computation
QED


Exercise-lemma fin_seq_bounded "Finite sequences are bounded"
  Given: (u : ℕ → ℝ) (N : ℕ)
  Assume:
  Conclusion: ∃ M, ∀ n ≤ N, |u n| ≤ M
Proof:
  Let's prove by induction that ∀ N, ∃ M, ∀ n ≤ N, |u n| ≤ M
  · Let's prove that |u 0| works
    Fix n ≤ 0
    Since n ≤ 0 we get that n = 0
      hence |u n| = |u 0|
      finally we conclude that |u n| ≤ |u 0|
  · Fix N
    Assume that ∃ M, ∀ n ≤ N, |u n| ≤ M
    Since ∃ M, ∀ n ≤ N, |u n| ≤ M we get M such that ∀ n ≤ N, |u n| ≤ M
    Let's prove that max M |u (N + 1)| works
    Fix n ≤ N + 1
    We discuss depending on whether n ≤ N or n = N + 1
    · Assume that n ≤ N
      Calc
        |u n| ≤ M           since n ≤ N and ∀ n ≤ N, |u n| ≤ M
        _     ≤ max M |u (N + 1)| by computation
    · Assume that n = N + 1
      Calc
        |u n| = |u (N + 1)|       since n = N + 1
        _     ≤ max M |u (N + 1)| by computation
QED

Exercise "Convergent sequences are bounded"
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (hu : u converges to l)
  Conclusion:  ∃ M, ∀ n, |u n| ≤ M
Proof:
  Since u converges to l and 1 > 0 we get N such that ∀ n ≥ N, |u n - l| < 1
  We obtain M such that ∀ n ≤ N, |u n| ≤ M
  Let's prove that max M (1 + |l|) works
  Fix n
  We discuss depending on whether n ≤ N or n ≥ N
  · Assume that n ≤ N
    Calc
      |u n| ≤ M               since n ≤ N and ∀ n ≤ N, |u n| ≤ M
      _     ≤ max M (1 + |l|) by computation

  · Assume that n ≥ N
    Since n ≥ N and ∀ n ≥ N, |u n - l| < 1 we get that |u n - l| < 1
    Calc
      |u n| ≤ |u n - l| + |l| by computation
      _     < 1 + |l| since |u n - l| < 1
      _     ≤ max M (1 + |l|) by computation
QED

