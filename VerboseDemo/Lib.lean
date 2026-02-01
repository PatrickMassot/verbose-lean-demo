import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean

import Verbose.English.All

macro "setup_env" : command => `(set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.unnecessarySimpa false
)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab Max.max]
def delabMax : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Max.max 4
  let m := mkIdent `max
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($(m) $(x) $(y))

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def continuous_fun_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def seq_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

notation:50 f:80 " is continuous at " x₀ => continuous_fun_at f x₀
notation:50 u:80 " converges to " l => seq_tendsto u l

def pair (n : ℤ) := ∃ k, n = 2*k
notation:50 n:60 " is even" => pair n

def impair (n : ℤ) := ∃ k, n = 2*k + 1
notation:50 n:60 " is odd" => impair n

lemma non_pair_et_impair (n : ℤ) : ¬ (n is even ∧ n is odd) := by
  rintro ⟨⟨k, rfl⟩, ⟨l, h⟩⟩
  omega

lemma non_pair_impair (n : ℤ) (h : n is even) (h' : n is odd) : False :=
  non_pair_et_impair n ⟨h, h'⟩

lemma pair_iff_even (n : ℤ) : n is even ↔ Even n := by
  apply exists_congr (fun k ↦ ?_)
  rw [Int.two_mul]

lemma impair_iff_odd (n : ℤ) : n is odd ↔ Odd n := Iff.rfl

@[push_neg_extra]
lemma non_pair_ssi_impair (n : ℤ) : ¬ n is even ↔ n is odd := by
  simp [pair_iff_even, impair_iff_odd]

@[push_neg_extra]
lemma non_impair_ssi_pair (n : ℤ) : ¬ n is odd ↔ n is even := by
  simp [pair_iff_even, impair_iff_odd]

-- Les deux lemmes suivants sont nécéssaires si `sufficesPushNeg` a déplié la
-- définition de pair ou impair

@[push_neg_extra]
lemma non_pair_ssi_impair' (n : ℤ) : (∀ k, n ≠ 2*k) ↔ n is odd := by
  rw [← non_pair_ssi_impair, «pair», not_exists]

@[push_neg_extra]
lemma non_impair_ssi_pair' (n : ℤ) : (∀ k, n ≠ 2*k + 1) ↔ n is even := by
  rw [← non_impair_ssi_pair, «impair», not_exists]

lemma impair_car_non_pair (n : ℤ) (h : ¬ n is even) : n is odd :=
  (non_pair_ssi_impair n).1 h

lemma pair_car_non_impair (n : ℤ) (h : ¬ n is odd) : n is even :=
  (non_impair_ssi_pair n).1 h

lemma non_pair_car_impair (n : ℤ) (h : n is odd) : ¬ n is even :=
  (non_pair_ssi_impair n).2 h

lemma non_impair_car_pair (n : ℤ) (h : n is even) : ¬ n is odd :=
  (non_impair_ssi_pair n).2 h

lemma impair_succ_pair (n : ℤ) (h : n is even) : (n + 1) is odd := by
  rcases h with ⟨k, rfl⟩
  use k

lemma pair_succ_impair (n : ℤ) (h : n is odd) : (n + 1) is even := by
  rcases h with ⟨k, rfl⟩
  use k+1
  ring

open Verbose.English

lemma le_of_abs_le' {α : Type*}  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {x y : α} : |x| ≤ y → -y ≤ x := fun h ↦ abs_le.1 h |>.1

/-- Multiplicité de `2` dans la décomposition en produit de facteurs premiers d’un entier -/
axiom v₂ : ℤ → ℤ

axiom v₂_square (p : ℤ) : v₂ (p^2) is even

axiom v₂_two_mul (p : ℤ) (hp : p ≠ 0) : v₂ (2*p) = v₂ p + 1

lemma lt_lt_of_abs_lt {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α} : |a| < b → -b < a ∧ a < b := abs_lt.1

lemma lt_of_abs_lt' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {a b : α} (h : |a| < b) : -b < a := (abs_lt.1 h).1

lemma lt_of_abs_lt'' {a b c : ℝ} (h : |a| < b/c) : -b/c < a := by grind [abs_lt]

configureAnonymousFactSplittingLemmas
  le_le_of_abs_le le_le_of_max_le le_of_max_le_left le_of_max_le_right
  le_of_abs_le le_of_abs_le'
  lt_of_abs_lt lt_of_abs_lt' lt_of_abs_lt''
  non_pair_impair pair_car_non_impair impair_car_non_pair non_pair_car_impair non_impair_car_pair
  pair_succ_impair impair_succ_pair
  v₂_square v₂_two_mul pow_ne_zero lt_lt_of_abs_lt
  lt_trans

lemma abs_lt_of_lt_lt {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b < a) (h' : a < b) : |a| < b := abs_lt.2 ⟨h, h'⟩

lemma abs_lt_of_lt_lt' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h' : a < b) (h : -b < a) : |a| < b := abs_lt.2 ⟨h, h'⟩

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm abs_lt_of_lt_lt
abs_lt_of_lt_lt'

useDefaultDataProviders

useDefaultSuggestionProviders

configureUnfoldableDefs continuous_fun_at seq_tendsto pair impair

configureHelpProviders SinceHypHelp SinceGoalHelp helpByContradictionGoal helpShowContrapositiveGoal

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le eq_zero_or_eq_zero_of_mul_eq_zero Classical.em le_total

axiom abs_mul_nat (n : ℕ) (x : ℝ) : |(OfNat.ofNat n : ℝ)*x| = (OfNat.ofNat n : ℝ) *|x|


addAnonymousComputeLemma abs_mul_nat
addAnonymousComputeLemma abs_mul

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

macro "seq " i:ident " ↦ " y:term : term => `(fun ($i : ℕ) ↦ ($y : ℝ))

axiom stupid_arch {A : ℝ} : ∃ N : Nat, N ≥ A

axiom A {ε a : ℝ} (h : ε > 0) (h' : a ≥ 1/ε) : ε ≥ 1/a
axiom A' {ε a : ℝ} (h : ε > 0) (h' : a > 1/ε) : ε > 1/a

lemma B {a b : ℕ} (ha : 0 < a) (h : a ≤ b) : 1/b ≤ 1/a := by
  apply one_div_le_one_div_of_le <;> assumption_mod_cast

lemma C {a b : ℕ} (ha : 0 < a) (h : a < b) : 1/b < 1/a := by
  apply one_div_lt_one_div_of_lt <;> assumption_mod_cast

lemma one_div_pos_of_pos {ε : ℝ} (h : ε > 0) : 1/ε > 0 :=
  one_div_pos.mpr h


addAnonymousFactSplittingLemma stupid_arch
addAnonymousFactSplittingLemma A
addAnonymousFactSplittingLemma A'
addAnonymousFactSplittingLemma B
addAnonymousFactSplittingLemma one_div_pos_of_pos
addAnonymousFactSplittingLemma lt_of_lt_of_le
addAnonymousFactSplittingLemma lt_of_abs_lt


addAnonymousFactSplittingLemma Nat.le_ceil
addAnonymousComputeLemma Nat.le_ceil

lemma le_of_abs_le'' {a b c : ℝ} (h : |a| ≤ b/c) : -b/c ≤ a := by
  grind

addAnonymousFactSplittingLemma le_of_abs_le''
addAnonymousCaseSplittingLemma  Nat.le_or_eq_of_le_succ
lemma barbaz (x y : ℝ) : |x| ≤ |x - y| + |y| := by grind

addAnonymousComputeLemma barbaz

