/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import TauCeti.Data.Fin.Tuple.Perm

/-!
# Iterated directional derivatives on `W^{k,p}`

Iterating `TauCeti.Wkp.lineDerivL` along a tuple `m : Fin j → E` defines
`TauCeti.Wkp.iteratedLineDerivL` and its order-zero specialisation
`TauCeti.Wkp.iteratedLineDerivZeroL`. Both are multilinear in each direction slot, commute with
order truncation (`TauCeti.Wkp.toOrderL_iteratedLineDerivL`), and are invariant under every
permutation of the direction tuple (`TauCeti.Wkp.iteratedLineDerivL_comp_perm`,
`TauCeti.Wkp.iteratedLineDerivZeroL_comp_perm`).

No boundedness or boundary regularity of `Ω` is assumed.

## Main declarations

* `TauCeti.Wkp.iteratedLineDerivL` and `TauCeti.Wkp.iteratedLineDerivZeroL`: iterated bundled
  directional derivatives along a tuple `Fin j → E`.
* `TauCeti.Wkp.toOrderL_iteratedLineDerivL` and
  `TauCeti.Wkp.value_iteratedLineDerivL_eq_iteratedLineDerivZeroL`: compatibility with order
  truncation and `Lᵖ` values.
* `TauCeti.Wkp.iteratedLineDerivL_comp_perm` and `TauCeti.Wkp.iteratedLineDerivZeroL_comp_perm`:
  permutation invariance of iterated directional derivatives.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.2.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, §4.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace Wkp

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Iterated directional derivatives -/

/-- **Iterated bundled directional derivative.** Differentiate an element of `W^{k+j,p}(Ω)`
successively along `m 0, m 1, …, m (j - 1)`, landing in `W^{k,p}(Ω)`. -/
def iteratedLineDerivL (k : ℕ) :
    (j : ℕ) → (Fin j → E) → Wkp mu Omega p (k + j) →L[ℝ] Wkp mu Omega p k
  | 0, _ => ContinuousLinearMap.id ℝ (Wkp mu Omega p k)
  | j + 1, m => (iteratedLineDerivL k j (Fin.tail m)).comp (lineDerivL (m 0) (k + j))

@[simp]
theorem iteratedLineDerivL_zero (k : ℕ) (m : Fin 0 → E) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k 0 m =
      ContinuousLinearMap.id ℝ (Wkp mu Omega p k) :=
  (rfl)

theorem iteratedLineDerivL_succ (k j : ℕ) (m : Fin (j + 1) → E) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k (j + 1) m =
      (iteratedLineDerivL k j (Fin.tail m)).comp (lineDerivL (m 0) (k + j)) :=
  (rfl)

@[simp]
theorem iteratedLineDerivL_one (k : ℕ) (m : Fin 1 → E) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k 1 m = lineDerivL (m 0) k := by
  rw [iteratedLineDerivL_succ, iteratedLineDerivL_zero]
  exact ContinuousLinearMap.id_comp _

/-- Updating slot `i` of the direction tuple with `v₁ + v₂` splits `iteratedLineDerivL` as a
sum. -/
@[simp]
theorem iteratedLineDerivL_update_add (k : ℕ) :
    ∀ (j : ℕ) (m : Fin j → E) (i : Fin j) (v₁ v₂ : E),
      iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j
          (Function.update m i (v₁ + v₂)) =
        iteratedLineDerivL k j (Function.update m i v₁) +
          iteratedLineDerivL k j (Function.update m i v₂)
  | 0, _, i, _, _ => i.elim0
  | j + 1, m, i, v₁, v₂ => by
      cases i using Fin.cases with
      | zero =>
          simp only [iteratedLineDerivL_succ, Function.update_self, Fin.tail_update_zero,
            lineDerivL_add_left, ContinuousLinearMap.comp_add]
      | succ i =>
          simp only [iteratedLineDerivL_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm,
            Fin.tail_update_succ, iteratedLineDerivL_update_add k j (Fin.tail m) i v₁ v₂,
            ContinuousLinearMap.add_comp]

/-- Updating slot `i` of the direction tuple with `c • v` scales `iteratedLineDerivL` by `c`. -/
@[simp]
theorem iteratedLineDerivL_update_smul (k : ℕ) :
    ∀ (j : ℕ) (m : Fin j → E) (i : Fin j) (c : ℝ) (v : E),
      iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j
          (Function.update m i (c • v)) =
        c • iteratedLineDerivL k j (Function.update m i v)
  | 0, _, i, _, _ => i.elim0
  | j + 1, m, i, c, v => by
      cases i using Fin.cases with
      | zero =>
          simp only [iteratedLineDerivL_succ, Function.update_self, Fin.tail_update_zero,
            lineDerivL_smul_left, ContinuousLinearMap.comp_smul]
      | succ i =>
          simp only [iteratedLineDerivL_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm,
            Fin.tail_update_succ, iteratedLineDerivL_update_smul k j (Fin.tail m) i c v,
            ContinuousLinearMap.smul_comp]

/-- Evaluating `iteratedLineDerivL` at a tuple with zero in slot `i` gives the zero map. -/
@[simp]
theorem iteratedLineDerivL_update_zero (k j : ℕ) (m : Fin j → E) (i : Fin j) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j
        (Function.update m i 0) = 0 := by
  simpa using iteratedLineDerivL_update_smul (mu := mu) (Omega := Omega) (p := p) k j m i 0 0

/-- The `Lᵖ` value of `iteratedLineDerivL` depends only on the `Lᵖ` value of the input,
not on the target order `k`. -/
private theorem value_iteratedLineDerivL_eq_of_value_eq {k₁ k₂ : ℕ} :
    ∀ (j : ℕ) (m : Fin j → E)
      {u₁ : Wkp mu Omega p (k₁ + j)} {u₂ : Wkp mu Omega p (k₂ + j)},
      value (k₁ + j) u₁ = value (k₂ + j) u₂ →
      value k₁ (iteratedLineDerivL k₁ j m u₁) = value k₂ (iteratedLineDerivL k₂ j m u₂)
  | 0, _, _, _, h => h
  | j + 1, m, _, _, h => by
      rw [iteratedLineDerivL_succ, ContinuousLinearMap.comp_apply, iteratedLineDerivL_succ,
        ContinuousLinearMap.comp_apply]
      exact value_iteratedLineDerivL_eq_of_value_eq j (Fin.tail m)
        (value_lineDerivL_eq_of_value_eq h (m 0))

/-- **Order-zero iterated directional derivative.** Differentiate an element of `W^{j,p}(Ω)` along
`j` directions `m : Fin j → E`, landing directly in `Lᵖ(Ω)` without arithmetic casts on `0 + j`. -/
def iteratedLineDerivZeroL (j : ℕ) (m : Fin j → E) :
    Wkp mu Omega p j →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  (iteratedLineDerivL 0 j m).comp (toOrderL (Nat.zero_add j).le)

@[simp]
theorem iteratedLineDerivZeroL_zero (m : Fin 0 → E) :
    iteratedLineDerivZeroL (E := E) (mu := mu) (Omega := Omega) (p := p) 0 m =
      ContinuousLinearMap.id ℝ (Lp ℝ p (mu.restrict Omega)) := by
  rw [iteratedLineDerivZeroL, iteratedLineDerivL_zero, toOrderL_self, ContinuousLinearMap.id_comp]

theorem iteratedLineDerivZeroL_succ (j : ℕ) (m : Fin (j + 1) → E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) (j + 1) m =
      (iteratedLineDerivZeroL j (Fin.tail m)).comp (lineDerivL (m 0) j) := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [iteratedLineDerivZeroL, iteratedLineDerivZeroL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, iteratedLineDerivL_succ,
    ContinuousLinearMap.comp_apply]
  refine (value_zero _).symm.trans ((value_iteratedLineDerivL_eq_of_value_eq j (Fin.tail m)
    ((value_lineDerivL_eq_of_value_eq (value_toOrderL _ u) (m 0)).trans
      (value_toOrderL _ _).symm)).trans (value_zero _))

@[simp]
theorem iteratedLineDerivZeroL_one (m : Fin 1 → E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) 1 m = lineDerivL (m 0) 0 := by
  rw [iteratedLineDerivZeroL_succ, iteratedLineDerivZeroL_zero]
  exact ContinuousLinearMap.id_comp _

/-- Updating slot `i` of the direction tuple with `v₁ + v₂` splits `iteratedLineDerivZeroL` as
a sum. -/
@[simp]
theorem iteratedLineDerivZeroL_update_add (j : ℕ) (m : Fin j → E) (i : Fin j) (v₁ v₂ : E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j
        (Function.update m i (v₁ + v₂)) =
      iteratedLineDerivZeroL j (Function.update m i v₁) +
        iteratedLineDerivZeroL j (Function.update m i v₂) := by
  simp only [iteratedLineDerivZeroL, iteratedLineDerivL_update_add, ContinuousLinearMap.add_comp]

/-- Updating slot `i` of the direction tuple with `c • v` scales `iteratedLineDerivZeroL` by
`c`. -/
@[simp]
theorem iteratedLineDerivZeroL_update_smul (j : ℕ) (m : Fin j → E) (i : Fin j) (c : ℝ) (v : E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j
        (Function.update m i (c • v)) =
      c • iteratedLineDerivZeroL j (Function.update m i v) := by
  simp only [iteratedLineDerivZeroL, iteratedLineDerivL_update_smul, ContinuousLinearMap.smul_comp]

/-- Evaluating `iteratedLineDerivZeroL` at a tuple with zero in slot `i` gives the zero map. -/
@[simp]
theorem iteratedLineDerivZeroL_update_zero (j : ℕ) (m : Fin j → E) (i : Fin j) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j
        (Function.update m i 0) = 0 := by
  rw [iteratedLineDerivZeroL, iteratedLineDerivL_update_zero, ContinuousLinearMap.zero_comp]

/-- Order truncation commutes with `TauCeti.Wkp.iteratedLineDerivL`. -/
theorem toOrderL_iteratedLineDerivL {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (j : ℕ) (m : Fin j → E)
    (u : Wkp mu Omega p (k₂ + j)) :
    toOrderL h (iteratedLineDerivL k₂ j m u) =
      iteratedLineDerivL k₁ j m (toOrderL (Nat.add_le_add_right h j) u) :=
  ext k₁ ((value_toOrderL h _).trans
    (value_iteratedLineDerivL_eq_of_value_eq j m
      (value_toOrderL (Nat.add_le_add_right h j) u).symm))

/-- The `Lᵖ` value of `iteratedLineDerivL k j m u` agrees with
`iteratedLineDerivZeroL j m (toOrderL _ u)`. -/
theorem value_iteratedLineDerivL_eq_iteratedLineDerivZeroL (k j : ℕ) (m : Fin j → E)
    (u : Wkp mu Omega p (k + j)) :
    value k (iteratedLineDerivL k j m u) =
      iteratedLineDerivZeroL j m (toOrderL (Nat.le_add_left j k) u) := by
  rw [← toOrderL_zero_left_apply k (Nat.zero_le k), toOrderL_iteratedLineDerivL,
    iteratedLineDerivZeroL, ContinuousLinearMap.comp_apply, toOrderL_toOrderL]

/-- **Permutation invariance of `iteratedLineDerivL`.** Reordering the tuple of directions by any
permutation `σ : Equiv.Perm (Fin j)` leaves the operator unchanged. -/
@[simp]
theorem iteratedLineDerivL_comp_perm (k : ℕ) (j : ℕ) (m : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j (m ∘ σ) =
      iteratedLineDerivL k j m := by
  refine comp_perm_eq_of_cons_of_swap
    (fun i m' => iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k i m')
    (fun i v m₁ m₂ h => ?_) (fun i m' => ?_) j m σ
  · rw [iteratedLineDerivL_succ, iteratedLineDerivL_succ, Fin.cons_zero, Fin.cons_zero,
      Fin.tail_cons, Fin.tail_cons, h]
  · simp only [iteratedLineDerivL_succ, ContinuousLinearMap.comp_assoc,
      Fin.tail_tail_comp_swap_zero_one]
    simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.tail_def, Fin.succ_zero_eq_one,
      Equiv.swap_apply_right]
    congr 1
    exact lineDerivL_comp_lineDerivL_comm (m' 0) (m' 1) (k + i)

/-- **Permutation invariance of `iteratedLineDerivZeroL`.** -/
@[simp]
theorem iteratedLineDerivZeroL_comp_perm (j : ℕ) (m : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j (m ∘ σ) =
      iteratedLineDerivZeroL j m := by
  rw [iteratedLineDerivZeroL, iteratedLineDerivZeroL, iteratedLineDerivL_comp_perm]

end Sobolev

end Wkp

end TauCeti
