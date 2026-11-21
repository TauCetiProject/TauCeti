/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Multilinear
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Data.Fin.Tuple.Perm
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Iterated directional derivatives, contractions, and all-order symmetry on `W^{k,p}`

Iterating `TauCeti.Wkp.lineDerivL` along a tuple `m : Fin j → E` defines
`TauCeti.Wkp.iteratedLineDerivL` and its order-zero specialisation
`TauCeti.Wkp.iteratedLineDerivZeroL`. Both are multilinear in each direction slot and invariant
under every permutation of the direction tuple (`TauCeti.Wkp.iteratedLineDerivL_comp_perm`,
`TauCeti.Wkp.iteratedLineDerivZeroL_comp_perm`).

At positive number of directions, `iteratedLineDerivZeroL (j + 1) m u` agrees with
`(IteratedGradient.evalL j m).compLp` applied to `iteratedGradient j u`
(`TauCeti.Wkp.iteratedLineDerivZeroL_succ_apply`), so every weak derivative field
`iteratedGradient j u` is symmetric almost everywhere as a continuous multilinear form
(`TauCeti.Wkp.domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae`), and every
directional evaluation `(D^{j+1} u)(m 0, …, m j)` of `u ∈ W^{k+j+1,p}(Ω)` is the value of an
element of `W^{k,p}(Ω)` (`TauCeti.Wkp.value_iteratedLineDerivL_eq_evalL_compLp`). Differentiating
`i` times in a repeated direction `h` contracts the `i` outermost slots of `iteratedGradient` at
`h` (`TauCeti.Wkp.iteratedGradient_iteratedLineDerivL_const`).

No boundedness or boundary regularity of `Ω` is assumed.

## Main declarations

* `TauCeti.Wkp.iteratedLineDerivL` and `TauCeti.Wkp.iteratedLineDerivZeroL`: iterated bundled
  directional derivatives along a tuple `Fin j → E`.
* `TauCeti.Wkp.iteratedLineDerivL_comp_perm`: permutation invariance of iterated directional
  derivatives.
* `TauCeti.Wkp.iteratedLineDerivZeroL_succ_apply` and
  `TauCeti.Wkp.value_iteratedLineDerivL_eq_evalL_compLp`: identification of iterated directional
  derivatives with multilinear evaluations of `Wkp.iteratedGradient`.
* `TauCeti.Wkp.iteratedGradient_iteratedLineDerivL_const`: repeated-direction differentiation
  contracts the outer slots of `Wkp.iteratedGradient`.
* `TauCeti.Wkp.domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae`: almost-everywhere
  full symmetry of weak derivatives of arbitrary order.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.2.
* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, §4.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace Wkp

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Iterated directional derivatives and all-order symmetry -/

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
          have htail (v : E) : Fin.tail (Function.update m 0 v) = Fin.tail m :=
            funext fun r => Function.update_of_ne (Fin.succ_ne_zero r) v m
          simp only [iteratedLineDerivL_succ, Function.update_self, htail, lineDerivL_add_left,
            ContinuousLinearMap.comp_add]
      | succ i =>
          have htail (v : E) :
              Fin.tail (Function.update m i.succ v) = Function.update (Fin.tail m) i v :=
            funext fun r => by simp [Fin.tail, Function.update_apply]
          simp only [iteratedLineDerivL_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm,
            htail, iteratedLineDerivL_update_add k j (Fin.tail m) i v₁ v₂,
            ContinuousLinearMap.add_comp]

/-- Updating slot `i` of the direction tuple with `c • v` scales `iteratedLineDerivL` by `c`. -/
theorem iteratedLineDerivL_update_smul (k : ℕ) :
    ∀ (j : ℕ) (m : Fin j → E) (i : Fin j) (c : ℝ) (v : E),
      iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j
          (Function.update m i (c • v)) =
        c • iteratedLineDerivL k j (Function.update m i v)
  | 0, _, i, _, _ => i.elim0
  | j + 1, m, i, c, v => by
      cases i using Fin.cases with
      | zero =>
          have htail (w : E) : Fin.tail (Function.update m 0 w) = Fin.tail m :=
            funext fun r => Function.update_of_ne (Fin.succ_ne_zero r) w m
          simp only [iteratedLineDerivL_succ, Function.update_self, htail, lineDerivL_smul_left,
            ContinuousLinearMap.comp_smul]
      | succ i =>
          have htail (w : E) :
              Fin.tail (Function.update m i.succ w) = Function.update (Fin.tail m) i w :=
            funext fun r => by simp [Fin.tail, Function.update_apply]
          simp only [iteratedLineDerivL_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm,
            htail, iteratedLineDerivL_update_smul k j (Fin.tail m) i c v,
            ContinuousLinearMap.smul_comp]

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
theorem iteratedLineDerivZeroL_update_add (j : ℕ) (m : Fin j → E) (i : Fin j) (v₁ v₂ : E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j
        (Function.update m i (v₁ + v₂)) =
      iteratedLineDerivZeroL j (Function.update m i v₁) +
        iteratedLineDerivZeroL j (Function.update m i v₂) := by
  simp only [iteratedLineDerivZeroL, iteratedLineDerivL_update_add, ContinuousLinearMap.add_comp]

/-- Updating slot `i` of the direction tuple with `c • v` scales `iteratedLineDerivZeroL` by
`c`. -/
theorem iteratedLineDerivZeroL_update_smul (j : ℕ) (m : Fin j → E) (i : Fin j) (c : ℝ) (v : E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j
        (Function.update m i (c • v)) =
      c • iteratedLineDerivZeroL j (Function.update m i v) := by
  simp only [iteratedLineDerivZeroL, iteratedLineDerivL_update_smul, ContinuousLinearMap.smul_comp]

/-- The `Lᵖ` value of `iteratedLineDerivL k j m u` agrees with
`iteratedLineDerivZeroL j m (toOrderL _ u)`. -/
theorem value_iteratedLineDerivL_eq_iteratedLineDerivZeroL (k j : ℕ) (m : Fin j → E)
    (u : Wkp mu Omega p (k + j)) :
    value k (iteratedLineDerivL k j m u) =
      iteratedLineDerivZeroL j m (toOrderL (Nat.le_add_left j k) u) := by
  rw [iteratedLineDerivZeroL, ContinuousLinearMap.comp_apply,
    ← value_zero (iteratedLineDerivL 0 j m _)]
  exact value_iteratedLineDerivL_eq_of_value_eq j m
    ((value_toOrderL (Nat.le_add_left j k) u).symm.trans
      (value_toOrderL (Nat.zero_add j).le _).symm)

/-- **Permutation invariance of `iteratedLineDerivL`.** Reordering the tuple of directions by any
permutation `σ : Equiv.Perm (Fin j)` leaves the operator unchanged. -/
theorem iteratedLineDerivL_comp_perm (k : ℕ) (j : ℕ) (m : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j (m ∘ σ) =
      iteratedLineDerivL k j m := by
  refine Fin.comp_perm_eq_of_cons_of_swap
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
theorem iteratedLineDerivZeroL_comp_perm (j : ℕ) (m : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j (m ∘ σ) =
      iteratedLineDerivZeroL j m := by
  rw [iteratedLineDerivZeroL, iteratedLineDerivZeroL, iteratedLineDerivL_comp_perm]

/-- **Iterated directional derivatives evaluate `iteratedGradient`.** Differentiating
`u ∈ W^{j+1,p}(Ω)` along `m : Fin (j + 1) → E` produces `(IteratedGradient.evalL j m).compLp`
applied to `iteratedGradient j u`. -/
theorem iteratedLineDerivZeroL_succ_apply :
    ∀ (j : ℕ) (m : Fin (j + 1) → E) (u : Wkp mu Omega p (j + 1)),
      iteratedLineDerivZeroL (j + 1) m u =
        (IteratedGradient.evalL j m).compLp (iteratedGradient j u)
  | 0, m, u => by
      rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply, iteratedLineDerivZeroL_zero,
        ContinuousLinearMap.id_apply, lineDerivL_zero_apply, IteratedGradient.evalL_zero]
  | j + 1, m, u => by
      rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply,
        iteratedLineDerivZeroL_succ_apply j (Fin.tail m) (lineDerivL (m 0) (j + 1) u),
        iteratedGradient_lineDerivL, ← IteratedGradient.contractL_one,
        ContinuousLinearMap.compLp_compLp, IteratedGradient.evalL_comp_contractL_one,
        Fin.cons_self_tail]

/-- `Lᵖ` bound for `(j + 1)`-fold directional derivatives in terms of the top seminorm. -/
theorem norm_iteratedLineDerivZeroL_succ_apply_le (j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (j + 1)) :
    ‖iteratedLineDerivZeroL (j + 1) m u‖ ≤ (∏ r, ‖m r‖) * ‖iteratedGradient j u‖ := by
  rw [iteratedLineDerivZeroL_succ_apply]
  exact ((IteratedGradient.evalL j m).norm_compLp_le _).trans
    (mul_le_mul_of_nonneg_right (IteratedGradient.norm_evalL_le j m) (norm_nonneg _))

/-- **Multilinear evaluations of `D^{j+1} u` belong to `W^{k,p}(Ω)` when `u ∈ W^{k+j+1,p}(Ω)`.**
For `u ∈ W^{k+j+1,p}(Ω)`, `iteratedLineDerivL k (j + 1) m u ∈ W^{k,p}(Ω)` has `Lᵖ` value
`(IteratedGradient.evalL j m).compLp (iteratedGradient j (toOrderL _ u))`. -/
theorem value_iteratedLineDerivL_eq_evalL_compLp (k j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (k + (j + 1))) :
    value k (iteratedLineDerivL k (j + 1) m u) =
      (IteratedGradient.evalL j m).compLp
        (iteratedGradient j (toOrderL (Nat.le_add_left (j + 1) k) u)) := by
  rw [value_iteratedLineDerivL_eq_iteratedLineDerivZeroL, iteratedLineDerivZeroL_succ_apply]

/-! ### Repeated-direction contractions -/

private theorem iteratedGradient_iteratedLineDerivL_const_of_value_eq (k : ℕ) (h : E) :
    ∀ (i : ℕ) {u : Wkp mu Omega p (k + 1 + i)} {u' : Wkp mu Omega p (k + i + 1)},
      value (k + 1 + i) u = value (k + i + 1) u' →
      iteratedGradient k (iteratedLineDerivL (k + 1) i (fun _ => h) u) =
        (IteratedGradient.contractL k i h).compLp (iteratedGradient (k + i) u')
  | 0, u, u', hu => by
      obtain rfl := ext (k + 1) hu
      dsimp only [Nat.add_zero]
      rw [iteratedLineDerivL_zero, ContinuousLinearMap.id_apply, IteratedGradient.contractL_zero,
        ContinuousLinearMap.id_compLp]
  | i + 1, u, u', hu => by
      have hd : value (k + 1 + i) (lineDerivL h (k + 1 + i) u) =
          value (k + i + 1) (lineDerivL h (k + i + 1) u') :=
        value_lineDerivL_eq_of_value_eq hu h
      -- By right-recursion of `Nat.add` (`Nat.add_succ`), `(k + 1) + (i + 1)` is definitionally
      -- `(k + 1 + i) + 1` and `k + (i + 1)` is definitionally `(k + i) + 1`, aligning the
      -- dependent `Wkp`/`IteratedGradient` indices across the rewrite chain.
      rw [iteratedLineDerivL_succ, ContinuousLinearMap.comp_apply, Fin.tail_def,
        iteratedGradient_iteratedLineDerivL_const_of_value_eq k h i hd,
        iteratedGradient_lineDerivL, ← IteratedGradient.contractL_one,
        ContinuousLinearMap.compLp_compLp, IteratedGradient.contractL_one,
        ← IteratedGradient.contractL_succ k i h]
      -- The remaining goal aligns the dependent index `(k + i) + 1` with `k + (i + 1)` via
      -- `Nat.add_succ`.
      rfl

/-- Differentiating `i` times in a repeated direction `h` contracts the `i` outermost slots of
`iteratedGradient` at `h`. -/
theorem iteratedGradient_iteratedLineDerivL_const (k : ℕ) (h : E) (i : ℕ)
    (u : Wkp mu Omega p (k + 1 + i)) :
    iteratedGradient k (iteratedLineDerivL (k + 1) i (fun _ => h) u) =
      (IteratedGradient.contractL k i h).compLp
        (iteratedGradient (k + i) (toOrderL (Nat.add_right_comm k i 1).le u)) :=
  iteratedGradient_iteratedLineDerivL_const_of_value_eq k h i
    (value_toOrderL (Nat.add_right_comm k i 1).le u).symm

/-! ### Full symmetry of weak derivatives at arbitrary order -/

/-- Multilinear evaluation of `iteratedGradient j u` in `Lᵖ(Ω)` is invariant under every
permutation of the `j + 1` directions. -/
theorem evalL_compLp_iteratedGradient_comp_perm (j : ℕ) (u : Wkp mu Omega p (j + 1))
    (m : Fin (j + 1) → E) (σ : Equiv.Perm (Fin (j + 1))) :
    (IteratedGradient.evalL j (m ∘ σ)).compLp (iteratedGradient j u) =
      (IteratedGradient.evalL j m).compLp (iteratedGradient j u) := by
  rw [← iteratedLineDerivZeroL_succ_apply, ← iteratedLineDerivZeroL_succ_apply,
    iteratedLineDerivZeroL_comp_perm]

/-- **Weak derivatives of arbitrary order are symmetric almost everywhere.** For every
`u ∈ W^{j+1,p}(Ω)`, at almost every `x ∈ Ω` and for every permutation
`σ : Equiv.Perm (Fin (j + 1))`, the scalar continuous multilinear map attached to
`iteratedGradient j u x` is invariant under `domDomCongr σ`. -/
theorem domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae (j : ℕ)
    (u : Wkp mu Omega p (j + 1)) :
    ∀ᵐ x ∂mu.restrict Omega, ∀ σ : Equiv.Perm (Fin (j + 1)),
      (IteratedGradient.toContinuousMultilinearMapₗᵢ E j
        (iteratedGradient j u x)).domDomCongr σ =
        IteratedGradient.toContinuousMultilinearMapₗᵢ E j (iteratedGradient j u x) := by
  let b := stdOrthonormalBasis ℝ E
  have hbasis (σ : Equiv.Perm (Fin (j + 1))) (r : Fin (j + 1) → Fin (Module.finrank ℝ E)) :
      ∀ᵐ x ∂mu.restrict Omega,
        IteratedGradient.evalL j (fun i => b (r (σ i))) (iteratedGradient j u x) =
          IteratedGradient.evalL j (fun k => b (r k)) (iteratedGradient j u x) := by
    have heq := evalL_compLp_iteratedGradient_comp_perm j u (fun k => b (r k)) σ
    rw [Function.comp_def] at heq
    filter_upwards [(IteratedGradient.evalL j (fun i => b (r (σ i)))).coeFn_compLp
      (iteratedGradient j u),
      (IteratedGradient.evalL j (fun k => b (r k))).coeFn_compLp (iteratedGradient j u)]
      with x hx₁ hx₂
    rw [← hx₁, ← hx₂, heq]
  filter_upwards [ae_all_iff.2 fun σ => ae_all_iff.2 fun r => hbasis σ r] with x hx σ
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ => b.toBasis) fun r => ?_)
  simpa [ContinuousMultilinearMap.domDomCongr_apply,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_apply] using hx σ r

end Sobolev

end Wkp

end TauCeti
