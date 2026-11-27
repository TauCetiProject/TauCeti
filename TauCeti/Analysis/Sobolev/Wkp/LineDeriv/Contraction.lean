/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Multilinear
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Iterated
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Contractions and all-order symmetry of iterated directional derivatives on `W^{k,p}`

At positive number of directions, `TauCeti.Wkp.iteratedLineDerivZeroL (j + 1) m u` agrees with
`(IteratedGradient.evalTupleL j (m ∘ Fin.rev)).compLp` applied to `iteratedGradient j u`
(`TauCeti.Wkp.iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp`), so every weak derivative field
`iteratedGradient j u` is symmetric almost everywhere as a continuous multilinear form
(`TauCeti.Wkp.domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae`), and every
directional evaluation `(D^{j+1} u)(m 0, …, m j)` of `u ∈ W^{k+j+1,p}(Ω)` is the value of an
element of `W^{k,p}(Ω)` (`TauCeti.Wkp.value_iteratedLineDerivL_eq_evalTupleL_compLp`).
Differentiating `i` times in a repeated direction `h` contracts the `i` outermost slots of
`iteratedGradient` at `h` (`TauCeti.Wkp.iteratedGradient_iteratedLineDerivL_const`).

No boundedness or boundary regularity of `Ω` is assumed.

## Main declarations

* `TauCeti.Wkp.iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp` and
  `TauCeti.Wkp.iteratedLineDerivZeroL_succ_ae`: identification of `iteratedLineDerivZeroL` with
  tuple evaluation of `Wkp.iteratedGradient`.
* `TauCeti.Wkp.value_iteratedLineDerivL_eq_evalTupleL_compLp`,
  `TauCeti.Wkp.value_iteratedLineDerivL_ae`, and
  `TauCeti.Wkp.value_iteratedLineDerivL_const`: identification of general-order iterated
  directional derivatives with tuple evaluations and full contractions of `Wkp.iteratedGradient`.
* `TauCeti.Wkp.iteratedGradient_iteratedLineDerivL` and
  `TauCeti.Wkp.iteratedGradient_iteratedLineDerivL_const`: arbitrary-tuple and repeated-direction
  outer-slot contraction of `Wkp.iteratedGradient`.
* `TauCeti.Wkp.domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae`: almost-everywhere
  full symmetry of weak derivatives of arbitrary order.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.2.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, §4.1.
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

/-! ### Contraction and multilinear evaluation of iterated derivatives -/

/-- **Iterated directional derivatives evaluate `iteratedGradient`.** Differentiating
`u ∈ W^{j+1,p}(Ω)` along `m : Fin (j + 1) → E` produces
`(IteratedGradient.evalTupleL j (m ∘ Fin.rev)).compLp` applied to `iteratedGradient j u`. -/
theorem iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp :
    ∀ (j : ℕ) (m : Fin (j + 1) → E) (u : Wkp mu Omega p (j + 1)),
      iteratedLineDerivZeroL (j + 1) m u =
        (IteratedGradient.evalTupleL j (m ∘ Fin.rev)).compLp (iteratedGradient j u)
  | 0, m, u => by
      rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply, iteratedLineDerivZeroL_zero,
        ContinuousLinearMap.id_apply, lineDerivL_zero_apply, IteratedGradient.evalTupleL_zero,
        Function.comp_apply, Fin.rev_zero, Fin.last_zero]
  | j + 1, m, u => by
      rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply,
        iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp j (Fin.tail m)
          (lineDerivL (m 0) (j + 1) u),
        iteratedGradient_lineDerivL, ContinuousLinearMap.compLp_compLp]
      congr 1
      ext G
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        ← IteratedGradient.evalTupleL_snoc_apply, ← Fin.cons_comp_rev, Fin.cons_self_tail]

/-- Almost-everywhere pointwise form of
`TauCeti.Wkp.iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp`. -/
theorem iteratedLineDerivZeroL_succ_ae (j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (j + 1)) :
    ∀ᵐ x ∂mu.restrict Omega,
      iteratedLineDerivZeroL (j + 1) m u x =
        IteratedGradient.evalTupleL j (m ∘ Fin.rev) (iteratedGradient j u x) := by
  rw [iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp]
  exact (IteratedGradient.evalTupleL j (m ∘ Fin.rev)).coeFn_compLp (iteratedGradient j u)

/-- `Lᵖ` bound for `(j + 1)`-fold directional derivatives in terms of the top seminorm. -/
theorem norm_iteratedLineDerivZeroL_succ_apply_le (j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (j + 1)) :
    ‖iteratedLineDerivZeroL (j + 1) m u‖ ≤ (∏ r, ‖m r‖) * ‖iteratedGradient j u‖ := by
  rw [iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp]
  refine ((IteratedGradient.evalTupleL j (m ∘ Fin.rev)).norm_compLp_le _).trans_eq ?_
  rw [IteratedGradient.norm_evalTupleL]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun r => ‖m r‖)

/-- **Multilinear evaluations of `D^{j+1} u` belong to `W^{k,p}(Ω)` when `u ∈ W^{k+j+1,p}(Ω)`.**
For `u ∈ W^{k+j+1,p}(Ω)`, `iteratedLineDerivL k (j + 1) m u ∈ W^{k,p}(Ω)` has `Lᵖ` value
`(IteratedGradient.evalTupleL j (m ∘ Fin.rev)).compLp (iteratedGradient j (toOrderL _ u))`. -/
theorem value_iteratedLineDerivL_eq_evalTupleL_compLp (k j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (k + (j + 1))) :
    value k (iteratedLineDerivL k (j + 1) m u) =
      (IteratedGradient.evalTupleL j (m ∘ Fin.rev)).compLp
        (iteratedGradient j (toOrderL (Nat.le_add_left (j + 1) k) u)) := by
  rw [value_iteratedLineDerivL_eq_iteratedLineDerivZeroL,
    iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp]

/-- Almost-everywhere pointwise form of
`TauCeti.Wkp.value_iteratedLineDerivL_eq_evalTupleL_compLp`. -/
theorem value_iteratedLineDerivL_ae (k j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (k + (j + 1))) :
    ∀ᵐ x ∂mu.restrict Omega,
      value k (iteratedLineDerivL k (j + 1) m u) x =
        IteratedGradient.evalTupleL j (m ∘ Fin.rev)
          (iteratedGradient j (toOrderL (Nat.le_add_left (j + 1) k) u) x) := by
  rw [value_iteratedLineDerivL_eq_evalTupleL_compLp]
  exact (IteratedGradient.evalTupleL j (m ∘ Fin.rev)).coeFn_compLp _

/-- Specializing `TauCeti.Wkp.value_iteratedLineDerivL_eq_evalTupleL_compLp` to a constant direction
tuple gives the scalar full contraction `TauCeti.IteratedGradient.fullContractL`. -/
theorem value_iteratedLineDerivL_const (k j : ℕ) (h : E) (u : Wkp mu Omega p (k + (j + 1))) :
    value k (iteratedLineDerivL k (j + 1) (fun _ => h) u) =
      (IteratedGradient.fullContractL j h).compLp
        (iteratedGradient j (toOrderL (Nat.le_add_left (j + 1) k) u)) := by
  rw [value_iteratedLineDerivL_eq_evalTupleL_compLp, Function.comp_def,
    IteratedGradient.evalTupleL_const]

/-! ### Outer-slot contractions of arbitrary and repeated directions -/

private theorem iteratedGradient_iteratedLineDerivL_of_value_eq (k : ℕ) :
    ∀ (i : ℕ) (m : Fin i → E)
      {u : Wkp mu Omega p (k + 1 + i)} {u' : Wkp mu Omega p (k + i + 1)},
      value (k + 1 + i) u = value (k + i + 1) u' →
      iteratedGradient k (iteratedLineDerivL (k + 1) i m u) =
        (IteratedGradient.applyL k i m).compLp (iteratedGradient (k + i) u')
  | 0, _, u, u', hu => by
      obtain rfl := ext (k + 1) hu
      dsimp only [Nat.add_zero]
      rw [iteratedLineDerivL_zero, ContinuousLinearMap.id_apply, IteratedGradient.applyL_zero,
        ContinuousLinearMap.id_compLp]
  | i + 1, m, u, u', hu => by
      have hd : value (k + 1 + i) (lineDerivL (m 0) (k + 1 + i) u) =
          value (k + i + 1) (lineDerivL (m 0) (k + i + 1) u') :=
        value_lineDerivL_eq_of_value_eq hu (m 0)
      -- By right-recursion of `Nat.add` (`Nat.add_succ`), `(k + 1) + (i + 1)` is definitionally
      -- `(k + 1 + i) + 1` and `k + (i + 1)` is definitionally `(k + i) + 1`, aligning the
      -- dependent `Wkp`/`IteratedGradient` indices across the rewrite chain.
      rw [iteratedLineDerivL_succ, ContinuousLinearMap.comp_apply,
        iteratedGradient_iteratedLineDerivL_of_value_eq k i (Fin.tail m) hd,
        iteratedGradient_lineDerivL, ContinuousLinearMap.compLp_compLp,
        ← IteratedGradient.applyL_succ k i m]
      -- The remaining goal aligns the dependent index `(k + i) + 1` with `k + (i + 1)` via
      -- `Nat.add_succ`.
      rfl

/-- Differentiating `i` times along `m : Fin i → E` evaluates the `i` outermost slots of
`iteratedGradient` at `m`. -/
theorem iteratedGradient_iteratedLineDerivL (k i : ℕ) (m : Fin i → E)
    (u : Wkp mu Omega p (k + 1 + i)) :
    iteratedGradient k (iteratedLineDerivL (k + 1) i m u) =
      (IteratedGradient.applyL k i m).compLp
        (iteratedGradient (k + i) (toOrderL (Nat.add_right_comm k i 1).le u)) :=
  iteratedGradient_iteratedLineDerivL_of_value_eq k i m
    (value_toOrderL (Nat.add_right_comm k i 1).le u).symm

/-- Differentiating `i` times in a repeated direction `h` contracts the `i` outermost slots of
`iteratedGradient` at `h`. -/
theorem iteratedGradient_iteratedLineDerivL_const (k : ℕ) (h : E) (i : ℕ)
    (u : Wkp mu Omega p (k + 1 + i)) :
    iteratedGradient k (iteratedLineDerivL (k + 1) i (fun _ => h) u) =
      (IteratedGradient.contractL k i h).compLp
        (iteratedGradient (k + i) (toOrderL (Nat.add_right_comm k i 1).le u)) := by
  rw [iteratedGradient_iteratedLineDerivL, IteratedGradient.applyL_const]

/-! ### Full symmetry of weak derivatives at arbitrary order -/

/-- Tuple evaluation of `iteratedGradient j u` in `Lᵖ(Ω)` is invariant under every
permutation of the `j + 1` directions. -/
theorem evalTupleL_compLp_iteratedGradient_comp_perm (j : ℕ) (u : Wkp mu Omega p (j + 1))
    (m : Fin (j + 1) → E) (σ : Equiv.Perm (Fin (j + 1))) :
    (IteratedGradient.evalTupleL j (m ∘ σ)).compLp (iteratedGradient j u) =
      (IteratedGradient.evalTupleL j m).compLp (iteratedGradient j u) := by
  have hm : m = (m ∘ Fin.rev) ∘ Fin.rev := funext fun i => by simp
  have hσ : (m ∘ σ) = ((m ∘ Fin.rev) ∘ ⇑(Fin.revPerm.trans (σ.trans Fin.revPerm))) ∘ Fin.rev :=
    funext fun i => by simp
  rw [hσ, ← iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp, iteratedLineDerivZeroL_comp_perm]
  conv_rhs => rw [hm, ← iteratedLineDerivZeroL_succ_eq_evalTupleL_compLp]

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
        IteratedGradient.evalTupleL j (fun i => b (r (σ i))) (iteratedGradient j u x) =
          IteratedGradient.evalTupleL j (fun k => b (r k)) (iteratedGradient j u x) := by
    have heq := evalTupleL_compLp_iteratedGradient_comp_perm j u (fun k => b (r k)) σ
    rw [Function.comp_def] at heq
    filter_upwards [(IteratedGradient.evalTupleL j (fun i => b (r (σ i)))).coeFn_compLp
      (iteratedGradient j u),
      (IteratedGradient.evalTupleL j (fun k => b (r k))).coeFn_compLp (iteratedGradient j u)]
      with x hx₁ hx₂
    rw [← hx₁, ← hx₂, heq]
  filter_upwards [ae_all_iff.2 fun σ => ae_all_iff.2 fun r => hbasis σ r] with x hx σ
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ => b.toBasis) fun r => ?_)
  simpa [ContinuousMultilinearMap.domDomCongr_apply,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_apply, Function.comp_def] using
    hx (Fin.revPerm.trans (σ.trans Fin.revPerm)) (r ∘ Fin.rev)

end Sobolev

end Wkp

end TauCeti
