/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
public import TauCeti.Analysis.Complex.MDeriv.Basic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.GroupTheory.Perm.FiberSubgroup

/-!
# Mixed partial derivatives and multi-index Taylor coefficients

For an entire function `f : (Fin n → ℂ) → ℂ`, the mixed partial derivative `TauCeti.mDeriv σ f z`
equals the iterated Fréchet derivative of total order `∑ i, σ i` evaluated on any tuple of standard
basis vectors matching the multiplicities `σ` (`TauCeti.mDeriv_eq_iteratedFDeriv`), and hence
equals `(∏ i, (σ i)!) • TauCeti.mvTaylorCoeff f z σ`
(`TauCeti.mDeriv_eq_prod_factorial_smul_mvTaylorCoeff`).

## Main results

* `TauCeti.mDeriv_eq_iteratedFDeriv`: agreement of `mDeriv σ f z` with `iteratedFDeriv` on a tuple
  of coordinate basis vectors.
* `TauCeti.mDeriv_eq_prod_factorial_smul_mvTaylorCoeff`:
  `mDeriv σ f z = (∏ i, (σ i)!) • mvTaylorCoeff f z σ`.
-/

public section

open Finset Function

namespace TauCeti

private theorem mDeriv_eq_iteratedFDeriv_aux {n : ℕ} (k : ℕ) :
    ∀ {f : (Fin n → ℂ) → ℂ} (_hf : Differentiable ℂ f) {σ : Fin n → ℕ}
      (_hsum : ∑ i, σ i = k) (v : Fin k → Fin n)
      (_hv : ∀ i, (univ.filter fun j ↦ v j = i).card = σ i) (z : Fin n → ℂ),
      mDeriv σ f z = iteratedFDeriv ℂ k f z fun j ↦ Pi.single (v j) 1 := by
  induction k with
  | zero =>
    intro f _ σ hsum _ _ z
    have hσ : σ = 0 := funext fun i ↦ sum_eq_zero_iff.mp hsum i (mem_univ i)
    simp [hσ]
  | succ k ih =>
    intro f hf σ _hsum v hv z
    let i : Fin n := v (Fin.last k)
    let v' : Fin k → Fin n := Fin.init v
    let σ' : Fin n → ℕ := fun a ↦ (univ.filter fun j : Fin k ↦ v' j = a).card
    have hv' : ∀ a, (univ.filter fun j ↦ v' j = a).card = σ' a := fun _ ↦ rfl
    have hsum' : ∑ a, σ' a = k := by
      simp only [σ']
      rw [← Finset.card_eq_sum_card_fiberwise (f := v') fun j _ ↦ mem_univ (v' j),
        Finset.card_univ, Fintype.card_fin]
    have hσ_eq : σ = σ' + Pi.single i 1 := by
      ext a
      rw [Pi.add_apply, ← hv a, card_filter, Fin.sum_univ_castSucc, ← card_filter]
      simp only [v', Fin.init, σ', i, Pi.single_apply]
      by_cases h : v (Fin.last k) = a <;> simp [h, Ne.symm]
    rw [hσ_eq, ← mDeriv_mDeriv hf, mDeriv_single, Function.iterate_one,
      ih (differentiable_partialDeriv hf i) hsum' v' hv' z]
    let L : ((Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)
    have hL : partialDeriv i f = L ∘ fderiv ℂ f := by
      ext y
      simp [L, partialDeriv_apply]
    have hcd : ContDiffAt ℂ ⊤ (fderiv ℂ f) z :=
      ((hf.contDiff_of_finiteDimensional (n := ⊤)).fderiv_right le_top).contDiffAt
    rw [hL, L.iteratedFDeriv_comp_left hcd (le_top : (k : WithTop ℕ∞) ≤ ⊤),
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.apply_apply, iteratedFDeriv_succ_apply_right]
    rfl

/-- For an entire function `f : (Fin n → ℂ) → ℂ` and any tuple `v` of coordinate indices in which
each `i` appears `σ i` times, `mDeriv σ f z` equals `iteratedFDeriv ℂ (∑ i, σ i) f z` evaluated
on `j ↦ Pi.single (v j) 1`. -/
theorem mDeriv_eq_iteratedFDeriv {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (σ : Fin n → ℕ) (v : Fin (∑ i, σ i) → Fin n)
    (hv : ∀ i, (univ.filter fun j ↦ v j = i).card = σ i) (z : Fin n → ℂ) :
    mDeriv σ f z = iteratedFDeriv ℂ (∑ i, σ i) f z fun j ↦ Pi.single (v j) 1 :=
  mDeriv_eq_iteratedFDeriv_aux (∑ i, σ i) hf rfl v hv z

/-- **Mixed partial derivatives and multi-index Taylor coefficients.** For an entire function
`f : (Fin n → ℂ) → ℂ`, `mDeriv σ f z = (∏ i, (σ i)!) • mvTaylorCoeff f z σ`. -/
theorem mDeriv_eq_prod_factorial_smul_mvTaylorCoeff {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (σ : Fin n → ℕ) (z : Fin n → ℂ) :
    mDeriv σ f z = (∏ i, (σ i).factorial) • mvTaylorCoeff f z σ := by
  obtain ⟨v, hv⟩ :=
    exists_forall_card_filter_eq (α := Fin (∑ i, σ i)) (Fintype.card_fin _).symm
  have han : AnalyticAt ℂ f z :=
    hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem
  rw [mDeriv_eq_iteratedFDeriv hf σ v hv z, han.prod_factorial_smul_mvTaylorCoeff σ v hv]

end TauCeti
