/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Leibniz
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# The Leibniz rule for the weak gradient and the weak Hessian

Let `ζ` be a smooth function on a finite-dimensional real inner product space. This file computes
the recorded weak derivatives of any Sobolev function whose value is `ζ u`:

* if `u, w ∈ W^{1,p}(Ω)` and `w = ζ u` almost everywhere on `Ω`, then
  `∇w = ζ ∇u + u ∇ζ` (`TauCeti.Wkp.iteratedGradient_zero_ae_eq_of_value_ae_eq_mul`);
* if `u, w ∈ W^{2,p}(Ω)` and `w = ζ u` almost everywhere on `Ω`, then the weak Hessian is

  `D²w = ζ D²u + ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`

  (`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`), where `D²w` is
  `TauCeti.Wkp.iteratedGradient 1 w`, a field of endomorphisms of `E`, and `a ⊗ b` denotes the
  rank-one map `v ↦ ⟪a, v⟫ b`. The remainder `∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` is at most
  `2 ‖∇ζ‖ ‖∇u‖ + ‖D²ζ‖ |u|` pointwise in operator norm (`TauCeti.norm_leibnizRemainder_le`).

Nothing is assumed about `ζ` beyond smoothness, nor about `Ω` beyond openness: the formulas follow
from uniqueness of weak derivatives, so they hold for every `w` with value `ζ u`, however it was
produced. When `ζ` has compact support in `Ω` and `p < ∞`, such a `w` exists in `W^{k,p}_0(Ω)` by
`TauCeti.Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul`.

Such a `w` also exists in `W^{k,p}(Ω)` whenever `ζ` is smooth on an open set containing the
compact set `closure Ω` (`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn`), for every
`1 ≤ p ≤ ∞`. The factor need not be smooth away from `closure Ω`: this is the
form in which the derivatives of a coefficient field smooth on a larger domain act on Sobolev
functions on a compactly contained subdomain.

The Hessian formula is what localizes a second-order estimate. Writing `L = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ`, it
gives `L(ζ u) = ζ L u + (terms in ∇u and u)`, so an estimate for compactly supported functions,
applied to `ζ u`, controls `ζ D²u` by `ζ L u` and lower-order norms of `u`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1(iv).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  proof of Theorem 9.11.
-/

public section

namespace TauCeti

open scoped Gradient

section LeibnizRemainder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Leibniz remainder `∇ζ ⊗ v + v ⊗ ∇ζ + s D²ζ` of the weak Hessian of `ζ u`
(`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`, with `v = ∇u` and `s = u`) is at
most `2 ‖∇ζ‖ ‖v‖ + ‖D²ζ‖ |s|` in operator norm. -/
theorem norm_leibnizRemainder_le (zeta : E → ℝ) (v : E) (s : ℝ) (x : E) :
    ‖(innerSL ℝ (∇ zeta x)).smulRight v + (innerSL ℝ v).smulRight (∇ zeta x)
        + s • fderiv ℝ (∇ zeta) x‖ ≤
      2 * ‖∇ zeta x‖ * ‖v‖ + ‖fderiv ℝ (∇ zeta) x‖ * ‖s‖ := by
  refine norm_add₃_le.trans (le_of_eq ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, innerSL_apply_norm, norm_smul]
  ring

end LeibnizRemainder

namespace Wkp

open MeasureTheory TopologicalSpace
open scoped Gradient ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {zeta : E → ℝ}

/-- **The Leibniz rule for the weak gradient.** If `u, w ∈ W^{1,p}(Ω)` and `w = ζ u` almost
everywhere on `Ω` for a smooth `ζ`, then `∇w = ζ ∇u + u ∇ζ` almost everywhere on `Ω`. -/
theorem iteratedGradient_zero_ae_eq_of_value_ae_eq_mul (hzeta : ContDiff ℝ ∞ zeta)
    {u w : Wkp mu Omega p 1}
    (hw : (value 1 w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => zeta x * value 1 u x) :
    (iteratedGradient 0 w : E → E) =ᵐ[mu.restrict Omega]
      fun x => zeta x • iteratedGradient 0 u x + value 1 u x • ∇ zeta x := by
  have h := ((hasWeakFDerivOn_value u).contDiff_smul_gradient hzeta).congr_ae
    (w := (value 1 w : E → ℝ)) (hw.mono fun x hx => by simp only [hx, smul_eq_mul])
  filter_upwards [(hasWeakFDerivOn_value w).ae_eq h] with x hx
  exact innerSL_inj.1 hx

/-- **The Leibniz rule for the weak Hessian.** If `u, w ∈ W^{2,p}(Ω)` and `w = ζ u` almost
everywhere on `Ω` for a smooth `ζ`, then almost everywhere on `Ω`

`D²w = ζ D²u + ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`,

where `D²` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1`, `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`, and `a ⊗ b` is the rank-one map
`v ↦ ⟪a, v⟫ b`. -/
theorem iteratedGradient_one_ae_eq_of_value_ae_eq_mul (hzeta : ContDiff ℝ ∞ zeta)
    {u w : Wkp mu Omega p 2}
    (hw : (value 2 w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => zeta x * value 2 u x) :
    (iteratedGradient 1 w : E → E →L[ℝ] E) =ᵐ[mu.restrict Omega] fun x =>
      zeta x • iteratedGradient 1 u x
        + (innerSL ℝ (∇ zeta x)).smulRight (iteratedGradient 0 (lowerOrder 1 u) x)
        + (innerSL ℝ (iteratedGradient 0 (lowerOrder 1 u) x)).smulRight (∇ zeta x)
        + value 2 u x • fderiv ℝ (∇ zeta) x := by
  -- The weak gradient of `w` is `ζ ∇u + u ∇ζ`, by the first-order rule.
  have hgrad := iteratedGradient_zero_ae_eq_of_value_ae_eq_mul (u := lowerOrder 1 u)
    (w := lowerOrder 1 w) hzeta (by simpa only [value_succ] using hw)
  -- Differentiate the two summands by the two forms of the Leibniz rule.
  have h₁ := (hasWeakFDerivOn_iteratedGradient 0 u).contDiff_smul hzeta
  have h₂ := (hasWeakFDerivOn_value (lowerOrder 1 u)).smul_contDiff
    (hzeta.gradient_right (m := ∞) (by simp))
  have h := (h₁.add h₂).congr_ae hgrad.symm
  have hfd : ∀ x, fderiv ℝ zeta x = innerSL ℝ (∇ zeta x) := fun _ => toDual_gradient.symm
  filter_upwards [(hasWeakFDerivOn_iteratedGradient 0 w).ae_eq h] with x hx
  simp only [hx, Pi.add_apply, value_succ, hfd]
  abel

/-- **Smooth multiplication in `W^{k,p}`.** Let `Ω` have compact closure inside an open set `U`.
If `ψ` is smooth on `U` and `u ∈ W^{k,p}(Ω)`, then `ψ u` lies in `W^{k,p}(Ω)`: some element of
`W^{k,p}(Ω)` has value `ψ u` almost everywhere on `Ω`.

No bound on `ψ` or its derivatives is assumed: they are bounded on the compact set `closure Ω`,
which is all the proof uses. -/
theorem exists_value_ae_eq_mul_of_contDiffOn {U : Set E} (hU : IsOpen U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    {psi : E → ℝ} (hpsi : ContDiffOn ℝ ∞ psi U) (u : Wkp mu Omega p k) :
    ∃ w : Wkp mu Omega p k, (value k w : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x := by
  -- A function continuous on `U` is bounded on `Ω`, so multiplying by it preserves `Lᵖ(Ω)`.
  have hLp : ∀ {phi : E → ℝ}, ContinuousOn phi U → ∀ f : Lp ℝ p (mu.restrict Omega),
      ∃ g : Lp ℝ p (mu.restrict Omega), (g : E → ℝ) =ᵐ[mu.restrict Omega]
        fun x => phi x * f x := fun {phi} hphi f => by
    have h : MemLp (fun x => phi x * f x) p (mu.restrict Omega) :=
      ((hphi.mono hΩU).memLp_top_restrict_of_subset_isCompact hΩ Omega.isOpen.measurableSet
        subset_closure).fun_mul (Lp.memLp f)
    exact ⟨h.toLp _, h.coeFn_toLp⟩
  induction k generalizing psi with
  | zero => simpa only [value_zero] using hLp hpsi.continuousOn (value 0 u)
  | succ k ih =>
    obtain ⟨g, hg⟩ := hLp hpsi.continuousOn (value (k + 1) u)
    set b := stdOrthonormalBasis ℝ E
    refine (exists_value_eq_of_forall_hasWeakLineDerivOn b g k fun i => ?_).imp
      fun w (hw : value (k + 1) w = g) => hw ▸ hg
    -- `∂ᵢ(ψ u) = ψ ∂ᵢu + (∂ᵢψ) u`, and both summands lie in `W^{k,p}(Ω)` by induction.
    obtain ⟨d, hd⟩ := exists_hasWeakLineDerivOn_value k u (b i)
    obtain ⟨w₁, hw₁⟩ := ih hpsi d
    obtain ⟨w₂, hw₂⟩ := ih ((hpsi.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)
      (lowerOrder k u)
    refine ⟨w₁ + w₂, (((hd.contDiffOn_smul (hpsi.mono (subset_closure.trans hΩU))).congr_ae
      ?_).congr_ae_deriv ?_)⟩
    · filter_upwards [hg] with x hx
      rw [hx, smul_eq_mul]
    · filter_upwards [value_add k w₁ w₂ ▸ Lp.coeFn_add (value k w₁) (value k w₂), hw₁, hw₂]
        with x hx h₁ h₂
      rw [hx, Pi.add_apply, h₁, h₂, ← value_succ, smul_eq_mul, smul_eq_mul]

end Wkp

end TauCeti
