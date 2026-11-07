/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Leibniz
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.Lp.Norm
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
  `2 ‖∇ζ‖ ‖∇u‖ + ‖D²ζ‖ |u|` pointwise in operator norm (`TauCeti.norm_leibnizRemainder_le`), and it
  vanishes off the support of `ζ` (`TauCeti.leibnizRemainder_eq_zero_of_notMem_tsupport`).
* consequently `‖D²w - ζ D²u‖ ≤ 2 c₁ ‖∇u‖ + c₂ ‖u‖` for `‖∇ζ‖ ≤ c₁`, `‖D²ζ‖ ≤ c₂`
  (`TauCeti.Wkp.norm_iteratedGradient_one_sub_toLp_le_of_value_ae_eq_mul`), and for a cutoff `ζ`
  with `|ζ| ≤ 1`, `‖D²w‖ ≤ ‖D²u‖ + 2 c₁ ‖∇u‖ + c₂ ‖u‖`
  (`TauCeti.Wkp.norm_iteratedGradient_one_le_of_value_ae_eq_mul`).

Nothing is assumed about `ζ` beyond smoothness, nor about `Ω` beyond openness: the formulas follow
from uniqueness of weak derivatives, so they hold for every `w` with value `ζ u`, however it was
produced. When `ζ` has compact support in `Ω` and `p < ∞`, such a `w` exists in `W^{k,p}_0(Ω)` by
`TauCeti.Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul`.

Such a `w` also exists in `W^{k,p}(Ω)` whenever `ζ` is smooth on an open set containing the
compact set `closure Ω` (`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn`), for every
`1 ≤ p ≤ ∞`. The factor need not be smooth away from `closure Ω`: this is the
form in which the derivatives of a coefficient field smooth on a larger domain act on Sobolev
functions on a compactly contained subdomain. On an arbitrary open `Ω`, such a `w` exists in
`W^{k,p}(Ω)` whenever `ζ` has compact support
(`TauCeti.Wkp.exists_value_ae_eq_mul_of_hasCompactSupport`); the support may meet `∂Ω`, which is
the situation of a cutoff near a boundary point.

The Hessian formula is what localizes a second-order estimate. Writing `L = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ`, it
gives `L(ζ u) = ζ L u + (terms in ∇u and u)`, so an estimate for compactly supported functions,
applied to `ζ u`, controls `ζ D²u` by `ζ L u` and lower-order norms of `u`. In that form, for `ζ`
compactly supported with `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`, the remainder is an element `T` of `Lᵖ`
vanishing off the support of `ζ` with `‖T‖ ≤ 2 M₁ ‖∇u‖ + M₂ ‖u‖`
(`TauCeti.Wkp.exists_iteratedGradient_one_ae_eq_smul_add_of_value_ae_eq_mul`).

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

/-- The Leibniz remainder `∇ζ ⊗ v + v ⊗ ∇ζ + s D²ζ` vanishes off the support of `ζ`. -/
theorem leibnizRemainder_eq_zero_of_notMem_tsupport {zeta : E → ℝ} {x : E}
    (hx : x ∉ tsupport zeta) (v : E) (s : ℝ) :
    (innerSL ℝ (∇ zeta x)).smulRight v + (innerSL ℝ v).smulRight (∇ zeta x)
      + s • fderiv ℝ (∇ zeta) x = 0 := by
  have hs0 := tsupport_iteratedGradientChain_subset zeta 0
  have hs1 := tsupport_iteratedGradientChain_subset zeta 1
  rw [iteratedGradientChain_zero] at hs0
  rw [iteratedGradientChain_succ, iteratedGradientChain_zero] at hs1
  have h1 : ∇ zeta x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs0 h)
  have h2 : fderiv ℝ (∇ zeta) x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs1 h)
  simp [h1, h2]

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

/-- **The weak Hessian of a product, minus the principal part.** If `u, w ∈ W^{2,p}(Ω)` and
`w = ζ u` almost everywhere on `Ω` for a smooth `ζ` with `‖∇ζ‖ ≤ c₁` and `‖D²ζ‖ ≤ c₂`, and
`ζ D²u ∈ Lᵖ(Ω)`, then

`‖D²w - ζ D²u‖ ≤ 2 c₁ ‖∇u‖ + c₂ ‖u‖`. -/
theorem norm_iteratedGradient_one_sub_toLp_le_of_value_ae_eq_mul {u w : Wkp mu Omega p 2}
    {c₁ c₂ : ℝ} (hzeta : ContDiff ℝ ∞ zeta) (hg : ∀ x, ‖∇ zeta x‖ ≤ c₁)
    (hh : ∀ x, ‖fderiv ℝ (∇ zeta) x‖ ≤ c₂)
    (hzu : MemLp (fun x => zeta x • iteratedGradient 1 u x) p (mu.restrict Omega))
    (hw : (value 2 w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => zeta x * value 2 u x) :
    ‖iteratedGradient 1 w - hzu.toLp _‖ ≤
      2 * c₁ * ‖iteratedGradient 0 (lowerOrder 1 u)‖ + c₂ * ‖value 2 u‖ := by
  have hc₁ : 0 ≤ c₁ := (norm_nonneg _).trans (hg 0)
  have hc₂ : 0 ≤ c₂ := (norm_nonneg _).trans (hh 0)
  have hD := iteratedGradient_one_ae_eq_of_value_ae_eq_mul hzeta hw
  refine TauCeti.Lp.norm_le_add_of_ae_norm_le (by positivity) hc₂ ?_
  filter_upwards [Lp.coeFn_sub (iteratedGradient 1 w) (hzu.toLp _), hD, hzu.coeFn_toLp] with
    x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, add_assoc, add_assoc, add_sub_cancel_left, ← add_assoc]
  exact (norm_leibnizRemainder_le zeta _ _ x).trans (by gcongr <;> apply_assumption)

/-- **The weak Hessian of a cutoff.** If `u, w ∈ W^{2,p}(Ω)` and `w = η u` almost everywhere on `Ω`
for a smooth `η` with `|η| ≤ 1`, `‖∇η‖ ≤ c₁` and `‖D²η‖ ≤ c₂`, then

`‖D²w‖ ≤ ‖D²u‖ + 2 c₁ ‖∇u‖ + c₂ ‖u‖`. -/
theorem norm_iteratedGradient_one_le_of_value_ae_eq_mul {u w : Wkp mu Omega p 2} {c₁ c₂ : ℝ}
    (hzeta : ContDiff ℝ ∞ zeta) (habs : ∀ x, |zeta x| ≤ 1)
    (hg : ∀ x, ‖∇ zeta x‖ ≤ c₁) (hh : ∀ x, ‖fderiv ℝ (∇ zeta) x‖ ≤ c₂)
    (hw : (value 2 w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => zeta x * value 2 u x) :
    ‖iteratedGradient 1 w‖ ≤ ‖iteratedGradient 1 u‖ +
      (2 * c₁ * ‖iteratedGradient 0 (lowerOrder 1 u)‖ + c₂ * ‖value 2 u‖) := by
  have hzu : MemLp (fun x => zeta x • iteratedGradient 1 u x) p (mu.restrict Omega) :=
    (memLp_top_of_bound hzeta.continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using habs x)).smul
      (Lp.memLp _)
  have hzun : ‖hzu.toLp _‖ ≤ ‖iteratedGradient 1 u‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hzu.coeFn_toLp] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (habs x)
  have h := norm_add_le (hzu.toLp _)
    (iteratedGradient 1 w - hzu.toLp _)
  rw [add_sub_cancel] at h
  exact h.trans
    (add_le_add hzun (norm_iteratedGradient_one_sub_toLp_le_of_value_ae_eq_mul hzeta hg hh hzu hw))

/-- **The Leibniz remainder of a cutoff in `Lᵖ`.** Let `ζ` be smooth with compact support,
`‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`, and let `u, w ∈ W^{2,p}(Ω)` with `w = ζ u` almost everywhere on `Ω`.
Then `D²w = ζ D²u + T` for some `T ∈ Lᵖ(Ω)` that vanishes off the support of `ζ` and satisfies
`‖T‖ ≤ 2 M₁ ‖∇u‖ + M₂ ‖u‖`, where `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. This is the form in which the
Leibniz rule `TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul` enters the localization
of second-order estimates. -/
theorem exists_iteratedGradient_one_ae_eq_smul_add_of_value_ae_eq_mul (hzeta : ContDiff ℝ ∞ zeta)
    (hcpt : HasCompactSupport zeta) {M₁ M₂ : ℝ} (hM₁ : ∀ x, ‖∇ zeta x‖ ≤ M₁)
    (hM₂ : ∀ x, ‖fderiv ℝ (∇ zeta) x‖ ≤ M₂) {u w : Wkp mu Omega p 2}
    (hw : (value 2 w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => zeta x * value 2 u x) :
    ∃ T : Lp (IteratedGradient E 1) p (mu.restrict Omega),
      (∀ᵐ x ∂mu.restrict Omega, iteratedGradient 1 w x = zeta x • iteratedGradient 1 u x + T x) ∧
      (∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport zeta → T x = 0) ∧
      ‖T‖ ≤ 2 * M₁ * ‖iteratedGradient 0 (lowerOrder 1 u)‖ + M₂ * ‖value 2 u‖ := by
  have hζH : MemLp (fun x => zeta x • iteratedGradient 1 u x) p (mu.restrict Omega) :=
    (hzeta.continuous.memLp_top_of_hasCompactSupport hcpt (mu.restrict Omega)).smul (Lp.memLp _)
  -- The remainder `∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` is the difference `D²w - ζ D²u` in `Lᵖ`.
  have hT : ∀ᵐ x ∂mu.restrict Omega, (iteratedGradient 1 w - hζH.toLp _) x =
      (innerSL ℝ (∇ zeta x)).smulRight (iteratedGradient 0 (lowerOrder 1 u) x)
        + (innerSL ℝ (iteratedGradient 0 (lowerOrder 1 u) x)).smulRight (∇ zeta x)
        + value 2 u x • fderiv ℝ (∇ zeta) x := by
    filter_upwards [Lp.coeFn_sub (iteratedGradient 1 w) (hζH.toLp _),
      iteratedGradient_one_ae_eq_of_value_ae_eq_mul hzeta hw, hζH.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    simp only [add_assoc, add_sub_cancel_left]
  refine ⟨iteratedGradient 1 w - hζH.toLp _, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub (iteratedGradient 1 w) (hζH.toLp _), hζH.coeFn_toLp]
      with x h1 h2
    rw [h1, Pi.sub_apply, h2, add_sub_cancel]
  · filter_upwards [hT] with x hx hxK
    rw [hx, leibnizRemainder_eq_zero_of_notMem_tsupport hxK]
  · exact norm_iteratedGradient_one_sub_toLp_le_of_value_ae_eq_mul hzeta hM₁ hM₂ hζH hw

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

/-- **Multiplication by a compactly supported smooth function in `W^{k,p}`.** If `ψ` is smooth with
compact support and `u ∈ W^{k,p}(Ω)`, then `ψ u` lies in `W^{k,p}(Ω)`: some element of
`W^{k,p}(Ω)` has value `ψ u` almost everywhere on `Ω`. The open set `Ω` is arbitrary, and the
support of `ψ` may meet `∂Ω`. -/
theorem exists_value_ae_eq_mul_of_hasCompactSupport (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ ∞ psi) (hcpt : HasCompactSupport psi) (u : Wkp mu Omega p k) :
    ∃ w : Wkp mu Omega p k, (value k w : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x := by
  -- Multiply on the bounded set `Ω ∩ B(0, r)` containing `Ω ∩ tsupport ψ`, then extend by zero.
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : E)).1 hcpt.isCompact.isBounded
  set Omega' : Opens E := Omega ⊓ ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have hsub : Omega' ≤ Omega := inf_le_left
  have hcl : closure (Omega' : Set E) ⊆ Metric.closedBall 0 r :=
    closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.2) Metric.isClosed_closedBall
  obtain ⟨w', hw'⟩ := exists_value_ae_eq_mul_of_contDiffOn isOpen_univ
    ((isCompact_closedBall 0 r).of_isClosed_subset isClosed_closure hcl) (Set.subset_univ _) k
    hpsi.contDiffOn (restrictL hsub k u)
  obtain ⟨w, hw⟩ := exists_value_ae_eq_indicator_of_isClosed (V := Omega) (isClosed_tsupport psi)
    (fun x hx => Opens.mem_inf.2 ⟨hx.1, hr hx.2⟩) k w' (by
      filter_upwards [hw'] with x hx hxK
      rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul])
  have hm : MeasurableSet (Omega' : Set E) := Omega'.isOpen.measurableSet
  refine ⟨w, ?_⟩
  filter_upwards [hw, ae_restrict_of_ae ((ae_restrict_iff' hm).1 hw'),
    ae_restrict_of_ae ((ae_restrict_iff' hm).1 (value_restrictL_ae hsub k u)),
    ae_restrict_mem Omega.isOpen.measurableSet] with x h₁ h₂ h₃ hxΩ
  rw [h₁]
  by_cases hx : x ∈ (Omega' : Set E)
  · rw [Set.indicator_of_mem hx, h₂ hx, h₃ hx]
  · have hxψ : x ∉ tsupport psi := fun h => hx (Opens.mem_inf.2 ⟨hxΩ, hr h⟩)
    rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hxψ, zero_mul]

end Wkp

end TauCeti
