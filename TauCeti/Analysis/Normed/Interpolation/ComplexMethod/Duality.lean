/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.InterValued
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Basic
public import TauCeti.Analysis.Normed.Interpolation.Regular
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The upper space of the dual couple embeds in the dual of the complex method

Let `(X₀, X₁)` be a regular couple of complex Banach spaces and `0 < θ < 1`. The dual couple
`(X₀*, X₁*)` (`CompatibleCouple.dual`) lives in `(X₀ ∩ X₁)*`, so every element `u` of its sum
space pairs with every `x ∈ X₀ ∩ X₁`. Calderón's duality theorem identifies the dual of the
complex interpolation space `[X₀, X₁]_θ` isometrically with the upper complex interpolation space
`[X₀*, X₁*]^θ` of the dual couple. This file proves one of its two inequalities: the pairing
satisfies

`|⟨u, x⟩| ≤ ‖u‖^[θ] ‖x‖_θ` for `u ∈ [X₀*, X₁*]^θ` and `x ∈ X₀ ∩ X₁`,

so, `X₀ ∩ X₁` being dense in `[X₀, X₁]_θ`, each `u` extends to a continuous functional on
`[X₀, X₁]_θ` of norm at most `‖u‖^[θ]`. The resulting map
`UpperComplexMethodSpace.toStrongDual : [X₀*, X₁*]^θ →L[ℂ] ([X₀, X₁]_θ)*` is injective and does
not increase norms. Its surjectivity and the reverse inequality `‖u‖^[θ] ≤ ‖⟨u, ·⟩‖`, which
make it an isometric isomorphism, are not proved here.

## The argument

Let `G` be an upper strip function of the dual couple with `deriv G θ = u` and boundary
difference quotients `q`. For an admissible function `Φ` with values in `X₀ ∩ X₁` and real
`h ≠ 0`, the scalar function `z ↦ ⟨(h i)⁻¹ (G (z + h i) - G z), Φ z⟩` is holomorphic and bounded
on the strip, and on the line `re z = j` it pairs a difference quotient of `G` in `Xⱼ*` with
`Φ z ∈ Xⱼ`. The maximum principle bounds its value at `θ` by `‖q‖` times the boundary norms of
`Φ`, and letting `h → 0` gives `|⟨u, Φ θ⟩| ≤ ‖q‖ sup_j sup_t ‖Φ (j + i t)‖_j`
(`IsUpperStripFunction.norm_sumSpaceEmbed_deriv_apply_le`).

These intersection-valued functions are enough to approach `‖x‖_θ`
(`ComplexMethodSpace.exists_inter_of_norm_ofInter_lt`, in `ComplexMethod/InterValued.lean`), which
gives the duality estimate.

## Main declarations

* `IsUpperStripFunction.norm_sumSpaceEmbed_deriv_apply_le`: the pairing estimate for an upper
  strip function of the dual couple and an intersection-valued admissible function.
* `UpperComplexMethodSpace.norm_sumSpaceEmbed_toSum_apply_le`: `|⟨u, x⟩| ≤ ‖u‖^[θ] ‖x‖_θ`.
* `UpperComplexMethodSpace.toStrongDual`: the injective contraction
  `[X₀*, X₁*]^θ →L[ℂ] ([X₀, X₁]_θ)*`, characterized by `toStrongDual_apply_ofInter`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.5
  (Theorem 4.5.1).
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2
  (Theorem 2.2).
-/

public noncomputable section

open Bornology Complex Complex.HadamardThreeLines Filter Metric Set Topology
open TauCeti.Complex.HadamardThreeLines
open scoped BoundedContinuousFunction ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### The pairing estimate -/

section Pairing

omit [ContinuousAdd V] [T1Space V]

variable {C} {hC : C.IsRegular}

/-- `(h i)⁻¹ ((t + h) - t) = i⁻¹` has norm one. -/
private theorem norm_inv_mul_I_mul_sub {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    ‖((h : ℂ) * I)⁻¹ * (((t + h : ℝ) : ℂ) - t)‖ = 1 := by
  rw [norm_mul, norm_inv, norm_mul, norm_I, mul_one, ofReal_add, add_sub_cancel_left, norm_real,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hh)]

namespace IsUpperStripFunction

variable {G : ℂ → (C.dual hC).SumSpace}
  {q : (offDiag (univ : Set ℝ) →ᵇ StrongDual ℂ X₀) × (offDiag (univ : Set ℝ) →ᵇ StrongDual ℂ X₁)}

-- The instance arguments are given explicitly: `IsUpperStripFunction` sees the sum space of the
-- dual couple through its quotient instances, the calculus lemmas through its normed ones.
/-- Paired with a fixed `y ∈ X₀ ∩ X₁`, an upper strip function of the dual couple has derivative
`⟨deriv G z, y⟩` at every point `z` of the open strip. -/
private theorem hasDerivAt_sumSpaceEmbed_apply (hG : (C.dual hC).IsUpperStripFunction G q)
    (y : C.inter) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    HasDerivAt (fun w => (C.dual hC).sumSpaceEmbed (G w) y)
      ((C.dual hC).sumSpaceEmbed (deriv G z) y) z :=
  HasFDerivAt.comp_hasDerivAt (𝕜 := ℂ) (F := (C.dual hC).SumSpace) (E := ℂ) z
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := (C.dual hC).SumSpace) (F := ℂ)
      ((ContinuousLinearMap.apply ℂ ℂ y).comp (C.dual hC).sumSpaceEmbed))
    (DifferentiableAt.hasDerivAt (𝕜 := ℂ) (F := (C.dual hC).SumSpace) (hG.differentiableAt hz))

/-- On the closed strip, the vertical difference quotients of `G` pair with `y` to at most
`‖q‖ ‖y‖`. -/
private theorem norm_inv_mul_sumSpaceEmbed_sub_apply_le
    (hG : (C.dual hC).IsUpperStripFunction G q) {h : ℝ} (hh : h ≠ 0) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (y : C.inter) :
    ‖((h : ℂ) * I)⁻¹ * (C.dual hC).sumSpaceEmbed (G (z + h * I) - G z) y‖ ≤ ‖q‖ * ‖y‖ := by
  have hsub := hG.norm_sub_le (z := z + h * I) (by simpa using hz) hz
  rw [add_sub_cancel_left] at hsub
  calc _ ≤ ‖((h : ℂ) * I)⁻¹‖ * (‖G (z + h * I) - G z‖ * ‖y‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (C.norm_dual_sumSpaceEmbed_apply_le hC _ _)
          (norm_nonneg _)
    _ ≤ ‖((h : ℂ) * I)⁻¹‖ * ((‖q‖ * ‖(h : ℂ) * I‖) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖q‖ * ‖y‖ := by
        rw [norm_inv, ← mul_assoc, mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.2
          (mul_ne_zero (ofReal_ne_zero.2 hh) I_ne_zero)), mul_one]

/-- On the line `re z = 0` the difference quotients of `G` lie in `X₀*`, so their pairing with
`y` is at most `‖q‖ ‖y‖_{X₀}`. -/
private theorem norm_inv_mul_sumSpaceEmbed_sub_apply_mul_I_le
    (hG : (C.dual hC).IsUpperStripFunction G q) {h : ℝ} (hh : h ≠ 0) (t : ℝ) (y : C.inter) :
    ‖((h : ℂ) * I)⁻¹ * (C.dual hC).sumSpaceEmbed (G (t * I + h * I) - G (t * I)) y‖ ≤
      ‖q‖ * ‖C.interFst y‖ := by
  have hzt : (t * I + h * I : ℂ) = ((t + h : ℝ) : ℂ) * I := by push_cast; ring
  rw [hzt, hG.sub_mul_I (show t + h ≠ t by simpa using hh), map_smul, smul_apply, smul_eq_mul,
    ← mul_assoc, norm_mul, norm_inv_mul_I_mul_sub hh t, one_mul, sumSpaceEmbed_fstToSum,
    dual_embed₀]
  exact ((q.1 _).le_opNorm (C.interFst y)).trans (mul_le_mul_of_nonneg_right
    ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans (norm_fst_le q)) (norm_nonneg _))

/-- On the line `re z = 1` the difference quotients of `G` lie in `X₁*`, so their pairing with
`y` is at most `‖q‖ ‖y‖_{X₁}`. -/
private theorem norm_inv_mul_sumSpaceEmbed_sub_apply_one_add_mul_I_le
    (hG : (C.dual hC).IsUpperStripFunction G q) {h : ℝ} (hh : h ≠ 0) (t : ℝ) (y : C.inter) :
    ‖((h : ℂ) * I)⁻¹ * (C.dual hC).sumSpaceEmbed (G (1 + t * I + h * I) - G (1 + t * I)) y‖ ≤
      ‖q‖ * ‖C.interSnd y‖ := by
  have hzt : (1 + t * I + h * I : ℂ) = 1 + ((t + h : ℝ) : ℂ) * I := by push_cast; ring
  rw [hzt, hG.sub_one_add_mul_I (show t + h ≠ t by simpa using hh), map_smul, smul_apply,
    smul_eq_mul, ← mul_assoc, norm_mul, norm_inv_mul_I_mul_sub hh t, one_mul,
    sumSpaceEmbed_sndToSum, dual_embed₁]
  exact ((q.2 _).le_opNorm (C.interSnd y)).trans (mul_le_mul_of_nonneg_right
    ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans (norm_snd_le q)) (norm_nonneg _))

/-- **The pairing estimate.** Let `(X₀, X₁)` be a regular couple and `0 < θ < 1`. Let `G` be an
upper strip function of the dual couple `(X₀*, X₁*)` with boundary difference quotients `q`, and
let `Φ` be a function with values in `X₀ ∩ X₁`, holomorphic on the open strip and continuous and
bounded on the closed strip, whose boundary values are bounded by `M` in `X₀` on `re z = 0` and in
`X₁` on `re z = 1`. Then `|⟨deriv G θ, Φ θ⟩| ≤ ‖q‖ M`. -/
theorem norm_sumSpaceEmbed_deriv_apply_le (hG : (C.dual hC).IsUpperStripFunction G q) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 1) {Φ : ℂ → C.inter} (hΦ : DiffContOnCl ℂ Φ (verticalStrip 0 1))
    (hΦb : IsBounded (Φ '' verticalClosedStrip 0 1)) {M : ℝ}
    (h₀ : ∀ t : ℝ, ‖C.interFst (Φ (t * I))‖ ≤ M)
    (h₁ : ∀ t : ℝ, ‖C.interSnd (Φ (1 + t * I))‖ ≤ M) :
    ‖(C.dual hC).sumSpaceEmbed (deriv G θ) (Φ θ)‖ ≤ ‖q‖ * M := by
  set P := (C.dual hC).sumSpaceEmbed
  have hqM : 0 ≤ ‖q‖ * M := mul_nonneg (norm_nonneg q) ((norm_nonneg _).trans (h₀ 0))
  have hcl : closure (verticalStrip 0 1) = re ⁻¹' Icc 0 1 := closure_verticalStrip zero_lt_one
  have hGc : ContinuousOn G (re ⁻¹' Icc 0 1) := hcl ▸ hG.diffContOnCl.continuousOn
  -- `φ h z = ⟨(h i)⁻¹ (G (z + h i) - G z), Φ z⟩`, a bounded holomorphic function on the strip.
  set φ : ℝ → ℂ → ℂ := fun h z => ((h : ℂ) * I)⁻¹ * (P (G (z + h * I)) (Φ z) - P (G z) (Φ z))
  have hbound : ∀ h : ℝ, h ≠ 0 → ‖φ h θ‖ ≤ ‖q‖ * M := by
    intro h hh
    have hmaps (s : Set ℝ) : MapsTo (fun z : ℂ => z + h * I) (re ⁻¹' s) (re ⁻¹' s) :=
      fun z hz => by simpa using hz
    have hd : DiffContOnCl ℂ (φ h) (verticalStrip 0 1) :=
      ⟨(((P.differentiable.comp_differentiableOn (hG.diffContOnCl.differentiableOn.comp
          (differentiableOn_id.add_const _) (hmaps _))).clm_apply hΦ.differentiableOn).fun_sub
          ((P.differentiable.comp_differentiableOn hG.diffContOnCl.differentiableOn).clm_apply
            hΦ.differentiableOn)).const_mul _,
        hcl ▸ ((((P.continuous.comp_continuousOn (hGc.comp (continuousOn_id.add continuousOn_const)
          (hmaps _))).clm_apply (hcl ▸ hΦ.continuousOn)).fun_sub
          ((P.continuous.comp_continuousOn hGc).clm_apply (hcl ▸ hΦ.continuousOn))).const_mul _)⟩
    have hφ : ∀ z, φ h z = ((h : ℂ) * I)⁻¹ * P (G (z + h * I) - G z) (Φ z) := fun z => by
      rw [map_sub, sub_apply]
    obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 hΦb
    have hB : BddAbove ((norm ∘ φ h) '' verticalClosedStrip 0 1) := ⟨‖q‖ * K, by
      rintro _ ⟨z, hz, rfl⟩
      exact (hφ z ▸ norm_inv_mul_sumSpaceEmbed_sub_apply_le hG hh hz (Φ z)).trans
        (mul_le_mul_of_nonneg_left (hK _ (mem_image_of_mem _ hz)) (norm_nonneg q))⟩
    have ha : ∀ z ∈ re ⁻¹' {0}, ‖φ h z‖ ≤ ‖q‖ * M := fun z hz => by
      obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = t * I := ⟨z.im, Complex.ext (by simpa using hz) (by simp)⟩
      exact (hφ _ ▸ norm_inv_mul_sumSpaceEmbed_sub_apply_mul_I_le hG hh t _).trans
        (mul_le_mul_of_nonneg_left (h₀ t) (norm_nonneg q))
    have hb : ∀ z ∈ re ⁻¹' {1}, ‖φ h z‖ ≤ ‖q‖ * M := fun z hz => by
      obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = 1 + t * I :=
        ⟨z.im, Complex.ext (by simpa using hz) (by simp)⟩
      exact (hφ _ ▸ norm_inv_mul_sumSpaceEmbed_sub_apply_one_add_mul_I_le hG hh t _).trans
        (mul_le_mul_of_nonneg_left (h₁ t) (norm_nonneg q))
    have := norm_le_interp_of_mem_verticalClosedStrip₀₁' (φ h) (z := (θ : ℂ))
      (by simpa using Ioo_subset_Icc_self hθ) hd hB ha hb
    simpa [← Real.rpow_add' hqM] using this
  -- Letting `h → 0`, the difference quotients at `θ` tend to the derivative.
  have hmap : Tendsto (fun h : ℝ => (h : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous fun h : ℝ => (h : ℂ) * I).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun h hh => mul_ne_zero (ofReal_ne_zero.2 hh) I_ne_zero)
  have hderiv : HasDerivAt (fun w => P (G w) (Φ θ)) (P (deriv G θ) (Φ θ)) θ :=
    hasDerivAt_sumSpaceEmbed_apply hG (Φ θ) (by simpa using hθ)
  have hlim : Tendsto (fun h : ℝ => φ h θ) (𝓝[≠] 0) (𝓝 (P (deriv G θ) (Φ θ))) :=
    hderiv.tendsto_slope_zero.comp hmap
  exact le_of_tendsto hlim.norm (eventually_nhdsWithin_of_forall hbound)

end IsUpperStripFunction

end Pairing

/-! ### The upper space of the dual couple in the dual of the complex method -/

namespace UpperComplexMethodSpace

variable {C} [CompleteSpace X₀] [CompleteSpace X₁] {hC : C.IsRegular} {θ : ℝ}

/-- **Calderón's duality estimate.** For a regular Banach couple `(X₀, X₁)`, the pairing of
`u ∈ [X₀*, X₁*]^θ` with `x ∈ X₀ ∩ X₁` satisfies `|⟨u, x⟩| ≤ ‖u‖^[θ] ‖x‖_θ`. -/
theorem norm_sumSpaceEmbed_toSum_apply_le (u : (C.dual hC).UpperComplexMethodSpace θ)
    (x : C.inter) :
    ‖(C.dual hC).sumSpaceEmbed (toSum u) x‖ ≤ ‖u‖ * ‖ComplexMethodSpace.ofInter θ x‖ := by
  by_cases hθ : θ ∈ Ioo 0 1
  swap
  · simp [eq_zero_of_notMem hθ u]
  have key : ∀ ε > 0, ‖(C.dual hC).sumSpaceEmbed (toSum u) x‖ ≤
      (‖u‖ + ε) * (‖ComplexMethodSpace.ofInter θ x‖ + ε) := fun ε hε => by
    obtain ⟨q, rfl, hq⟩ := norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hε)
    obtain ⟨Φ, hΦ, hΦb, hΦθ, h₀, h₁⟩ := ComplexMethodSpace.exists_inter_of_norm_ofInter_lt hθ
      (lt_add_of_pos_right ‖ComplexMethodSpace.ofInter θ x‖ hε)
    have hG := (C.dual hC).isUpperStripFunction_upperStripFunction q
    have hA := hG.norm_sumSpaceEmbed_deriv_apply_le hθ hΦ hΦb (fun t => (h₀ t).le)
      (fun t => (h₁ t).le)
    rw [hΦθ] at hA
    rw [toSum_mk, (C.dual hC).upperStripDerivEval_apply (z := θ) (by simpa using hθ) q]
    exact hA.trans (mul_le_mul_of_nonneg_right ((Submodule.norm_coe q).trans_lt hq).le
      (by positivity))
  have hlim : Tendsto (fun ε : ℝ => (‖u‖ + ε) * (‖ComplexMethodSpace.ofInter θ x‖ + ε))
      (𝓝[>] 0) (𝓝 (‖u‖ * ‖ComplexMethodSpace.ofInter θ x‖)) :=
    ((by fun_prop : Continuous fun ε : ℝ =>
      (‖u‖ + ε) * (‖ComplexMethodSpace.ofInter θ x‖ + ε)).tendsto' 0 _ (by simp)).mono_left
        nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- Continuous functionals on `[X₀, X₁]_θ` agreeing on `X₀ ∩ X₁` are equal. -/
private theorem strongDual_ext_ofInter {f g : StrongDual ℂ (C.ComplexMethodSpace θ)}
    (h : ∀ x : C.inter, f (ComplexMethodSpace.ofInter θ x) = g (ComplexMethodSpace.ofInter θ x)) :
    f = g :=
  DFunLike.coe_injective <| (ComplexMethodSpace.denseRange_ofInter θ).equalizer f.continuous
    g.continuous (funext h)

variable (hC θ) in
/-- The extension of `x ↦ ⟨u, x⟩` from `X₀ ∩ X₁` to `[X₀, X₁]_θ`. -/
private def pairingExtension (u : (C.dual hC).UpperComplexMethodSpace θ) :
    StrongDual ℂ (C.ComplexMethodSpace θ) :=
  LinearMap.extendOfNorm ((C.dual hC).sumSpaceEmbed (toSum u)).toLinearMap
    (ComplexMethodSpace.ofInter θ).toLinearMap

private theorem pairingExtension_apply_ofInter (u : (C.dual hC).UpperComplexMethodSpace θ)
    (x : C.inter) :
    pairingExtension hC θ u (ComplexMethodSpace.ofInter θ x) =
      (C.dual hC).sumSpaceEmbed (toSum u) x :=
  LinearMap.extendOfNorm_eq (ComplexMethodSpace.denseRange_ofInter θ)
    ⟨_, norm_sumSpaceEmbed_toSum_apply_le u⟩ x

variable (hC θ) in
/-- **The upper space of the dual couple in the dual of the complex method (Calderón).** For a
regular Banach couple `(X₀, X₁)`, each `u ∈ [X₀*, X₁*]^θ` defines the continuous functional on
`[X₀, X₁]_θ` extending `x ↦ ⟨u, x⟩` from the dense subspace `X₀ ∩ X₁`
(`toStrongDual_apply_ofInter`). The map `u ↦ ⟨u, ·⟩` is injective (`toStrongDual_injective`) and
does not increase norms (`norm_toStrongDual_le`). -/
def toStrongDual :
    (C.dual hC).UpperComplexMethodSpace θ →L[ℂ] StrongDual ℂ (C.ComplexMethodSpace θ) :=
  LinearMap.mkContinuous
    { toFun := pairingExtension hC θ
      map_add' u v := strongDual_ext_ofInter fun x => by
        simp only [add_apply, pairingExtension_apply_ofInter, map_add]
      map_smul' c u := strongDual_ext_ofInter fun x => by
        simp only [smul_apply, pairingExtension_apply_ofInter, map_smul, RingHom.id_apply] }
    1 fun u => by
      rw [one_mul]
      exact LinearMap.opNorm_extendOfNorm_le (ComplexMethodSpace.denseRange_ofInter θ)
        (norm_nonneg u) (norm_sumSpaceEmbed_toSum_apply_le u)

/-- On `X₀ ∩ X₁`, the functional `toStrongDual hC θ u` is the pairing with `u`. -/
@[simp] theorem toStrongDual_apply_ofInter (u : (C.dual hC).UpperComplexMethodSpace θ)
    (x : C.inter) :
    toStrongDual hC θ u (ComplexMethodSpace.ofInter θ x) =
      (C.dual hC).sumSpaceEmbed (toSum u) x :=
  pairingExtension_apply_ofInter u x

/-- `toStrongDual hC θ u` is the only continuous functional on `[X₀, X₁]_θ` that pairs with
`X₀ ∩ X₁` as `u` does. -/
theorem eq_toStrongDual_iff {u : (C.dual hC).UpperComplexMethodSpace θ}
    {f : StrongDual ℂ (C.ComplexMethodSpace θ)} :
    f = toStrongDual hC θ u ↔
      ∀ x : C.inter, f (ComplexMethodSpace.ofInter θ x) = (C.dual hC).sumSpaceEmbed (toSum u) x :=
  ⟨fun h x => h ▸ toStrongDual_apply_ofInter u x, fun h =>
    strongDual_ext_ofInter fun x => by rw [h, toStrongDual_apply_ofInter]⟩

/-- `toStrongDual` does not increase norms. -/
theorem norm_toStrongDual_le (u : (C.dual hC).UpperComplexMethodSpace θ) :
    ‖toStrongDual hC θ u‖ ≤ ‖u‖ :=
  LinearMap.opNorm_extendOfNorm_le (ComplexMethodSpace.denseRange_ofInter θ) (norm_nonneg u)
    (norm_sumSpaceEmbed_toSum_apply_le u)

theorem opNorm_toStrongDual_le : ‖toStrongDual (C := C) hC θ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_toStrongDual_le u

/-- `toStrongDual` is injective: an element of `[X₀*, X₁*]^θ` is determined by its pairing with
`X₀ ∩ X₁`. -/
theorem toStrongDual_injective : Function.Injective (toStrongDual (C := C) hC θ) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => toSum_injective ?_
  refine (C.dual hC).sumSpaceEmbed_injective ?_
  ext x
  simpa using congrArg (fun f => f (ComplexMethodSpace.ofInter θ x)) hu

end UpperComplexMethodSpace

end TauCeti.CompatibleCouple
