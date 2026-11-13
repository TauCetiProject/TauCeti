/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Ring.Units
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Continuity of inverses and left inverses of operators

Mathlib's `ContinuousLinearMap.HasLeftInverse` records that a continuous linear map has a left
inverse which is itself continuous and linear. This file adds two facts about it, and the
corresponding statement for continuous pseudo-inverses.

* Over `ℝ` or `ℂ`, every continuous linear map `f` out of a finite-dimensional space has a
  continuous pseudo-inverse `g`, with `f ∘ g ∘ f = f`, whatever the locally convex codomain: its
  range is finite-dimensional, hence has a closed complement by the Hahn–Banach theorem. When `f`
  is injective, `g` is a continuous left inverse of `f`.
* Having a continuous left inverse is stable in families. If `A x` depends continuously on `x`
  and `A x₀` has a continuous left inverse, then so does `A x` for `x` near `x₀`, and the left
  inverses can be chosen to depend continuously on `x` at `x₀`. If `P` is a left inverse of
  `A x₀`, then `P ∘ A x` is invertible near `x₀`, and `(P ∘ A x)⁻¹ ∘ P` is a left inverse of
  `A x`.

The second fact is what makes coordinates with respect to a moving family of linearly
independent vectors depend continuously on the base point, as in the local trivializations of a
subbundle spanned by local frames.

Inversion is also continuous along a continuous family of invertible operators between normed
spaces without completeness, even when continuity and invertibility hold only near one point.
This gives continuity of quotient-range coordinates for families of valid splittings.

## Main results

* `ContinuousLinearMap.exists_comp_comp_eq_self`: a continuous linear map out of a
  finite-dimensional space over `ℝ` or `ℂ` has a continuous pseudo-inverse.
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional_domain`: an injective
  continuous linear map out of a finite-dimensional space over `ℝ` or `ℂ` has a continuous left
  inverse.
* `ContinuousAt.clm_inverse_of_eventually_isInvertible`: inversion preserves continuity at a point
  where the family is eventually invertible, without completeness.
* `Continuous.clm_inverse`: inversion is continuous along a continuous family
  of invertible operators between normed spaces, with no completeness assumption.
* `ContinuousAt.eventually_isInvertible_clm_comp`: invertibility of a composite `P(σ) L(σ)` of
  continuous families out of a Banach space persists near a point.
* `ContinuousAt.exists_continuousAt_leftInverse`: continuously varying left inverses of a
  continuous family of operators whose member at `x₀` has a continuous left inverse.
-/

public section

noncomputable section

open Filter Function Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

namespace ContinuousLinearMap

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G] [IsTopologicalAddGroup G]
  [ContinuousSMul 𝕜 G]
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [T2Space F]

/-- Over `ℝ` or `ℂ`, a continuous linear map `f` out of a finite-dimensional space into a locally
convex (polynormable) space has a continuous *pseudo-inverse*: a continuous linear map `g` in the
opposite direction with `f ∘ g ∘ f = f`. This is the continuous counterpart of
`LinearMap.exists_comp_comp_eq_self`. -/
theorem exists_comp_comp_eq_self [IsRCLikeNormedField 𝕜] [PolynormableSpace 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : G →L[𝕜] F) : ∃ g : F →L[𝕜] G, f ∘L g ∘L f = f := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- A continuous projection `p` onto the range, followed by a right inverse of `f` on its range.
  obtain ⟨p, hp⟩ :=
    Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f.toLinearMap)
  obtain ⟨σ, hσ⟩ :=
    f.toLinearMap.rangeRestrict.exists_rightInverse_of_surjective f.toLinearMap.range_rangeRestrict
  refine ⟨(LinearMap.toContinuousLinearMap σ).comp p, ext fun v ↦ ?_⟩
  have hv : p (f v) = f.toLinearMap.rangeRestrict v :=
    hp ⟨f v, LinearMap.mem_range_self f.toLinearMap v⟩
  simpa [hv] using congrArg Subtype.val (LinearMap.congr_fun hσ (f.toLinearMap.rangeRestrict v))

/-- Over `ℝ` or `ℂ`, an injective continuous linear map out of a finite-dimensional space into a
locally convex (polynormable) space has a continuous left inverse: any continuous pseudo-inverse
`g` of `f` (`ContinuousLinearMap.exists_comp_comp_eq_self`) is one, since `f (g (f v)) = f v`. -/
theorem HasLeftInverse.of_injective_of_finiteDimensional_domain [IsRCLikeNormedField 𝕜]
    [PolynormableSpace 𝕜 F] [FiniteDimensional 𝕜 G] {f : G →L[𝕜] F} (hf : Injective f) :
    f.HasLeftInverse := by
  obtain ⟨g, hg⟩ := f.exists_comp_comp_eq_self
  exact ⟨g, fun v ↦ hf congr($hg v)⟩

end ContinuousLinearMap

/-- Inversion preserves continuity at a point of an eventually invertible operator family,
without completeness of either space. -/
theorem ContinuousAt.clm_inverse_of_eventually_isInvertible {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : X → E →L[𝕜] F} {x₀ : X} (hf : ContinuousAt f x₀)
    (h : ∀ᶠ y in 𝓝 x₀, (f y).IsInvertible) :
    ContinuousAt (fun x => (f x).inverse) x₀ := by
  set g : X → F →L[𝕜] E := fun y => (f y).inverse
  have hfn : Tendsto (fun y => ‖f y - f x₀‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hf
  have hsmall : ∀ᶠ y in 𝓝 x₀, ‖f y - f x₀‖ * ‖g x₀‖ ≤ 1 / 2 := by
    have := hfn.mul_const ‖g x₀‖
    rw [zero_mul] at this
    exact (this.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ => le_of_lt
  -- Squeeze the inverse difference by a constant multiple of the original difference.
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hfn.const_mul (2 * ‖g x₀‖ ^ 2))
  filter_upwards [hsmall, h] with y hy hiy
  have hsub : g y - g x₀ = g y ∘L (f x₀ - f y) ∘L g x₀ :=
    hiy.inverse_sub_inverse h.self_of_nhds
  have hd : ‖f x₀ - f y‖ = ‖f y - f x₀‖ := norm_sub_rev _ _
  have he : ‖g y - g x₀‖ ≤ ‖g y‖ * ‖f y - f x₀‖ * ‖g x₀‖ := by
    rw [hsub, ← hd]
    calc ‖g y ∘L (f x₀ - f y) ∘L g x₀‖
        ≤ ‖g y‖ * ‖(f x₀ - f y) ∘L g x₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖g y‖ * (‖f x₀ - f y‖ * ‖g x₀‖) := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = _ := by ring
  have ha : ‖g y‖ ≤ ‖g x₀‖ + ‖g y - g x₀‖ := by
    simpa using norm_add_le (g x₀) (g y - g x₀)
  have ha0 := norm_nonneg (g y)
  have hdc : 0 ≤ ‖f y - f x₀‖ * ‖g x₀‖ := by positivity
  -- Absorb the small perturbation to bound the nearby inverses uniformly.
  have h2 : ‖g y‖ ≤ 2 * ‖g x₀‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hy ha0]
  calc ‖g y - g x₀‖ ≤ ‖g y‖ * (‖f y - f x₀‖ * ‖g x₀‖) := by rw [← mul_assoc]; exact he
    _ ≤ (2 * ‖g x₀‖) * (‖f y - f x₀‖ * ‖g x₀‖) := mul_le_mul_of_nonneg_right h2 hdc
    _ = 2 * ‖g x₀‖ ^ 2 * ‖f y - f x₀‖ := by ring

/-- If `P(σ) L(σ)` is invertible and both families are continuous at `σ`, then `P(σ') L(σ')` is
invertible for all `σ'` near `σ`, provided the domain of `L(σ)` is complete. -/
theorem ContinuousAt.eventually_isInvertible_clm_comp {E X Y Z : Type*} [TopologicalSpace E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [SeminormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z] {P : E → Y →L[𝕜] Z}
    {L : E → X →L[𝕜] Y} {σ : E} (hP : ContinuousAt P σ) (hL : ContinuousAt L σ)
    (h : (P σ ∘L L σ).IsInvertible) :
    ∀ᶠ σ' in 𝓝 σ, (P σ' ∘L L σ').IsInvertible :=
  (hP.clm_comp hL).eventually h.eventually_nhds

/-- Inversion is continuous along a continuous family of invertible operators, without
completeness of either space. -/
theorem Continuous.clm_inverse {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : X → E →L[𝕜] F} (hf : Continuous f) (h : ∀ x, (f x).IsInvertible) :
    Continuous (fun x => (f x).inverse) :=
  continuous_iff_continuousAt.mpr fun _ =>
    hf.continuousAt.clm_inverse_of_eventually_isInvertible (.of_forall h)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {X : Type*} [TopologicalSpace X]

/-- **Left inverses vary continuously.** Let `A x` be a continuous linear map depending
continuously on `x` at `x₀`, into a normed space from a Banach space. If `A x₀` has a continuous
left inverse, then there are continuous linear maps `L x`, depending continuously on `x` at `x₀`,
such that `L x` is a left inverse of `A x` for all `x` near `x₀`. -/
theorem ContinuousAt.exists_continuousAt_leftInverse {A : X → G →L[𝕜] F} {x₀ : X}
    (hA : ContinuousAt A x₀) (h : (A x₀).HasLeftInverse) :
    ∃ L : X → F →L[𝕜] G, ContinuousAt L x₀ ∧ ∀ᶠ x in 𝓝 x₀, LeftInverse (L x) (A x) := by
  obtain ⟨P, hP⟩ := h
  -- The compression `P ∘ A x` is the identity at `x₀`, hence invertible near `x₀`.
  have hQ : ContinuousAt (fun x ↦ P ∘L A x) x₀ := (continuousAt_const (y := P)).clm_comp hA
  have hQ₀ : P ∘L A x₀ = ((1 : (G →L[𝕜] G)ˣ) : G →L[𝕜] G) := ContinuousLinearMap.ext hP
  refine ⟨fun x ↦ Ring.inverse (P ∘L A x) ∘L P,
    ContinuousAt.clm_comp ((NormedRing.inverse_continuousAt 1).comp_of_eq hQ hQ₀)
      continuousAt_const, ?_⟩
  filter_upwards [hQ.preimage_mem_nhds (hQ₀ ▸ Units.nhds 1)] with x hx v
  have := congrArg (fun T : G →L[𝕜] G ↦ T v) (Ring.inverse_mul_cancel _ hx)
  simpa using this
