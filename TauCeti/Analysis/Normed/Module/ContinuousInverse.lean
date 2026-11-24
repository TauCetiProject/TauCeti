/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse

/-!
# Continuity of inverses and left inverses of operators

Mathlib's `ContinuousLinearMap.HasLeftInverse` records that a continuous linear map has a left
inverse which is itself continuous and linear. This file adds two facts about it, and the
corresponding statement for continuous pseudo-inverses.

* Over `ℝ` or `ℂ`, every continuous linear map `f` of finite rank (for instance, one out of a
  finite-dimensional space) from a topological vector space into a Hausdorff locally convex
  space has a continuous pseudo-inverse `g`, with `f ∘ g ∘ f = f`: its range is
  finite-dimensional, hence has a closed complement by the Hahn–Banach theorem. When `f` is
  injective, `g` is a continuous left inverse of `f`.
* Having a continuous left inverse is stable in families of operators from a Banach space into
  a topological vector space. If `A x` depends continuously on `x` and `A x₀` has a continuous
  left inverse, then so does `A x` for `x` near `x₀`, and the left inverses can be chosen to
  depend continuously on `x` at `x₀`. If `P` is a left inverse of `A x₀`, then `P ∘ A x` is
  invertible near `x₀`, and `(P ∘ A x)⁻¹ ∘ P` (`ContinuousLinearMap.leftInverseAlong`) is a left
  inverse of `A x`.

The second fact is what makes coordinates with respect to a moving family of linearly
independent vectors depend continuously on the base point, as in the local trivializations of a
subbundle spanned by local frames.

Inversion is also continuous along a continuous family of invertible operators between seminormed
spaces without completeness, even when continuity and invertibility hold only near one point.
This gives continuity of quotient-range coordinates for families of valid splittings.

## Main results

* `ContinuousLinearMap.exists_comp_comp_eq_self`: over `ℝ` or `ℂ`, a continuous linear map of
  finite rank from a topological vector space into a Hausdorff locally convex space has a
  continuous pseudo-inverse.
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional_domain`: over `ℝ` or `ℂ`,
  an injective continuous linear map from a finite-dimensional topological vector space into a
  Hausdorff locally convex space has a continuous left inverse.
* `ContinuousWithinAt.clm_inverse_of_eventually_isInvertible`,
  `ContinuousAt.clm_inverse_of_eventually_isInvertible`: inversion preserves continuity within a
  set or at a point where the family is invertible nearby, without completeness.
* `Continuous.clm_inverse`: inversion is continuous along a continuous family
  of invertible operators between seminormed spaces, with no completeness assumption.
* `ContinuousWithinAt.continuousLinearEquiv_symm`: the inverses of a family of continuous linear
  equivalences continuous within a set at a point are continuous there, without completeness.
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
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [T2Space F]

/-- Over `ℝ` or `ℂ`, a continuous linear map `f` of finite rank (for instance, one out of a
finite-dimensional space) from a topological vector space into a Hausdorff locally convex
(polynormable) space has a continuous *pseudo-inverse*: a continuous linear map `g` in the
opposite direction with `f ∘ g ∘ f = f`. This is the continuous counterpart of
`LinearMap.exists_comp_comp_eq_self`. -/
theorem exists_comp_comp_eq_self [IsRCLikeNormedField 𝕜] [PolynormableSpace 𝕜 F]
    (f : G →L[𝕜] F) [FiniteDimensional 𝕜 f.range] : ∃ g : F →L[𝕜] G, f ∘L g ∘L f = f := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- Mathlib's Hahn–Banach lemma below assumes `IsTopologicalAddGroup F`, which follows from
  -- `PolynormableSpace 𝕜 F` but is not found by instance search.
  have := PolynormableSpace.isTopologicalAddGroup 𝕜 F
  -- A continuous projection `p` onto the range, followed by a continuous right inverse `σ` of
  -- `f` on its range, which is finite-dimensional.
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional f.range
  obtain ⟨σ, hσ⟩ := HasRightInverse.of_surjective_of_finiteDimensional
    (f := f.rangeRestrict) (LinearMap.surjective_rangeRestrict _)
  refine ⟨σ ∘L p, ext fun v ↦ ?_⟩
  -- `p` fixes `f v`, and `σ` lifts it to a preimage of `f v`.
  have hv : p (f v) = ⟨f v, LinearMap.mem_range_self _ v⟩ := hp ⟨f v, _⟩
  simpa [hv] using congrArg Subtype.val (hσ ⟨f v, LinearMap.mem_range_self _ v⟩)

/-- Over `ℝ` or `ℂ`, an injective continuous linear map `f` from a finite-dimensional
topological vector space into a Hausdorff locally convex (polynormable) space has a continuous
left inverse. -/
theorem HasLeftInverse.of_injective_of_finiteDimensional_domain [IsRCLikeNormedField 𝕜]
    [PolynormableSpace 𝕜 F] [FiniteDimensional 𝕜 G] {f : G →L[𝕜] F} (hf : Injective f) :
    f.HasLeftInverse := by
  obtain ⟨g, hg⟩ := f.exists_comp_comp_eq_self
  exact ⟨g, fun v ↦ hf congr($hg v)⟩

end ContinuousLinearMap

/-- Inversion preserves continuity within a set at a point of an operator family which is
invertible at that point and eventually invertible within the set, without completeness of
either space. -/
theorem ContinuousWithinAt.clm_inverse_of_eventually_isInvertible {X E F : Type*}
    [TopologicalSpace X] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : X → E →L[𝕜] F} {s : Set X} {x₀ : X}
    (hf : ContinuousWithinAt f s x₀) (h₀ : (f x₀).IsInvertible)
    (h : ∀ᶠ y in 𝓝[s] x₀, (f y).IsInvertible) :
    ContinuousWithinAt (fun x => (f x).inverse) s x₀ := by
  set g : X → F →L[𝕜] E := fun y => (f y).inverse
  have hfn : Tendsto (fun y => ‖f y - f x₀‖) (𝓝[s] x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hf
  have hsmall : ∀ᶠ y in 𝓝[s] x₀, ‖f y - f x₀‖ * ‖g x₀‖ ≤ 1 / 2 := by
    have := hfn.mul_const ‖g x₀‖
    rw [zero_mul] at this
    exact (this.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ => le_of_lt
  -- Squeeze the inverse difference by a constant multiple of the original difference.
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hfn.const_mul (2 * ‖g x₀‖ ^ 2))
  filter_upwards [hsmall, h] with y hy hiy
  have hsub : g y - g x₀ = g y ∘L (f x₀ - f y) ∘L g x₀ :=
    hiy.inverse_sub_inverse h₀
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

/-- Inversion preserves continuity at a point of an eventually invertible operator family,
without completeness of either space. -/
theorem ContinuousAt.clm_inverse_of_eventually_isInvertible {X E F : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : X → E →L[𝕜] F} {x₀ : X} (hf : ContinuousAt f x₀)
    (h : ∀ᶠ y in 𝓝 x₀, (f y).IsInvertible) :
    ContinuousAt (fun x => (f x).inverse) x₀ := by
  rw [← continuousWithinAt_univ] at hf ⊢
  exact hf.clm_inverse_of_eventually_isInvertible h.self_of_nhds (by rwa [nhdsWithin_univ])

/-- Inversion is continuous along a continuous family of invertible operators, without
completeness of either space. -/
theorem Continuous.clm_inverse {X E F : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : X → E →L[𝕜] F} (hf : Continuous f) (h : ∀ x, (f x).IsInvertible) :
    Continuous (fun x => (f x).inverse) :=
  continuous_iff_continuousAt.mpr fun _ =>
    hf.continuousAt.clm_inverse_of_eventually_isInvertible (.of_forall h)

/-- The inverses of a family of continuous linear equivalences, continuous within a set at a
point, are continuous within that set at that point, without completeness of either space. -/
theorem ContinuousWithinAt.continuousLinearEquiv_symm {X E F : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {e : X → E ≃L[𝕜] F} {s : Set X} {x₀ : X}
    (he : ContinuousWithinAt (fun x ↦ (e x : E →L[𝕜] F)) s x₀) :
    ContinuousWithinAt (fun x ↦ ((e x).symm : F →L[𝕜] E)) s x₀ := by
  simpa only [ContinuousLinearMap.inverse_equiv] using
    he.clm_inverse_of_eventually_isInvertible ContinuousLinearMap.isInvertible_equiv
      (.of_forall fun _ ↦ ContinuousLinearMap.isInvertible_equiv)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F] {X : Type*} [TopologicalSpace X]

/-- **Left inverses vary continuously.** Let `A x` be a continuous linear map depending
continuously on `x` at `x₀`, from a Banach space into a topological vector space (for the
topology of bounded convergence on `G →L[𝕜] F`, the operator norm topology when `F` is normed).
If `A x₀` has a continuous left inverse, then there are continuous linear maps `L x`, depending
continuously on `x` at `x₀`, such that `L x` is a left inverse of `A x` for all `x` near `x₀`. -/
theorem ContinuousAt.exists_continuousAt_leftInverse {A : X → G →L[𝕜] F} {x₀ : X}
    (hA : ContinuousAt A x₀) (h : (A x₀).HasLeftInverse) :
    ∃ L : X → F →L[𝕜] G, ContinuousAt L x₀ ∧ ∀ᶠ x in 𝓝 x₀, LeftInverse (L x) (A x) := by
  obtain ⟨P, hP⟩ := h
  -- The compression `P ∘ A x` is the identity at `x₀`, hence invertible near `x₀`.
  have hQ : ContinuousAt (fun x ↦ P ∘L A x) x₀ :=
    (ContinuousLinearMap.postcomp G P).continuous.continuousAt.comp hA
  have hQ₀ : (P ∘L A x₀).IsInvertible := by
    rw [show P ∘L A x₀ = .id 𝕜 G from ContinuousLinearMap.ext hP]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 G, rfl⟩
  have hQev := hQ.eventually hQ₀.eventually_nhds
  refine ⟨fun x ↦ (A x).leftInverseAlong P, ?_,
    hQev.mono fun x hx ↦ ContinuousLinearMap.leftInverseAlong_apply_self hx⟩
  simp_rw [ContinuousLinearMap.leftInverseAlong_def]
  exact (ContinuousLinearMap.precomp G P).continuous.continuousAt.comp
    (hQ.clm_inverse_of_eventually_isInvertible hQev)
