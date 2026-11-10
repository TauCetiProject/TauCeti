/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Fixed complements to nearby operator ranges

A continuous family of split injections with a complete ambient space has a single closed
complement to its ranges near each parameter. The complement parametrizes all nearby
quotients through `ContinuousLinearMap.quotientRangeEquiv`. This is the local
linear input for quotient bundles, such as the intrinsic normal bundle of an immersion.

The proof uses Mathlib's `ContinuousLinearEquiv.equivOfRightInverse` and openness of
invertibility. Completeness of the nearby complements — the complete model fibres above —
follows from `ContinuousLinearMap.completeSpace_of_isInvertible`, which transfers completeness
of the codomain back to the domain of an invertible operator.
Complementary coordinate operators are continuous on a domain of valid splittings, using
Mathlib's regularity of operator inversion.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
the normal-bundle construction preceding Theorem 6.24.
-/

public section

open Set Filter Topology

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A fixed complement to a split injection still parametrizes the quotient by every
sufficiently nearby range. The source and ambient spaces may be infinite dimensional. -/
theorem ContinuousAt.exists_isInvertible_coprod_subtypeL
    [TopologicalSpace X] [CompleteSpace F]
    {A : X → E →L[𝕜] F} {x₀ : X} (hA : ContinuousAt A x₀)
    (h₀ : (A x₀).HasLeftInverse) :
    ∃ Q : Submodule 𝕜 F, IsClosed (Q : Set F) ∧
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, ((A x).coprod Q.subtypeL).IsInvertible := by
  let Q := h₀.leftInverse.ker
  have hQ : IsClosed (Q : Set F) := h₀.leftInverse.isClosed_ker
  let e := ContinuousLinearEquiv.equivOfRightInverse h₀.leftInverse (A x₀)
    h₀.leftInverse_leftInverse
  have : CompleteSpace (E × Q) :=
    ContinuousLinearMap.completeSpace_of_isInvertible
      (ContinuousLinearMap.isInvertible_equiv (f := e.symm))
  have he : ((A x₀).coprod Q.subtypeL).IsInvertible := by
    refine ⟨e.symm, ?_⟩
    apply ContinuousLinearMap.ext
    intro p
    exact ContinuousLinearEquiv.equivOfRightInverse_symm_apply _ _ _ p
  have hnear : ∀ᶠ x in 𝓝 x₀, ((A x).coprod Q.subtypeL).IsInvertible :=
    (hA.continuousLinearMapCoprod continuousAt_const).eventually he.eventually_nhds
  obtain ⟨U, hUsub, hU, hx₀⟩ := mem_nhds_iff.mp hnear
  exact ⟨Q, hQ, U, hU, hx₀, fun x hx => hUsub hx⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Complementary coordinate operators are continuous at a parameter where the operator
family is continuous and the fixed complement is valid. -/
theorem ContinuousAt.quotientRangeCoordinate [TopologicalSpace X] [CompleteSpace (E × G)]
    {A : X → E →L[𝕜] F} {x : X} (hA : ContinuousAt A x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContinuousAt (fun y => (A y).quotientRangeCoordinate B) x := by
  have hcop : ContinuousAt (fun y => (A y).coprod B) x :=
    hA.continuousLinearMapCoprod continuousAt_const
  have hi : ContinuousAt (fun y => ((A y).coprod B).inverse) x :=
    (h.contDiffAt_map_inverse (n := 0)).continuousAt.comp
      (f := fun y => (A y).coprod B) hcop
  simpa only [ContinuousLinearMap.quotientRangeCoordinate_def] using
    (continuousAt_const (y := ContinuousLinearMap.snd 𝕜 E G)).clm_comp hi

/-- A continuous operator family with a fixed valid complement has continuous
complementary coordinate operators. The parameter space need only be topological, and no
completeness is needed because every coproduct is invertible: the inverses are controlled by the
resolvent identity `g y - g x = g y (f x - f y) g x`. -/
theorem Continuous.quotientRangeCoordinate [TopologicalSpace X]
    {A : X → E →L[𝕜] F} (hA : Continuous A) (B : G →L[𝕜] F)
    (h : ∀ x, ((A x).coprod B).IsInvertible) :
    Continuous (fun x => (A x).quotientRangeCoordinate B) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  set f : X → E × G →L[𝕜] F := fun y => (A y).coprod B with hfdef
  set g : X → F →L[𝕜] E × G := fun y => (f y).inverse with hgdef
  have hf : ContinuousAt f x₀ := hA.continuousAt.continuousLinearMapCoprod continuousAt_const
  have hfn : Filter.Tendsto (fun y => ‖f y - f x₀‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hf
  have hsmall : ∀ᶠ y in 𝓝 x₀, ‖f y - f x₀‖ * ‖g x₀‖ ≤ 1 / 2 := by
    have := hfn.mul_const ‖g x₀‖
    rw [zero_mul] at this
    exact (this.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ => le_of_lt
  have hg : ContinuousAt g x₀ := by
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hfn.const_mul (2 * ‖g x₀‖ ^ 2))
    filter_upwards [hsmall] with y hy
    have hsub : g y - g x₀ = g y ∘L (f x₀ - f y) ∘L g x₀ := by
      ext v : 1
      have h1 : g y (f y (g x₀ v)) = g x₀ v := (h y).inverse_apply_self _
      have h2 : f x₀ (g x₀ v) = v := (h x₀).self_apply_inverse v
      have e : (f x₀ - f y) (g x₀ v) = v - f y (g x₀ v) := by
        rw [sub_apply, h2]
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, e, map_sub, h1,
        sub_apply]
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
    have h2 : ‖g y‖ ≤ 2 * ‖g x₀‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hy ha0]
    calc ‖g y - g x₀‖ ≤ ‖g y‖ * (‖f y - f x₀‖ * ‖g x₀‖) := by rw [← mul_assoc]; exact he
      _ ≤ (2 * ‖g x₀‖) * (‖f y - f x₀‖ * ‖g x₀‖) := mul_le_mul_of_nonneg_right h2 hdc
      _ = 2 * ‖g x₀‖ ^ 2 * ‖f y - f x₀‖ := by ring
  simpa only [ContinuousLinearMap.quotientRangeCoordinate_def] using
    (continuousAt_const (y := ContinuousLinearMap.snd 𝕜 E G)).clm_comp hg
