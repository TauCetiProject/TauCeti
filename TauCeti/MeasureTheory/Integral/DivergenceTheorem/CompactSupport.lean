/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.FDeriv.Integral

/-!
# Compactly supported divergence on a vector space

The divergence of a globally `C¹`, compactly supported vector field is integrable and has zero
integral over the whole space: each summand is a directional derivative of a compactly supported
component, so it integrates to zero by
`TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable`.

It also localizes the divergence integral over a set of unique differentiability to a box
containing the part of the support inside that set, which the half-space and quadrant divergence
theorems share.
-/

public section

noncomputable section

open Set

namespace MeasureTheory

/-- Let `f` be `C¹` on a measurable set `s` of unique differentiability, and let the part of its
support inside `s` lie in a box `Icc a b ⊆ s`. Then its divergence within `s` is integrable on the
box and on `s`, and its integrals over both agree. -/
theorem _root_.ContDiffOn.integrableOn_divergence_and_setIntegral_eq_Icc {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → F)} {s : Set (Fin (n + 1) → ℝ)}
    (hf : ContDiffOn ℝ 1 f s) (hs : UniqueDiffOn ℝ s) (hsm : MeasurableSet s)
    {a b : Fin (n + 1) → ℝ} (hab : Icc a b ⊆ s)
    (hsupp : ∀ x ∈ s, x ∈ tsupport f → x ∈ Icc a b) :
    IntegrableOn (fun x ↦ ∑ i : Fin (n + 1),
      fderivWithin ℝ f s x (Pi.single i 1) i) (Icc a b) ∧
    IntegrableOn (fun x ↦ ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i) s ∧
    (∫ x in s, ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i) =
      ∫ x in Icc a b, ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i := by
  let D (x : Fin (n + 1) → ℝ) := ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i
  have hDzero {x : Fin (n + 1) → ℝ} (hx : x ∈ s) (hk : x ∉ Icc a b) : D x = 0 := by
    have hn : x ∉ tsupport f := fun hx' ↦ hk (hsupp x hx hx')
    have hd := (HasFDerivWithinAt.of_notMem_tsupport ℝ (s := s) hn).fderivWithin (hs x hx)
    simp [D, hd]
  have hDc : ContinuousOn D s := by
    apply continuousOn_finsetSum
    intro i _
    exact (continuous_apply i).comp_continuousOn
      ((hf.continuousOn_fderivWithin hs (by simp)).clm_apply continuousOn_const)
  have hDi : IntegrableOn D (Icc a b) := (hDc.mono hab).integrableOn_compact isCompact_Icc
  exact ⟨hDi, hDi.of_forall_sdiff_eq_zero hsm fun x hx ↦ hDzero hx.1 hx.2,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hsm hab fun x hx ↦ hDzero hx.1 hx.2⟩

/-- The divergence of a globally `C¹`, compactly supported coordinate vector field, with
components in a real normed space `F`, is integrable and has zero integral on the whole space. -/
theorem integral_divergence_eq_zero {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → F)}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) ∧
      (∫ x, ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) = 0 := by
  -- Each summand is continuous with compact support, hence integrable.
  have hint (i : Fin (n + 1)) : Integrable fun x ↦ fderiv ℝ f x (Pi.single i 1) i :=
    ((continuous_apply i).comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ _).comp_left rfl)
  refine ⟨integrable_finsetSum _ fun i _ ↦ hint i, ?_⟩
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  -- The `i`-th summand is the derivative of the `i`-th component `x ↦ f x i` in direction
  -- `Pi.single i 1`, whose integral vanishes.
  have h := TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable (μ := volume)
    (D := fun x ↦ (ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) countable_empty
    ((continuous_apply i).comp hf.continuous) (hc.comp_left rfl)
    (fun x _ ↦ hasFDerivAt_pi'.1 (hf.differentiable one_ne_zero x).hasFDerivAt i) (Pi.single i 1)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using h

end MeasureTheory
