/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import TauCeti.Geometry.Manifold.DeRham.SimplyConnected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Primitives of holomorphic functions on discs and simply connected domains

Mathlib's `DifferentiableOn.isExactOn_ball` gives every holomorphic function on a disc a
primitive there. This file records:

* gluing from a convex part of a disc to the whole disc
  (`DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter`);
* exactness of `z ↦ z⁻¹` on `Complex.slitPlane` via `Complex.log`
  (`TauCeti.isExactOn_inv_slitPlane`);
* the correspondence between complex primitives of `f` and real `1`-form primitives of `f(z) dz`
  (`TauCeti.isPrimitiveOn_toSpanSingleton_iff`,
  `TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn`);
* global primitives of holomorphic (or conservative continuous) functions on simply connected open
  sets in `ℂ`, and more generally on open sets whose connected components are simply connected
  (`DifferentiableOn.isExactOn_of_isSimplyConnected`,
  `DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn`,
  `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected`).

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, Sections 4.4 and 4.6, and Chapter 8,
  Section 1 (monodromy and primitives on simply connected regions).
-/

public section

open Complex Metric Set
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function `g : ℂ → E` is a primitive of the real `1`-form `z ↦ (v ↦ v • f z)` on `s` if and
only if `s` is open and `g` has complex derivative `f z` at every `z ∈ s`. -/
theorem TauCeti.isPrimitiveOn_toSpanSingleton_iff {f g : ℂ → E} {s : Set ℂ} :
    TauCeti.IsPrimitiveOn (I := 𝓘(ℝ, ℂ))
        ((fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ E (0 : Fin 1)
          ((ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ)) :
            TauCeti.RoughForm 𝓘(ℝ, ℂ) ℂ E 1) g s ↔
      IsOpen s ∧ ∀ z ∈ s, HasDerivAt g (f z) z := by
  rw [TauCeti.isPrimitiveOn_ofSubsingleton_iff]
  simp only [← TauCeti.hasDerivAt_iff_hasFDerivAt_restrictScalars]

variable [CompleteSpace E]

/-- On an open subset `s ⊆ ℂ` with complete coefficients `E`, the real `1`-form
`z ↦ (v ↦ v • f z)` admits local primitives on `s` if and only if `f` is holomorphic on `s`. -/
theorem TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn
    {f : ℂ → E} {s : Set ℂ} (hs : IsOpen s) :
    (∀ z ∈ s, ∃ (g : ℂ → E) (U : Set ℂ), z ∈ U ∧
      TauCeti.IsPrimitiveOn (I := 𝓘(ℝ, ℂ))
        ((fun w ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ E (0 : Fin 1)
          ((ContinuousLinearMap.toSpanSingleton ℂ (f w)).restrictScalars ℝ)) :
            TauCeti.RoughForm 𝓘(ℝ, ℂ) ℂ E 1) g U) ↔
      DifferentiableOn ℂ f s := by
  constructor
  · intro h z hz
    obtain ⟨g, U, hzU, hgU⟩ := h z hz
    rw [TauCeti.isPrimitiveOn_toSpanSingleton_iff] at hgU
    have hdiff : DifferentiableOn ℂ f U :=
      Complex.IsExactOn.differentiableOn hgU.1 ⟨g, hgU.2⟩
    exact ((hdiff z hzU).differentiableAt (hgU.1.mem_nhds hzU)).differentiableWithinAt
  · intro hf z hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs z hz
    obtain ⟨g, hg⟩ := (hf.mono hball).isExactOn_ball
    exact ⟨g, ball z r, mem_ball_self hr,
      TauCeti.isPrimitiveOn_toSpanSingleton_iff.mpr ⟨isOpen_ball, hg⟩⟩

/-- **Primitives on simply connected domains.** Every holomorphic function on a simply connected
open subset `s ⊆ ℂ` with complete coefficients has a complex primitive on `s`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected {f : ℂ → E} {s : Set ℂ}
    (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) (hsc : IsSimplyConnected s) :
    Complex.IsExactOn f s := by
  have hloc :=
    (TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn hs).mpr hf
  obtain ⟨g, hg⟩ := TauCeti.exists_isPrimitiveOn_of_isSimplyConnected hs hsc hloc
  exact ⟨g, (TauCeti.isPrimitiveOn_toSpanSingleton_iff.mp hg).2⟩

/-- Every holomorphic function on an open subset `s ⊆ ℂ` whose connected components are all simply
connected (with complete coefficients) has a complex primitive on `s`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn {f : ℂ → E}
    {s : Set ℂ} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s)
    (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s := by
  have hloc :=
    (TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn hs).mpr hf
  obtain ⟨g, hg⟩ :=
    TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn hs hsc hloc
  exact ⟨g, (TauCeti.isPrimitiveOn_toSpanSingleton_iff.mp hg).2⟩

/-- **Morera's theorem on simply connected domains.** A continuous function on a simply connected
open subset `s ⊆ ℂ` whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected {f : ℂ → E} {s : Set ℂ}
    (hf : Complex.IsConservativeOn f s) (hfc : ContinuousOn f s) (hs : IsOpen s)
    (hsc : IsSimplyConnected s) : Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected hs hsc

/-- A continuous function on an open subset `s ⊆ ℂ` whose connected components are simply connected
and whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    {f : ℂ → E} {s : Set ℂ} (hf : Complex.IsConservativeOn f s) (hfc : ContinuousOn f s)
    (hs : IsOpen s) (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected_connectedComponentIn hs hsc

/-- A holomorphic integrand `g` on a disc has a primitive on the disc agreeing with any given
primitive `f` of `g` on the intersection of the disc with a convex set `U`. -/
theorem DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter {f g : ℂ → E} {c : ℂ} {r : ℝ}
    {U : Set ℂ} (hg : DifferentiableOn ℂ g (ball c r)) (hU : Convex ℝ U)
    (hf : ∀ z ∈ ball c r ∩ U, HasDerivWithinAt f (g z) (ball c r ∩ U) z) :
    ∃ G : ℂ → E, (∀ z ∈ ball c r, HasDerivAt G (g z) z) ∧ EqOn G f (ball c r ∩ U) := by
  obtain ⟨P, hP⟩ := hg.isExactOn_ball
  rcases (ball c r ∩ U).eq_empty_or_nonempty with hV | ⟨z₀, hz₀⟩
  · exact ⟨P, hP, by simp [hV]⟩
  refine ⟨fun z ↦ P z + (f z₀ - P z₀), fun z hz ↦ (hP z hz).add_const _, fun z hz ↦ ?_⟩
  have hderiv (w) (hw : w ∈ ball c r ∩ U) :
      HasDerivWithinAt (f - P) 0 (ball c r ∩ U) w := by
    simpa using (hf w hw).sub (hP w hw.1).hasDerivWithinAt
  have := ((convex_ball c r).inter hU).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ norm_zero.le) hz₀ hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, Pi.sub_apply, Pi.sub_apply] at this
  simp [← this]

/-- The holomorphic function `z ↦ z⁻¹` has a complex primitive on `Complex.slitPlane`, namely
the principal branch `Complex.log`. -/
theorem TauCeti.isExactOn_inv_slitPlane : Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) Complex.slitPlane :=
  ⟨Complex.log, fun _ hz ↦ Complex.hasDerivAt_log hz⟩
