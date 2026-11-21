/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import TauCeti.Geometry.Manifold.DeRham.SimplyConnected
import TauCeti.Analysis.Complex.HasPrimitives.Local

/-!
# Primitives of holomorphic functions on simply connected domains

This file deduces global primitives on simply connected open subsets of `ℂ` (and open subsets whose
connected components are simply connected) for holomorphic functions and continuous conservative
functions, via the correspondence between complex primitives and real `1`-form primitives in
`TauCeti.Analysis.Complex.HasPrimitives.Local`.

## Main declarations

* `DifferentiableOn.isExactOn_of_isSimplyConnected` and
  `DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn` -- global primitives of
  holomorphic functions on simply connected open sets in `ℂ` and on open sets whose connected
  components are simply connected.
* `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected` and
  `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn` -- Morera's
  theorem on simply connected open sets and open sets with simply connected components.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 8, Section 1 (monodromy and primitives on
  simply connected regions).
-/

public section

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

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
