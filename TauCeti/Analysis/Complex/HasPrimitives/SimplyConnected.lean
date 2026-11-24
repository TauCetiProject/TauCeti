/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.Analysis.Complex.HasPrimitives.Local
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive.SimplyConnected

/-!
# Holomorphic functions on simply connected domains have primitives

Mathlib's `DifferentiableOn.isExactOn_ball` gives a holomorphic function on a disc, with values in
a complete complex normed space, a primitive there. This file extends it to every simply connected
open set `Ω ⊆ ℂ` (`DifferentiableOn.isExactOn_of_isSimplyConnected`), every open set whose
connected components are simply connected
(`DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn`), and continuous
conservative functions (`Complex.IsConservativeOn.isExactOn_of_isSimplyConnected`,
`Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn`).

The real `1`-form `v ↦ v • f z` on each connected component has local primitives on discs by
`DifferentiableOn.isExactOn_ball`
(`TauCeti.hasLocalPrimitivesOn_toSpanSingleton_iff_differentiableOn`). A `1`-form with local
primitives on a simply connected manifold has a global primitive
(`TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn`), which gives a complex
primitive of `f` on `Ω`.

## Main results

* `DifferentiableOn.isExactOn_of_isSimplyConnected`: a holomorphic function on a simply connected
  open subset of `ℂ`, with values in a complete complex normed space, has a primitive there.
* `DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn`: a holomorphic function on
  an open subset of `ℂ` whose connected components are simply connected has a primitive there.
* `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected` and
  `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn`: Morera's theorem
  on simply connected open sets and open sets with simply connected components.

## References

* Walter Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.11 (a holomorphic function on a
  simply connected plane region has a primitive).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 8, Section 1 (monodromy and primitives on
  simply connected regions).
-/

public section

open Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every holomorphic function on an open subset `s ⊆ ℂ` whose connected components are all simply
connected (with complete coefficients) has a complex primitive on `s`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s)
    (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s := by
  have hloc :=
    (TauCeti.hasLocalPrimitivesOn_toSpanSingleton_iff_differentiableOn hs).mpr hf
  obtain ⟨g, hg⟩ :=
    TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn hs hsc hloc
  exact ⟨g, (TauCeti.isPrimitiveOn_toSpanSingleton_iff.mp hg).2⟩

/-- **Holomorphic functions on simply connected domains have primitives.** A holomorphic function
on a simply connected open set `Ω ⊆ ℂ`, with values in a complete complex normed space, has a
primitive on `Ω`. This extends `DifferentiableOn.isExactOn_ball` from discs to simply connected
domains. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected [CompleteSpace F] {f : ℂ → F}
    {Ω : Set ℂ} (hf : DifferentiableOn ℂ f Ω) (hΩ : IsOpen Ω) (hΩc : IsSimplyConnected Ω) :
    Complex.IsExactOn f Ω :=
  hf.isExactOn_of_isSimplyConnected_connectedComponentIn hΩ
    fun _ hz ↦ (hΩc.isPathConnected.isConnected.isPreconnected.connectedComponentIn hz).symm ▸ hΩc

/-- **Morera's theorem on simply connected domains.** A continuous function on a simply connected
open subset `s ⊆ ℂ` whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hf : Complex.IsConservativeOn f s) (hfc : ContinuousOn f s)
    (hs : IsOpen s) (hsc : IsSimplyConnected s) : Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected hs hsc

/-- A continuous function on an open subset `s ⊆ ℂ` whose connected components are simply connected
and whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    [CompleteSpace F] {f : ℂ → F} {s : Set ℂ} (hf : Complex.IsConservativeOn f s)
    (hfc : ContinuousOn f s) (hs : IsOpen s)
    (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected_connectedComponentIn hs hsc
