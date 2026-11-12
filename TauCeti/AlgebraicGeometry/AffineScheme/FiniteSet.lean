/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Spectrum.Prime.FiniteSet
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Basic open neighborhoods in affine opens

A finite subset of an open inside an affine chart can be enclosed in one basic open of that
chart, while staying inside the prescribed open.
-/

public section

namespace AlgebraicGeometry

/-- A finite set in an open subset of an affine open lies in a single basic open
contained in that subset. -/
theorem IsAffineOpen.exists_basicOpen_le_of_finite {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) {O : X.Opens} (hO : O ≤ U) {s : Set X} (hs : s.Finite)
    (hsO : s ⊆ O) : ∃ r : Γ(X, U), s ⊆ X.basicOpen r ∧ X.basicOpen r ≤ O := by
  obtain ⟨r, hsr, hrO⟩ := PrimeSpectrum.exists_basicOpen_le_of_finite
    (hU.fromSpec ⁻¹ᵁ O).isOpen (hs.preimage hU.fromSpec.isOpenEmbedding.injective.injOn)
    (Set.preimage_mono hsO)
  refine ⟨r, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hO (hsO hx)
    rw [SetLike.mem_coe, ← Scheme.Hom.mem_preimage, hU.fromSpec_preimage_basicOpen]
    exact hsr hx
  · rw [← hU.fromSpec_image_basicOpen]
    rintro _ ⟨y, hy, rfl⟩
    exact hrO hy

end AlgebraicGeometry
