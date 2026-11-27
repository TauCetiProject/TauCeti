/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution

/-!
# Rescaling the Haar measure of a Hecke algebra

For `c ∈ A` and an `A`-valued Haar measure `μ`, convolution against `c • μ` is `c` times
convolution against `μ` (`TauCeti.HaarMeasureWithValues.convolution_smul_measure`). For a unit `c`,
multiplication by `c` is therefore a ring isomorphism `H(G, cμ) ≃ H(G, μ)` of Hecke algebras
(`TauCeti.HeckeAlgebra.rescaleRingEquiv`): the Hecke algebra does not depend, up to isomorphism, on
the normalisation of the Haar measure.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, pp. 11–12.
-/

public section

namespace TauCeti

variable {A G : Type*} [Group G] [TopologicalSpace G]

namespace HeckeAlgebra

variable [CommSemiring A] [IsTopologicalGroup G] [T2Space G] (μ : HaarMeasureWithValues A G)

/-- **Rescaling the Haar measure by a unit does not change the Hecke algebra**: multiplication by
`c` is a ring isomorphism `H(G, cμ) ≃ H(G, μ)`, since
`(c f₁) ⋆_μ (c f₂) = c (c (f₁ ⋆_μ f₂)) = c (f₁ ⋆_{cμ} f₂)`. -/
noncomputable def rescaleRingEquiv (c : Aˣ) :
    HeckeAlgebra ((c : A) • μ) ≃+* HeckeAlgebra μ where
  toFun f := ⟨(c : A) • f.toCompactlySupported⟩
  invFun f := ⟨((c⁻¹ : Aˣ) : A) • f.toCompactlySupported⟩
  left_inv f := by
    ext1
    simp [smul_smul]
  right_inv f := by
    ext1
    simp [smul_smul]
  map_mul' f₁ f₂ := by
    ext1
    simp [smul_smul]
  map_add' f₁ f₂ := by
    ext1
    simp

/-- `rescaleRingEquiv μ c` multiplies the underlying function by `c`. -/
@[simp]
theorem toCompactlySupported_rescaleRingEquiv (c : Aˣ) (f : HeckeAlgebra ((c : A) • μ)) :
    (rescaleRingEquiv μ c f).toCompactlySupported = (c : A) • f.toCompactlySupported :=
  (rfl)

/-- The inverse of `rescaleRingEquiv μ c` multiplies the underlying function by `c⁻¹`. -/
@[simp]
theorem toCompactlySupported_rescaleRingEquiv_symm (c : Aˣ) (f : HeckeAlgebra μ) :
    ((rescaleRingEquiv μ c).symm f).toCompactlySupported =
      ((c⁻¹ : Aˣ) : A) • f.toCompactlySupported :=
  (rfl)

/-- `rescaleRingEquiv μ c` is `A`-linear. -/
theorem rescaleRingEquiv_smul (c : Aˣ) (a : A) (f : HeckeAlgebra ((c : A) • μ)) :
    rescaleRingEquiv μ c (a • f) = a • rescaleRingEquiv μ c f := by
  ext1
  simp [toCompactlySupported_smul, smul_comm a (c : A)]

end HeckeAlgebra

end TauCeti
