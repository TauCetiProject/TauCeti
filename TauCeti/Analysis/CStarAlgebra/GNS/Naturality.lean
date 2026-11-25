/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness
public import TauCeti.Algebra.Order.Module.PositiveLinearMap

/-!
# Naturality of the GNS construction

For a surjective unital star homomorphism `θ : A →⋆ₐ[ℂ] B` of unital C⋆-algebras and a positive
functional `τ` on `B`, the GNS data of `τ ∘ θ` and of `τ` are unitarily equivalent through
`â ↦ (θ a)^`. A unital star isomorphism `θ : A ≃⋆ₐ[ℂ] B` is the case `θ.toStarAlgHom`,
`θ.surjective`. The representation `a ↦ π_τ(θ a)` of `A` on the GNS space of `τ`, with the GNS
vector of `τ`, is a cyclic vector realization of `τ ∘ θ`, so `PositiveLinearMap.gnsEquiv` gives
the unitary. It intertwines `π_{τ ∘ θ}(a)` with `π_τ(θ a)` and preserves the GNS vectors. Tracial
states are the case of interest, but neither the trace property nor normalization is used.

## Main definitions

* `PositiveLinearMap.gnsEquivComp`: the unitary from the GNS space of `τ ∘ θ` to that of `τ`.

## Main statements

* `PositiveLinearMap.gnsEquivComp_apply_coe`: it sends `â` to `(θ a)^`.
* `PositiveLinearMap.gnsEquivComp_intertwines`: it intertwines the GNS representations.
* `PositiveLinearMap.gnsEquivComp_gnsVector`: it preserves the GNS vectors.
* `PositiveLinearMap.gnsEquivComp_unique`: it is determined by `â ↦ (θ a)^`.

The `symm` versions of the first three describe the inverse unitary.
-/

public section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace PositiveLinearMap

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (θ : A →⋆ₐ[ℂ] B) (hθ : Function.Surjective θ)

omit [PartialOrder A] [StarOrderedRing A] in
include hθ in
/-- The GNS vector of `τ` is cyclic for the representation `a ↦ π_τ(θ a)` of `A`. -/
theorem denseRange_gnsStarAlgHom_comp_gnsVector :
    DenseRange fun a : A => (τ.gnsStarAlgHom.comp θ).toNonUnitalStarAlgHom a τ.gnsVector := by
  have h := τ.denseRange_gnsStarAlgHom_gnsVector
  rw [DenseRange, ← hθ.range_comp] at h
  simpa [DenseRange, Function.comp_def] using h

/-- The GNS vector of `τ` realizes `τ ∘ θ` through the representation `a ↦ π_τ(θ a)`. -/
theorem inner_gnsVector_gnsStarAlgHom_comp (a : A) :
    ⟪τ.gnsVector, (τ.gnsStarAlgHom.comp θ).toNonUnitalStarAlgHom a τ.gnsVector⟫_ℂ =
      (τ.comp (PositiveLinearMap.ofClass θ)) a := by
  simp

/-- **Naturality of GNS.** For a surjective unital star homomorphism `θ : A →⋆ₐ[ℂ] B` and a
positive functional `τ` on `B`, the GNS space of `τ ∘ θ` is unitarily equivalent to that of `τ`
through `â ↦ (θ a)^`, the unitary `PositiveLinearMap.gnsEquiv` of the cyclic realization
`a ↦ π_τ(θ a)` with vector the GNS vector of `τ`. For a unital star isomorphism `θ`, take
`θ.toStarAlgHom` and `θ.surjective`. -/
def gnsEquivComp : (τ.comp (PositiveLinearMap.ofClass θ)).GNS ≃ₗᵢ[ℂ] τ.GNS :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv
    (τ.gnsStarAlgHom.comp θ).toNonUnitalStarAlgHom τ.gnsVector
    (τ.denseRange_gnsStarAlgHom_comp_gnsVector θ hθ) (τ.inner_gnsVector_gnsStarAlgHom_comp θ)

/-- The naturality unitary sends the class of `a` to the class of `θ a`. -/
@[simp]
theorem gnsEquivComp_apply_coe (a : A) :
    τ.gnsEquivComp θ hθ ((τ.comp (PositiveLinearMap.ofClass θ)).toPreGNS a :
      (τ.comp (PositiveLinearMap.ofClass θ)).GNS) = (τ.toPreGNS (θ a) : τ.GNS) := by
  rw [gnsEquivComp, gnsEquiv_apply_coe]
  simp

/-- The naturality unitary intertwines `π_{τ ∘ θ}(a)` with `π_τ(θ a)`. -/
@[simp]
theorem gnsEquivComp_intertwines (a : A) (v : (τ.comp (PositiveLinearMap.ofClass θ)).GNS) :
    τ.gnsEquivComp θ hθ ((τ.comp (PositiveLinearMap.ofClass θ)).gnsNonUnitalStarAlgHom a v) =
      τ.gnsNonUnitalStarAlgHom (θ a) (τ.gnsEquivComp θ hθ v) := by
  rw [gnsEquivComp, gnsEquiv_intertwines]
  simp

/-- The naturality unitary sends the GNS vector of `τ ∘ θ` to that of `τ`. -/
@[simp]
theorem gnsEquivComp_gnsVector :
    τ.gnsEquivComp θ hθ (τ.comp (PositiveLinearMap.ofClass θ)).gnsVector = τ.gnsVector :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv_apply_gnsVector
    (τ.gnsStarAlgHom.comp θ) τ.gnsVector _ _

/-- The inverse naturality unitary sends the class of `θ a` to the class of `a`. -/
@[simp]
theorem gnsEquivComp_symm_apply_coe (a : A) :
    (τ.gnsEquivComp θ hθ).symm (τ.toPreGNS (θ a) : τ.GNS) =
      ((τ.comp (PositiveLinearMap.ofClass θ)).toPreGNS a :
        (τ.comp (PositiveLinearMap.ofClass θ)).GNS) := by
  rw [LinearIsometryEquiv.symm_apply_eq, gnsEquivComp_apply_coe]

/-- The inverse naturality unitary intertwines `π_τ(θ a)` with `π_{τ ∘ θ}(a)`. -/
@[simp]
theorem gnsEquivComp_symm_intertwines (a : A) (w : τ.GNS) :
    (τ.gnsEquivComp θ hθ).symm (τ.gnsNonUnitalStarAlgHom (θ a) w) =
      (τ.comp (PositiveLinearMap.ofClass θ)).gnsNonUnitalStarAlgHom a
        ((τ.gnsEquivComp θ hθ).symm w) := by
  rw [LinearIsometryEquiv.symm_apply_eq, gnsEquivComp_intertwines,
    LinearIsometryEquiv.apply_symm_apply]

/-- The inverse naturality unitary sends the GNS vector of `τ` to that of `τ ∘ θ`. -/
@[simp]
theorem gnsEquivComp_symm_gnsVector :
    (τ.gnsEquivComp θ hθ).symm τ.gnsVector = (τ.comp (PositiveLinearMap.ofClass θ)).gnsVector := by
  rw [LinearIsometryEquiv.symm_apply_eq, gnsEquivComp_gnsVector]

/-- The naturality unitary is the only unitary sending the class of `a` to the class of `θ a`. -/
theorem gnsEquivComp_unique (U : (τ.comp (PositiveLinearMap.ofClass θ)).GNS ≃ₗᵢ[ℂ] τ.GNS)
    (hU : ∀ a, U ((τ.comp (PositiveLinearMap.ofClass θ)).toGNS a) = τ.toGNS (θ a)) :
    U = τ.gnsEquivComp θ hθ :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv_unique _ _ _ _ U fun a => by
    simpa [toGNS_apply] using hU a

end PositiveLinearMap
