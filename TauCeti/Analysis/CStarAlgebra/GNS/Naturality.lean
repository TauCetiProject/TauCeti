/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness

/-!
# Naturality of the GNS construction

For a unital star isomorphism `θ : A ≃⋆ₐ[ℂ] B` of unital C⋆-algebras and a positive functional `τ`
on `B`, the GNS data of `τ ∘ θ` and of `τ` are unitarily equivalent through `â ↦ (θ a)^`. The
representation `a ↦ π_τ(θ a)` of `A` on the GNS space of `τ`, with the GNS vector of `τ`, is a
cyclic vector realization of `τ ∘ θ`, so `PositiveLinearMap.gnsEquiv` gives the unitary. It
intertwines `π_{τ ∘ θ}(a)` with `π_τ(θ a)` and preserves the GNS vectors. Tracial states are the
case of interest, but neither the trace property nor normalization is used.

## Main definitions

* `PositiveLinearMap.gnsEquivComp`: the unitary from the GNS space of `τ ∘ θ` to that of `τ`.

## Main statements

* `PositiveLinearMap.gnsEquivComp_apply_coe`: it sends `â` to `(θ a)^`.
* `PositiveLinearMap.gnsEquivComp_intertwines`: it intertwines the GNS representations.
* `PositiveLinearMap.gnsEquivComp_gnsVector`: it preserves the GNS vectors.
* `PositiveLinearMap.gnsEquivComp_unique`: it is determined by `â ↦ (θ a)^`.
-/

public section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace PositiveLinearMap

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (θ : A ≃⋆ₐ[ℂ] B)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The GNS vector of `τ` is cyclic for the representation `a ↦ π_τ(θ a)` of `A`. -/
theorem denseRange_gnsStarAlgHom_comp_gnsVector :
    DenseRange fun a : A => (τ.gnsStarAlgHom.comp θ.toStarAlgHom).toNonUnitalStarAlgHom a
      τ.gnsVector := by
  have h : DenseRange ((fun b : B => τ.gnsStarAlgHom b τ.gnsVector) ∘ θ) := by
    rw [DenseRange, (EquivLike.surjective θ).range_comp]
    exact τ.denseRange_gnsStarAlgHom_gnsVector
  exact h

/-- The GNS vector of `τ` realizes `τ ∘ θ` through the representation `a ↦ π_τ(θ a)`. -/
theorem inner_gnsVector_gnsStarAlgHom_comp (a : A) :
    ⟪τ.gnsVector, (τ.gnsStarAlgHom.comp θ.toStarAlgHom).toNonUnitalStarAlgHom a
      τ.gnsVector⟫_ℂ = (τ.comp (PositiveLinearMap.ofClass θ)) a := by
  simp
  rfl

/-- **Naturality of GNS.** For a unital star isomorphism `θ : A ≃⋆ₐ[ℂ] B` and a positive functional
`τ` on `B`, the GNS space of `τ ∘ θ` is unitarily equivalent to that of `τ` through
`â ↦ (θ a)^`, the unitary `PositiveLinearMap.gnsEquiv` of the cyclic realization
`a ↦ π_τ(θ a)` with vector the GNS vector of `τ`. -/
def gnsEquivComp : (τ.comp (PositiveLinearMap.ofClass θ)).GNS ≃ₗᵢ[ℂ] τ.GNS :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv
    (τ.gnsStarAlgHom.comp θ.toStarAlgHom).toNonUnitalStarAlgHom τ.gnsVector
    (τ.denseRange_gnsStarAlgHom_comp_gnsVector θ) (τ.inner_gnsVector_gnsStarAlgHom_comp θ)

/-- The naturality unitary sends the class of `a` to the class of `θ a`. -/
@[simp]
theorem gnsEquivComp_apply_coe (a : A) :
    τ.gnsEquivComp θ ((τ.comp (PositiveLinearMap.ofClass θ)).toPreGNS a :
      (τ.comp (PositiveLinearMap.ofClass θ)).GNS) = (τ.toPreGNS (θ a) : τ.GNS) := by
  rw [gnsEquivComp, gnsEquiv_apply_coe]
  simp

/-- The naturality unitary intertwines `π_{τ ∘ θ}(a)` with `π_τ(θ a)`. -/
@[simp]
theorem gnsEquivComp_intertwines (a : A) (v : (τ.comp (PositiveLinearMap.ofClass θ)).GNS) :
    τ.gnsEquivComp θ ((τ.comp (PositiveLinearMap.ofClass θ)).gnsNonUnitalStarAlgHom a v) =
      τ.gnsNonUnitalStarAlgHom (θ a) (τ.gnsEquivComp θ v) :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv_intertwines
    (τ.gnsStarAlgHom.comp θ.toStarAlgHom).toNonUnitalStarAlgHom τ.gnsVector _ _ a v

/-- The naturality unitary sends the GNS vector of `τ ∘ θ` to that of `τ`. -/
@[simp]
theorem gnsEquivComp_gnsVector :
    τ.gnsEquivComp θ (τ.comp (PositiveLinearMap.ofClass θ)).gnsVector = τ.gnsVector :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv_apply_gnsVector
    (τ.gnsStarAlgHom.comp θ.toStarAlgHom) τ.gnsVector _ _

/-- The naturality unitary is the only unitary sending the class of `a` to the class of `θ a`. -/
theorem gnsEquivComp_unique (U : (τ.comp (PositiveLinearMap.ofClass θ)).GNS ≃ₗᵢ[ℂ] τ.GNS)
    (hU : ∀ a, U ((τ.comp (PositiveLinearMap.ofClass θ)).toGNS a) = τ.toGNS (θ a)) :
    U = τ.gnsEquivComp θ :=
  (τ.comp (PositiveLinearMap.ofClass θ)).gnsEquiv_unique _ _ _ _ U fun a => by
    simpa [toGNS_apply] using hU a

end PositiveLinearMap
