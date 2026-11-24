/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.InnerProductSpace.QuaternionicStructure
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# The modular conjugation of a tracial functional

Let `f` be a tracial positive functional on a possibly nonunital C⋆-algebra `A`,
`f (a * b) = f (b * a)`. On the GNS space `L²(A, f)` the classes `[a]` of `a` and `[a⋆]` of `a⋆`
have the same norm, `f (a⋆ a) = f (a a⋆)`, so `[a] ↦ [a⋆]` extends to a conjugate-linear isometry
`J` of the GNS space, the *modular conjugation*. It is an involution, it is antiunitary,
`⟪J x, J y⟫ = ⟪y, x⟫`, and for unital `A` it fixes the cyclic vector `Ω = [1]`. Conjugating the
GNS representation by `J` gives right multiplication: `J π(a) J [b] = [b a⋆]`.

## Main definitions

* `PositiveLinearMap.gnsConj f hf`: the modular conjugation `[a] ↦ [a⋆]`, a conjugate-linear
  isometric equivalence `f.GNS ≃ₗᵢ⋆[ℂ] f.GNS`.

## Main results

* `PositiveLinearMap.gnsConj_toGNS`, `PositiveLinearMap.gnsConj_coe_toPreGNS`: `J [a] = [a⋆]`.
* `PositiveLinearMap.gnsConj_gnsConj`, `PositiveLinearMap.gnsConj_symm`: `J` is an involution.
* `PositiveLinearMap.inner_gnsConj_gnsConj`: `⟪J x, J y⟫ = ⟪y, x⟫`.
* `PositiveLinearMap.gnsConj_gnsVector`: `J Ω = Ω`.
* `PositiveLinearMap.gnsConj_gnsNonUnitalStarAlgHom_gnsConj_toGNS`: `J π(a) J [b] = [b a⋆]`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), Chapter 2, for the GNS representation of a tracial state.
-/

public section

open UniformSpace
open scoped ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ)

/-- The conjugation `a ↦ a⋆` of the pre-GNS space of a tracial functional, a conjugate-linear
isometric involution. -/
private noncomputable def preGNSConj (hf : ∀ a b, f (a * b) = f (b * a)) :
    f.PreGNS ≃ₗᵢ⋆[ℂ] f.PreGNS where
  toFun x := f.toPreGNS (star (f.ofPreGNS x))
  invFun x := f.toPreGNS (star (f.ofPreGNS x))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  left_inv _ := by simp
  right_inv _ := by simp
  norm_map' x := by simp [preGNS_norm_def, hf (f.ofPreGNS x)]

/-- The **modular conjugation** of a tracial positive functional `f`: the conjugate-linear
isometric involution of the GNS space extending `[a] ↦ [a⋆]`. -/
noncomputable def gnsConj (hf : ∀ a b, f (a * b) = f (b * a)) : f.GNS ≃ₗᵢ⋆[ℂ] f.GNS :=
  (preGNSConj f hf).completion

variable (hf : ∀ a b, f (a * b) = f (b * a))

/-- The modular conjugation sends the class of `a` to the class of `a⋆`. -/
@[simp]
theorem gnsConj_coe_toPreGNS (a : A) :
    gnsConj f hf (f.toPreGNS a : f.GNS) = (f.toPreGNS (star a) : f.GNS) :=
  LinearIsometryEquiv.completion_apply_coe _ (f.toPreGNS a)

/-- The modular conjugation sends the class of `a` to the class of `a⋆`, in terms of the class
map `f.toGNS`. -/
-- Not a simp lemma: `toGNS_apply` already rewrites the class map to the completion embedding.
theorem gnsConj_toGNS (a : A) : gnsConj f hf (f.toGNS a) = f.toGNS (star a) := by
  simp

/-- The modular conjugation is its own inverse. -/
@[simp]
theorem gnsConj_symm : (gnsConj f hf).symm = gnsConj f hf :=
  LinearIsometryEquiv.completion_symm (preGNSConj f hf)

/-- The modular conjugation is an involution. -/
@[simp]
theorem gnsConj_gnsConj (x : f.GNS) : gnsConj f hf (gnsConj f hf x) = x := by
  simpa only [gnsConj_symm] using (gnsConj f hf).apply_symm_apply x

/-- The modular conjugation is antiunitary: `⟪J x, J y⟫ = ⟪y, x⟫`. -/
@[simp]
theorem inner_gnsConj_gnsConj (x y : f.GNS) :
    inner ℂ (gnsConj f hf x) (gnsConj f hf y) = inner ℂ y x :=
  ((gnsConj f hf).toLinearIsometry.inner_map_map_eq_conj x y).trans (inner_conj_symm y x)

/-- Conjugating the GNS representation by the modular conjugation gives right multiplication by
the adjoint: `J π(a) J [b] = [b a⋆]`. -/
theorem gnsConj_gnsNonUnitalStarAlgHom_gnsConj_toGNS (a b : A) :
    gnsConj f hf (f.gnsNonUnitalStarAlgHom a (gnsConj f hf (f.toGNS b))) =
      f.toGNS (b * star a) := by
  rw [gnsConj_toGNS, gnsNonUnitalStarAlgHom_apply_toGNS, gnsConj_toGNS, star_mul, star_star]

/-- For a unital algebra, the modular conjugation fixes the cyclic vector `Ω = [1]`. -/
@[simp]
theorem gnsConj_gnsVector {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : B →ₚ[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a)) :
    gnsConj f hf f.gnsVector = f.gnsVector := by
  have h : f.gnsVector = f.toGNS 1 := by simp [gnsVector_def]
  rw [h, gnsConj_toGNS, star_one]

end PositiveLinearMap
