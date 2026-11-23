/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Changes of coordinates in equations over groups

A coefficient-preserving word homomorphism acts on tuples by evaluation. When it is bijective,
this action transports solution sets and radicals, and induces an isomorphism of coordinate
groups. The results apply to inconsistent systems and arbitrary coefficient homomorphisms.

A `G`-isomorphism `φ : G[X] ≃* G[Y]` induces a bijection `imageEquivV` between the solutions of a
system `S` and those of its image `φ S`; it carries the radical of `S` to that of `φ S`
(`Rad_image_mulEquiv`) and induces the isomorphism of coordinate groups
`CoordGroup.imageMulEquiv`. More generally, for any equivalent target system `T` with
`V_H(φ S) = V_H(T)`, this induces a solution bijection `equivVOfVImageEq`, carries `Rad ι S` to
`Rad ι T` (`Rad_of_V_image_eq`), and induces a `G`-isomorphism `CoordGroup.mulEquivOfVImageEq`
of radical coordinate groups. Specializing to conjugation in `G[Y]` (`u * φ w * u⁻¹ = w'`) gives
`equivVOfConjMulEquiv`, `Rad_singleton_of_conj_mulEquiv`, and `CoordGroup.mulEquivOfConjMulEquiv`.
The change of coordinates `x ↦ x g` of one variable, a transvection, fixes the commutator equation
`[x, g] = 1`, so it carries its solutions, the centralizer of `ι g`, onto themselves.

## Main definitions

* `TauCeti.GroupAlgGeom.coordinateChangeEquiv`, `TauCeti.GroupAlgGeom.coordinateChangeEquivV`:
  a bijective coefficient-preserving word map gives an equivalence of tuples, restricting to an
  equivalence of solution sets.
* `TauCeti.GroupAlgGeom.CoordGroup.equivOfCoordinateChange`: the induced isomorphism of
  coordinate groups.
* `TauCeti.GroupAlgGeom.imageEquivV`, `TauCeti.GroupAlgGeom.equivVOfVImageEq`,
  `TauCeti.GroupAlgGeom.equivVOfConjMulEquiv`: the bijections of solution sets induced by a
  `G`-isomorphism, to any system with the same algebraic set as `φ S`, and by a `G`-isomorphism
  followed by conjugation.
* `TauCeti.GroupAlgGeom.CoordGroup.imageMulEquiv`,
  `TauCeti.GroupAlgGeom.CoordGroup.mulEquivOfVImageEq`,
  `TauCeti.GroupAlgGeom.CoordGroup.mulEquivOfConjMulEquiv`: the induced isomorphisms of coordinate
  groups.

## Main results

* `TauCeti.GroupAlgGeom.image_coordinateChangeEquiv_V`: a change of coordinates `σ` carries
  `V_H(S)` onto `V_H(σ⁻¹(S))`.
* `TauCeti.GroupAlgGeom.mem_V_image_mulEquiv_iff`,
  `TauCeti.GroupAlgGeom.mem_V_iff_of_V_image_eq`,
  `TauCeti.GroupAlgGeom.mem_V_singleton_iff_of_conj_gHom`: membership in the solutions of the
  image of a system under a `G`-isomorphism, of any system with the same solutions as the image
  under a `G`-homomorphism, and of a single equation under a `G`-homomorphism followed by
  conjugation.
* `TauCeti.GroupAlgGeom.Rad_image_mulEquiv`,
  `TauCeti.GroupAlgGeom.Rad_of_V_image_eq`,
  `TauCeti.GroupAlgGeom.Rad_singleton_of_conj_mulEquiv`: a `G`-isomorphism carries the radical of
  a system to the radical of its image, of any system with the same solutions, and of a conjugate
  of the image of a single equation.
* `TauCeti.GroupAlgGeom.image_transvection_V_singleton_commutatorElement`: the transvection
  `x ↦ x g` carries the solutions of `[x, g] = 1` onto themselves.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.3, Corollary 6, and §3.5: the construction is the
  invertible case of the word-map correspondence.
-/

public section

namespace TauCeti
namespace GroupAlgGeom

open Monoid.Coprod

variable {G H X Y Z : Type*} [Group G] [Group H] (ι : G →* H)

section CoordinateChange

variable (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (hσ : Function.Bijective σ)

include σ hσ

include ι

/-- A bijective coefficient-preserving word map gives an equivalence of tuples. -/
noncomputable def coordinateChangeEquiv : (X → H) ≃ (Y → H) where
  toFun := wordMap ι (fun y => σ (inr (FreeGroup.of y)))
  invFun := wordMap ι (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x)))
  left_inv v := by
    rw [← wordMap_comp, GHom.comp_symmOfBijective]
    simpa only [GHom.coe_id, id_eq] using wordMap_id (ι := ι) v
  right_inv v := by
    rw [← wordMap_comp, GHom.symmOfBijective_comp]
    simpa only [GHom.coe_id, id_eq] using wordMap_id (ι := ι) v

/-- The tuple equivalence applies the word map. -/
@[simp] theorem coordinateChangeEquiv_apply (v : X → H) :
    coordinateChangeEquiv ι σ hσ v =
      wordMap ι (fun y => σ (inr (FreeGroup.of y))) v := by
  simp [coordinateChangeEquiv]

/-- The inverse tuple equivalence applies the inverse word map. -/
@[simp] theorem coordinateChangeEquiv_symm_apply (v : Y → H) :
    (coordinateChangeEquiv ι σ hσ).symm v =
      wordMap ι (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x))) v := by
  simp [coordinateChangeEquiv]

/-- A bijective word map restricts to an equivalence of solution sets. -/
noncomputable def coordinateChangeEquivV (S : Set (GX G X)) :
    V ι S ≃ V ι (σ ⁻¹' S) :=
  (coordinateChangeEquiv ι σ hσ).subtypeEquiv
    (fun v => (wordMap_mem_V_iff ι σ hσ.2 S v).symm)

/-- On tuples, the solution equivalence applies the word map. -/
@[simp] theorem coordinateChangeEquivV_apply_coe (S : Set (GX G X)) (v : V ι S) :
    ((coordinateChangeEquivV ι σ hσ S v : V ι (σ ⁻¹' S)) : Y → H) =
      wordMap ι (fun y => σ (inr (FreeGroup.of y))) v := by
  -- The subtype equivalence applies the tuple equivalence to the underlying value.
  change coordinateChangeEquiv ι σ hσ (v : X → H) = _
  simp

/-- A change of coordinates carries the solutions of `S` onto the solutions of the transformed
system `σ⁻¹(S)`. -/
theorem image_coordinateChangeEquiv_V (S : Set (GX G X)) :
    coordinateChangeEquiv ι σ hσ '' V ι S = V ι (σ ⁻¹' S) := by
  ext v
  rw [Equiv.image_eq_preimage_symm, Set.mem_preimage, ← wordMap_mem_V_iff ι σ hσ.2,
    ← coordinateChangeEquiv_apply ι σ hσ, Equiv.apply_symm_apply]

/-- On tuples, the inverse solution equivalence applies the inverse word map. -/
@[simp] theorem coordinateChangeEquivV_symm_apply_coe
    (S : Set (GX G X)) (v : V ι (σ ⁻¹' S)) :
    (((coordinateChangeEquivV ι σ hσ S).symm v : V ι S) : X → H) =
      wordMap ι (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x))) v := by
  -- The inverse subtype equivalence applies the inverse tuple equivalence to the value.
  change (coordinateChangeEquiv ι σ hσ).symm (v : Y → H) = _
  simp

/-- Radicals transform by inverse image under a bijective coefficient-preserving word map. -/
theorem Rad_preimage (S : Set (GX G X)) :
    Rad ι (σ ⁻¹' S) = (Rad ι S).comap σ.toMonoidHom := by
  refine le_antisymm (Rad_preimage_le_comap ι σ S) ?_
  intro w hw
  rw [mem_Rad]
  intro v hv
  obtain ⟨u, rfl⟩ := (coordinateChangeEquiv ι σ hσ).surjective v
  have hu : u ∈ V ι S := by
    apply (wordMap_mem_V_iff ι σ hσ.2 S u).1
    simpa using hv
  have h := (mem_Rad).1 hw u hu
  rw [coordinateChangeEquiv_apply, eval_wordMap]
  exact h

namespace CoordGroup

/-- A change of coordinates induces an isomorphism from the coordinate group of the
transformed system to that of the original system. -/
noncomputable def equivOfCoordinateChange (S : Set (GX G X)) :
    CoordGroup ι (σ ⁻¹' S) ≃* CoordGroup ι S :=
  QuotientGroup.congr _ _ (MulEquiv.ofBijective σ.toMonoidHom hσ) (by
    rw [Rad_preimage ι σ hσ S]
    exact Subgroup.map_comap_eq_self_of_surjective hσ.2 _)

@[simp]
theorem equivOfCoordinateChange_mk (S : Set (GX G X)) (w : GX G Y) :
    equivOfCoordinateChange ι σ hσ S (w : CoordGroup ι (σ ⁻¹' S)) =
      (σ w : CoordGroup ι S) := by
  simp [equivOfCoordinateChange]

/-- The inverse coordinate-group isomorphism applies the inverse word homomorphism. -/
@[simp]
theorem equivOfCoordinateChange_symm_mk (S : Set (GX G X)) (w : GX G X) :
    (equivOfCoordinateChange ι σ hσ S).symm (w : CoordGroup ι S) =
      ((σ.symmOfBijective hσ) w : CoordGroup ι (σ ⁻¹' S)) := by
  apply (equivOfCoordinateChange ι σ hσ S).injective
  simp

/-- The coordinate-group equivalence has the coefficient-preserving word-map homomorphism
as its underlying homomorphism. -/
theorem equivOfCoordinateChange_toMonoidHom (S : Set (GX G X)) :
    (equivOfCoordinateChange ι σ hσ S).toMonoidHom =
      (homOfWordMap ι σ S).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w => simp

/-- The coordinate-group isomorphism fixes coefficients. -/
theorem equivOfCoordinateChange_coeff (S : Set (GX G X)) (g : G) :
    equivOfCoordinateChange ι σ hσ S (coeff ι (σ ⁻¹' S) g) = coeff ι S g := by
  simp [coeff_apply]

/-- The inverse coordinate-group isomorphism fixes coefficients. -/
theorem equivOfCoordinateChange_symm_coeff (S : Set (GX G X)) (g : G) :
    (equivOfCoordinateChange ι σ hσ S).symm (coeff ι S g) =
      coeff ι (σ ⁻¹' S) g := by
  apply (equivOfCoordinateChange ι σ hσ S).injective
  simp

/-- The coordinate-group isomorphism sends a coordinate `y` of the generic point of the
transformed system to the class of the word `σ y`. -/
@[simp]
theorem equivOfCoordinateChange_genericPoint (S : Set (GX G X)) (y : Y) :
    equivOfCoordinateChange ι σ hσ S (genericPoint ι (σ ⁻¹' S) y) =
      (σ (inr (FreeGroup.of y)) : CoordGroup ι S) := by
  simp [genericPoint_apply]

/-- The inverse coordinate-group isomorphism sends a coordinate `x` of the generic point of the
system to the class of the word `σ⁻¹ x`. -/
@[simp]
theorem equivOfCoordinateChange_symm_genericPoint (S : Set (GX G X)) (x : X) :
    (equivOfCoordinateChange ι σ hσ S).symm (genericPoint ι S x) =
      ((σ.symmOfBijective hσ) (inr (FreeGroup.of x)) : CoordGroup ι (σ ⁻¹' S)) := by
  simp [genericPoint_apply]

/-- The coordinate-group isomorphism sends the generic point of the transformed system to the
image of the generic point of the system under the word map of `σ`. -/
@[simp]
theorem equivOfCoordinateChange_comp_genericPoint (S : Set (GX G X)) :
    ⇑(equivOfCoordinateChange ι σ hσ S) ∘ genericPoint ι (σ ⁻¹' S) =
      wordMap (coeff ι S) (fun y => σ (inr (FreeGroup.of y))) (genericPoint ι S) := by
  funext y
  simp

/-- The inverse coordinate-group isomorphism sends the generic point of the system to the image
of the generic point of the transformed system under the word map of `σ⁻¹`. -/
@[simp]
theorem equivOfCoordinateChange_symm_comp_genericPoint (S : Set (GX G X)) :
    ⇑(equivOfCoordinateChange ι σ hσ S).symm ∘ genericPoint ι S =
      wordMap (coeff ι (σ ⁻¹' S)) (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x)))
        (genericPoint ι (σ ⁻¹' S)) := by
  funext x
  simp

end CoordGroup

end CoordinateChange

/-! ### `G`-isomorphisms -/

section MulEquiv

variable (φ : GX G X ≃* GX G Y) (hφ : ∀ g, φ (inl g) = inl g)

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` induces a bijection between the solutions of a system
`S` and the solutions of its image `φ S`: a solution `v` of `S` goes to the point with
coordinates the values at `v` of the words `φ⁻¹ y`. -/
noncomputable def imageEquivV (S : Set (GX G X)) : V ι S ≃ V ι (φ '' S) :=
  (coordinateChangeEquivV ι (GHom.ofMulEquiv φ.symm fun g => φ.symm_apply_eq.2 (hφ g).symm)
    (GHom.ofMulEquiv_bijective _ _) S).trans <| Set.equivOfEq <| by
      rw [GHom.coe_ofMulEquiv]
      exact congrArg (V ι) (φ.toEquiv.image_eq_preimage_symm S).symm

/-- On tuples, the solution bijection applies the word map of the words `φ⁻¹ y`. -/
@[simp]
theorem imageEquivV_apply_coe (S : Set (GX G X)) (v : V ι S) :
    (imageEquivV ι φ hφ S v : Y → H) = wordMap ι (fun y => φ.symm (inr (FreeGroup.of y))) v := by
  simp [imageEquivV]

/-- On tuples, the inverse solution bijection applies the word map of the words `φ x`. -/
@[simp]
theorem imageEquivV_symm_apply_coe (S : Set (GX G X)) (v : V ι (φ '' S)) :
    ((imageEquivV ι φ hφ S).symm v : X → H) = wordMap ι (fun x => φ (inr (FreeGroup.of x))) v := by
  simp [imageEquivV]

include hφ in
/-- A point is a solution of the image `φ S` of a system under a `G`-isomorphism exactly when
the point with coordinates its values at the words `φ x` is a solution of `S`. -/
theorem mem_V_image_mulEquiv_iff (S : Set (GX G X)) (v : Y → H) :
    v ∈ V ι (φ '' S) ↔ wordMap ι (fun x => φ (inr (FreeGroup.of x))) v ∈ V ι S := by
  simpa using (Set.ext_iff.1 (preimage_wordMap_V_eq_V_image ι (GHom.ofMulEquiv φ hφ) S) v).symm

include hφ in
/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` carries the radical of a system to the radical of its
image. -/
theorem Rad_image_mulEquiv (S : Set (GX G X)) :
    Rad ι (φ '' S) = (Rad ι S).map (φ : GX G X →* GX G Y) := by
  rw [Set.image_eq_preimage_of_inverse φ.symm_apply_apply φ.apply_symm_apply,
    Subgroup.map_equiv_eq_comap_symm]
  ext w
  simpa using SetLike.ext_iff.1 (Rad_preimage ι
    (GHom.ofMulEquiv φ.symm fun g => φ.symm_apply_eq.2 (hφ g).symm)
    (GHom.ofMulEquiv_bijective _ _) S) w

namespace CoordGroup

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` induces an isomorphism from the coordinate group of a
system to the coordinate group of its image, given by `φ` on representatives. -/
noncomputable def imageMulEquiv (S : Set (GX G X)) : CoordGroup ι S ≃* CoordGroup ι (φ '' S) :=
  QuotientGroup.congr _ _ φ (Rad_image_mulEquiv ι φ hφ S).symm

@[simp]
theorem imageMulEquiv_mk (S : Set (GX G X)) (w : GX G X) :
    imageMulEquiv ι φ hφ S (w : CoordGroup ι S) = (φ w : CoordGroup ι (φ '' S)) :=
  QuotientGroup.congr_mk _ _ _ _ w

@[simp]
theorem imageMulEquiv_symm_mk (S : Set (GX G X)) (w : GX G Y) :
    (imageMulEquiv ι φ hφ S).symm (w : CoordGroup ι (φ '' S)) =
      (φ.symm w : CoordGroup ι S) := by
  simp [imageMulEquiv]

/-- The coordinate-group isomorphism induced by a `G`-isomorphism commutes with the coefficient
maps. -/
theorem imageMulEquiv_coeff (S : Set (GX G X)) (g : G) :
    imageMulEquiv ι φ hφ S (coeff ι S g) = coeff ι (φ '' S) g := by
  simp [coeff_apply, hφ]

/-- The inverse of the coordinate-group isomorphism induced by a `G`-isomorphism commutes with the
coefficient maps. -/
theorem imageMulEquiv_symm_coeff (S : Set (GX G X)) (g : G) :
    (imageMulEquiv ι φ hφ S).symm (coeff ι (φ '' S) g) = coeff ι S g := by
  rw [MulEquiv.symm_apply_eq, imageMulEquiv_coeff]

/-- The coordinate-group isomorphism induced by a `G`-isomorphism `φ` sends a coordinate `x` of
the generic point of the system to the class of the word `φ x`. -/
@[simp]
theorem imageMulEquiv_genericPoint (S : Set (GX G X)) (x : X) :
    imageMulEquiv ι φ hφ S (genericPoint ι S x) =
      (φ (inr (FreeGroup.of x)) : CoordGroup ι (φ '' S)) := by
  simp [genericPoint_apply]

/-- The inverse of the coordinate-group isomorphism induced by a `G`-isomorphism `φ` sends a
coordinate `y` of the generic point of the image system to the class of the word `φ⁻¹ y`. -/
@[simp]
theorem imageMulEquiv_symm_genericPoint (S : Set (GX G X)) (y : Y) :
    (imageMulEquiv ι φ hφ S).symm (genericPoint ι (φ '' S) y) =
      (φ.symm (inr (FreeGroup.of y)) : CoordGroup ι S) := by
  simp [genericPoint_apply]

/-- The coordinate-group isomorphism induced by a `G`-isomorphism `φ` sends the generic point of
the system to the image of the generic point of the image system under the word map of `φ`. -/
@[simp]
theorem imageMulEquiv_comp_genericPoint (S : Set (GX G X)) :
    ⇑(imageMulEquiv ι φ hφ S) ∘ genericPoint ι S =
      wordMap (coeff ι (φ '' S)) (fun x => φ (inr (FreeGroup.of x)))
        (genericPoint ι (φ '' S)) := by
  funext x
  simp

/-- The inverse of the coordinate-group isomorphism induced by a `G`-isomorphism `φ` sends the
generic point of the image system to the image of the generic point of the system under the word
map of `φ⁻¹`. -/
@[simp]
theorem imageMulEquiv_symm_comp_genericPoint (S : Set (GX G X)) :
    ⇑(imageMulEquiv ι φ hφ S).symm ∘ genericPoint ι (φ '' S) =
      wordMap (coeff ι S) (fun y => φ.symm (inr (FreeGroup.of y))) (genericPoint ι S) := by
  funext y
  simp

end CoordGroup

section VImageEq

variable {S : Set (GX G X)} {T : Set (GX G Y)}

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` induces a bijection between the solutions of `S` and
those of any system `T` having the same solution set as `φ '' S`. -/
noncomputable def equivVOfVImageEq (hV : V ι (φ '' S) = V ι T) : V ι S ≃ V ι T :=
  (imageEquivV ι φ hφ S).trans (Set.equivOfEq hV)

/-- On tuples, `equivVOfVImageEq` applies the word map of the words `φ⁻¹ y`. -/
@[simp]
theorem equivVOfVImageEq_apply_coe (hV : V ι (φ '' S) = V ι T) (v : V ι S) :
    (equivVOfVImageEq ι φ hφ hV v : Y → H) =
      wordMap ι (fun y => φ.symm (inr (FreeGroup.of y))) v := by
  simp [equivVOfVImageEq]

/-- On tuples, the inverse of `equivVOfVImageEq` applies the word map of the words `φ x`. -/
@[simp]
theorem equivVOfVImageEq_symm_apply_coe (hV : V ι (φ '' S) = V ι T) (v : V ι T) :
    ((equivVOfVImageEq ι φ hφ hV).symm v : X → H) =
      wordMap ι (fun x => φ (inr (FreeGroup.of x))) v := by
  simp [equivVOfVImageEq]

include hφ in
/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` carries the radical of `S` to the radical of any system
`T` having the same solution set as `φ '' S`. -/
theorem Rad_of_V_image_eq (hV : V ι (φ '' S) = V ι T) :
    Rad ι T = (Rad ι S).map (φ : GX G X →* GX G Y) := by
  rw [Rad_def, ← hV, ← Rad_def, Rad_image_mulEquiv ι φ hφ]

namespace CoordGroup

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` induces an isomorphism from the coordinate group of `S`
to that of any system `T` having the same solution set as `φ '' S`, given by `φ` on
representatives. -/
noncomputable def mulEquivOfVImageEq (hV : V ι (φ '' S) = V ι T) :
    CoordGroup ι S ≃* CoordGroup ι T :=
  (imageMulEquiv ι φ hφ S).trans
    (QuotientGroup.quotientMulEquivOfEq (by rw [Rad_def, hV, Rad_def]))

@[simp]
theorem mulEquivOfVImageEq_mk (hV : V ι (φ '' S) = V ι T) (t : GX G X) :
    mulEquivOfVImageEq ι φ hφ hV (t : CoordGroup ι S) = (φ t : CoordGroup ι T) := by
  simp [mulEquivOfVImageEq]

@[simp]
theorem mulEquivOfVImageEq_symm_mk (hV : V ι (φ '' S) = V ι T) (t : GX G Y) :
    (mulEquivOfVImageEq ι φ hφ hV).symm (t : CoordGroup ι T) = (φ.symm t : CoordGroup ι S) := by
  apply (mulEquivOfVImageEq ι φ hφ hV).injective
  simp

/-- The coordinate-group isomorphism induced by a `G`-isomorphism and solution-set equivalence
commutes with the coefficient maps. -/
theorem mulEquivOfVImageEq_coeff (hV : V ι (φ '' S) = V ι T) (g : G) :
    mulEquivOfVImageEq ι φ hφ hV (coeff ι S g) = coeff ι T g := by
  simp [coeff_apply, hφ]

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism and solution-set
equivalence commutes with the coefficient maps. -/
theorem mulEquivOfVImageEq_symm_coeff (hV : V ι (φ '' S) = V ι T) (g : G) :
    (mulEquivOfVImageEq ι φ hφ hV).symm (coeff ι T g) = coeff ι S g := by
  rw [MulEquiv.symm_apply_eq, mulEquivOfVImageEq_coeff]

/-- The coordinate-group isomorphism induced by a `G`-isomorphism `φ` and solution-set
equivalence sends a coordinate `x` of the generic point of `S` to the class of `φ x`. -/
@[simp]
theorem mulEquivOfVImageEq_genericPoint (hV : V ι (φ '' S) = V ι T) (x : X) :
    mulEquivOfVImageEq ι φ hφ hV (genericPoint ι S x) =
      (φ (inr (FreeGroup.of x)) : CoordGroup ι T) := by
  simp [genericPoint_apply]

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism `φ` and solution-set
equivalence sends a coordinate `y` of the generic point of `T` to the class of `φ⁻¹ y`. -/
@[simp]
theorem mulEquivOfVImageEq_symm_genericPoint (hV : V ι (φ '' S) = V ι T) (y : Y) :
    (mulEquivOfVImageEq ι φ hφ hV).symm (genericPoint ι T y) =
      (φ.symm (inr (FreeGroup.of y)) : CoordGroup ι S) := by
  simp [genericPoint_apply]

/-- The coordinate-group isomorphism induced by a `G`-isomorphism `φ` and solution-set
equivalence sends the generic point of `S` to the image of the generic point of `T` under the word
map of `φ`. -/
@[simp]
theorem mulEquivOfVImageEq_comp_genericPoint (hV : V ι (φ '' S) = V ι T) :
    ⇑(mulEquivOfVImageEq ι φ hφ hV) ∘ genericPoint ι S =
      wordMap (coeff ι T) (fun x => φ (inr (FreeGroup.of x))) (genericPoint ι T) := by
  funext x
  simp

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism `φ` and solution-set
equivalence sends the generic point of `T` to the image of the generic point of `S` under the word
map of `φ⁻¹`. -/
@[simp]
theorem mulEquivOfVImageEq_symm_comp_genericPoint (hV : V ι (φ '' S) = V ι T) :
    ⇑(mulEquivOfVImageEq ι φ hφ hV).symm ∘ genericPoint ι T =
      wordMap (coeff ι S) (fun y => φ.symm (inr (FreeGroup.of y))) (genericPoint ι S) := by
  funext y
  simp

end CoordGroup

end VImageEq

section ConjMulEquiv

variable {w : GX G X} {u w' : GX G Y}

private theorem V_image_singleton_eq_of_conj (hw' : u * φ w * u⁻¹ = w') :
    V ι (φ '' {w}) = V ι {w'} := by
  rw [Set.image_singleton, ← hw', V_singleton_conj]

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` followed by conjugation `u * φ w * u⁻¹ = w'` in `G[Y]`
induces a bijection between the solutions of `w = 1` and those of `w' = 1`. -/
noncomputable def equivVOfConjMulEquiv (hw' : u * φ w * u⁻¹ = w') :
    V ι {w} ≃ V ι {w'} :=
  equivVOfVImageEq ι φ hφ (V_image_singleton_eq_of_conj ι φ hw')

/-- On tuples, `equivVOfConjMulEquiv` applies the word map of the words `φ⁻¹ y`. -/
@[simp]
theorem equivVOfConjMulEquiv_apply_coe (hw' : u * φ w * u⁻¹ = w') (v : V ι {w}) :
    (equivVOfConjMulEquiv ι φ hφ hw' v : Y → H) =
      wordMap ι (fun y => φ.symm (inr (FreeGroup.of y))) v :=
  equivVOfVImageEq_apply_coe ι φ hφ _ v

/-- On tuples, the inverse of `equivVOfConjMulEquiv` applies the word map of the words `φ x`. -/
@[simp]
theorem equivVOfConjMulEquiv_symm_apply_coe (hw' : u * φ w * u⁻¹ = w') (v : V ι {w'}) :
    ((equivVOfConjMulEquiv ι φ hφ hw').symm v : X → H) =
      wordMap ι (fun x => φ (inr (FreeGroup.of x))) v :=
  equivVOfVImageEq_symm_apply_coe ι φ hφ _ v

include hφ in
/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` carries the radical of `{w}` to the radical of any
conjugate `w' = u * φ w * u⁻¹` of `φ w`. -/
theorem Rad_singleton_of_conj_mulEquiv (hw' : u * φ w * u⁻¹ = w') :
    Rad ι {w'} = (Rad ι {w}).map (φ : GX G X →* GX G Y) :=
  Rad_of_V_image_eq ι φ hφ (V_image_singleton_eq_of_conj ι φ hw')

namespace CoordGroup

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` followed by conjugation `u * φ w * u⁻¹ = w'` induces an
isomorphism from the coordinate group of `{w}` to that of `{w'}`, given by `φ` on
representatives. -/
noncomputable def mulEquivOfConjMulEquiv (hw' : u * φ w * u⁻¹ = w') :
    CoordGroup ι {w} ≃* CoordGroup ι {w'} :=
  mulEquivOfVImageEq ι φ hφ (V_image_singleton_eq_of_conj ι φ hw')

@[simp]
theorem mulEquivOfConjMulEquiv_mk (hw' : u * φ w * u⁻¹ = w') (t : GX G X) :
    mulEquivOfConjMulEquiv ι φ hφ hw' (t : CoordGroup ι {w}) = (φ t : CoordGroup ι {w'}) :=
  mulEquivOfVImageEq_mk ι φ hφ _ t

@[simp]
theorem mulEquivOfConjMulEquiv_symm_mk (hw' : u * φ w * u⁻¹ = w') (t : GX G Y) :
    (mulEquivOfConjMulEquiv ι φ hφ hw').symm (t : CoordGroup ι {w'}) =
      (φ.symm t : CoordGroup ι {w}) :=
  mulEquivOfVImageEq_symm_mk ι φ hφ _ t

/-- The coordinate-group isomorphism induced by a `G`-isomorphism and conjugation commutes with
the coefficient maps. -/
theorem mulEquivOfConjMulEquiv_coeff (hw' : u * φ w * u⁻¹ = w') (g : G) :
    mulEquivOfConjMulEquiv ι φ hφ hw' (coeff ι {w} g) = coeff ι {w'} g :=
  mulEquivOfVImageEq_coeff ι φ hφ _ g

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism and conjugation commutes
with the coefficient maps. -/
theorem mulEquivOfConjMulEquiv_symm_coeff (hw' : u * φ w * u⁻¹ = w') (g : G) :
    (mulEquivOfConjMulEquiv ι φ hφ hw').symm (coeff ι {w'} g) = coeff ι {w} g :=
  mulEquivOfVImageEq_symm_coeff ι φ hφ _ g

/-- The coordinate-group isomorphism induced by a `G`-isomorphism `φ` and conjugation sends a
coordinate `x` of the generic point of `{w}` to the class of the word `φ x`. -/
@[simp]
theorem mulEquivOfConjMulEquiv_genericPoint (hw' : u * φ w * u⁻¹ = w') (x : X) :
    mulEquivOfConjMulEquiv ι φ hφ hw' (genericPoint ι {w} x) =
      (φ (inr (FreeGroup.of x)) : CoordGroup ι {w'}) :=
  mulEquivOfVImageEq_genericPoint ι φ hφ _ x

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism `φ` and conjugation
sends a coordinate `y` of the generic point of `{w'}` to the class of the word `φ⁻¹ y`. -/
@[simp]
theorem mulEquivOfConjMulEquiv_symm_genericPoint (hw' : u * φ w * u⁻¹ = w') (y : Y) :
    (mulEquivOfConjMulEquiv ι φ hφ hw').symm (genericPoint ι {w'} y) =
      (φ.symm (inr (FreeGroup.of y)) : CoordGroup ι {w}) :=
  mulEquivOfVImageEq_symm_genericPoint ι φ hφ _ y

/-- The coordinate-group isomorphism induced by a `G`-isomorphism `φ` and conjugation sends the
generic point of `{w}` to the image of the generic point of `{w'}` under the word map of `φ`. -/
@[simp]
theorem mulEquivOfConjMulEquiv_comp_genericPoint (hw' : u * φ w * u⁻¹ = w') :
    ⇑(mulEquivOfConjMulEquiv ι φ hφ hw') ∘ genericPoint ι {w} =
      wordMap (coeff ι {w'}) (fun x => φ (inr (FreeGroup.of x))) (genericPoint ι {w'}) :=
  mulEquivOfVImageEq_comp_genericPoint ι φ hφ _

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism `φ` and conjugation
sends the generic point of `{w'}` to the image of the generic point of `{w}` under the word map
of `φ⁻¹`. -/
@[simp]
theorem mulEquivOfConjMulEquiv_symm_comp_genericPoint (hw' : u * φ w * u⁻¹ = w') :
    ⇑(mulEquivOfConjMulEquiv ι φ hφ hw').symm ∘ genericPoint ι {w'} =
      wordMap (coeff ι {w}) (fun y => φ.symm (inr (FreeGroup.of y))) (genericPoint ι {w}) :=
  mulEquivOfVImageEq_symm_comp_genericPoint ι φ hφ _

end CoordGroup

end ConjMulEquiv

end MulEquiv

section GHomVImageEq

/-- When `V ι (σ '' S) = V ι T` for a `G`-homomorphism `σ : G[X] →* G[Y]`, a point solves `T`
if and only if the tuple of its values at the words `σ x` solves `S`. -/
theorem mem_V_iff_of_V_image_eq (σ : GHom (inl : G →* GX G X) (inl : G →* GX G Y))
    {S : Set (GX G X)} {T : Set (GX G Y)} (hV : V ι (σ '' S) = V ι T) (v : Y → H) :
    v ∈ V ι T ↔ wordMap ι (fun x => σ (inr (FreeGroup.of x))) v ∈ V ι S := by
  rw [← hV]
  simpa using (Set.ext_iff.1 (preimage_wordMap_V_eq_V_image ι σ S) v).symm

/-- When `u * σ w * u⁻¹ = w'` for a `G`-homomorphism `σ : G[X] →* G[Y]`, a point solves `w' = 1`
if and only if the tuple of its values at the words `σ x` solves `w = 1`. -/
theorem mem_V_singleton_iff_of_conj_gHom (σ : GHom (inl : G →* GX G X) (inl : G →* GX G Y))
    {w : GX G X} {u w' : GX G Y} (hw' : u * σ w * u⁻¹ = w') (v : Y → H) :
    v ∈ V ι {w'} ↔ wordMap ι (fun x => σ (inr (FreeGroup.of x))) v ∈ V ι {w} :=
  mem_V_iff_of_V_image_eq ι σ (by rw [Set.image_singleton, ← hw', V_singleton_conj]) v

end GHomVImageEq

/-! ### The commutator equation -/

section Commutator

open FreeGroup
open scoped commutatorElement

/-- The change of coordinates `x ↦ x g` of `G[x]`, the transvection `GX.transvection () 1 (inl g)`,
carries the solutions of `[x, g] = 1`, the centralizer of `ι g`, onto themselves. -/
theorem image_transvection_V_singleton_commutatorElement (g : G) :
    coordinateChangeEquiv ι
        (GHom.ofMulEquiv (GX.transvection () 1 (inl g) (one_mem _) (GX.inl_mem_avoiding () g))
          (GX.transvection_inl _ _))
        (GHom.ofMulEquiv_bijective _ _) ''
        V ι {⁅(inr (of ()) : GX G Unit), (inl g : GX G Unit)⁆} =
      V ι {⁅(inr (of ()) : GX G Unit), (inl g : GX G Unit)⁆} := by
  refine (image_coordinateChangeEquiv_V ι _ _ _).trans (congrArg (V ι) ?_)
  -- The transvection fixes the commutator, so it fixes the system.
  ext w
  simp [← MulEquiv.eq_symm_apply, commutatorElement_def, mul_assoc]

end Commutator

end GroupAlgGeom
end TauCeti
