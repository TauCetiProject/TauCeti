/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism

/-!
# Changes of coordinates in equations over groups

A coefficient-preserving word homomorphism acts on tuples by evaluation. When it is bijective,
this action transports solution sets and radicals, and induces an isomorphism of coordinate
groups. The results apply to inconsistent systems and arbitrary coefficient homomorphisms.

A `G`-isomorphism `φ : G[X] ≃* G[Y]` induces a bijection `imageEquivV` between the solutions of a
system `S` and those of its image `φ S`; it carries the radical of `S` to that of `φ S`
(`Rad_image_mulEquiv`) and induces the isomorphism of coordinate groups
`CoordGroup.imageMulEquiv`. Combined with conjugation in `G[Y]` (`u * φ w * u⁻¹ = w'`), it gives
a bijection `equivVOfConjMulEquiv` of single-equation solution sets, carries `Rad ι {w}` to
`Rad ι {w'}` (`Rad_singleton_of_conj_mulEquiv`), and induces a `G`-isomorphism
`CoordGroup.mulEquivOfConjMulEquiv` of radical coordinate groups. The change of coordinates
`x ↦ x g` of one variable, a transvection, fixes the commutator equation `[x, g] = 1`, so it
carries its solutions, the centralizer of `ι g`, onto themselves.

## Main definitions

* `TauCeti.GroupAlgGeom.coordinateChangeEquiv`, `TauCeti.GroupAlgGeom.coordinateChangeEquivV`:
  a bijective coefficient-preserving word map gives an equivalence of tuples, restricting to an
  equivalence of solution sets.
* `TauCeti.GroupAlgGeom.CoordGroup.equivOfCoordinateChange`: the induced isomorphism of
  coordinate groups.
* `TauCeti.GroupAlgGeom.imageEquivV`, `TauCeti.GroupAlgGeom.equivVOfConjMulEquiv`: the bijections
  of solution sets induced by a `G`-isomorphism, and by a `G`-isomorphism followed by conjugation.
* `TauCeti.GroupAlgGeom.CoordGroup.imageMulEquiv`,
  `TauCeti.GroupAlgGeom.CoordGroup.mulEquivOfConjMulEquiv`: the induced isomorphisms of
  coordinate groups.

## Main results

* `TauCeti.GroupAlgGeom.image_coordinateChangeEquiv_V`: a change of coordinates `σ` carries
  `V_H(S)` onto `V_H(σ⁻¹(S))`.
* `TauCeti.GroupAlgGeom.mem_V_image_mulEquiv_iff`,
  `TauCeti.GroupAlgGeom.mem_V_singleton_of_conj_mulEquiv_iff`: membership in the solutions of the
  image of a system under a `G`-isomorphism, and under a `G`-isomorphism followed by conjugation.
* `TauCeti.GroupAlgGeom.Rad_image_mulEquiv`,
  `TauCeti.GroupAlgGeom.Rad_singleton_of_conj_mulEquiv`: a `G`-isomorphism carries the radical of
  a system to the radical of its image, and of a conjugate of the image of a single equation.
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

end CoordGroup

section ConjMulEquiv

variable {w : GX G X} {u w' : GX G Y}

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` followed by conjugation `u * φ w * u⁻¹ = w'` in `G[Y]`
induces a bijection between the solutions of `w = 1` and those of `w' = 1`. -/
noncomputable def equivVOfConjMulEquiv (hw' : u * φ w * u⁻¹ = w') :
    V ι {w} ≃ V ι {w'} :=
  (imageEquivV ι φ hφ {w}).trans <| Set.equivOfEq <| by
    rw [Set.image_singleton, ← hw', V_singleton_conj]

/-- On tuples, `equivVOfConjMulEquiv` applies the word map of the words `φ⁻¹ y`. -/
@[simp]
theorem equivVOfConjMulEquiv_apply_coe (hw' : u * φ w * u⁻¹ = w') (v : V ι {w}) :
    (equivVOfConjMulEquiv ι φ hφ hw' v : Y → H) =
      wordMap ι (fun y => φ.symm (inr (FreeGroup.of y))) v := by
  simp [equivVOfConjMulEquiv]

/-- On tuples, the inverse of `equivVOfConjMulEquiv` applies the word map of the words `φ x`. -/
@[simp]
theorem equivVOfConjMulEquiv_symm_apply_coe (hw' : u * φ w * u⁻¹ = w') (v : V ι {w'}) :
    ((equivVOfConjMulEquiv ι φ hφ hw').symm v : X → H) =
      wordMap ι (fun x => φ (inr (FreeGroup.of x))) v := by
  simp [equivVOfConjMulEquiv]

include hφ in
/-- When `u * φ w * u⁻¹ = w'` for a `G`-isomorphism `φ`, a point solves `w' = 1` if and only if
the tuple of its values at the words `φ x` solves `w = 1`. -/
theorem mem_V_singleton_of_conj_mulEquiv_iff (hw' : u * φ w * u⁻¹ = w') (v : Y → H) :
    v ∈ V ι {w'} ↔ wordMap ι (fun x => φ (inr (FreeGroup.of x))) v ∈ V ι {w} := by
  rw [← hw', V_singleton_conj, ← Set.image_singleton, mem_V_image_mulEquiv_iff ι φ hφ]

include hφ in
/-- A `G`-isomorphism followed by conjugation preserves consistency of a single equation. -/
theorem nonempty_V_singleton_of_conj_mulEquiv_iff (hw' : u * φ w * u⁻¹ = w') :
    (V ι {w}).Nonempty ↔ (V ι {w'}).Nonempty := by
  simp_rw [← Set.nonempty_coe_sort]
  exact (equivVOfConjMulEquiv ι φ hφ hw').nonempty_congr

include hφ in
/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` carries the radical of `{w}` to the radical of any
conjugate `w' = u * φ w * u⁻¹` of `φ w`. -/
theorem Rad_singleton_of_conj_mulEquiv (hw' : u * φ w * u⁻¹ = w') :
    Rad ι {w'} = (Rad ι {w}).map (φ : GX G X →* GX G Y) := by
  rw [← hw', Rad_singleton_conj, ← Set.image_singleton, Rad_image_mulEquiv ι φ hφ]

include hφ in
/-- An equation carried by a `G`-isomorphism and conjugation to a coefficient `c` that remains
nontrivial in `H` has no solutions in `H`. -/
theorem V_singleton_eq_empty_of_conj_mulEquiv_inl {c : G} (hw' : u * φ w * u⁻¹ = inl c)
    (hc : ι c ≠ 1) : V ι {w} = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun v hv =>
    (V_singleton_inl_eq_empty hc).subset (equivVOfConjMulEquiv ι φ hφ hw' ⟨v, hv⟩).2

include hφ in
/-- An equation carried by a `G`-isomorphism and conjugation to a coefficient `c` that remains
nontrivial in `H` has radical `⊤`. -/
theorem Rad_singleton_eq_top_of_conj_mulEquiv_inl {c : G} (hw' : u * φ w * u⁻¹ = inl c)
    (hc : ι c ≠ 1) : Rad ι {w} = ⊤ :=
  Rad_eq_top_of_V_eq_empty (V_singleton_eq_empty_of_conj_mulEquiv_inl ι φ hφ hw' hc)

include hφ in
/-- An equation carried by a `G`-isomorphism and conjugation to a coefficient `c` with `ι c = 1`
(in particular `c = 1`) is satisfied by every point of `H^X`. -/
theorem V_singleton_eq_univ_of_conj_mulEquiv_inl {c : G} (hw' : u * φ w * u⁻¹ = inl c)
    (hc : ι c = 1) : V ι {w} = Set.univ := by
  refine Set.eq_univ_of_forall fun v => mem_V.2 ?_
  rintro _ rfl
  have key := congrArg (fun z => eval ι v (φ.symm z)) hw'
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, φ.symm_apply_eq.2 (hφ c).symm,
    eval_inl, hc] at key
  exact conj_eq_one_iff.1 key

include hφ in
/-- An equation carried by a `G`-isomorphism and conjugation to a coefficient `c` with `ι c = 1`
has radical `I ι Set.univ`. -/
theorem Rad_singleton_eq_I_univ_of_conj_mulEquiv_inl {c : G} (hw' : u * φ w * u⁻¹ = inl c)
    (hc : ι c = 1) : Rad ι {w} = I ι Set.univ := by
  rw [Rad_def, V_singleton_eq_univ_of_conj_mulEquiv_inl ι φ hφ hw' hc]

namespace CoordGroup

/-- A `G`-isomorphism `φ : G[X] ≃* G[Y]` followed by conjugation `u * φ w * u⁻¹ = w'` induces an
isomorphism from the coordinate group of `{w}` to that of `{w'}`, given by `φ` on
representatives. -/
noncomputable def mulEquivOfConjMulEquiv (hw' : u * φ w * u⁻¹ = w') :
    CoordGroup ι {w} ≃* CoordGroup ι {w'} :=
  QuotientGroup.congr _ _ φ (Rad_singleton_of_conj_mulEquiv ι φ hφ hw').symm

@[simp]
theorem mulEquivOfConjMulEquiv_mk (hw' : u * φ w * u⁻¹ = w') (t : GX G X) :
    mulEquivOfConjMulEquiv ι φ hφ hw' (t : CoordGroup ι {w}) = (φ t : CoordGroup ι {w'}) :=
  QuotientGroup.congr_mk _ _ _ _ t

@[simp]
theorem mulEquivOfConjMulEquiv_symm_mk (hw' : u * φ w * u⁻¹ = w') (t : GX G Y) :
    (mulEquivOfConjMulEquiv ι φ hφ hw').symm (t : CoordGroup ι {w'}) =
      (φ.symm t : CoordGroup ι {w}) := by
  simp [mulEquivOfConjMulEquiv]

/-- The coordinate-group isomorphism induced by a `G`-isomorphism and conjugation commutes with
the coefficient maps. -/
theorem mulEquivOfConjMulEquiv_coeff (hw' : u * φ w * u⁻¹ = w') (g : G) :
    mulEquivOfConjMulEquiv ι φ hφ hw' (coeff ι {w} g) = coeff ι {w'} g := by
  simp [coeff_apply, hφ]

/-- The inverse coordinate-group isomorphism induced by a `G`-isomorphism and conjugation commutes
with the coefficient maps. -/
theorem mulEquivOfConjMulEquiv_symm_coeff (hw' : u * φ w * u⁻¹ = w') (g : G) :
    (mulEquivOfConjMulEquiv ι φ hφ hw').symm (coeff ι {w'} g) = coeff ι {w} g := by
  rw [MulEquiv.symm_apply_eq, mulEquivOfConjMulEquiv_coeff]

/-- `mulEquivOfConjMulEquiv` as a `G`-homomorphism between the coordinate groups. -/
noncomputable def gHomOfConjMulEquiv (hw' : u * φ w * u⁻¹ = w') :
    GHom (coeff ι {w}) (coeff ι {w'}) :=
  GHom.ofMulEquiv (mulEquivOfConjMulEquiv ι φ hφ hw')
    (mulEquivOfConjMulEquiv_coeff ι φ hφ hw')

theorem gHomOfConjMulEquiv_bijective (hw' : u * φ w * u⁻¹ = w') :
    Function.Bijective (gHomOfConjMulEquiv ι φ hφ hw') :=
  GHom.ofMulEquiv_bijective _ _

include hφ in
/-- If `ι` is injective and the transformed equation `w' = u * φ w * u⁻¹` has a solution in `H`,
the coefficient map into the coordinate group of `{w}` is injective. -/
theorem coeff_injective_of_conj_mulEquiv (hι : Function.Injective ι)
    (hw' : u * φ w * u⁻¹ = w') (hV : (V ι {w'}).Nonempty) :
    Function.Injective (coeff ι {w}) :=
  coeff_injective hι ((nonempty_V_singleton_of_conj_mulEquiv_iff ι φ hφ hw').2 hV)

end CoordGroup

end ConjMulEquiv

end MulEquiv

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
