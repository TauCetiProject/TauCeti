/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Coordinate groups under a change of the coefficient group

Let `f : G →* G'` be a homomorphism of coefficient groups and `ι : G' →* H`. A system `S ⊆ G[X]`
has the same solutions in `H` through `ι ∘ f` as its image `f(S) ⊆ G'[X]` through `ι`, so the
map `G[X] → G'[X]` induced by `f` passes to an injective homomorphism of coordinate groups
`CoordGroup.mapCoeff f ι S : G_{R(S)} → G'_{R(f(S))}`.

## Main definitions

* `TauCeti.GroupAlgGeom.CoordGroup.mapCoeff`: the homomorphism of coordinate groups induced by a
  change of the coefficient group.

## Main results

* `TauCeti.GroupAlgGeom.V_image_map`: the solutions of the image of a system under a change of
  coefficients are those of the system.
* `TauCeti.GroupAlgGeom.CoordGroup.mapCoeff_injective`: the homomorphism of coordinate groups
  induced by a change of coefficients is injective; it sends the generic point to the generic
  point (`TauCeti.GroupAlgGeom.CoordGroup.mapCoeff_comp_genericPoint`).

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Lemma 37 (homomorphisms of coordinate groups induced by homomorphisms of the
  groups; here the coefficient group itself changes).
-/

public section

namespace TauCeti.GroupAlgGeom

variable {G G' H X : Type*} [Group G] [Group G'] [Group H]

variable (f : G →* G') (ι : G' →* H) (S : Set (GX G X))

/-- The solutions of `S` through `ι ∘ f` are those of its image under the change of
coefficients `f`. -/
theorem V_image_map : V ι (Monoid.Coprod.map f (FreeGroup.map id) '' S) = V (ι.comp f) S := by
  ext v
  simp [eval_map]

namespace CoordGroup

/-- The homomorphism `G_{R(S)} → G'_{R(f(S))}` of coordinate groups induced by a change of
coefficients `f : G →* G'`, the solutions being taken in `H` through `ι`. -/
noncomputable def mapCoeff :
    GHom (coeff (ι.comp f) S) ((coeff ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)).comp f) :=
  { toMonoidHom := QuotientGroup.map _ _ (Monoid.Coprod.map f (FreeGroup.map id)) (by
      intro w hw
      rw [Subgroup.mem_comap, mem_Rad]
      intro v hv
      rw [V_image_map] at hv
      simpa using (mem_Rad.1 hw) v hv)
    map_coeff' := fun g => by simp [coeff_apply] }

variable {f ι S}

/-- The class of a word `w` is sent to the class of its image `f(w)`. -/
@[simp]
theorem mapCoeff_mk (w : GX G X) :
    mapCoeff f ι S (w : CoordGroup (ι.comp f) S) =
      (Monoid.Coprod.map f (FreeGroup.map id) w :
        CoordGroup ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)) := (rfl)

/-- The homomorphism of coordinate groups sends each coordinate of the generic point of `S` to
that of the generic point of `f(S)`. -/
@[simp]
theorem mapCoeff_genericPoint (x : X) :
    mapCoeff f ι S (genericPoint (ι.comp f) S x) =
      genericPoint ι (Monoid.Coprod.map f (FreeGroup.map id) '' S) x := by
  simp [genericPoint_apply]

/-- The homomorphism of coordinate groups sends the generic point of `S` to that of `f(S)`. -/
@[simp]
theorem mapCoeff_comp_genericPoint :
    ⇑(mapCoeff f ι S) ∘ genericPoint (ι.comp f) S =
      genericPoint ι (Monoid.Coprod.map f (FreeGroup.map id) '' S) :=
  funext mapCoeff_genericPoint

/-- The homomorphism of coordinate groups induced by a change of coefficients is injective: a
word over `G` vanishes at every solution of `f(S)` in `H` exactly when it vanishes at every
solution of `S` through `ι ∘ f`, these being the same points. -/
theorem mapCoeff_injective : Function.Injective (mapCoeff f ι S) := by
  refine (injective_iff_map_eq_one _).2 fun c hc => ?_
  induction c using QuotientGroup.induction_on with | H w => ?_
  rw [mapCoeff_mk, QuotientGroup.eq_one_iff, mem_Rad, V_image_map] at hc
  exact (QuotientGroup.eq_one_iff w).2 (mem_Rad.2 fun v hv => by simpa using hc v hv)

end CoordGroup

end TauCeti.GroupAlgGeom
