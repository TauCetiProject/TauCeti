/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Neighbourhood
public import TauCeti.RingTheory.Spectrum.Prime.Point

/-!
# Pointed étale neighbourhoods as triples

The induced category of étale algebra, prime, and residue-map triples of Stacks Tag 04GW is
empty for a trivial target algebra. For a nontrivial target, its objects and morphisms retain
the prime and residue data. For a field target, the point/residue-field correspondence gives
an equivalence with pointed étale algebras.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationConstruction.lean`, `PointedEtaleNeighborhood`.
-/

public section

universe u v

namespace TauCeti.StrictHenselization

open CategoryTheory
open TauCeti.ResidueField

section CommRing

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- An étale algebra, a prime, and an algebra map from its residue field to `Ω`. -/
structure TripleNeighbourhood where
  /-- The étale algebra underlying the triple. -/
  carrier : Type (max u v)
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [etale : Algebra.Etale R carrier]
  /-- The prime and residue-field algebra map specifying the point. -/
  data : PointData R carrier Ω

attribute [instance] TripleNeighbourhood.commRing TripleNeighbourhood.algebra
  TripleNeighbourhood.etale

/-- Regard a prime and residue-field map as a pointed étale algebra. -/
-- Exposure identifies the source carrier in public, dependently typed point and morphism equations.
@[expose] noncomputable def TripleNeighbourhood.toNeighbourhood
    (triple : TripleNeighbourhood R Ω) : Neighbourhood R Ω :=
  Neighbourhood.mk' triple.carrier triple.data.toAlgHom

/-- The point of the neighbourhood associated with a triple is its induced algebra map. -/
@[simp]
theorem TripleNeighbourhood.toNeighbourhood_point (triple : TripleNeighbourhood R Ω) :
    (triple.toNeighbourhood R Ω).point = triple.data.toAlgHom :=
  Neighbourhood.point_mk' _ _

end CommRing

section Field

variable (R : Type u) (Ω : Type v) [CommRing R] [Field Ω] [Algebra R Ω]

/-- Extract the prime and residue-field embedding from a pointed étale algebra. -/
noncomputable def Neighbourhood.toTriple
    (point : Neighbourhood R Ω) : TripleNeighbourhood R Ω :=
  { carrier := point.obj.left
    commRing := inferInstance
    algebra := inferInstance
    etale := inferInstance
    data := (pointDataEquiv : PointData R point.obj.left Ω ≃ _).symm
      point.point }

/-- The point map of the triple extracted from a neighbourhood is its original point map. -/
@[simp]
theorem Neighbourhood.toTriple_point (point : Neighbourhood R Ω) :
    HEq (point.toTriple R Ω).data.toAlgHom
      point.point := by
  simp only [Neighbourhood.toTriple]
  apply heq_of_eq
  exact (pointDataEquiv_apply
    ((pointDataEquiv : PointData R point.obj.left Ω ≃ _).symm
      point.point)).symm.trans
      (Equiv.apply_symm_apply (pointDataEquiv : PointData R point.obj.left Ω ≃ _)
        point.point)

/-- Converting a triple to a pointed neighbourhood and back recovers the triple. -/
@[simp]
theorem TripleNeighbourhood.toNeighbourhood_toTriple (triple : TripleNeighbourhood R Ω) :
    (triple.toNeighbourhood R Ω).toTriple R Ω = triple := by
  cases triple with
  | mk carrier data =>
    -- The carrier and its ring and algebra instances are preserved definitionally. Identify these
    -- dependent indices first: public point equations compare maps, not enclosing triple records.
    change TripleNeighbourhood.mk carrier
      ((pointDataEquiv : PointData R carrier Ω ≃ _).symm
        (TripleNeighbourhood.mk carrier data).toNeighbourhood.point) =
      TripleNeighbourhood.mk carrier data
    rw [TripleNeighbourhood.toNeighbourhood_point]
    apply congrArg (TripleNeighbourhood.mk carrier)
    simpa only [pointDataEquiv_apply] using
      Equiv.symm_apply_apply (pointDataEquiv : PointData R carrier Ω ≃ _) data

/-- Triples and pointed étale neighbourhoods are equivalent as objects. -/
noncomputable def tripleNeighbourhoodEquiv :
    TripleNeighbourhood R Ω ≃ Neighbourhood R Ω where
  toFun := TripleNeighbourhood.toNeighbourhood R Ω
  invFun := Neighbourhood.toTriple R Ω
  left_inv := TripleNeighbourhood.toNeighbourhood_toTriple R Ω
  right_inv := by
    intro point
    apply Neighbourhood.ext R Ω _ point
    · rfl
    · apply heq_of_eq
      ext element
      have h := DFunLike.congr_fun (eq_of_heq (Neighbourhood.toTriple_point R Ω point)) element
      rw [← TripleNeighbourhood.toNeighbourhood_point] at h
      -- `point` is not exposed, so `h` (stated for `point`) must be converted to the `.down` form.
      exact (Neighbourhood.point_apply _ _).symm.trans (h.trans (Neighbourhood.point_apply _ _))

/-- Extracting a triple and then forgetting its prime/residue presentation recovers the point. -/
@[simp]
theorem Neighbourhood.toTriple_toNeighbourhood (point : Neighbourhood R Ω) :
    (point.toTriple R Ω).toNeighbourhood R Ω = point :=
  (tripleNeighbourhoodEquiv R Ω).right_inv point

/-- The forward object equivalence uses the pointed algebra of a triple. -/
@[simp]
theorem tripleNeighbourhoodEquiv_apply (triple : TripleNeighbourhood R Ω) :
    tripleNeighbourhoodEquiv R Ω triple = triple.toNeighbourhood R Ω := by
  rfl

/-- The inverse object equivalence extracts the prime and residue embedding. -/
@[simp]
theorem tripleNeighbourhoodEquiv_symm_apply (point : Neighbourhood R Ω) :
    (tripleNeighbourhoodEquiv R Ω).symm point = point.toTriple R Ω := by
  rfl

end Field

section Nontrivial

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Nontrivial Ω]
  [Algebra R Ω]

/-- Triples agree when their associated pointed étale neighbourhoods agree. -/
@[ext]
theorem TripleNeighbourhood.ext {first second : TripleNeighbourhood R Ω}
    (equality : first.toNeighbourhood R Ω = second.toNeighbourhood R Ω) : first = second := by
  cases first with
  | mk firstCarrier firstData =>
    cases second with
    | mk secondCarrier secondData =>
      have hcat := congrArg (fun point : Neighbourhood R Ω => point.obj.left) equality
      cases hcat
      have hpoint : firstData.toAlgHom = secondData.toAlgHom := by
        have h : HEq (TripleNeighbourhood.mk firstCarrier firstData).toNeighbourhood.point
            (TripleNeighbourhood.mk firstCarrier secondData).toNeighbourhood.point := by
          rw [equality]
        rw [TripleNeighbourhood.toNeighbourhood_point, TripleNeighbourhood.toNeighbourhood_point]
          at h
        exact eq_of_heq h
      congr 1
      exact PointData.toAlgHom_injective hpoint

end Nontrivial

section CommRingTripleCategory

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- The category induced by nontrivial-target triples and their pointed algebras. -/
abbrev TripleCategory :=
  InducedCategory (Neighbourhood R Ω)
    (fun (triple : { _triple : TripleNeighbourhood R Ω // Nontrivial Ω }) =>
      triple.val.toNeighbourhood R Ω)

/-- Triple morphisms agree when their underlying algebra maps agree. -/
@[ext]
theorem TripleCategory.hom_ext {first second : TripleCategory R Ω}
    {left right : first ⟶ second}
    (equality : left.hom.hom.left.hom = right.hom.hom.left.hom) : left = right := by
  apply InducedCategory.hom_ext
  exact Neighbourhood.hom_ext equality

/-- A triple-category morphism commutes with the induced algebra-valued points. -/
@[simp]
theorem TripleCategory.hom_point {first second : TripleCategory R Ω}
    (morphism : first ⟶ second) :
    second.val.data.toAlgHom.comp morphism.hom.hom.left.hom = first.val.data.toAlgHom := by
  have h := Neighbourhood.point_comp_hom morphism.hom
  rwa [TripleNeighbourhood.toNeighbourhood_point, TripleNeighbourhood.toNeighbourhood_point] at h

/-- Construct a morphism of triples from a map preserving their points. -/
noncomputable def TripleCategory.homMk (first second : TripleCategory R Ω)
    (map : first.val.carrier →ₐ[R] second.val.carrier)
    (hpoint : second.val.data.toAlgHom.comp map = first.val.data.toAlgHom) : first ⟶ second :=
  InducedCategory.homMk
    (Neighbourhood.homMk' map (by
      rwa [TripleNeighbourhood.toNeighbourhood_point, TripleNeighbourhood.toNeighbourhood_point]))

/-- The algebra map underlying a constructed triple morphism is the supplied map. -/
@[simp]
theorem TripleCategory.homMk_left (first second : TripleCategory R Ω)
    (map : first.val.carrier →ₐ[R] second.val.carrier)
    (hpoint : second.val.data.toAlgHom.comp map = first.val.data.toAlgHom) :
    (TripleCategory.homMk R Ω first second map hpoint).hom.hom.left.hom = map :=
  Neighbourhood.homMk'_hom_left_hom (B := first.val.toNeighbourhood R Ω)
    (C := second.val.toNeighbourhood R Ω) map _

/-- A morphism of triples is an algebra map preserving the prime and residue-field map. -/
theorem tripleCategory_hom_iff (first second : TripleCategory R Ω)
    (map : first.val.carrier →ₐ[R] second.val.carrier) :
    (∃ morphism : first ⟶ second, morphism.hom.hom.left.hom = map) ↔
      ∃ hprime : first.val.data.1.asIdeal = second.val.data.1.asIdeal.comap map.toRingHom,
        second.val.data.2.comp
          (Ideal.ResidueField.mapₐ first.val.data.1.asIdeal second.val.data.1.asIdeal map hprime) =
          first.val.data.2 := by
  have nontrivial : Nontrivial Ω := first.property
  constructor
  · rintro ⟨morphism, equality⟩
    apply (PointData.toAlgHom_comp_iff first.val.data second.val.data map).mp
    rw [← equality]
    exact TripleCategory.hom_point R Ω morphism
  · intro h
    have hcomp := (PointData.toAlgHom_comp_iff first.val.data second.val.data map).mpr h
    exact ⟨TripleCategory.homMk R Ω first second map hcomp,
      TripleCategory.homMk_left R Ω first second map hcomp⟩

end CommRingTripleCategory

section CommRingTripleCategoryExt

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- Triple-category objects agree when their pointed étale neighbourhoods agree. -/
@[ext]
theorem TripleCategory.ext {first second : TripleCategory R Ω}
    (equality : first.val.toNeighbourhood R Ω = second.val.toNeighbourhood R Ω) :
    first = second := by
  have nontrivial : Nontrivial Ω := first.property
  exact Subtype.ext (TripleNeighbourhood.ext R Ω equality)

end CommRingTripleCategoryExt

section Field

variable (R : Type u) (Ω : Type v) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The category of Stacks 04GW triples is equivalent to pointed étale neighbourhoods. -/
noncomputable def tripleCategoryEquivalence : TripleCategory R Ω ≌ Neighbourhood R Ω :=
  Equivalence.induced
    ({ toFun := fun triple => triple.val.toNeighbourhood R Ω
       invFun := fun point => ⟨point.toTriple R Ω, inferInstance⟩
       left_inv := by
         intro triple
         apply Subtype.ext
         exact TripleNeighbourhood.toNeighbourhood_toTriple R Ω triple.val
       right_inv := Neighbourhood.toTriple_toNeighbourhood R Ω } :
      { _triple : TripleNeighbourhood R Ω // Nontrivial Ω } ≃ Neighbourhood R Ω)

/-- The forward equivalence sends a triple to its pointed neighbourhood. -/
@[simp]
theorem tripleCategoryEquivalence_functor_obj (triple : TripleCategory R Ω) :
    (tripleCategoryEquivalence R Ω).functor.obj triple =
      triple.val.toNeighbourhood R Ω := by
  rfl

/-- The forward equivalence retains the underlying neighbourhood morphism. -/
@[simp]
theorem tripleCategoryEquivalence_functor_map {first second : TripleCategory R Ω}
    (morphism : first ⟶ second) :
    HEq ((tripleCategoryEquivalence R Ω).functor.map morphism) morphism.hom := by
  rfl

/-- The inverse equivalence records the prime and residue embedding of the point. -/
@[simp]
theorem tripleCategoryEquivalence_inverse_obj (point : Neighbourhood R Ω) :
    (tripleCategoryEquivalence R Ω).inverse.obj point =
      (⟨point.toTriple R Ω, inferInstance⟩ : TripleCategory R Ω) := by
  rfl

end Field

end TauCeti.StrictHenselization
