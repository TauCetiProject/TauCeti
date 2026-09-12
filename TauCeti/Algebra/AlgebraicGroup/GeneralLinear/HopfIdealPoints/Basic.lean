/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# General-linear points cut out by Hopf ideals

This file transports the algebra-valued points of a quotient of the coordinate Hopf algebra of
`GLₙ` through `GeneralLinear.pointsMulEquiv`. The resulting matrix subgroup is characterized by
vanishing on the Hopf ideal and is functorial in the value algebra.

## Main declarations

* `TauCeti.GeneralLinear.hopfIdealPointsSubgroup`: the matrix subgroup cut out by a Hopf ideal
  in the general-linear coordinate ring.
* `TauCeti.GeneralLinear.mem_hopfIdealPointsSubgroup_iff`: membership is characterized by
  vanishing on the Hopf ideal.
* `TauCeti.GeneralLinear.hopfIdealPointsSubgroup_le_of_le`: larger Hopf ideals cut out smaller
  point subgroups.
* `TauCeti.GeneralLinear.hopfIdealPointsSubgroup_sup`: a join of Hopf ideals cuts out the
  intersection of the point subgroups.
* `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup`: functoriality of that subgroup in the
  value algebra.
* `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup_injective`: an injective homomorphism of
  value algebras induces an injective map of point subgroups.
* `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroupCongr`: that functoriality read through
  presentations of two subgroups as point subgroups, so that a carrier defined by a Hopf ideal
  states its induced map in its own named API.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u w w'

variable {R : Type u} [CommRing R] (n : ℕ)

section HopfIdealPoints

variable {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The subgroup of `GLₙ(A)` cut out by a Hopf ideal in the general-linear coordinate Hopf
algebra. -/
noncomputable def hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A] : Subgroup (Matrix.GeneralLinearGroup (Fin n) A) :=
  (CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I (CommAlgCat.of R A)).map
    (pointsMulEquiv n).toMonoidHom

/-- Membership in the general-linear point subgroup cut out by a Hopf ideal is vanishing on
that ideal. -/
@[simp]
theorem mem_hopfIdealPointsSubgroup_iff
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A] (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ hopfIdealPointsSubgroup n I A ↔
      ∀ x ∈ I, ((pointsMulEquiv (R := R) n).symm g).ofConv x = 0 := by
  unfold hopfIdealPointsSubgroup
  rw [Subgroup.mem_map_equiv, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]

/-- A general-linear point lying in the subgroup cut out by a Hopf ideal remains in that
subgroup after transport to its matrix representation. -/
theorem pointsMulEquiv_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A]
    (q : HopfAlgebra.points
      (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A))
    (hq : q ∈ CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I (CommAlgCat.of R A)) :
    pointsMulEquiv n q ∈ hopfIdealPointsSubgroup n I A := by
  exact ⟨q, hq, rfl⟩

/-- A point pulled back along a coordinate morphism that kills a Hopf ideal lies in the
general-linear subgroup cut out by that ideal. -/
theorem pointsMulEquiv_mapPointsFunctor_mem_hopfIdealPointsSubgroup
    {H : CommHopfAlgCat.{u} R}
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (φ : coordinateHopfAlgebra R n ⟶ H)
    (hφ : I.toIdeal ≤ RingHom.ker φ.hom.toAlgHom.toRingHom)
    (A : Type w) [CommRing A] [Algebra R A]
    (p : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R A)) :
    pointsMulEquiv n ((CommHopfAlgCat.mapPointsFunctor φ).app (CommAlgCat.of R A) p) ∈
      hopfIdealPointsSubgroup n I A := by
  let q : HopfAlgebra.points
      (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A) :=
    (CommHopfAlgCat.mapPointsFunctor φ).app (CommAlgCat.of R A) p
  apply pointsMulEquiv_mem_hopfIdealPointsSubgroup n I A q
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  dsimp only [q]
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply]
  have hx' := hφ hx
  rw [RingHom.mem_ker] at hx'
  have hxmap : φ.hom x = 0 := by
    simpa only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx'
  rw [hxmap, map_zero]

/-- Applying a value-algebra homomorphism entrywise preserves the general-linear point subgroup
cut out by a Hopf ideal. -/
theorem map_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (φ : A →ₐ[R] B)
    {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ hopfIdealPointsSubgroup n I A) :
    Matrix.GeneralLinearGroup.map (φ : A →+* B) g ∈ hopfIdealPointsSubgroup n I B := by
  obtain ⟨q, hq, rfl⟩ := hg
  refine ⟨AlgHom.mapValue φ q,
    CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I φ hq, ?_⟩
  simpa only [MulEquiv.coe_toMonoidHom] using pointsMulEquiv_mapValue n φ q

/-- The map between general-linear point subgroups cut out by the same Hopf ideal, induced by a
homomorphism of value algebras. -/
noncomputable def mapHopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (φ : A →ₐ[R] B) :
    hopfIdealPointsSubgroup n I A →* hopfIdealPointsSubgroup n I B :=
  (((Matrix.GeneralLinearGroup.map (φ : A →+* B)).domRestrict
    (hopfIdealPointsSubgroup n I A)).codRestrict
      (hopfIdealPointsSubgroup n I B)
      fun g => map_mem_hopfIdealPointsSubgroup n I φ g.property)

/-- The induced map on a general-linear Hopf-ideal point subgroup applies the value-algebra
homomorphism entrywise. -/
@[simp]
theorem coe_mapHopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (φ : A →ₐ[R] B)
    (g : hopfIdealPointsSubgroup n I A) :
    (mapHopfIdealPointsSubgroup n I φ g : Matrix.GeneralLinearGroup (Fin n) B) =
      Matrix.GeneralLinearGroup.map (φ : A →+* B) g := by
  rfl

/-- The identity value-algebra homomorphism induces the identity on a general-linear Hopf-ideal
point subgroup. -/
@[simp]
theorem mapHopfIdealPointsSubgroup_id
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A] :
    mapHopfIdealPointsSubgroup n I (AlgHom.id R A) =
      MonoidHom.id (hopfIdealPointsSubgroup n I A) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [coe_mapHopfIdealPointsSubgroup, MonoidHom.id_apply, AlgHom.id_toRingHom,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]

/-- Maps between general-linear Hopf-ideal point subgroups preserve composition of value-algebra
homomorphisms. -/
@[simp]
theorem mapHopfIdealPointsSubgroup_comp
    {C : Type*} [CommRing C] [Algebra R C]
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    mapHopfIdealPointsSubgroup n I (ψ.comp φ) =
      (mapHopfIdealPointsSubgroup n I ψ).comp
        (mapHopfIdealPointsSubgroup n I φ) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [coe_mapHopfIdealPointsSubgroup, MonoidHom.comp_apply,
    coe_mapHopfIdealPointsSubgroup, coe_mapHopfIdealPointsSubgroup,
    AlgHom.comp_toRingHom, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]

/-- An injective homomorphism of value algebras induces an injective map of general-linear
Hopf-ideal point subgroups: reading a matrix point over a subalgebra as a point over the ambient
algebra loses no information. -/
theorem mapHopfIdealPointsSubgroup_injective
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapHopfIdealPointsSubgroup n I φ) := by
  have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (φ : A →+* B)) :=
    Units.map_injective (Matrix.map_injective hφ)
  intro g g' h
  refine Subtype.ext (hmap ?_)
  rw [← coe_mapHopfIdealPointsSubgroup, ← coe_mapHopfIdealPointsSubgroup, h]

/-! ### Transport along a presentation of the point subgroup

A carrier cut out by a Hopf ideal typically carries its own `points A` together with a lemma
`points_def : points A = hopfIdealPointsSubgroup n I A`. The declarations below read the
functoriality above through two such presentations, so that a carrier states its induced map in
its own named API rather than in the presentation that API is defined by. -/

/-- `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup` read through presentations of two subgroups
as Hopf-ideal point subgroups of the general linear group. -/
noncomputable def mapHopfIdealPointsSubgroupCongr
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    {PA : Subgroup (Matrix.GeneralLinearGroup (Fin n) A)}
    {PB : Subgroup (Matrix.GeneralLinearGroup (Fin n) B)}
    (hA : PA = hopfIdealPointsSubgroup n I A) (hB : PB = hopfIdealPointsSubgroup n I B)
    (φ : A →ₐ[R] B) : PA →* PB :=
  (mapHopfIdealPointsSubgroup n I φ).subgroupCongr hA hB

/-- The transported map applies the value-algebra homomorphism entrywise. -/
@[simp]
theorem coe_mapHopfIdealPointsSubgroupCongr
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    {PA : Subgroup (Matrix.GeneralLinearGroup (Fin n) A)}
    {PB : Subgroup (Matrix.GeneralLinearGroup (Fin n) B)}
    (hA : PA = hopfIdealPointsSubgroup n I A) (hB : PB = hopfIdealPointsSubgroup n I B)
    (φ : A →ₐ[R] B) (g : PA) :
    (mapHopfIdealPointsSubgroupCongr n I hA hB φ g :
        Matrix.GeneralLinearGroup (Fin n) B) =
      Matrix.GeneralLinearGroup.map (φ : A →+* B) g := by
  simp only [mapHopfIdealPointsSubgroupCongr, MonoidHom.coe_subgroupCongr_apply,
    coe_mapHopfIdealPointsSubgroup]

/-- The identity value-algebra homomorphism induces the identity on a presented point subgroup. -/
@[simp]
theorem mapHopfIdealPointsSubgroupCongr_id
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    {PA : Subgroup (Matrix.GeneralLinearGroup (Fin n) A)}
    (hA : PA = hopfIdealPointsSubgroup n I A) :
    mapHopfIdealPointsSubgroupCongr n I hA hA (AlgHom.id R A) = MonoidHom.id PA := by
  rw [mapHopfIdealPointsSubgroupCongr, mapHopfIdealPointsSubgroup_id,
    MonoidHom.subgroupCongr_id]

/-- The maps induced on presented point subgroups compose.

Not a `simp` lemma: the middle subgroup and its presentation appear only on the right-hand side,
so `simp` would have to invent them and would rewrite into an unrelated instantiation. Rewrite
pointwise through `TauCeti.GeneralLinear.coe_mapHopfIdealPointsSubgroupCongr` instead. -/
theorem mapHopfIdealPointsSubgroupCongr_comp
    {C : Type*} [CommRing C] [Algebra R C]
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    {PA : Subgroup (Matrix.GeneralLinearGroup (Fin n) A)}
    {PB : Subgroup (Matrix.GeneralLinearGroup (Fin n) B)}
    {PC : Subgroup (Matrix.GeneralLinearGroup (Fin n) C)}
    (hA : PA = hopfIdealPointsSubgroup n I A) (hB : PB = hopfIdealPointsSubgroup n I B)
    (hC : PC = hopfIdealPointsSubgroup n I C) (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    mapHopfIdealPointsSubgroupCongr n I hA hC (ψ.comp φ) =
      (mapHopfIdealPointsSubgroupCongr n I hB hC ψ).comp
        (mapHopfIdealPointsSubgroupCongr n I hA hB φ) := by
  simp only [mapHopfIdealPointsSubgroupCongr, mapHopfIdealPointsSubgroup_comp,
    MonoidHom.subgroupCongr_comp hA hB hC]

/-- An injective value-algebra homomorphism induces an injective map of presented point
subgroups. -/
theorem mapHopfIdealPointsSubgroupCongr_injective
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    {PA : Subgroup (Matrix.GeneralLinearGroup (Fin n) A)}
    {PB : Subgroup (Matrix.GeneralLinearGroup (Fin n) B)}
    (hA : PA = hopfIdealPointsSubgroup n I A) (hB : PB = hopfIdealPointsSubgroup n I B)
    {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapHopfIdealPointsSubgroupCongr n I hA hB φ) :=
  MonoidHom.subgroupCongr_injective hA hB (mapHopfIdealPointsSubgroup_injective n I hφ)

/-- Larger Hopf ideals cut out smaller general-linear point subgroups. -/
theorem hopfIdealPointsSubgroup_le_of_le
    {I J : HopfIdeal R (coordinateHopfAlgebra R n)} (hIJ : I ≤ J)
    (A : Type w) [CommRing A] [Algebra R A] :
    hopfIdealPointsSubgroup n J A ≤ hopfIdealPointsSubgroup n I A :=
  Subgroup.map_mono (CommHopfAlgCat.quotientPointsSubgroup_le_of_le
    (coordinateHopfAlgebra R n) hIJ (CommAlgCat.of R A))

/-- **A join of Hopf ideals cuts out the intersection of the point subgroups.** Scheme-theoretic
intersection of two closed subgroup schemes of `GLₙ` is intersection of their matrix points. -/
theorem hopfIdealPointsSubgroup_sup
    (I J : HopfIdeal R (coordinateHopfAlgebra R n))
    (A : Type w) [CommRing A] [Algebra R A] :
    hopfIdealPointsSubgroup n (I ⊔ J) A =
      hopfIdealPointsSubgroup n I A ⊓ hopfIdealPointsSubgroup n J A := by
  unfold hopfIdealPointsSubgroup
  rw [CommHopfAlgCat.quotientPointsSubgroup_sup]
  exact Subgroup.map_inf _ _ _ (pointsMulEquiv n).injective

end HopfIdealPoints

end TauCeti.GeneralLinear
