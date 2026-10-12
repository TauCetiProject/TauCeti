/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Chosen split maximal tori over a ring

`SplitMaximalTorus R H r` is a closed immersion of the standard rank-`r` split torus into
the affine group with coordinate algebra `H`, maximal on every geometric fiber. It carries
the coordinate morphism itself, rather than an existence assertion. The corresponding Hopf
ideal and its quotient presentation are recovered from that morphism.

Maximality on geometric fibers is essential: maximality merely among tori over the base
does not imply this condition. A chosen split maximal torus does not include a pinning or
trivializations of the root spaces over the base.

Chosen split maximal tori are transported along isomorphisms of coordinate Hopf algebras
(`SplitMaximalTorus.comapOfIso`) and base-changed along ring maps `R → S`
(`SplitMaximalTorus.baseChange`). The base-changed torus is cut out by the base change of the
original defining ideal, and its geometric fibers are geometric fibers of the original torus, so
a torus chosen over `ℤ` specializes to every commutative ring.

## Main declarations

* `TauCeti.SplitMaximalTorus`: a chosen split maximal torus of an affine group over a ring.
* `TauCeti.SplitMaximalTorus.comapOfIso`: transport along an isomorphism of coordinate Hopf
  algebras.
* `TauCeti.SplitMaximalTorus.baseChange`: base change along `R → S`.
* `TauCeti.SplitMaximalTorus.definingIdeal_baseChange`: the base-changed torus is cut out by the
  base change of the defining ideal.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.2.1 and Example 3.2.3.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A parametrized split maximal torus of an affine group over `R`. The coordinate map is
surjective, expressing a closed immersion, and its defining ideal is maximal as a torus
on every geometric fiber. -/
structure SplitMaximalTorus (R : Type u) [CommRing R]
    (H : CommHopfAlgCat.{u} R) [Algebra.FiniteType R H] (r : ℕ) where
  /-- Restriction of functions to the chosen rank-`r` split torus. -/
  coordinateMap : H ⟶
    (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj
  /-- The chosen torus is a closed subgroup. -/
  surjective : Function.Surjective coordinateMap.hom
  /-- The chosen torus is maximal in every geometric fiber. -/
  maximal : ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k)
        (HopfIdeal.kerOfSurjective coordinateMap.hom surjective))

namespace SplitMaximalTorus

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R}
    [Algebra.FiniteType R H] {r : ℕ}

/-- A chosen split maximal torus is determined by its coordinate map. -/
@[ext]
theorem ext {T U : SplitMaximalTorus R H r} (h : T.coordinateMap = U.coordinateMap) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- The Hopf ideal cutting out the chosen split maximal torus. -/
noncomputable def definingIdeal (T : SplitMaximalTorus R H r) : HopfIdeal R H :=
  HopfIdeal.kerOfSurjective T.coordinateMap.hom T.surjective

/-- A function belongs to the defining ideal exactly when its restriction to the torus is zero. -/
@[simp]
theorem mem_definingIdeal (T : SplitMaximalTorus R H r) (x : H) :
    x ∈ T.definingIdeal ↔ T.coordinateMap.hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective T.coordinateMap.hom T.surjective

/-- The quotient coordinate algebra of the chosen torus is the standard split-torus algebra. -/
noncomputable def coordinateIso (T : SplitMaximalTorus R H r) :
    FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _
    (CommHopfAlgCat.quotientKerOfSurjectiveIso T.coordinateMap T.surjective)

/-- The quotient presentation recovers restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_coordinateIso_hom (T : SplitMaximalTorus R H r) :
    FiniteTypeCommHopfAlgCat.mkQuotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal ≫
        T.coordinateIso.hom =
      ObjectProperty.homMk T.coordinateMap :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed subgroup defined by the chosen torus is a split torus over the base ring. -/
theorem splitTorus_quotient (T : SplitMaximalTorus R H r) :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨T.coordinateIso.symm⟩⟩

/-- The chosen torus is maximal after extension to any algebraically closed field over `R`. -/
theorem isMaximalTorus_geometricFiber (T : SplitMaximalTorus R H r)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) T.definingIdeal) :=
  T.maximal k

section ComapOfIso

variable {L : CommHopfAlgCat.{u} R} [Algebra.FiniteType R L]

/-- Transport of a chosen split maximal torus across an isomorphism `e : H ≅ L` of coordinate
Hopf algebras: the torus of `L` becomes a torus of `H` by restricting functions along `e`. -/
noncomputable def comapOfIso (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    SplitMaximalTorus R H r where
  coordinateMap := e.hom ≫ T.coordinateMap
  surjective := by
    rw [CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact T.surjective.comp (ConcreteCategory.bijective_of_isIso e.hom).2
  maximal := by
    intro k _ _ _
    have hker (hs : Function.Surjective (e.hom ≫ T.coordinateMap).hom) :
        HopfIdeal.kerOfSurjective _ hs = T.definingIdeal.comapOfSurjective e.hom.hom
          (ConcreteCategory.bijective_of_isIso e.hom).2 := by
      ext x
      simp [definingIdeal]
    let ek : FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.baseChange (K := k) H) ≅
        FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.baseChange (K := k) L) :=
      ObjectProperty.isoMk _ ((CommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e)
    rw [hker, CommHopfAlgCat.baseChangeHopfIdeal_comapOfIso]
    exact (T.isMaximalTorus_geometricFiber k).comapOfIso ek

/-- The transported torus has coordinate map `e.hom ≫ T.coordinateMap`. -/
@[simp]
theorem comapOfIso_coordinateMap (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).coordinateMap = e.hom ≫ T.coordinateMap :=
  (rfl)

/-- The defining ideal of the transported torus is the pullback of the original defining ideal
along `e`. -/
@[simp]
theorem definingIdeal_comapOfIso (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).definingIdeal =
      T.definingIdeal.comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 := by
  ext x
  simp

end ComapOfIso

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The coordinate map of the base-changed torus cuts out the base change of the defining
ideal. -/
private theorem kerOfSurjective_baseChangeMap_comp (T : SplitMaximalTorus R H r)
    (hT : Function.Surjective (CommHopfAlgCat.baseChangeMap (K := S) T.coordinateMap ≫
      (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom).hom) :
    HopfIdeal.kerOfSurjective _ hT = CommHopfAlgCat.baseChangeHopfIdeal (K := S) T.definingIdeal :=
  ((HopfIdeal.map_id _).symm.trans
    (CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective (Iso.refl _)
      (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))) T.surjective hT
      (by rw [Iso.refl_inv, Category.id_comp]))).symm

/-- **Base change of a chosen split maximal torus** along `R → S`. Its coordinate map is the
base change of the original one, read in the standard split-torus coordinates over `S`; its
geometric fibers are geometric fibers of the original torus. -/
noncomputable def baseChange (T : SplitMaximalTorus R H r) :
    SplitMaximalTorus S (CommHopfAlgCat.baseChange (K := S) H) r where
  coordinateMap := CommHopfAlgCat.baseChangeMap (K := S) T.coordinateMap ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
      (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom
  surjective := by
    rw [CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp
      (CommHopfAlgCat.baseChangeMap_surjective _ T.surjective)
  maximal := by
    intro k _ _ _
    let _ : Algebra R k := ((algebraMap S k).comp (algebraMap R S)).toAlgebra
    let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let e : FiniteTypeCommHopfAlgCat.of k
          (CommHopfAlgCat.baseChange (K := k) (CommHopfAlgCat.baseChange (K := S) H)) ≅
        FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.baseChange (K := k) H) :=
      ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso R k H)
    rw [kerOfSurjective_baseChangeMap_comp, CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal]
    exact (T.isMaximalTorus_geometricFiber k).comapOfIso e

/-- The base-changed torus has the base-changed coordinate map. -/
@[simp]
theorem baseChange_coordinateMap (T : SplitMaximalTorus R H r) :
    (T.baseChange S).coordinateMap =
      CommHopfAlgCat.baseChangeMap (K := S) T.coordinateMap ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
          (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom :=
  (rfl)

/-- The defining ideal of the base-changed torus is the base change of the defining ideal. -/
@[simp]
theorem definingIdeal_baseChange (T : SplitMaximalTorus R H r) :
    (T.baseChange S).definingIdeal =
      CommHopfAlgCat.baseChangeHopfIdeal (K := S) T.definingIdeal :=
  kerOfSurjective_baseChangeMap_comp S T (T.baseChange S).surjective

end BaseChange

end SplitMaximalTorus

end TauCeti
