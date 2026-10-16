/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Dynamic Levi subgroups under closed immersions

A morphism of affine group schemes carries the Levi subgroup of a cocharacter into the Levi
subgroup of the induced cocharacter. If the morphism is injective on `R[T;T⁻¹] ⊗ A`-valued
points, Levi membership is detected by the ambient group, so the Levi subgroup is the inverse
image of an ambient Levi subgroup. This injectivity holds for every closed immersion: in
coordinates a closed immersion is a surjective bialgebra homomorphism, and pre-composition by
one is injective on points (`TauCeti.AlgHom.mapDomain_injective_of_surjective`).

Consequently, a Hopf ideal cutting out the ambient Levi has image cutting out the Levi of the
closed subgroup, which gives a representing closed subgroup scheme.

The naturality and membership results hold over a commutative semiring and for arbitrary
commutative value algebras; the representability result holds over a commutative ring. No
smoothness or finite-type assumption is needed.

## Main results

* `TauCeti.Cocharacter.mapDomain_conjugate`: a group-scheme morphism commutes with generic
  cocharacter conjugation.
* `TauCeti.Cocharacter.mem_levi_iff_of_injective`: an injective map on Laurent-valued points
  detects Levi membership in the ambient group.
* `TauCeti.Cocharacter.levi_eq_comap_of_injective`: under the same hypothesis, the Levi is the
  inverse image of the ambient Levi.
* `TauCeti.Cocharacter.mem_levi_iff_of_surjective` and
  `TauCeti.Cocharacter.levi_eq_comap_of_surjective`: the closed-immersion specializations.
* `TauCeti.Cocharacter.mem_quotientPointsSubgroup_map_iff_mem_levi` and
  `TauCeti.Cocharacter.leviClosedSubgroupPointsIso`: the image of a Hopf ideal cutting out the
  ambient Levi represents the Levi of the closed subgroup.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

namespace TauCeti.Cocharacter

open WithConv

variable {R H K A : Type*} [CommSemiring R] [Semiring H] [Semiring K]
variable [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K]
variable [CommSemiring A] [Algebra R A]

/-- The generic point of a cocharacter commutes with precomposition by a bialgebra morphism. -/
theorem mapDomain_genericPoint (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) :
    AlgHom.mapDomain φ (genericPoint A l) = genericPoint A (l.comp φ) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  simp only [AlgHom.mapDomain_apply_apply, genericPoint_eq_pointsHom,
    pointsHom_apply, BialgHom.coe_comp, Function.comp_apply]

/-- A constant point commutes with precomposition by a bialgebra morphism. -/
theorem mapDomain_constPoint (φ : H →ₐc[R] K)
    (g : WithConv (K →ₐ[R] A)) :
    AlgHom.mapDomain φ (constPoint A g) =
      constPoint A (AlgHom.mapDomain φ g) := by
  rw [constPoint_apply, constPoint_apply]
  convert DFunLike.congr_fun
    (AlgHom.mapValue_mapDomain φ (IsScalarTower.toAlgHom R A (LaurentPolynomial A))) g using 1 <;>
      simp only [MonoidHom.comp_apply, AlgHom.mapDomain_apply, AlgHom.mapValue_apply,
        AlgHom.comp_assoc]

/-- Generic conjugation is natural in the coordinate Hopf algebra. -/
theorem mapDomain_conjugate (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) (g : WithConv (K →ₐ[R] A)) :
    AlgHom.mapDomain φ (conjugate A l g) =
      conjugate A (l.comp φ) (AlgHom.mapDomain φ g) := by
  simp only [conjugate_apply, map_mul, map_inv, mapDomain_genericPoint,
    mapDomain_constPoint]

/-- Every morphism of affine group schemes carries the Levi of a cocharacter into the Levi of
the induced cocharacter. -/
theorem mapDomain_mem_levi (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) {g : WithConv (K →ₐ[R] A)}
    (hg : g ∈ levi A l) : AlgHom.mapDomain φ g ∈ levi A (l.comp φ) := by
  rw [mem_levi_iff, ← mapDomain_conjugate, ← mapDomain_constPoint,
    mem_levi_iff.mp hg]

/-- If pre-composition by `φ` is injective on `LaurentPolynomial A`-valued points, a point is in
the dynamic Levi exactly when its image lies in the ambient dynamic Levi. This applies to closed
immersions, see `mem_levi_iff_of_surjective`. -/
theorem mem_levi_iff_of_injective (φ : H →ₐc[R] K)
    (hφ : Function.Injective (AlgHom.mapDomain (A := LaurentPolynomial A) φ))
    (l : K →ₐc[R] LaurentPolynomial R)
    (g : WithConv (K →ₐ[R] A)) :
    g ∈ levi A l ↔ AlgHom.mapDomain φ g ∈ levi A (l.comp φ) := by
  refine ⟨mapDomain_mem_levi φ l, fun hg => ?_⟩
  apply mem_levi_iff.mpr
  apply hφ
  rw [mapDomain_conjugate, mapDomain_constPoint]
  exact mem_levi_iff.mp hg

/-- If pre-composition by `φ` is injective on `LaurentPolynomial A`-valued points, the dynamic
Levi is the inverse image of the ambient dynamic Levi. -/
theorem levi_eq_comap_of_injective (φ : H →ₐc[R] K)
    (hφ : Function.Injective (AlgHom.mapDomain (A := LaurentPolynomial A) φ))
    (l : K →ₐc[R] LaurentPolynomial R) :
    levi A l = (levi A (l.comp φ)).comap (AlgHom.mapDomain φ) := by
  ext g
  exact mem_levi_iff_of_injective φ hφ l g

/-- For a closed immersion, a point is in the dynamic Levi exactly when its image lies in the
ambient dynamic Levi. This holds over every commutative value algebra, including nonreduced
ones. -/
theorem mem_levi_iff_of_surjective (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) (g : WithConv (K →ₐ[R] A)) :
    g ∈ levi A l ↔ AlgHom.mapDomain φ g ∈ levi A (l.comp φ) :=
  mem_levi_iff_of_injective φ (AlgHom.mapDomain_injective_of_surjective φ hφ) l g

/-- The dynamic Levi of a closed subgroup is the inverse image of the ambient dynamic Levi. -/
theorem levi_eq_comap_of_surjective (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    levi A l = (levi A (l.comp φ)).comap (AlgHom.mapDomain φ) :=
  levi_eq_comap_of_injective φ (AlgHom.mapDomain_injective_of_surjective φ hφ) l

end TauCeti.Cocharacter

namespace TauCeti.Cocharacter

open CategoryTheory

universe u v w

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- Let `φ` be a closed immersion and `J` a Hopf ideal cutting out the Levi of the induced
cocharacter in the ambient group. Then the image of `J` cuts out the Levi of the closed
subgroup. -/
theorem mem_quotientPointsSubgroup_map_iff_mem_levi (φ : H ⟶ K)
    (hφ : Function.Surjective φ.hom) (l : K →ₐc[R] LaurentPolynomial R) (J : HopfIdeal R H)
    (A : CommAlgCat.{w} R)
    (hJ : ∀ g : HopfAlgebra.points (R := R) (H := H) A,
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H J A ↔ g ∈ levi A (l.comp φ.hom))
    (g : HopfAlgebra.points (R := R) (H := K) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup K (J.map φ.hom) A ↔ g ∈ levi A l := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff φ,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, hJ]
  exact (mem_levi_iff_of_surjective φ.hom hφ l g).symm

/-- The quotient by the image of a Hopf ideal cutting out the ambient Levi represents the
dynamic Levi of the closed subgroup, naturally in the commutative value algebra. -/
noncomputable def leviClosedSubgroupPointsIso (φ : H ⟶ K)
    (hφ : Function.Surjective φ.hom) (l : K →ₐc[R] LaurentPolynomial R) (J : HopfIdeal R H)
    (hJ : ∀ (A : CommAlgCat.{w} R) (g : HopfAlgebra.points (R := R) (H := H) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H J A ↔ g ∈ levi A (l.comp φ.hom)) :
    HopfAlgebra.pointsFunctor (R := R) (H := CommHopfAlgCat.quotient K (J.map φ.hom)) ≅
      leviFunctor l :=
  CommHopfAlgCat.quotientPointsSubgroupRepresentingIso K (J.map φ.hom) (fun A ↦ levi A l)
    (fun A g ↦ mem_quotientPointsSubgroup_map_iff_mem_levi φ hφ l J A (hJ A) g)

/-- The ambient point underlying the represented Levi point is induced by the quotient
coordinate map. -/
@[simp]
theorem coe_leviClosedSubgroupPointsIso_hom_app_apply (φ : H ⟶ K)
    (hφ : Function.Surjective φ.hom) (l : K →ₐc[R] LaurentPolynomial R) (J : HopfIdeal R H)
    (hJ : ∀ (A : CommAlgCat.{w} R) (g : HopfAlgebra.points (R := R) (H := H) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H J A ↔ g ∈ levi A (l.comp φ.hom))
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := CommHopfAlgCat.quotient K (J.map φ.hom)) A) :
    (((eqToHom (leviFunctor_obj l A))
      ((leviClosedSubgroupPointsIso φ hφ l J hJ).hom.app A f) : levi A l) :
        HopfAlgebra.points (R := R) (H := K) A) =
      CommHopfAlgCat.quotientPointsHom K (J.map φ.hom) A f := by
  unfold leviClosedSubgroupPointsIso
  convert CommHopfAlgCat.coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
    K (J.map φ.hom) (fun B ↦ levi B l)
    (fun B g ↦ mem_quotientPointsSubgroup_map_iff_mem_levi φ hφ l J B (hJ B) g) A f using 1
  rfl

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the
dynamic-Levi point. -/
@[simp]
theorem quotientPointsHom_leviClosedSubgroupPointsIso_inv_app_apply (φ : H ⟶ K)
    (hφ : Function.Surjective φ.hom) (l : K →ₐc[R] LaurentPolynomial R) (J : HopfIdeal R H)
    (hJ : ∀ (A : CommAlgCat.{w} R) (g : HopfAlgebra.points (R := R) (H := H) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H J A ↔ g ∈ levi A (l.comp φ.hom))
    (A : CommAlgCat.{w} R) (g : levi A l) :
    CommHopfAlgCat.quotientPointsHom K (J.map φ.hom) A
      ((leviClosedSubgroupPointsIso φ hφ l J hJ).inv.app A g) = g.1 := by
  unfold leviClosedSubgroupPointsIso
  convert CommHopfAlgCat.quotientPointsHom_quotientPointsSubgroupRepresentingIso_inv_app_apply
    K (J.map φ.hom) (fun B ↦ levi B l)
    (fun B g ↦ mem_quotientPointsSubgroup_map_iff_mem_levi φ hφ l J B (hJ B) g) A g using 1

end TauCeti.Cocharacter
