/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel

/-!
# Split extensions are semidirect products

Let `G = Spec H` be an affine group over a commutative ring `R`, let `N ⊆ G` be the normal closed
subgroup cut out by a normal Hopf ideal `I`, and let `T ⊆ G` be the closed subgroup cut out by a
Hopf ideal `J`. Suppose `π : G → Q` is a homomorphism of affine groups (dually, a Hopf-algebra
morphism `K ⟶ H`) whose kernel is `N`, and suppose that the composite `T → G → Q` is an
isomorphism. Then multiplication `N ⋊ T → G` is an isomorphism of affine groups:

```text
G ≅ N ⋊ T.
```

The proof is on points over every commutative `R`-algebra `A`, followed by Yoneda. If
`u t = u' t'` with `u, u' ∈ N(A)` and `t, t' ∈ T(A)`, then `π(t) = π(t')`, since `π` kills
`N(A)`; hence `t = t'` because `T(A) → Q(A)` is injective, and then `u = u'`. Given `g ∈ G(A)`,
choose `t ∈ T(A)` with `π(t) = π(g)`; then `g t⁻¹` lies in the kernel `N(A)` of `π`, so `g` is
a product `u t`.

## Main declarations

* `TauCeti.CommHopfAlgCat.bijective_mapPointsFunctor_productMapOfNormal_app_of_isIso`: on
  points over every commutative algebra, multiplication `N ⋊ T → G` is bijective.
* `TauCeti.CommHopfAlgCat.isIso_productMapOfNormal_of_isIso`: multiplication `N ⋊ T → G` is an
  isomorphism of affine groups.
* `TauCeti.CommHopfAlgCat.normalSemidirectProductIsoOfIsIso`: the resulting isomorphism of
  coordinate Hopf algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 2 (semidirect products).
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory Opposite CartesianMonoidalCategory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R]

variable {H K : _root_.CommHopfAlgCat.{u} R} (I J : HopfIdeal R H) (hI : I.IsNormal)
  (π : K ⟶ H)

/-- **Split extensions are semidirect products, on points.** Let `I` be a normal Hopf ideal of
`H` and `π : K ⟶ H` a Hopf-algebra morphism with kernel Hopf ideal `I`, so that `π` represents a
homomorphism `G → Q` with kernel `N`. If the closed subgroup `T` cut out by `J` maps
isomorphically to `Q`, then over every commutative algebra `A`, multiplication
`N(A) ⋊ T(A) → G(A)` is bijective. -/
theorem bijective_mapPointsFunctor_productMapOfNormal_app_of_isIso
    (hπ : kernelHopfIdeal π = I) [IsIso (π ≫ mkQuotient H J)] (A : CommAlgCat.{u} R) :
    Function.Bijective
      ((mapPointsFunctor (productMapOfNormal H I J hI ≫
        (normalSemidirectProductIso H I J hI).hom)).app A) := by
  let φ := productMapOfNormal H I J hI ≫ (normalSemidirectProductIso H I J hI).hom
  let e := grpObjPointsMulEquiv (quotientNormalConjugation H I J hI).coordinateHopfAlgebra (op A)
  let a := grpObjPointsMulEquiv (quotient H I) (op A)
  let b := grpObjPointsMulEquiv (quotient H J) (op A)
  let ιI := quotientPointsHom H I A
  let ιJ := quotientPointsHom H J A
  let p := BialgHom.mapDomain (A := A) π.hom
  have hmul (q) : (mapPointsFunctor φ).app A (e q) =
      ιI (a (q ≫ fst _ _)) * ιJ (b (q ≫ snd _ _)) :=
    mapPointsFunctor_productMapOfNormal_app_grpObjPointsMulEquiv H I J hI A q
  have hker (u) : p (ιI u) = 1 := mapDomain_quotientPointsHom_eq_one π hπ A u
  -- On the acting factor, `π` is the bijective point map of `π ≫ mkQuotient H J`.
  have hcomp (t) : p (ιJ t) = (mapPointsFunctor (π ≫ mkQuotient H J)).app A t :=
    (mapPointsFunctor_comp_app_apply π (mkQuotient H J) A t).symm
  have hbij : Function.Bijective ((mapPointsFunctor (π ≫ mkQuotient H J)).app A) :=
    ConcreteCategory.bijective_of_isIso
      (((pointsFunctor (R := R)).map (π ≫ mkQuotient H J).op).app A)
  constructor
  · intro x y hxy
    obtain ⟨q, rfl⟩ := e.surjective x
    obtain ⟨q', rfl⟩ := e.surjective y
    rw [hmul, hmul] at hxy
    have hp := congrArg p hxy
    rw [map_mul, map_mul, hker, hker, one_mul, one_mul] at hp
    have hsnd : q ≫ snd _ _ = q' ≫ snd _ _ :=
      b.injective (hbij.1 ((hcomp _).symm.trans (hp.trans (hcomp _))))
    rw [hsnd] at hxy
    have hfst : q ≫ fst _ _ = q' ≫ fst _ _ :=
      a.injective (quotientPointsHom_injective H I A (mul_right_cancel hxy))
    rw [CartesianMonoidalCategory.hom_ext q q' hfst hsnd]
  · intro g
    -- Normalize the carriers of the points functor to the point groups used by `e`, `a`, `b`.
    change HopfAlgebra.points (R := R) (H := H) A at g
    obtain ⟨t, ht⟩ := hbij.2 (p g)
    -- As for `g`: `hbij` gives `t` in the carrier of the points functor, and `b.symm` expects
    -- the definitionally equal point group of `quotient H J`.
    change HopfAlgebra.points (R := R) (H := quotient H J) A at t
    replace ht : p (ιJ t) = p g := (hcomp t).trans ht
    have hmem : g * (ιJ t)⁻¹ ∈ quotientPointsSubgroup H I A := by
      have h1 : p (g * (ιJ t)⁻¹) = 1 := by rw [map_mul, map_inv, ht, mul_inv_cancel]
      rw [← hπ, ← mapPointsFunctor_app_eq_one_iff π A, ← BialgHom.mapDomain_apply]
      exact h1
    obtain ⟨u, hu⟩ := hmem
    let q : op A ⟶ (quotientNormalConjugation H I J hI).coordinateHopfAlgebra.grpObj :=
      lift (a.symm u) (b.symm t)
    have hq₁ : q ≫ fst _ _ = a.symm u := lift_fst _ _
    have hq₂ : q ≫ snd _ _ = b.symm t := lift_snd _ _
    refine ⟨e q, (hmul q).trans ?_⟩
    rw [hq₁, hq₂, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hu, inv_mul_cancel_right]

/-- **Split extensions are semidirect products.** Let `I` be a normal Hopf ideal of `H` and
`π : K ⟶ H` a Hopf-algebra morphism with kernel Hopf ideal `I`, so that `π` represents a
homomorphism `G → Q` with kernel `N`. If the closed subgroup `T` cut out by `J` maps
isomorphically to `Q`, then multiplication `N ⋊ T → G` is an isomorphism of affine groups. -/
theorem isIso_productMapOfNormal_of_isIso (hπ : kernelHopfIdeal π = I)
    [IsIso (π ≫ mkQuotient H J)] : IsIso (productMapOfNormal H I J hI) := by
  let φ := productMapOfNormal H I J hI ≫ (normalSemidirectProductIso H I J hI).hom
  have : IsIso (mapPointsFunctor.{u, u, u} φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun A ↦ (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_mapPointsFunctor_productMapOfNormal_app_of_isIso I J hI π hπ A)
  have : IsIso φ := isIso_of_isIso_mapPointsFunctor φ
  exact IsIso.of_isIso_comp_right _ (normalSemidirectProductIso H I J hI).hom

/-- The isomorphism `G ≅ N ⋊ T` of a split extension, as an isomorphism of coordinate Hopf
algebras whose forward morphism is dual to multiplication. -/
noncomputable def normalSemidirectProductIsoOfIsIso (hπ : kernelHopfIdeal π = I)
    [IsIso (π ≫ mkQuotient H J)] : H ≅ normalSemidirectProduct H I J hI :=
  have := isIso_productMapOfNormal_of_isIso I J hI π hπ
  asIso (productMapOfNormal H I J hI)

/-- The forward morphism of `normalSemidirectProductIsoOfIsIso` is dual to multiplication. -/
@[simp]
theorem normalSemidirectProductIsoOfIsIso_hom (hπ : kernelHopfIdeal π = I)
    [IsIso (π ≫ mkQuotient H J)] :
    (normalSemidirectProductIsoOfIsIso I J hI π hπ).hom = productMapOfNormal H I J hI := by
  rw [normalSemidirectProductIsoOfIsIso, asIso_hom]

end

end TauCeti.CommHopfAlgCat
