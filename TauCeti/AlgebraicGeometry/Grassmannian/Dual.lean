/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints
public import TauCeti.RingTheory.Grassmannian.Dual

/-!
# The dual Grassmannian

Let `M` be a finite projective module over a commutative ring `R`, of constant rank `k + l`, with
dual `M^∨`. This file constructs the isomorphism of Grassmannian schemes over `Spec R`

`G(k, M) ≅ G(l, M^∨)` (`Module.Grassmannian.schemeDualIso`).

A point of `G(k, M)` over an `R`-algebra `A` is a submodule `N ⊆ A ⊗[R] M` with finite projective
quotient of rank `k`; `N` is then a subbundle of rank `l`
(`Module.Grassmannian.rankAtStalk_toSubmodule`). The isomorphism sends the point classifying `N`
to the point classifying its annihilator `N^⊥ ⊆ A ⊗[R] M^∨`, the kernel of the restriction
`(A ⊗[R] M)^∨ → N^∨` (`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_hom`), and its inverse
sends the point classifying `K` to the point classifying the coannihilator of `K`
(`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_inv`). So over every `A`, the point of
`G(l, M^∨)` classifying `K` is the annihilator of the point of `G(k, M)` classifying `N` exactly
when `N` is the coannihilator of `K`.

The maps of points are natural in `A` (`Module.Grassmannian.baseChangeDualEquiv_map`), so each is
composition with a morphism of schemes (`AlgebraicGeometry.Scheme.homOfAffinePoints`), and the
two composites are identities because they are on points.

## Main definitions

* `Module.Grassmannian.schemeDualIso h`: the isomorphism `G(k, M) ≅ G(l, M^∨)` for `M` finite
  projective of constant rank `k + l`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_schemeDualIso_hom` and
  `Module.Grassmannian.toSchemeHom_comp_schemeDualIso_inv`: the isomorphism on points.
* `Module.Grassmannian.schemeDualIso_hom_toSpec` and
  `Module.Grassmannian.schemeDualIso_inv_toSpec`: the isomorphism lies over `Spec R`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M M' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {k l : ℕ}

section OfPoints

/-! The helpers in this section build a morphism of Grassmannian schemes from a family of maps
of points natural in the algebra `A`, and prove that morphisms out of the Grassmannian are
determined by their values on points. They follow the construction of
`Module.Grassmannian.baseChangeHom` from `baseChangeAux` and `baseChangePoint` in
`TauCeti/AlgebraicGeometry/Grassmannian/BaseChange.lean`, over a fixed base ring. -/

/-- Morphisms out of the Grassmannian agree when they agree on the point classifying every `N`. -/
private theorem hom_ext_of_points {X : Scheme.{u}} {f g : scheme R M k ⟶ X}
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)),
      toSchemeHom N ≫ f = toSchemeHom N ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  -- make `B` an `R`-algebra through `a`, so that `a` classifies a point over `B`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  let _ : Algebra R B := φ.hom.toAlgebra
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  exact h B N

/-- The point of `G(l, M')` assigned by `F` to the point classified by `a`. The algebra structure
on `A` is an explicit argument, so that `pointsAux_congr` can compare different choices. -/
private noncomputable def pointsAux
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    (A : Type u) [CommRing A] (_ : Algebra R A) (a : Spec (.of A) ⟶ scheme R M k)
    (ha : a ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec (.of A) ⟶ scheme R M' l :=
  toSchemeHom (F A ((schemeHomEquiv R M k A).symm ⟨a, ha⟩))

-- `pointsAux` depends on the algebra structure on `A` only through its equality class.
private lemma pointsAux_congr
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    (A : Type u) [CommRing A] (i j : Algebra R A) (h : i = j) (a : Spec (.of A) ⟶ scheme R M k)
    (ha ha') : pointsAux F A i a ha = pointsAux F A j a ha' := by
  subst h
  rfl

/-- The map of affine points induced by `F`: the algebra structure of `A` over `R` is read off
from the composite `Spec A ⟶ G(k, M) ⟶ Spec R`. -/
private noncomputable def pointsMap
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    {A : CommRingCat.{u}} (a : Spec A ⟶ scheme R M k) : Spec A ⟶ scheme R M' l :=
  letI : Algebra R A := (Spec.preimage (a ≫ toSpec R M k)).hom.toAlgebra
  pointsAux F A ‹_› a (Spec.map_preimage _).symm

private lemma pointsMap_toSchemeHom
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    pointsMap F (toSchemeHom N) = toSchemeHom (F A N) := by
  have hφ : (Spec.preimage (toSchemeHom N ≫ toSpec R M k)).hom = algebraMap R A := by
    rw [toSchemeHom_toSpec, Spec.preimage_map, CommRingCat.hom_ofHom]
  have hi : (Spec.preimage (toSchemeHom N ≫ toSpec R M k)).hom.toAlgebra = ‹Algebra R A› :=
    Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r
  unfold pointsMap
  rw [pointsAux_congr F A _ _ hi _ _ (toSchemeHom_toSpec N), pointsAux]
  congr 2
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `pointsMap F` is natural in the affine scheme when `F` is natural in the algebra. -/
private lemma pointsMap_comp
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    (hF : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)), F B (map f N) = map f (F A N))
    {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B) (a : Spec B ⟶ scheme R M k) :
    pointsMap F (ψ ≫ a) = ψ ≫ pointsMap F a := by
  -- give `B` and `C` the algebra structures over `R` read off from `a` and `ψ ≫ a`; with them,
  -- `χ` is an `R`-algebra map `χ'`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R B := φ.hom.toAlgebra
  let _ : Algebra R C := (χ.hom.comp φ.hom).toAlgebra
  let χ' : B →ₐ[R] C := { χ.hom with commutes' := fun _ ↦ rfl }
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := (toSchemeHom_map χ' N).symm
  rw [h, pointsMap_toSchemeHom, pointsMap_toSchemeHom, hF, toSchemeHom_map]
  -- `χ'` has underlying ring map `χ`
  rfl

/-- The morphism `G(k, M) ⟶ G(l, M')` given on points by a family of maps `F` natural in the
algebra. -/
private noncomputable def homOfPointsMap
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    (hF : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)), F B (map f N) = map f (F A N)) :
    scheme R M k ⟶ scheme R M' l :=
  Scheme.homOfAffinePoints (pointsMap F) (pointsMap_comp F hF)

@[reassoc]
private lemma toSchemeHom_comp_homOfPointsMap
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → G(l, A ⊗[R] M'; A))
    (hF : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)), F B (map f N) = map f (F A N))
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ homOfPointsMap F hF = toSchemeHom (F A N) :=
  (Scheme.comp_homOfAffinePoints _ _ _).trans (pointsMap_toSchemeHom F N)

end OfPoints

variable [Module.Finite R M] [Module.Projective R M]

/-- **The dual Grassmannian.** If `M` is finite projective of constant rank `k + l` over `R`, then
`G(k, M) ≅ G(l, M^∨)` over `Spec R` (`Module.Grassmannian.schemeDualIso_hom_toSpec`). It sends
the point classifying `N` to the point classifying the annihilator of `N`
(`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_hom`), and its inverse takes coannihilators
(`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_inv`). -/
noncomputable def schemeDualIso (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    scheme R M k ≅ scheme R (Module.Dual R M) l where
  hom := homOfPointsMap (fun A _ _ ↦ baseChangeDualEquiv A h)
    fun _ _ _ _ _ _ f N ↦ baseChangeDualEquiv_map h f N
  inv := homOfPointsMap (fun A _ _ ↦ (baseChangeDualEquiv A h).symm)
    fun _ _ _ _ _ _ f K ↦ baseChangeDualEquiv_symm_map h f K
  hom_inv_id := hom_ext_of_points fun A _ _ N ↦ by
    rw [toSchemeHom_comp_homOfPointsMap_assoc, toSchemeHom_comp_homOfPointsMap,
      Equiv.symm_apply_apply, Category.comp_id]
  inv_hom_id := hom_ext_of_points fun A _ _ K ↦ by
    rw [toSchemeHom_comp_homOfPointsMap_assoc, toSchemeHom_comp_homOfPointsMap,
      Equiv.apply_symm_apply, Category.comp_id]

/-- **`schemeDualIso` on points.** The morphism classifying `N` over an `R`-algebra `A`, composed
with `schemeDualIso h`, classifies the annihilator of `N` in `A ⊗[R] M^∨`
(`Module.Grassmannian.mem_baseChangeDualEquiv_iff`). -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_schemeDualIso_hom (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ (schemeDualIso h).hom = toSchemeHom (baseChangeDualEquiv A h N) :=
  toSchemeHom_comp_homOfPointsMap _ (fun _ _ _ _ _ _ f N ↦ baseChangeDualEquiv_map h f N) N

/-- **The inverse of `schemeDualIso` on points.** The morphism classifying `K` over an
`R`-algebra `A`, composed with the inverse of `schemeDualIso h`, classifies the point of
`G(k, M)` whose annihilator is `K`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_schemeDualIso_inv (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    {A : Type u} [CommRing A] [Algebra R A] (K : G(l, A ⊗[R] Module.Dual R M; A)) :
    toSchemeHom K ≫ (schemeDualIso h).inv = toSchemeHom ((baseChangeDualEquiv A h).symm K) :=
  toSchemeHom_comp_homOfPointsMap _ (fun _ _ _ _ _ _ f K ↦ baseChangeDualEquiv_symm_map h f K) K

/-- `schemeDualIso h` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schemeDualIso_hom_toSpec (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    (schemeDualIso h).hom ≫ toSpec R (Module.Dual R M) l = toSpec R M k :=
  hom_ext_of_points fun A _ _ N ↦ by
    rw [toSchemeHom_comp_schemeDualIso_hom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec]

/-- The inverse of `schemeDualIso h` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schemeDualIso_inv_toSpec (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    (schemeDualIso h).inv ≫ toSpec R M k = toSpec R (Module.Dual R M) l := by
  rw [Iso.inv_comp_eq, schemeDualIso_hom_toSpec]

end Module.Grassmannian
