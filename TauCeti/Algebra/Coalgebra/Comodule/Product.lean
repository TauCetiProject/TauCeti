/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.Algebra.Coalgebra.ComoduleCat

/-!
# Products of comodules

This file equips the product of two right comodules over a fixed coalgebra with the direct-sum
coaction. For comodules `M` and `N`, the coaction on `M × N` is
`ρ(m, n) = (inl ⊗ id) (ρ m) + (inr ⊗ id) (ρ n)`.

The file also records that the four standard linear maps for a product,
`fst`, `snd`, `inl`, and `inr`, are comodule morphisms for this coaction. This is additive
infrastructure for the finite-dimensional comodule representation category in the
reductive-groups roadmap.

## Main declarations

* `TauCeti.Comodule.Prod`: the direct-sum comodule structure on `M × N`.
* `TauCeti.Comodule.prodFst`, `prodSnd`, `prodInl`, `prodInr`: the four canonical comodule
  morphisms.
* `TauCeti.ComoduleCat.prod`: the bundled product comodule, with projections and `prodLift`.

## References

This supplies a prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target
"Comodules over a coalgebra/Hopf algebra": the finite-dimensional comodule category should be an
additive category before tensor products, duals, and Tannakian reconstruction are built on top.
The construction is the standard direct sum of comodules; see Sweedler, *Hopf Algebras*,
Chapter 2.
-/

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type w} {N : Type x}
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The direct-sum coaction on the product of two comodules. -/
def prodCoact : M × N →ₗ[R] (M × N) ⊗[R] C :=
  LinearMap.coprod
    ((TensorProduct.map (LinearMap.inl R M N) LinearMap.id) ∘ₗ
      coact (R := R) (C := C) (M := M))
    ((TensorProduct.map (LinearMap.inr R M N) LinearMap.id) ∘ₗ
      coact (R := R) (C := C) (M := N))

/-- The product coaction evaluated on a pair. -/
@[simp]
theorem prodCoact_apply (x : M × N) :
    prodCoact (R := R) (C := C) (M := M) (N := N) x =
      TensorProduct.map (LinearMap.inl R M N) LinearMap.id
          (coact (R := R) (C := C) (M := M) x.1) +
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id
          (coact (R := R) (C := C) (M := N) x.2) :=
  rfl

/-- The product coaction after the left inclusion. -/
@[simp]
theorem prodCoact_inl (m : M) :
    prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m) =
      TensorProduct.map (LinearMap.inl R M N) LinearMap.id
        (coact (R := R) (C := C) (M := M) m) := by
  simp [prodCoact]

/-- The product coaction after the right inclusion. -/
@[simp]
theorem prodCoact_inr (n : N) :
    prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n) =
      TensorProduct.map (LinearMap.inr R M N) LinearMap.id
        (coact (R := R) (C := C) (M := N) n) := by
  simp [prodCoact]

private theorem prodCoact_coassoc_map {P : Type*} [AddCommMonoid P] [Module R P]
    [Comodule R C P] (f : P →ₗ[R] M × N)
    (hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ f =
        TensorProduct.map f LinearMap.id ∘ₗ coact (R := R) (C := C) (M := P))
    (p : P) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (f p))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (f p)) := by
  have hcoact :
      prodCoact (R := R) (C := C) (M := M) (N := N) (f p) =
        TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := P) p) :=
    LinearMap.congr_fun hcomp p
  rw [hcoact]
  have h :=
    congrArg
      (TensorProduct.map f
        (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)))
      (coassoc_apply (R := R) (C := C) (M := P) p)
  rw [TensorProduct.map_map_assoc] at h
  simpa only [LinearMap.rTensor_map, LinearMap.lTensor_map, LinearMap.rTensor_def,
    LinearMap.lTensor_def, hcomp, LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_id,
    TensorProduct.map_map] using h

private theorem prodCoact_coassoc_inl (m : M) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m)) := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inl R M N =
        TensorProduct.map (LinearMap.inl R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M) := by
    ext x
    simp
  exact prodCoact_coassoc_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inl R M N) hcomp m

private theorem prodCoact_coassoc_inr (n : N) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n)) := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inr R M N =
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := N) := by
    ext x
    simp
  exact prodCoact_coassoc_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inr R M N) hcomp n

private theorem prodCoact_coassoc :
    TensorProduct.assoc R (M × N) C C ∘ₗ
        (prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C ∘ₗ
          prodCoact (R := R) (C := C) (M := M) (N := N) =
      Coalgebra.comul.lTensor (M × N) ∘ₗ
        prodCoact (R := R) (C := C) (M := M) (N := N) := by
  apply LinearMap.prod_ext
  · ext m
    exact prodCoact_coassoc_inl (R := R) (C := C) (M := M) (N := N) m
  · ext n
    exact prodCoact_coassoc_inr (R := R) (C := C) (M := M) (N := N) n

private theorem prodCoact_counit_map {P : Type*} [AddCommMonoid P] [Module R P]
    [Comodule R C P] (f : P →ₗ[R] M × N)
    (hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ f =
        TensorProduct.map f LinearMap.id ∘ₗ coact (R := R) (C := C) (M := P))
    (p : P) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (f p)) =
      f p ⊗ₜ[R] 1 := by
  have hcoact :
      prodCoact (R := R) (C := C) (M := M) (N := N) (f p) =
        TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := P) p) :=
    LinearMap.congr_fun hcomp p
  rw [hcoact]
  have h :=
    congrArg (TensorProduct.map f (LinearMap.id : R →ₗ[R] R))
      (lTensor_counit_coact (R := R) (C := C) (M := P) p)
  simpa only [LinearMap.lTensor_map, LinearMap.lTensor_def, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_id, TensorProduct.map_map, TensorProduct.map_tmul,
    LinearMap.id_apply] using h

private theorem prodCoact_counit_inl (m : M) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m)) =
      LinearMap.inl R M N m ⊗ₜ[R] 1 := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inl R M N =
        TensorProduct.map (LinearMap.inl R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M) := by
    ext x
    simp
  exact prodCoact_counit_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inl R M N) hcomp m

private theorem prodCoact_counit_inr (n : N) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n)) =
      LinearMap.inr R M N n ⊗ₜ[R] 1 := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inr R M N =
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := N) := by
    ext x
    simp
  exact prodCoact_counit_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inr R M N) hcomp n

private theorem prodCoact_counit :
    Coalgebra.counit.lTensor (M × N) ∘ₗ
        prodCoact (R := R) (C := C) (M := M) (N := N) =
      (TensorProduct.mk R (M × N) R).flip 1 := by
  apply LinearMap.prod_ext
  · ext m
    exact prodCoact_counit_inl (R := R) (C := C) (M := M) (N := N) m
  · ext n
    exact prodCoact_counit_inr (R := R) (C := C) (M := M) (N := N) n

/-- The product of two right comodules, with the direct-sum coaction. -/
@[implicit_reducible]
def Prod : Comodule R C (M × N) where
  coact := prodCoact (R := R) (C := C) (M := M) (N := N)
  coassoc := prodCoact_coassoc (R := R) (C := C) (M := M) (N := N)
  lTensor_counit_comp_coact := prodCoact_counit (R := R) (C := C) (M := M) (N := N)

/-- The coaction in `Comodule.Prod` is `Comodule.prodCoact`. -/
@[simp]
theorem Prod_coact :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    coact (R := R) (C := C) (M := M × N) =
      prodCoact (R := R) (C := C) (M := M) (N := N) :=
  rfl

/-- The first projection from the product comodule. -/
def prodFst :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    Hom R C (M × N) M := by
  letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
  exact
      { toLinearMap := LinearMap.fst R M N
        map_coact := by
          apply LinearMap.prod_ext
          · ext m
            simp [TensorProduct.map_map]
          · ext n
            simp [prodCoact, TensorProduct.map_map] }

/-- The underlying linear map of the first projection from the product comodule. -/
@[simp]
theorem prodFst_toLinearMap :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    (prodFst (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.fst R M N :=
  rfl

/-- Evaluating the first projection from the product comodule returns the first component. -/
@[simp]
theorem prodFst_apply (x : M × N) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    prodFst (R := R) (C := C) (M := M) (N := N) x = x.1 :=
  rfl

/-- The second projection from the product comodule. -/
def prodSnd :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    Hom R C (M × N) N := by
  letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
  exact
      { toLinearMap := LinearMap.snd R M N
        map_coact := by
          apply LinearMap.prod_ext
          · ext m
            simp [prodCoact, TensorProduct.map_map]
          · ext n
            simp [TensorProduct.map_map] }

/-- The underlying linear map of the second projection from the product comodule. -/
@[simp]
theorem prodSnd_toLinearMap :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    (prodSnd (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.snd R M N :=
  rfl

/-- Evaluating the second projection from the product comodule returns the second component. -/
@[simp]
theorem prodSnd_apply (x : M × N) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    prodSnd (R := R) (C := C) (M := M) (N := N) x = x.2 :=
  rfl

/-- The left inclusion into the product comodule. -/
def prodInl :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    Hom R C M (M × N) := by
  letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
  exact
      { toLinearMap := LinearMap.inl R M N
        map_coact := by
          ext m
          simp }

/-- The underlying linear map of the left inclusion into the product comodule. -/
@[simp]
theorem prodInl_toLinearMap :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    (prodInl (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.inl R M N :=
  rfl

/-- Evaluating the left inclusion into the product comodule gives a pair with zero right
component. -/
@[simp]
theorem prodInl_apply (m : M) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    prodInl (R := R) (C := C) (M := M) (N := N) m = (m, 0) :=
  rfl

/-- The right inclusion into the product comodule. -/
def prodInr :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    Hom R C N (M × N) := by
  letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
  exact
      { toLinearMap := LinearMap.inr R M N
        map_coact := by
          ext n
          simp }

/-- The underlying linear map of the right inclusion into the product comodule. -/
@[simp]
theorem prodInr_toLinearMap :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    (prodInr (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.inr R M N :=
  rfl

/-- Evaluating the right inclusion into the product comodule gives a pair with zero left
component. -/
@[simp]
theorem prodInr_apply (n : N) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    prodInr (R := R) (C := C) (M := M) (N := N) n = (0, n) :=
  rfl

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
private theorem prodLeft_map_prod {P : Type*} [AddCommMonoid P] [Module R P]
    (f : P →ₗ[R] M) (g : P →ₗ[R] N) (t : P ⊗[R] C) :
    TensorProduct.prodLeft R R M N C
        (TensorProduct.map (f.prod g) LinearMap.id t) =
      (TensorProduct.map f LinearMap.id t, TensorProduct.map g LinearMap.id t) := by
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext <;> simp
  · intro p c
    rfl
  · intro t u ht hu
    simp [ht, hu]

/-- The product morphism induced by two morphisms with a common source. -/
def prodLift {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C P M) (g : Hom R C P N) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    Hom R C P (M × N) := by
  letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
  exact
    { toLinearMap := f.toLinearMap.prod g.toLinearMap
      map_coact := by
        ext p
        apply (TensorProduct.prodLeft R R M N C).injective
        simp [prodCoact, prodLeft_map_prod, LinearMap.inl, LinearMap.inr,
          Hom.map_coact_apply] }

/-- The underlying linear map of `Comodule.prodLift`. -/
@[simp]
theorem prodLift_toLinearMap {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C P M) (g : Hom R C P N) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    (prodLift (R := R) (C := C) (M := M) (N := N) f g).toLinearMap =
      f.toLinearMap.prod g.toLinearMap :=
  rfl

/-- Evaluating `Comodule.prodLift` gives the pair of evaluations. -/
@[simp]
theorem prodLift_apply {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C P M) (g : Hom R C P N) (p : P) :
    letI : Comodule R C (M × N) := Prod (R := R) (C := C) (M := M) (N := N)
    prodLift (R := R) (C := C) (M := M) (N := N) f g p = (f p, g p) :=
  rfl

end Comodule

namespace ComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The product of two bundled comodules, carried by the product of the underlying modules. -/
abbrev prod (M N : ComoduleCat.{u, v, w} R C) : ComoduleCat.{u, v, w} R C where
  carrier := M × N
  instComodule := Comodule.Prod (R := R) (C := C) (M := M) (N := N)

variable {R C}

/-- The first projection from the bundled product comodule. -/
abbrev prodFst (M N : ComoduleCat.{u, v, w} R C) : prod R C M N ⟶ M :=
  Comodule.prodFst (R := R) (C := C) (M := M) (N := N)

/-- The second projection from the bundled product comodule. -/
abbrev prodSnd (M N : ComoduleCat.{u, v, w} R C) : prod R C M N ⟶ N :=
  Comodule.prodSnd (R := R) (C := C) (M := M) (N := N)

/-- The morphism into the bundled product induced by a pair of morphisms. -/
abbrev prodLift {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prod R C M N :=
  Comodule.prodLift (R := R) (C := C) (M := M) (N := N) f g

/-- Evaluating the bundled first projection returns the first component. -/
@[simp]
theorem prodFst_apply (M N : ComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodFst M N x = x.1 :=
  rfl

/-- Evaluating the bundled second projection returns the second component. -/
@[simp]
theorem prodSnd_apply (M N : ComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodSnd M N x = x.2 :=
  rfl

/-- Evaluating the bundled product lift gives the pair of evaluations. -/
@[simp]
theorem prodLift_apply {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N)
    (p : P) :
    prodLift f g p = (f p, g p) :=
  rfl

/-- The first projection after the bundled product lift is the first morphism. -/
@[simp]
theorem prodLift_fst {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f := by
  ext p
  rfl

/-- The second projection after the bundled product lift is the second morphism. -/
@[simp]
theorem prodLift_snd {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g := by
  ext p
  rfl

/-- Morphisms into the bundled product are determined by their projections. -/
@[ext]
theorem prod_hom_ext {P M N : ComoduleCat.{u, v, w} R C} {f g : P ⟶ prod R C M N}
    (hfst : f ≫ prodFst M N = g ≫ prodFst M N)
    (hsnd : f ≫ prodSnd M N = g ≫ prodSnd M N) : f = g := by
  apply hom_ext
  intro p
  have hfstp := congrArg (fun h : P ⟶ M => h p) hfst
  have hsndp := congrArg (fun h : P ⟶ N => h p) hsnd
  change prodFst M N (f p) = prodFst M N (g p) at hfstp
  change prodSnd M N (f p) = prodSnd M N (g p) at hsndp
  exact Prod.ext (by simpa using hfstp) (by simpa using hsndp)

end ComoduleCat

end TauCeti
