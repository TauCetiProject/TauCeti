/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Prod
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
* `TauCeti.ComoduleCat.prod`: the bundled product comodule.

## References

This supplies a prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target
"Comodules over a coalgebra/Hopf algebra": the finite-dimensional comodule category should be an
additive category before tensor products, duals, and Tannakian reconstruction are built on top.
The construction is the standard direct sum of comodules; see Sweedler, *Hopf Algebras*,
Chapter 2.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Comodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M N : Type w}
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

private theorem prodCoact_coassoc_inl (m : M) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m)) := by
  simp only [prodCoact_inl]
  have h :=
    congrArg
      (TensorProduct.map (LinearMap.inl R M N)
        (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)))
      (coassoc_apply (R := R) (C := C) (M := M) m)
  rw [TensorProduct.map_map_assoc] at h
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inl R M N =
        TensorProduct.map (LinearMap.inl R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M) := by
    ext x
    simp
  simpa only [LinearMap.rTensor_map, LinearMap.lTensor_map, LinearMap.rTensor_def,
    LinearMap.lTensor_def, hcomp, LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_id,
    TensorProduct.map_map] using h

private theorem prodCoact_coassoc_inr (n : N) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n)) := by
  simp only [prodCoact_inr]
  have h :=
    congrArg
      (TensorProduct.map (LinearMap.inr R M N)
        (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)))
      (coassoc_apply (R := R) (C := C) (M := N) n)
  rw [TensorProduct.map_map_assoc] at h
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inr R M N =
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := N) := by
    ext x
    simp
  simpa only [LinearMap.rTensor_map, LinearMap.lTensor_map, LinearMap.rTensor_def,
    LinearMap.lTensor_def, hcomp, LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_id,
    TensorProduct.map_map] using h

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

private theorem prodCoact_counit_inl (m : M) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m)) =
      LinearMap.inl R M N m ⊗ₜ[R] 1 := by
  simp only [prodCoact_inl]
  have h :=
    congrArg (TensorProduct.map (LinearMap.inl R M N) (LinearMap.id : R →ₗ[R] R))
      (lTensor_counit_coact (R := R) (C := C) (M := M) m)
  simpa only [LinearMap.lTensor_map, LinearMap.lTensor_def, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_id, TensorProduct.map_map, TensorProduct.map_tmul,
    LinearMap.id_apply] using h

private theorem prodCoact_counit_inr (n : N) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n)) =
      LinearMap.inr R M N n ⊗ₜ[R] 1 := by
  simp only [prodCoact_inr]
  have h :=
    congrArg (TensorProduct.map (LinearMap.inr R M N) (LinearMap.id : R →ₗ[R] R))
      (lTensor_counit_coact (R := R) (C := C) (M := N) n)
  simpa only [LinearMap.lTensor_map, LinearMap.lTensor_def, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_id, TensorProduct.map_map, TensorProduct.map_tmul,
    LinearMap.id_apply] using h

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
@[reducible]
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

/-- The left inclusion into the bundled product comodule. -/
abbrev prodInl (M N : ComoduleCat.{u, v, w} R C) : M ⟶ prod R C M N :=
  Comodule.prodInl (R := R) (C := C) (M := M) (N := N)

/-- The right inclusion into the bundled product comodule. -/
abbrev prodInr (M N : ComoduleCat.{u, v, w} R C) : N ⟶ prod R C M N :=
  Comodule.prodInr (R := R) (C := C) (M := M) (N := N)

@[simp]
theorem prodFst_apply (M N : ComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodFst M N x = x.1 :=
  rfl

@[simp]
theorem prodSnd_apply (M N : ComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodSnd M N x = x.2 :=
  rfl

@[simp]
theorem prodInl_apply (M N : ComoduleCat.{u, v, w} R C) (m : M) :
    prodInl M N m = (m, 0) :=
  rfl

@[simp]
theorem prodInr_apply (M N : ComoduleCat.{u, v, w} R C) (n : N) :
    prodInr M N n = (0, n) :=
  rfl

end ComoduleCat

end TauCeti
