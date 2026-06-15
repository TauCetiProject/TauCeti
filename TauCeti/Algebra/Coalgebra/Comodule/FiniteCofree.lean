/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.Coalgebra.Comodule.Cofree
import TauCeti.Algebra.Coalgebra.Comodule.Finite

/-!
# Finitely generated cofree comodules

This file lifts the cofree right comodule `M ⊗[R] C` to the finitely generated comodule
category when both the coefficient module `M` and the coalgebra `C` are finitely generated
over `R`. It is the finite-category version of `ComoduleCat.cofree`.

This is Layer 1 infrastructure for the Tau Ceti reductive-groups roadmap target
"Comodules over a coalgebra/Hopf algebra": the finite-dimensional representation category
needs finite versions of the regular and cofree comodules before tensor products, duals, and
the embedding theorem can be developed.

## Main definitions

* `TauCeti.FGComoduleCat.cofree`: the cofree comodule as a finitely generated object.
* `TauCeti.FGComoduleCat.cofreeMap`: functoriality in the finite coefficient module.
* `TauCeti.FGComoduleCat.incl_cofree`: forgetting the finite cofree comodule gives the
  ambient cofree comodule.

## References

The cofree-comodule construction follows Sweedler, *Hopf Algebras*, Chapter 2, as in
`TauCeti.Algebra.Coalgebra.Comodule.Cofree`. The finite-generation proof reuses Mathlib's
`Module.Finite.tensorProduct`.
-/

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [Module.Finite R C]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.Finite R N]

/-- The cofree right `C`-comodule on a finitely generated module, bundled as an object of
`FGComoduleCat`.

The underlying module is `M ⊗[R] C`, with coaction `id ⊗ Δ` followed by reassociation. -/
noncomputable abbrev cofree (M : Type w) [AddCommMonoid M] [Module R M]
    [Module.Finite R M] : FGComoduleCat.{u, v, max w v} R C :=
  letI := Comodule.cofree R C M
  of (R := R) (C := C) (M ⊗[R] C)

/-- Forgetting the finitely generated cofree comodule to all comodules gives the ambient
cofree comodule. -/
@[simp]
theorem cofree_obj :
    (cofree (R := R) (C := C) M).obj = ComoduleCat.cofree R C M :=
  rfl

/-- The underlying type of the finitely generated cofree comodule is `M ⊗[R] C`. -/
@[simp]
theorem cofree_coe : (cofree (R := R) (C := C) M : Type (max w v)) = M ⊗[R] C :=
  rfl

/-- The coaction on the finitely generated cofree comodule is `id ⊗ Δ` followed by
reassociation. -/
@[simp]
theorem cofree_coact :
    letI := Comodule.cofree R C M
    Comodule.coact (R := R) (C := C) (M := cofree (R := R) (C := C) M)
      = (TensorProduct.assoc R M C C).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor M :=
  rfl

/-- The coaction on the finitely generated cofree comodule sends a simple tensor
`m ⊗ c` to `∑ (m ⊗ c₁) ⊗ c₂`. -/
@[simp]
theorem cofree_coact_tmul (m : M) (c : C) :
    letI := Comodule.cofree R C M
    Comodule.coact (R := R) (C := C) (M := cofree (R := R) (C := C) M) (m ⊗ₜ[R] c)
      = (TensorProduct.assoc R M C C).symm (m ⊗ₜ Coalgebra.comul c) :=
  Comodule.cofree_coact_tmul m c

/-- The inclusion of finitely generated comodules sends `FGComoduleCat.cofree` to
`ComoduleCat.cofree`. -/
@[simp]
theorem incl_cofree :
    (incl (R := R) (C := C)).obj (cofree (R := R) (C := C) M) =
      ComoduleCat.cofree R C M :=
  rfl

/-- The finite cofree comodule forgets to the tensor product module `M ⊗[R] C`. -/
@[simp]
theorem forget₂_semimoduleCat_cofree_obj :
    (forget₂ (FGComoduleCat.{u, v, max w v} R C) (SemimoduleCat.{max w v} R)).obj
        (cofree (R := R) (C := C) M) =
      SemimoduleCat.of R (M ⊗[R] C) :=
  rfl

/-- Functoriality of finite cofree comodules in the finite coefficient module.

An `R`-linear map `f : M → N` induces the comodule morphism `f ⊗ id`. -/
noncomputable abbrev cofreeMap (f : M →ₗ[R] N) :
    cofree (R := R) (C := C) M ⟶ cofree (R := R) (C := C) N :=
  letI := Comodule.cofree R C M
  letI := Comodule.cofree R C N
  ofHom (R := R) (C := C) (Comodule.Hom.cofreeMap (C := C) f)

/-- `cofreeMap f` acts as `f ⊗ id`. -/
@[simp]
theorem cofreeMap_apply (f : M →ₗ[R] N) (x : M ⊗[R] C) :
    cofreeMap (R := R) (C := C) f x = f.rTensor C x :=
  letI := Comodule.cofree R C M
  letI := Comodule.cofree R C N
  rfl

/-- On simple tensors, `cofreeMap f` applies `f` to the coefficient factor. -/
@[simp]
theorem cofreeMap_tmul (f : M →ₗ[R] N) (m : M) (c : C) :
    cofreeMap (R := R) (C := C) f (m ⊗ₜ[R] c) = f m ⊗ₜ[R] c :=
  letI := Comodule.cofree R C M
  letI := Comodule.cofree R C N
  rfl

/-- The finite cofree construction sends the identity linear map to the identity morphism. -/
@[simp]
theorem cofreeMap_id :
    cofreeMap (R := R) (C := C) (LinearMap.id : M →ₗ[R] M) =
      𝟙 (cofree (R := R) (C := C) M) :=
  by
    ext x
    simp

/-- The finite cofree construction preserves composition of coefficient-module maps. -/
@[simp]
theorem cofreeMap_comp {P : Type w} [AddCommMonoid P] [Module R P] [Module.Finite R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    cofreeMap (R := R) (C := C) (g.comp f) =
      cofreeMap (R := R) (C := C) f ≫ cofreeMap (R := R) (C := C) g := by
  ext x
  simp

end FGComoduleCat

end TauCeti
