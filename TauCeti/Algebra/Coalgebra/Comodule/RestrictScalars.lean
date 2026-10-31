/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.Cat
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed

/-!
# Restriction of scalars for comodules over a base-changed coalgebra

A comodule over `A ⊗[R] C` can be regarded as a `C`-comodule over `R`, without
changing its carrier. Its coaction uses the tensor cancellation equivalence
`M ⊗[A] (A ⊗[R] C) ≃ M ⊗[R] C`. Invariant vectors are unchanged.
This permits exactness of invariants to be transported to an extension field,
even when a finite-dimensional representation becomes infinite dimensional after
restriction to the original field.

`ComoduleCat.restrictScalars` packages the construction as a functor between the
categories of all comodules. It restricts the module action along `algebraMap R A`
and preserves the underlying carriers and functions.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2, change of base ring.
* M. Sweedler, *Hopf Algebras*, Chapter 2.

The tensor comparison is Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`.
-/

public section

open CategoryTheory
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

namespace TauCeti.Comodule

universe u v w x y

variable {R : Type u} {A : Type v} {C : Type w} {M : Type x}
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid C] [Module R C]
  [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

variable [Coalgebra R C] [Comodule A (A ⊗[R] C) M]

/-- The coaction obtained by cancelling the extended coefficient ring. -/
noncomputable def restrictScalarsCoact : M →ₗ[R] M ⊗[R] C :=
  (cancelBaseChange R A A M C).toLinearMap.restrictScalars R ∘ₗ
    (coact (R := A) (C := A ⊗[R] C) (M := M)).restrictScalars R

/-- The restricted coaction is the original coaction followed by tensor cancellation. -/
theorem restrictScalarsCoact_apply (m : M) :
    restrictScalarsCoact (R := R) (A := A) (C := C) m =
      cancelBaseChange R A A M C (coact (R := A) (C := A ⊗[R] C) m) :=
  (rfl)

private theorem cancelBaseChangeTensor_coact (z : M ⊗[A] (A ⊗[R] C)) :
    cancelBaseChangeTensor R A M C C
        (TensorProduct.assoc A M (A ⊗[R] C) (A ⊗[R] C)
          ((coact (R := A) (C := A ⊗[R] C) (M := M)).rTensor _ z)) =
      TensorProduct.assoc R M C C
        ((restrictScalarsCoact (R := R) (A := A) (C := C) (M := M)).rTensor C
          (cancelBaseChange R A A M C z)) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul m d =>
    induction d using TensorProduct.inductionOn with
    | add d e hd he => simp only [TensorProduct.tmul_add, map_add, hd, he]
    | tmul a c =>
      simp only [LinearMap.rTensor_tmul, cancelBaseChange_tmul, restrictScalarsCoact_apply]
      rw [map_smul]
      induction coact (R := A) (C := A ⊗[R] C) m using TensorProduct.inductionOn with
      | add z t hz ht => simp only [smul_add, map_add, TensorProduct.add_tmul, hz, ht]
      | tmul n d =>
        induction d using TensorProduct.inductionOn with
        | add d e hd he =>
          simp_all only [smul_add, TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]
        | tmul b d =>
          simp [smul_smul, mul_comm, TensorProduct.smul_tmul',
            TensorProduct.assoc_tmul]

/-- Regard a comodule over a scalar-extended coalgebra as a comodule over the
original coalgebra. Select this structure explicitly as a local instance. -/
@[instance_reducible]
noncomputable def restrictScalars : Comodule R C M where
  coact := restrictScalarsCoact (A := A)
  coassoc := by
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [restrictScalarsCoact_apply, ← cancelBaseChangeTensor_coact,
      coassoc_apply, cancelBaseChangeTensor_lTensor_comul]
  lTensor_counit_comp_coact := by
    ext m
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
    apply (TensorProduct.rid R M).injective
    rw [restrictScalarsCoact_apply, TensorProduct.rid_counit_cancelBaseChange,
      lTensor_counit_coact]
    simp

/-- The restricted structure has the coaction given by tensor cancellation. -/
@[simp]
theorem restrictScalars_coact :
    (restrictScalars (R := R) (A := A) (C := C) (M := M)).coact =
      restrictScalarsCoact (R := R) (A := A) (C := C) :=
  (rfl)

/-- Restriction of scalars preserves the equation defining a vector of a prescribed
coalgebra weight. In particular it preserves invariant vectors when the weight is `1`. -/
@[simp]
theorem restrictScalarsCoact_eq_tmul_iff (m : M) (c : C) :
    restrictScalarsCoact (R := R) (A := A) (C := C) m = m ⊗ₜ[R] c ↔
      coact (R := A) (C := A ⊗[R] C) m = m ⊗ₜ[A] (1 ⊗ₜ[R] c) := by
  rw [restrictScalarsCoact_apply, ← LinearEquiv.eq_symm_apply,
    cancelBaseChange_symm_tmul]

/-- Restriction of scalars preserves membership in the fixed subcomodule. -/
theorem mem_fixedSubcomodule_restrictScalars_iff
    {C : Type w} [AddCommMonoidWithOne C] [Module R C] [Coalgebra R C]
    [Comodule A (A ⊗[R] C) M] (m : M) :
    (letI := restrictScalars (R := R) (A := A) (C := C) (M := M);
      m ∈ fixedSubcomodule R C M) ↔ m ∈ fixedSubcomodule A (A ⊗[R] C) M := by
  simp only [mem_fixedSubcomodule, restrictScalars_coact,
    restrictScalarsCoact_eq_tmul_iff, Algebra.TensorProduct.one_def]

variable {N : Type y} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]
  [Comodule A (A ⊗[R] C) N]

/-- A morphism of comodules over a scalar-extended coalgebra remains a morphism
on restricting scalars, with the same underlying function. -/
noncomputable def Hom.restrictScalars (f : Hom A (A ⊗[R] C) M N) :
    letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
    letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := N)
    Hom R C M N := by
  letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
  letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := N)
  refine ⟨f.toLinearMap.restrictScalars R, ?_⟩
  ext m
  simp only [LinearMap.comp_apply, restrictScalars_coact, restrictScalarsCoact_apply,
    LinearMap.restrictScalars_apply, Hom.coe_toLinearMap]
  rw [← f.map_coact_apply]
  exact (cancelBaseChange_rTensor f.toLinearMap _).symm

/-- Restriction of a comodule morphism restricts its underlying linear map. -/
@[simp]
theorem Hom.restrictScalars_toLinearMap (f : Hom A (A ⊗[R] C) M N) :
    letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
    letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := N)
    (f.restrictScalars (R := R)).toLinearMap = f.toLinearMap.restrictScalars R :=
  (rfl)

/-- Restricting a comodule morphism leaves its function unchanged. -/
@[simp]
theorem Hom.restrictScalars_apply (f : Hom A (A ⊗[R] C) M N) (m : M) :
    f.restrictScalars (R := R) m = f m :=
  (rfl)

/-- Restriction of scalars preserves the identity comodule morphism. -/
-- Simplify before `ComoduleCat.ofHom_id` rewrites the identity in categorical form.
@[simp↓]
theorem Hom.restrictScalars_id :
    let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
    (Hom.id A (A ⊗[R] C) M).restrictScalars (R := R) = Hom.id R C M := by
  let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
  ext m
  simp only [Hom.restrictScalars_apply, Hom.id_apply]

/-- Restriction of scalars preserves composition of comodule morphisms. -/
@[simp]
theorem Hom.restrictScalars_comp {P : Type*} [AddCommMonoid P] [Module A P] [Module R P]
    [IsScalarTower R A P] [Comodule A (A ⊗[R] C) P]
    (g : Hom A (A ⊗[R] C) N P) (f : Hom A (A ⊗[R] C) M N) :
    let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
    let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := N)
    let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := P)
    (g.comp f).restrictScalars (R := R) =
      (g.restrictScalars (R := R)).comp (f.restrictScalars (R := R)) := by
  let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
  let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := N)
  let _ := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := P)
  ext m
  simp

end TauCeti.Comodule

namespace TauCeti.ComoduleCat

universe u v w x

variable (R : Type u) (A : Type v) (C : Type w)
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Regard a comodule over `A ⊗[R] C` as a `C`-comodule over `R`, restricting the module
scalars and cancelling scalar extension in its coaction. Underlying carriers and morphism
functions are unchanged; no finiteness assumption on the comodule is needed. -/
-- Expose the object carrier so vectors and morphism functions retain their original types.
@[expose]
noncomputable def restrictScalars :
    ComoduleCat.{v, max v w, x} A (A ⊗[R] C) ⥤ ComoduleCat.{u, w, x} R C where
  obj M :=
    letI := Module.compHom M (algebraMap R A)
    letI := IsScalarTower.of_compHom R A M
    letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
    of R C M
  map {M N} f :=
    letI := Module.compHom M (algebraMap R A)
    letI := Module.compHom N (algebraMap R A)
    letI := IsScalarTower.of_compHom R A M
    letI := IsScalarTower.of_compHom R A N
    f.restrictScalars (R := R)
  map_id M := by
    let _ := Module.compHom M (algebraMap R A)
    let _ := IsScalarTower.of_compHom R A M
    exact Comodule.Hom.restrictScalars_id (R := R) (A := A) (C := C) (M := M)
  map_comp {M N P} f g := by
    let _ := Module.compHom M (algebraMap R A)
    let _ := Module.compHom N (algebraMap R A)
    let _ := Module.compHom P (algebraMap R A)
    let _ := IsScalarTower.of_compHom R A M
    let _ := IsScalarTower.of_compHom R A N
    let _ := IsScalarTower.of_compHom R A P
    exact Comodule.Hom.restrictScalars_comp g f

/-- The restricted object uses the module action induced by `algebraMap R A` and the
coaction given by tensor cancellation. -/
@[simp]
theorem restrictScalars_obj (M : ComoduleCat.{v, max v w, x} A (A ⊗[R] C)) :
    (restrictScalars R A C).obj M =
      (letI := Module.compHom M (algebraMap R A)
       letI := IsScalarTower.of_compHom R A M
       letI := Comodule.restrictScalars (R := R) (A := A) (C := C) (M := M)
       of R C M) :=
  (rfl)

/-- The restricted scalar action is the original action through `algebraMap R A`. -/
@[simp]
theorem restrictScalars_obj_smul (M : ComoduleCat.{v, max v w, x} A (A ⊗[R] C))
    (r : R) (m : (restrictScalars R A C).obj M) :
    r • m = @SMul.smul A M inferInstance (algebraMap R A r) m :=
  (rfl)

/-- On objects, the coaction is the original coaction followed by tensor cancellation. -/
@[simp]
theorem restrictScalars_obj_coact (M : ComoduleCat.{v, max v w, x} A (A ⊗[R] C)) :
    letI := Module.compHom M (algebraMap R A)
    letI := IsScalarTower.of_compHom R A M
    Comodule.coact (R := R) (C := C) (M := (restrictScalars R A C).obj M) =
      Comodule.restrictScalarsCoact (R := R) (A := A) (C := C) (M := M) :=
  (rfl)

/-- On morphisms, restriction of scalars restricts the underlying linear map. -/
@[simp]
theorem restrictScalars_map_toLinearMap
    {M N : ComoduleCat.{v, max v w, x} A (A ⊗[R] C)} (f : M ⟶ N) :
    letI := Module.compHom M (algebraMap R A)
    letI := Module.compHom N (algebraMap R A)
    letI := IsScalarTower.of_compHom R A M
    letI := IsScalarTower.of_compHom R A N
    ((restrictScalars R A C).map f).toLinearMap = f.toLinearMap.restrictScalars R :=
  (rfl)

/-- Restriction of scalars preserves the underlying function of a morphism. -/
@[simp]
theorem restrictScalars_map_apply {M N : ComoduleCat.{v, max v w, x} A (A ⊗[R] C)}
    (f : M ⟶ N) (m : M) :
    hom R C ((restrictScalars R A C).map f) m = hom A (A ⊗[R] C) f m :=
  (rfl)

/-- Restriction of scalars is faithful. -/
instance restrictScalars_faithful : (restrictScalars R A C).Faithful where
  map_injective {M N} {f g} h := by
    ext m
    have hm := congrArg (fun k : (restrictScalars R A C).obj M ⟶
      (restrictScalars R A C).obj N => k m) h
    simp only [hom_ofHom, restrictScalars_map_apply] at hm
    -- Compute the object carrier after rewriting the morphism functions.
    simpa only [restrictScalars, hom_ofHom] using hm

end TauCeti.ComoduleCat
