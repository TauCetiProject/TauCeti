/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Coalgebra.Equiv
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra.Handle
public import TauCeti.Algebra.Coalgebra.BaseChange

/-!
# Transport, tensor products, and scalar extension of Frobenius coalgebras

This file shows that the Frobenius coalgebra interface, reconstructed coproducts, dual bases, and
handle elements are compatible with algebra equivalences, tensor products, and scalar extensions.

1. **Homomorphisms and trace-preserving algebra equivalences.** Any surjective linear map preserving
   multiplication and comultiplication pushes `Coalgebra.IsFrobenius` forward
   (`Coalgebra.IsFrobenius.of_surjective`), any multiplicative coalgebra map intertwines
   `Coalgebra.handleOp`, and any unital multiplicative coalgebra map preserves
   `Coalgebra.handleElem`. Any counit-preserving `e : A ≃ₐ[R] B` between Frobenius coalgebras
   upgrades to `e.toFrobeniusCoalgEquiv : A ≃ₗc[R] B`.
2. **Heterogeneous tensor products and scalar extension.** For an `R`-algebra `S`, a Frobenius
   `S`-coalgebra `A`, and a Frobenius `R`-coalgebra `B`, `A ⊗[R] B` satisfies
   `Coalgebra.IsFrobenius S (A ⊗[R] B)` (`TensorProduct.instIsFrobenius`), covering both `S = R` and
   `A = S`, compatibly with `TensorProduct.dualDistrib`, `Module.Dual.baseChange`,
   `LinearMap.frobeniusCoalgebra`, `LinearMap.traceDualBasis`, and `Coalgebra.handleElem`.

## Main definitions

* `AlgEquiv.toFrobeniusCoalgEquiv`, `LinearMap.frobeniusCoalgEquivOfAlgEquiv`.
* `TensorProduct.instIsFrobenius`: `Coalgebra.IsFrobenius S (A ⊗[R] B)`.

## Main results

* `Coalgebra.IsFrobenius.of_surjective`, `Coalgebra.map_handleOp`, `Coalgebra.map_handleElem`.
* `LinearMap.isPerfPair_mul_compr₂_comp_iff`, `LinearMap.traceDualBasis_map`.
* `Coalgebra.handleOp_tensorProduct_tmul`, `Coalgebra.handleElem_tensorProduct`,
  `Coalgebra.handleElem_baseChange`.
* `LinearMap.isPerfPair_mul_compr₂_dualDistrib_tmul`,
  `LinearMap.frobeniusCoalgebra_dualDistrib_tmul`, `LinearMap.traceDualBasis_tensorProduct`,
  `LinearMap.isPerfPair_mul_compr₂_dualBaseChange`, `LinearMap.frobeniusCoalgebra_dualBaseChange`,
  `LinearMap.traceDualBasis_baseChange`.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, §§2.3–2.4.
* F. Goertz, L. Marino, P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  `arXiv:2602.11120v1`, §§2–3.
-/

public section

noncomputable section

open TensorProduct

/-! ### Multiplicative coalgebra homomorphisms -/

section MulCoalgHom

variable {R A B F : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [Module R A] [Module R B]
  [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] [MulHomClass F A B]
  [CoalgHomClass F R A B]

/-- A surjective linear map that preserves multiplication and comultiplication pushes
`Coalgebra.IsFrobenius` forward. -/
theorem Coalgebra.IsFrobenius.of_surjective [Coalgebra.IsFrobenius R A] (f : F)
    (hf : Function.Surjective f) : Coalgebra.IsFrobenius R B := by
  let φ : A →ₗ[R] B := LinearMap.ofClass f
  have hleft (a₁ a₂ : A) : Coalgebra.IsFrobenius.left R B (f a₁ ⊗ₜ[R] f a₂) =
      _root_.TensorProduct.map φ φ (Coalgebra.IsFrobenius.left R A (a₁ ⊗ₜ[R] a₂)) := by
    rw [Coalgebra.IsFrobenius.left_tmul, Coalgebra.IsFrobenius.left_tmul,
      ← CoalgHomClass.map_comp_comul_apply f a₁]
    induction Coalgebra.comul (R := R) a₁ using TensorProduct.inductionOn <;> simp_all [φ, map_mul]
  have hright (a₁ a₂ : A) : Coalgebra.IsFrobenius.right R B (f a₁ ⊗ₜ[R] f a₂) =
      _root_.TensorProduct.map φ φ (Coalgebra.IsFrobenius.right R A (a₁ ⊗ₜ[R] a₂)) := by
    rw [Coalgebra.IsFrobenius.right_tmul, Coalgebra.IsFrobenius.right_tmul,
      ← CoalgHomClass.map_comp_comul_apply f a₂]
    induction Coalgebra.comul (R := R) a₂ using TensorProduct.inductionOn <;> simp_all [φ, map_mul]
  refine ⟨TensorProduct.ext' fun b₁ b₂ => ?_⟩
  obtain ⟨a₁, rfl⟩ := hf b₁; obtain ⟨a₂, rfl⟩ := hf b₂
  rw [hleft, hright, Coalgebra.IsFrobenius.left_eq_right]

/-- Any linear map preserving multiplication and comultiplication intertwines the handle
operator. -/
theorem Coalgebra.map_handleOp (f : F) (a : A) :
    f (Coalgebra.handleOp R A a) = Coalgebra.handleOp R B (f a) := by
  rw [Coalgebra.handleOp_apply, Coalgebra.handleOp_apply, ← CoalgHomClass.map_comp_comul_apply f a]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn <;> simp_all [map_mul]

end MulCoalgHom

/-- Any unital linear map preserving multiplication and comultiplication maps the handle element of
the source to that of the target. -/
theorem Coalgebra.map_handleElem {R A B F : Type*} [CommSemiring R]
    [NonAssocSemiring A] [NonAssocSemiring B] [Module R A] [Module R B]
    [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass R B B] [IsScalarTower R B B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] [MulHomClass F A B]
    [OneHomClass F A B] [CoalgHomClass F R A B] (f : F) :
    f (Coalgebra.handleElem R A) = Coalgebra.handleElem R B := by
  rw [← Coalgebra.handleOp_one, Coalgebra.map_handleOp, map_one, Coalgebra.handleOp_one]

/-! ### Transport along algebra equivalences -/

/-- Pulling a functional back along an algebra equivalence preserves perfectness of the associated
multiplication pairing. -/
theorem LinearMap.isPerfPair_mul_compr₂_comp_iff {R A B : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (εB : B →ₗ[R] R) :
    ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).IsPerfPair ↔ ((mul R B).compr₂ εB).IsPerfPair := by
  have hAB : ((mul R B).compr₂ εB).compl₁₂ e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.toLinearMap = (mul R A).compr₂ (εB ∘ₗ e.toLinearMap) := by ext; simp
  have hBA : ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).compl₁₂ e.symm.toLinearEquiv.toLinearMap
      e.symm.toLinearEquiv.toLinearMap = (mul R B).compr₂ εB := by ext; simp
  exact ⟨fun _ => hBA ▸ inferInstance, fun _ => hAB ▸ inferInstance⟩

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]
  (e : A ≃ₐ[R] B)

private theorem toFrobeniusCoalgEquiv_map_comp_comul
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) :
    TensorProduct.map e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) =
      Coalgebra.comul (R := R) ∘ₗ e.toLinearEquiv.toLinearMap := by
  ext a; refine Coalgebra.IsFrobenius.tensor_eq_of_forall_lid_rTensor_counit_mulLeft fun b => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_toLinearMap,
    Coalgebra.IsFrobenius.lid_rTensor_counit_mulLeft_comul]
  have hmap (t : A ⊗[R] A) : (_root_.TensorProduct.lid R B)
      (((Coalgebra.counit (R := R) ∘ₗ LinearMap.mulLeft R b).rTensor B)
        (TensorProduct.map e.toLinearMap e.toLinearMap t)) =
      e ((_root_.TensorProduct.lid R A)
        (((Coalgebra.counit (R := R) ∘ₗ LinearMap.mulLeft R (e.symm b)).rTensor A) t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, LinearMap.rTensor_tmul,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, _root_.TensorProduct.lid_tmul]
      rw [← e.apply_symm_apply b, ← map_mul e, he (e.symm b * u), e.symm_apply_apply, map_smul]
    | add t u ht hu => simp_all
  rw [hmap, Coalgebra.IsFrobenius.lid_rTensor_counit_mulLeft_comul, map_mul, e.apply_symm_apply]
  rfl

/-- **A counit-preserving algebra isomorphism between Frobenius coalgebras is a coalgebra
isomorphism**: without assuming commutativity of `A` or `B`, preserving multiplication and counit
forces preservation of comultiplication. -/
def toFrobeniusCoalgEquiv
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) : A ≃ₗc[R] B :=
  { e.toLinearEquiv with
    counit_comp := LinearMap.ext he, map_comp_comul := toFrobeniusCoalgEquiv_map_comp_comul e he }

@[simp] theorem coe_toFrobeniusCoalgEquiv
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) :
    ⇑(e.toFrobeniusCoalgEquiv he) = e := (rfl)

@[simp] theorem toFrobeniusCoalgEquiv_apply
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (a : A) :
    e.toFrobeniusCoalgEquiv he a = e a := (rfl)

@[simp] theorem toFrobeniusCoalgEquiv_symm_apply
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (b : B) :
    (e.toFrobeniusCoalgEquiv he).symm b = e.symm b := (rfl)

@[simp] theorem linearMapOfClass_toFrobeniusCoalgEquiv
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) :
    LinearMap.ofClass (e.toFrobeniusCoalgEquiv he) = e.toLinearMap := by ext; rfl

@[simp] theorem linearMapOfClass_toFrobeniusCoalgEquiv_symm
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) :
    LinearMap.ofClass (e.toFrobeniusCoalgEquiv he).symm = e.symm.toLinearMap := by ext; rfl

/-- A counit-preserving algebra isomorphism between Frobenius coalgebras intertwines their handle
operators. -/
theorem map_handleOp_of_counit_eq
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (a : A) :
    e (Coalgebra.handleOp R A a) = Coalgebra.handleOp R B (e a) := by
  have hcomul := CoalgHomClass.map_comp_comul_apply (e.toFrobeniusCoalgEquiv he) a
  simp only [linearMapOfClass_toFrobeniusCoalgEquiv, toFrobeniusCoalgEquiv_apply] at hcomul
  rw [Coalgebra.handleOp_apply, Coalgebra.handleOp_apply, ← hcomul]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn <;> simp_all [map_mul]

/-- A counit-preserving algebra isomorphism between Frobenius coalgebras maps the handle element of
`A` to that of `B`. -/
theorem map_handleElem_of_counit_eq
    (he : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) :
    e (Coalgebra.handleElem R A) = Coalgebra.handleElem R B := by
  simpa using e.map_handleOp_of_counit_eq he 1

end AlgEquiv

namespace LinearMap

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (εB : B →ₗ[R] R) [((mul R B).compr₂ εB).IsPerfPair]

/-- Transporting a basis along an algebra equivalence commutes with taking the trace-dual basis. -/
theorem traceDualBasis_map {ι : Type*} [Finite ι] (b : Module.Basis ι R A) (i : ι) :
    letI : ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).IsPerfPair :=
      (isPerfPair_mul_compr₂_comp_iff e εB).mpr inferInstance
    traceDualBasis εB (b.map e.toLinearEquiv) i = e (traceDualBasis (εB ∘ₗ e.toLinearMap) b i) := by
  let : ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).IsPerfPair :=
    (isPerfPair_mul_compr₂_comp_iff e εB).mpr inferInstance
  refine ((mul R B).compr₂ εB).toPerfPair.injective <| ext fun y => ?_
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply, traceDualBasis_mul,
    Module.Basis.map_repr, LinearEquiv.trans_apply]
  have h := (traceDualBasis_mul (εB ∘ₗ e.toLinearMap) b i (e.symm y)).symm
  simp only [comp_apply, AlgEquiv.toLinearMap_apply, map_mul, AlgEquiv.apply_symm_apply] at h
  exact h

section FiniteProjective

variable [Module.Finite R B] [Module.Projective R B]

/-- Reconstructing Frobenius coalgebras before and after pulling a perfect trace back along an
algebra equivalence `e : A ≃ₐ[R] B` makes `e` a coalgebra equivalence. -/
def frobeniusCoalgEquivOfAlgEquiv :
    letI : Module.Finite R A := .equiv e.symm.toLinearEquiv
    letI : Module.Projective R A := .of_equiv e.symm.toLinearEquiv
    letI : ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).IsPerfPair :=
      (isPerfPair_mul_compr₂_comp_iff e εB).mpr inferInstance
    letI := (εB ∘ₗ e.toLinearMap).frobeniusCoalgebra; letI := εB.frobeniusCoalgebra
    A ≃ₗc[R] B := by
  letI : Module.Finite R A := .equiv e.symm.toLinearEquiv
  letI : Module.Projective R A := .of_equiv e.symm.toLinearEquiv
  letI : ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).IsPerfPair :=
    (isPerfPair_mul_compr₂_comp_iff e εB).mpr inferInstance
  letI := frobeniusCoalgebra (εB ∘ₗ e.toLinearMap); letI := frobeniusCoalgebra εB
  haveI := frobeniusCoalgebra_isFrobenius (εB ∘ₗ e.toLinearMap)
  haveI := frobeniusCoalgebra_isFrobenius εB
  exact e.toFrobeniusCoalgEquiv fun a => by simp +zetaDelta

@[simp] theorem coe_frobeniusCoalgEquivOfAlgEquiv :
    ⇑(frobeniusCoalgEquivOfAlgEquiv e εB) = e := (rfl)

@[simp] theorem frobeniusCoalgEquivOfAlgEquiv_apply (a : A) :
    frobeniusCoalgEquivOfAlgEquiv e εB a = e a := (rfl)

@[simp] theorem frobeniusCoalgEquivOfAlgEquiv_symm_apply (b : B) :
    letI : Module.Finite R A := .equiv e.symm.toLinearEquiv
    letI : Module.Projective R A := .of_equiv e.symm.toLinearEquiv
    letI : ((mul R A).compr₂ (εB ∘ₗ e.toLinearMap)).IsPerfPair :=
      (isPerfPair_mul_compr₂_comp_iff e εB).mpr inferInstance
    letI := (εB ∘ₗ e.toLinearMap).frobeniusCoalgebra; letI := εB.frobeniusCoalgebra
    (frobeniusCoalgEquivOfAlgEquiv e εB).symm b = e.symm b := (rfl)

end FiniteProjective

end LinearMap

/-! ### Heterogeneous tensor products and scalar extension -/

section HetNonUnital

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonUnitalNonAssocSemiring A] [Module R A] [Module S A] [IsScalarTower R S A]
  [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass S A A] [IsScalarTower S A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct S A] [CoalgebraStruct R B]

private theorem TensorProduct.isFrobenius_left_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    haveI : SMulCommClass R S A := IsScalarTower.to_smulCommClass
    Coalgebra.IsFrobenius.left S (A ⊗[R] B) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B
        (Coalgebra.IsFrobenius.left S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
          Coalgebra.IsFrobenius.left R B (b₁ ⊗ₜ[R] b₂)) := by
  have : SMulCommClass R S A := IsScalarTower.to_smulCommClass
  simp only [Coalgebra.IsFrobenius.left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    TensorProduct.comul_tmul]
  induction Coalgebra.comul (R := S) a₁ using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction Coalgebra.comul (R := R) b₁ using TensorProduct.inductionOn <;>
      simp_all [tmul_add, add_tmul]
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]

private theorem TensorProduct.isFrobenius_right_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    haveI : SMulCommClass R S A := IsScalarTower.to_smulCommClass
    Coalgebra.IsFrobenius.right S (A ⊗[R] B) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B
        (Coalgebra.IsFrobenius.right S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
          Coalgebra.IsFrobenius.right R B (b₁ ⊗ₜ[R] b₂)) := by
  have : SMulCommClass R S A := IsScalarTower.to_smulCommClass
  simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    TensorProduct.comul_tmul]
  induction Coalgebra.comul (R := S) a₂ using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction Coalgebra.comul (R := R) b₂ using TensorProduct.inductionOn <;> simp_all [tmul_add]
  | add u v hu hv => simp only [tmul_add, add_tmul, map_add, hu, hv]

/-- **Heterogeneous tensor product of Frobenius coalgebras.** If `S` is a commutative `R`-algebra,
`A` is an `S`-Frobenius algebra-coalgebra, and `B` is an `R`-Frobenius algebra-coalgebra, then
`A ⊗[R] B` satisfies `Coalgebra.IsFrobenius S (A ⊗[R] B)`. Setting `S = R` gives tensor products
over `R`; setting `A = S` gives scalar extension `S ⊗[R] B`. -/
instance TensorProduct.instIsFrobenius [Coalgebra.IsFrobenius S A] [Coalgebra.IsFrobenius R B] :
    Coalgebra.IsFrobenius S (A ⊗[R] B) := by
  have : SMulCommClass R S A := IsScalarTower.to_smulCommClass
  refine ⟨TensorProduct.ext' fun z₁ z₂ => ?_⟩
  induction z₁ using TensorProduct.inductionOn with
  | tmul a₁ b₁ =>
    induction z₂ using TensorProduct.inductionOn with
    | tmul a₂ b₂ =>
      rw [isFrobenius_left_tmul, isFrobenius_right_tmul, Coalgebra.IsFrobenius.left_eq_right,
        Coalgebra.IsFrobenius.left_eq_right]
    | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]

/-- The handle operator on `A ⊗[R] B` acts factorwise on pure tensors. -/
@[simp] theorem Coalgebra.handleOp_tensorProduct_tmul (a : A) (b : B) :
    haveI : SMulCommClass R S A := IsScalarTower.to_smulCommClass
    handleOp S (A ⊗[R] B) (a ⊗ₜ[R] b) = handleOp S A a ⊗ₜ[R] handleOp R B b := by
  have : SMulCommClass R S A := IsScalarTower.to_smulCommClass
  simp only [handleOp_apply, TensorProduct.comul_tmul]
  induction Coalgebra.comul (R := S) a using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn <;> simp_all [tmul_add]
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]

end HetNonUnital

namespace Coalgebra

/-- The handle element of `A ⊗[R] B` is the pure tensor of the handle elements of `A` and `B`. -/
@[simp] theorem handleElem_tensorProduct {R S A B : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [NonAssocSemiring A] [Module R A] [Module S A] [IsScalarTower R S A]
    [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass S A A] [IsScalarTower S A A]
    [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    [CoalgebraStruct S A] [CoalgebraStruct R B] :
    haveI : SMulCommClass R S A := IsScalarTower.to_smulCommClass
    handleElem S (A ⊗[R] B) = handleElem S A ⊗ₜ[R] handleElem R B := by
  have : SMulCommClass R S A := IsScalarTower.to_smulCommClass
  rw [← handleOp_one, Algebra.TensorProduct.one_def, handleOp_tensorProduct_tmul, handleOp_one,
    handleOp_one]

/-- Extending scalars from `R` to `S` maps the handle element of `B` to `1 ⊗ₜ handleElem R B`. -/
theorem handleElem_baseChange {R S B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    [CoalgebraStruct R B] : handleElem S (S ⊗[R] B) = 1 ⊗ₜ[R] handleElem R B := by
  rw [handleElem_tensorProduct, handleElem_self]

end Coalgebra

namespace LinearMap

section TensorTrace

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[R] R) [((mul R A).compr₂ εA).IsPerfPair]
  (εB : B →ₗ[R] R) [((mul R B).compr₂ εB).IsPerfPair]

private theorem counit_tensorProduct_frobeniusCoalgebra :
    (letI := frobeniusCoalgebra εA; letI := frobeniusCoalgebra εB
      Coalgebra.counit (R := R) (A := A ⊗[R] B)) =
      TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB) := by
  let := frobeniusCoalgebra εA; let := frobeniusCoalgebra εB
  simp [TensorProduct.counit_eq_dualDistrib]

/-- The tensor product of two perfect traces on finite projective commutative `R`-algebras gives a
perfect trace pairing on `A ⊗[R] B`. -/
instance isPerfPair_mul_compr₂_dualDistrib_tmul :
    ((mul R (A ⊗[R] B)).compr₂ (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair := by
  let := frobeniusCoalgebra εA; let := frobeniusCoalgebra εB
  have := frobeniusCoalgebra_isFrobenius εA; have := frobeniusCoalgebra_isFrobenius εB
  exact counit_tensorProduct_frobeniusCoalgebra εA εB ▸ inferInstance

/-- Reconstructing the Frobenius coalgebra of `A ⊗[R] B` from `dualDistrib R A B (εA ⊗ₜ εB)` yields
the tensor product of the Frobenius coalgebras reconstructed from `εA` and `εB`. -/
theorem frobeniusCoalgebra_dualDistrib_tmul :
    frobeniusCoalgebra (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)) =
      (letI := frobeniusCoalgebra εA; letI := frobeniusCoalgebra εB
        (inferInstance : Coalgebra R (A ⊗[R] B))) := by
  let := frobeniusCoalgebra εA; let := frobeniusCoalgebra εB
  have := frobeniusCoalgebra_isFrobenius εA; have := frobeniusCoalgebra_isFrobenius εB
  exact frobeniusCoalgebra_eq (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))
    (TensorProduct.instCoalgebra (R := R) (S := R) (A := A) (B := B))
    (counit_tensorProduct_frobeniusCoalgebra εA εB) inferInstance

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B] in
/-- The trace-dual basis of a tensor-product basis is the tensor product of the trace-dual bases. -/
theorem traceDualBasis_tensorProduct {ι κ : Type*} [Finite ι] [Finite κ]
    (bA : Module.Basis ι R A) (bB : Module.Basis κ R B) (p : ι × κ) :
    haveI : Module.Finite R A := .of_basis bA; haveI : Module.Projective R A := .of_basis bA
    haveI : Module.Finite R B := .of_basis bB; haveI : Module.Projective R B := .of_basis bB
    traceDualBasis (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)) (bA.tensorProduct bB) p =
      traceDualBasis εA bA p.1 ⊗ₜ[R] traceDualBasis εB bB p.2 := by
  classical
  have : Module.Finite R A := .of_basis bA; have : Module.Projective R A := .of_basis bA
  have : Module.Finite R B := .of_basis bB; have : Module.Projective R B := .of_basis bB
  let εAB := TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)
  rcases p with ⟨i₁, i₂⟩
  refine ((mul R (A ⊗[R] B)).compr₂ εAB).toPerfPair.injective ((bA.tensorProduct bB).ext ?_)
  rintro ⟨j₁, j₂⟩
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply, traceDualBasis_mul,
    Module.Basis.repr_self, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul,
    εAB, TensorProduct.dualDistrib_apply, Finsupp.single_apply]
  by_cases h1 : j₁ = i₁ <;> by_cases h2 : j₂ = i₂ <;> simp [h1, h2]

end TensorTrace

section BaseChangeTrace

variable {R S B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring B] [Algebra R B] [Module.Finite R B] [Module.Projective R B]
variable (S) (ε : B →ₗ[R] R) [((mul R B).compr₂ ε).IsPerfPair]

private theorem counit_baseChange_frobeniusCoalgebra :
    (letI := frobeniusCoalgebra ε; Coalgebra.counit (R := S) (A := S ⊗[R] B)) =
      Module.Dual.baseChange S ε := by
  let := frobeniusCoalgebra ε; simp [TensorProduct.counit_baseChange_eq_dualBaseChange]

/-- Extending a perfect trace on a finite projective commutative `R`-algebra `B` along `S` via
`Module.Dual.baseChange S` gives a perfect trace pairing on `S ⊗[R] B`. -/
instance isPerfPair_mul_compr₂_dualBaseChange :
    ((mul S (S ⊗[R] B)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair := by
  let := frobeniusCoalgebra ε; have := frobeniusCoalgebra_isFrobenius ε
  exact counit_baseChange_frobeniusCoalgebra S ε ▸ inferInstance

/-- Reconstructing the Frobenius `S`-coalgebra of `S ⊗[R] B` from `Module.Dual.baseChange S ε`
yields the scalar extension of `ε.frobeniusCoalgebra`. -/
theorem frobeniusCoalgebra_dualBaseChange :
    frobeniusCoalgebra (Module.Dual.baseChange S ε) =
      (letI := frobeniusCoalgebra ε; (inferInstance : Coalgebra S (S ⊗[R] B))) := by
  let := frobeniusCoalgebra ε; have := frobeniusCoalgebra_isFrobenius ε
  exact frobeniusCoalgebra_eq (Module.Dual.baseChange S ε)
    (TensorProduct.instCoalgebra (R := R) (S := S) (A := S) (B := B))
    (counit_baseChange_frobeniusCoalgebra S ε) inferInstance

omit [Module.Finite R B] [Module.Projective R B] in
/-- Extending a basis along `S` commutes with taking the trace-dual basis. -/
theorem traceDualBasis_baseChange {ι : Type*} [Finite ι] (b : Module.Basis ι R B) (i : ι) :
    haveI : Module.Finite R B := .of_basis b; haveI : Module.Projective R B := .of_basis b
    traceDualBasis (Module.Dual.baseChange S ε) (b.baseChange S) i =
      1 ⊗ₜ[R] traceDualBasis ε b i := by
  classical
  have : Module.Finite R B := .of_basis b; have : Module.Projective R B := .of_basis b
  let εS := Module.Dual.baseChange S ε
  refine ((mul S (S ⊗[R] B)).compr₂ εS).toPerfPair.injective ((b.baseChange S).ext fun j => ?_)
  simp [εS, Algebra.smul_def, Finsupp.single_apply]

end BaseChangeTrace

end LinearMap
