/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Evaluation after scalar extension

This file defines the canonical pairing between the scalar extensions of a module and its linear
dual. It sends an `R`-linear functional extended to `A` to the corresponding `A`-linear functional
on the scalar extension of its domain. For a finite projective module, this map is an equivalence.
For an arbitrary base-change map, a nonzero functional remains nonzero when the scalar extension
is faithful, as recorded by `IsBaseChange.toDual_ne_zero`.

## Main declarations

* `TauCeti.Module.Dual.baseChangeEvaluation`: the canonical scalar-extended evaluation map.
* `TauCeti.Module.Dual.baseChangeEvaluation_one_tmul`: evaluation at a scalar-extended
  functional with coefficient one is its base change.
* `TauCeti.Module.Dual.baseChangeEvaluation_tmul`: its value on two pure tensors.
* `AlgHom.baseChangeEvaluation_rTensor`: naturality of evaluation in the scalar algebra.
* `Module.Dual.baseChangeEvaluation_one_tmul_baseChange`: naturality of evaluation
  with respect to a base-changed linear map.
* `Module.Dual.baseChange_rTensor`: base change of a functional is compatible with a change of
  coefficients `A ⟶ B`.
* `Module.Dual.baseChange_apply_one_tmul`, `Module.Dual.baseChange_apply_toAddMonoidHom_mk_one`,
  `Module.Dual.baseChange_apply_one`: the value of a base-changed functional at `1 ⊗ m`, at
  `(TensorProduct.mk ℤ A M 1).toAddMonoidHom m`, and at the unit of a base-changed algebra.
* `AddMonoidHom.apply_liftBaseChangeSemilinear_baseChange`: compatibility between a semilinear
  extension of `f : X →+ V` and the base change of an integral linear form agreeing with a linear
  form on `f(X)`.
* `TauCeti.Module.Dual.baseChangeEvaluationEquiv`: scalar extension commutes with the dual of a
  finite projective module.
* `TauCeti.Module.Dual.baseChange_coord`: base-changed dual basis elements recover the
  coordinates in the base-changed basis.
* `TauCeti.Module.Dual.eq_of_baseChange_eq`: base changes of all dual elements jointly
  separate vectors when the original module is projective.
* `TauCeti.Module.Dual.eq_zero_of_forall_baseChange_eq_zero`: base changes to a fraction ring of
  a set of functionals separating points separate points.
* `IsBaseChange.toDualBaseChange_tmul_tmul`: the value of Mathlib's comparison
  `IsBaseChange.toDualBaseChange` on two pure tensors, in simp normal form.

## References

The finite-projective equivalence is assembled from Mathlib's `dualTensorHomEquiv` and
`LinearMap.liftBaseChangeEquiv`.
-/

public section

open scoped TensorProduct

namespace TauCeti.Module.Dual

universe u w x

variable {R : Type u} {M : Type w} {A : Type x}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [CommSemiring A] [Algebra R A]

/-- The canonical pairing of scalar extensions, as the map sending a scalar-extended
`R`-linear functional to an `A`-linear functional on the scalar extension of its domain.

This map needs no finiteness hypothesis; for finite projective `M` it is an equivalence, see
`baseChangeEvaluationEquiv`. -/
def baseChangeEvaluation :
    A ⊗[R] Module.Dual R M →ₗ[A] Module.Dual A (A ⊗[R] M) :=
  (Module.Dual.baseChange A).liftBaseChange A

/-- Evaluating at the pure tensor `1 ⊗ φ` is the base change of `φ`. -/
theorem baseChangeEvaluation_one_tmul (φ : Module.Dual R M) :
    baseChangeEvaluation (R := R) (M := M) (A := A) (1 ⊗ₜ[R] φ) =
      Module.Dual.baseChange A φ := by
  simp only [baseChangeEvaluation, LinearMap.liftBaseChange_tmul, one_smul]

/-- On pure tensors, scalar-extended evaluation is
`⟨a ⊗ φ, b ⊗ m⟩ = a * b * algebraMap R A (φ m)`. -/
@[simp]
theorem baseChangeEvaluation_tmul (a b : A) (φ : Module.Dual R M) (m : M) :
    baseChangeEvaluation (R := R) (M := M) (A := A) (a ⊗ₜ[R] φ) (b ⊗ₜ[R] m) =
      a * b * algebraMap R A (φ m) := by
  simp only [baseChangeEvaluation, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
  rw [Algebra.algebraMap_self_apply]
  ac_rfl

/-- Scalar-extended evaluation is natural in the scalar algebra: extending scalars along
`f : A →ₐ[R] B` and then evaluating is `f` of the evaluation over `A`. -/
theorem _root_.AlgHom.baseChangeEvaluation_rTensor {B : Type*} [CommSemiring B] [Algebra R B]
    (f : A →ₐ[R] B) (ξ : A ⊗[R] Module.Dual R M) (v : A ⊗[R] M) :
    baseChangeEvaluation (R := R) (M := M) (A := B)
        (LinearMap.rTensor (Module.Dual R M) f.toLinearMap ξ)
        (LinearMap.rTensor M f.toLinearMap v) =
      f (baseChangeEvaluation (R := R) (M := M) (A := A) ξ v) := by
  induction ξ using TensorProduct.inductionOn with
  | add ξ ξ' hξ hξ' => simp only [map_add, LinearMap.add_apply, hξ, hξ']
  | tmul a φ =>
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => simp only [map_add, hv, hv']
    | tmul b m => simp [map_mul]

/-- Evaluation against a base-changed functional is natural with respect to the base change of
a linear map. -/
@[simp]
theorem _root_.Module.Dual.baseChangeEvaluation_one_tmul_baseChange
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (φ : Module.Dual R N) (t : A ⊗[R] M) :
    baseChangeEvaluation (R := R) (M := N) (A := A) (1 ⊗ₜ[R] φ) (f.baseChange A t) =
      baseChangeEvaluation (R := R) (M := M) (A := A) (1 ⊗ₜ[R] (φ.comp f)) t := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht
  | tmul a m => simp [baseChangeEvaluation_tmul]

/-- The base change of a functional `φ` takes `1 ⊗ m` to the image of `φ m` in `A`. -/
theorem _root_.Module.Dual.baseChange_apply_one_tmul (φ : Module.Dual R M) (m : M) :
    φ.baseChange A (1 ⊗ₜ[R] m) = algebraMap R A (φ m) := by
  rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]

/-- The base change of an integral functional `φ : Module.Dual ℤ M` evaluated at
`(TensorProduct.mk ℤ A M 1).toAddMonoidHom m` yields `(φ m : A)`. -/
theorem _root_.Module.Dual.baseChange_apply_toAddMonoidHom_mk_one {M A : Type*} [AddCommGroup M]
    [CommRing A] (φ : Module.Dual ℤ M) (m : M) :
    φ.baseChange A ((TensorProduct.mk ℤ A M 1).toAddMonoidHom m) = (φ m : A) := by
  rw [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply,
    Module.Dual.baseChange_apply_one_tmul, eq_intCast]

/-- Base change of a functional is compatible with a change of coefficients `A ⟶ B`: evaluating
the base change to `B` on the image of `v : A ⊗[R] M` is the image in `B` of the base change to
`A` evaluated on `v`. -/
theorem _root_.Module.Dual.baseChange_rTensor {B : Type*} [CommSemiring B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (φ : Module.Dual R M) (v : A ⊗[R] M) :
    φ.baseChange B (((Algebra.linearMap A B).restrictScalars R).rTensor M v) =
      algebraMap A B (φ.baseChange A v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a m =>
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply R A B]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The base change of a functional `φ` on an `R`-algebra `S` takes the unit of `A ⊗[R] S` to
the image of `φ 1` in `A`. -/
@[simp]
theorem _root_.Module.Dual.baseChange_apply_one {S : Type*} [Semiring S] [Algebra R S]
    (φ : Module.Dual R S) : φ.baseChange A 1 = algebraMap R A (φ 1) := by
  rw [Algebra.TensorProduct.one_def, Module.Dual.baseChange_apply_one_tmul]

/-- Evaluating `F : V →ₗ[T] T` on `f.liftBaseChangeSemilinear σ z` agrees with
`σ (Module.Dual.baseChange S φ z)` whenever `F` agrees with an integral linear form `φ` on
`f(X)`. -/
theorem _root_.AddMonoidHom.apply_liftBaseChangeSemilinear_baseChange {S T X V : Type*}
    [CommRing S] [Ring T] [AddCommGroup X] [AddCommGroup V] [Module T V]
    (f : X →+ V) (σ : S →+* T) (F : V →ₗ[T] T) (φ : Module.Dual ℤ X)
    (hF : ∀ x : X, F (f x) = (φ x : T)) (z : S ⊗[ℤ] X) :
    F (f.liftBaseChangeSemilinear σ z) = σ (Module.Dual.baseChange S φ z) :=
  f.apply_liftBaseChangeSemilinear σ F (Module.Dual.baseChange S φ)
    (fun x ↦ by rw [Module.Dual.baseChange_apply_one_tmul, eq_intCast, map_intCast, hF x]) z

section FiniteProjective

variable [Module.Finite R M] [Module.Projective R M]

/-- The scalar extension of the dual of a finite projective module is canonically equivalent to
the dual of its scalar extension. -/
private noncomputable def baseChangeEvaluationEquivRestrictScalars :
    A ⊗[R] Module.Dual R M ≃ₗ[R] Module.Dual A (A ⊗[R] M) :=
  (TensorProduct.comm R A (Module.Dual R M)).trans
    (dualTensorHomEquiv R M A) |>.trans
      ((LinearMap.liftBaseChangeEquiv A).restrictScalars R)

private theorem baseChangeEvaluationEquivRestrictScalars_toLinearMap :
    (baseChangeEvaluationEquivRestrictScalars (R := R) (A := A) (M := M)).toLinearMap =
      (baseChangeEvaluation (R := R) (M := M) (A := A)).restrictScalars R := by
  ext a φ b
  simp [baseChangeEvaluationEquivRestrictScalars, baseChangeEvaluation]

/-- Scalar extension commutes with the linear dual of a finite projective module. -/
noncomputable def baseChangeEvaluationEquiv :
    A ⊗[R] Module.Dual R M ≃ₗ[A] Module.Dual A (A ⊗[R] M) :=
  LinearEquiv.ofBijective (baseChangeEvaluation (R := R) (M := M) (A := A)) <| by
    rw [← LinearMap.coe_restrictScalars R]
    rw [← baseChangeEvaluationEquivRestrictScalars_toLinearMap]
    exact (baseChangeEvaluationEquivRestrictScalars (R := R) (A := A) (M := M)).bijective

/-- The finite-projective equivalence is the canonical scalar-extended evaluation map. -/
@[simp]
theorem baseChangeEvaluationEquiv_apply (z : A ⊗[R] Module.Dual R M) :
    baseChangeEvaluationEquiv (R := R) (A := A) (M := M) z =
      baseChangeEvaluation (R := R) (M := M) (A := A) z :=
  by simp only [baseChangeEvaluationEquiv, LinearEquiv.ofBijective_apply]

end FiniteProjective

/-- A coordinate in a base-changed basis is evaluation against the base change of the
corresponding element of the dual basis. -/
@[simp]
theorem baseChange_coord {ι : Type*} (b : Module.Basis ι R M) (i : ι) (z : A ⊗[R] M) :
    ((TensorProduct.isBaseChange R M A).basis b).repr z i =
      Module.Dual.baseChange A (b.coord i) z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hz hw
  | tmul a m =>
      calc
        ((TensorProduct.isBaseChange R M A).basis b).repr (a ⊗ₜ[R] m) i =
            ((TensorProduct.isBaseChange R M A).basis b).repr
              (a • (1 ⊗ₜ[R] m)) i := by
          simp [TensorProduct.smul_tmul']
        _ = a * ((TensorProduct.isBaseChange R M A).basis b).repr (1 ⊗ₜ[R] m) i := by simp
        _ = a * algebraMap R A (b.repr m i) := by
          simpa only [TensorProduct.mk_apply] using congrArg (a * ·)
            (IsBaseChange.basis_repr_comp_apply b (TensorProduct.isBaseChange R M A) m i)
        _ = Module.Dual.baseChange A (b.coord i) (a ⊗ₜ[R] m) := by
          simp [Module.Basis.coord_apply, Algebra.smul_def, mul_comm]

/-- If `M` is projective, the base changes of its `R`-linear functionals jointly separate vectors
in `A ⊗[R] M`.

Since contracting against `φ` is the base change of `φ`, this is the case of
`TensorProduct.tensor_eq_of_forall_tensorComponent_eq` with left factor `A`. -/
theorem eq_of_baseChange_eq [Module.Projective R M] {x y : A ⊗[R] M}
    (h : ∀ φ : Module.Dual R M,
      Module.Dual.baseChange A φ x = Module.Dual.baseChange A φ y) : x = y := by
  -- Contracting against `φ` is the base change of `φ`, viewed as an `R`-linear map.
  have hcomponent (φ : Module.Dual R M) :
      LinearMap.tensorComponent (M := A) φ = (Module.Dual.baseChange A φ).restrictScalars R :=
    TensorProduct.ext' fun a m ↦ by
      rw [LinearMap.tensorComponent_tmul, LinearMap.restrictScalars_apply,
        Module.Dual.baseChange_apply_tmul]
  refine TensorProduct.tensor_eq_of_forall_tensorComponent_eq fun φ ↦ ?_
  rw [hcomponent, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply]
  exact h φ

/-- If a set `Φ` of `R`-linear functionals jointly separates the points of `M`, then their base
changes to a fraction ring `K` of `R` jointly separate the points of `K ⊗[R] M`. Unlike
`eq_of_baseChange_eq`, `M` need not be projective. -/
theorem eq_zero_of_forall_baseChange_eq_zero {R M K : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] [CommRing K] [Algebra R K] [IsFractionRing R K] {Φ : Set (Module.Dual R M)}
    (hΦ : ∀ m : M, (∀ φ ∈ Φ, φ m = 0) → m = 0) {v : K ⊗[R] M}
    (h : ∀ φ ∈ Φ, Module.Dual.baseChange K φ v = 0) : v = 0 := by
  obtain ⟨⟨m, r⟩, hv⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K M 1) v
  have hm : m = 0 := hΦ m fun φ hφ ↦ IsFractionRing.injective R K <| by
    rw [map_zero, ← Module.Dual.baseChange_apply_one_tmul, ← TensorProduct.mk_apply, ← hv,
      Submonoid.smul_def, LinearMap.map_smul_of_tower, h φ hφ, smul_zero]
  rw [hm, map_zero, Submonoid.smul_def, ← algebraMap_smul K] at hv
  exact (IsLocalization.map_units K r).smul_eq_zero.mp hv

end TauCeti.Module.Dual

namespace IsBaseChange

variable {R A V W : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] [FaithfulSMul R A] {j : V →ₗ[R] W}

/-- A nonzero dual element remains nonzero under a faithful extension of scalars. -/
theorem toDual_ne_zero (h : IsBaseChange A j) (s : Module.Dual R V) (hs : s ≠ 0) :
    h.toDual s ≠ 0 := by
  intro hz
  apply hs
  ext v
  apply FaithfulSMul.algebraMap_injective R A
  have hv := DFunLike.congr_fun hz (j v)
  simpa only [toDual_comp_apply, LinearMap.zero_apply, map_zero] using hv

omit [FaithfulSMul R A] in
/-- `IsBaseChange.toDualBaseChange_tmul` for the canonical base change `A ⊗[R] V`, evaluated on
an arbitrary pure tensor `b ⊗ v`. -/
@[simp]
theorem toDualBaseChange_tmul_tmul [Module.Free R V] [Module.Finite R V] (a : A)
    (f : Module.Dual R V) (b : A) (v : V) :
    (TensorProduct.isBaseChange R V A).toDualBaseChange (a ⊗ₜ f) (b ⊗ₜ v) =
      a * b * algebraMap R A (f v) := by
  have h : (TensorProduct.isBaseChange R V A).toDualBaseChange (a ⊗ₜ f) (1 ⊗ₜ v) =
      a * algebraMap R A (f v) := toDualBaseChange_tmul ..
  rw [TensorProduct.tmul_eq_smul_one_tmul b, map_smul, h, smul_eq_mul, mul_left_comm, mul_assoc]

end IsBaseChange
