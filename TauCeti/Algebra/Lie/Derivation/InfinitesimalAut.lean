/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import TauCeti.Algebra.Lie.Derivation.BaseChange
public import TauCeti.Algebra.Lie.Derivation.FirstOrder

/-!
# Infinitesimal automorphisms are derivations

Let `A` be an `R`-algebra and `A[ε] = R[ε] ⊗[R] A` its trivial first-order deformation over the
dual numbers `R[ε]`. An **infinitesimal automorphism** of `A` is an `R[ε]`-algebra automorphism
of `A[ε]` that reduces to the identity modulo `ε`. Every derivation `D` of `A` gives one, namely
`1 + ε D`, the first-order automorphism `TauCeti.derivationLieAlgebra.firstOrderAlgEquiv` of the
extension of `D` to `A[ε]`. Conversely, an infinitesimal automorphism `σ` sends `1 ⊗ a` to
`1 ⊗ a + ε ⊗ D a` for a unique `D a ∈ A`; multiplicativity of `σ` is the Leibniz rule for `D`.
So `D ↦ 1 + ε D` is an isomorphism from the additive group of derivations of `A` onto the group
of infinitesimal automorphisms.

For `A` commutative, this is the affine case of the infinitesimal automorphisms of
`Spec A` over `Spec R`: automorphisms of `Spec A ×_R Spec R[ε]` over `Spec R[ε]` restricting to the
identity of `Spec A`.

## Main definitions

* `TauCeti.dualNumberTensorReduce`: reduction modulo `ε`, the `R`-algebra map
  `R[ε] ⊗[R] A → A`, `s ⊗ a ↦ s₀ a`.
* `TauCeti.dualNumberTensorEpsCoeff`: the `ε`-coefficient, the `R`-linear map
  `R[ε] ⊗[R] A → A`, `s ⊗ a ↦ s₁ a`, where `s = s₀ + s₁ ε`.
* `TauCeti.infinitesimalAlgAut R A`: the subgroup of `R[ε]`-algebra automorphisms of
  `R[ε] ⊗[R] A` that reduce to the identity modulo `ε`.
* `TauCeti.derivationLieAlgebra.infinitesimalAlgAutEquiv`: the isomorphism
  `D ↦ 1 + ε D` from the additive group of derivations onto `infinitesimalAlgAut R A`.

## Main results

* `TauCeti.dualNumberTensor_eq`: every element of `R[ε] ⊗[R] A` is `1 ⊗ x + ε ⊗ y`, with `x` its
  reduction and `y` its `ε`-coefficient.
* `TauCeti.derivationLieAlgebra.infinitesimalAlgAutEquiv_apply_tmul`: the automorphism attached to
  `D` sends `1 ⊗ a` to `1 ⊗ a + ε ⊗ D a`.

## References

* R. Hartshorne, *Deformation Theory*, Graduate Texts in Mathematics 257, Springer, 2010,
  Chapter 1, for first-order deformations over the dual numbers.
-/

public section

open scoped TensorProduct DualNumber
open TensorProduct

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]

/-- **Reduction modulo `ε`**: the `R`-algebra map `R[ε] ⊗[R] A → A`, `s ⊗ a ↦ s₀ a` for
`s = s₀ + s₁ ε`. -/
noncomputable def dualNumberTensorReduce : R[ε] ⊗[R] A →ₐ[R] A :=
  (Algebra.TensorProduct.lid R A).toAlgHom.comp
    (Algebra.TensorProduct.map (TrivSqZeroExt.fstHom R R R) (AlgHom.id R A))

/-- **The `ε`-coefficient**: the `R`-linear map `R[ε] ⊗[R] A → A`, `s ⊗ a ↦ s₁ a` for
`s = s₀ + s₁ ε`. -/
noncomputable def dualNumberTensorEpsCoeff : R[ε] ⊗[R] A →ₗ[R] A :=
  TensorProduct.lid R A ∘ₗ LinearMap.rTensor A (TrivSqZeroExt.sndHom R R)

variable {R A}

/-- Reduction modulo `ε` of a pure tensor. -/
@[simp]
theorem dualNumberTensorReduce_tmul (s : R[ε]) (a : A) :
    dualNumberTensorReduce R A (s ⊗ₜ[R] a) = TrivSqZeroExt.fst s • a := by
  simp [dualNumberTensorReduce]

/-- The `ε`-coefficient of a pure tensor. -/
@[simp]
theorem dualNumberTensorEpsCoeff_tmul (s : R[ε]) (a : A) :
    dualNumberTensorEpsCoeff R A (s ⊗ₜ[R] a) = TrivSqZeroExt.snd s • a := by
  simp [dualNumberTensorEpsCoeff]

/-- Reduction modulo `ε` takes scalars of `R[ε]` to their constant terms. -/
theorem dualNumberTensorReduce_smul (s : R[ε]) (x : R[ε] ⊗[R] A) :
    dualNumberTensorReduce R A (s • x) = TrivSqZeroExt.fst s • dualNumberTensorReduce R A x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [TensorProduct.smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul t a => rw [smul_tmul', dualNumberTensorReduce_tmul, dualNumberTensorReduce_tmul,
      smul_eq_mul, TrivSqZeroExt.fst_mul, mul_smul]

/-- **Coordinates on `R[ε] ⊗[R] A`**: every element is `1 ⊗ x + ε ⊗ y`, where `x` is its
reduction modulo `ε` and `y` its `ε`-coefficient. -/
theorem dualNumberTensor_eq (x : R[ε] ⊗[R] A) :
    x = 1 ⊗ₜ[R] dualNumberTensorReduce R A x + ε ⊗ₜ[R] dualNumberTensorEpsCoeff R A x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, tmul_add]
    abel
  | tmul s a =>
    rw [dualNumberTensorReduce_tmul, dualNumberTensorEpsCoeff_tmul, ← smul_tmul, ← smul_tmul,
      ← add_tmul]
    congr 1
    ext <;> simp

@[simp]
theorem dualNumberTensorReduce_one_tmul_add_eps_tmul (x y : A) :
    dualNumberTensorReduce R A (1 ⊗ₜ[R] x + ε ⊗ₜ[R] y) = x := by
  simp

@[simp]
theorem dualNumberTensorEpsCoeff_one_tmul_add_eps_tmul (x y : A) :
    dualNumberTensorEpsCoeff R A (1 ⊗ₜ[R] x + ε ⊗ₜ[R] y) = y := by
  simp

/-- `a ↦ ε ⊗ a` is injective: the `ε`-coefficient recovers `a`. -/
theorem eps_tmul_injective : Function.Injective fun a : A => (ε : R[ε]) ⊗ₜ[R] a := fun a b h => by
  simpa using congrArg (dualNumberTensorEpsCoeff R A) h

/-- Scalars of `R` act on `R[ε] ⊗[R] A` through the constants `R → R[ε]`. -/
theorem one_tmul_smul_eq_inl_smul (r : R) (a : A) :
    (1 : R[ε]) ⊗ₜ[R] (r • a) = (TrivSqZeroExt.inl r : R[ε]) • ((1 : R[ε]) ⊗ₜ[R] a) := by
  rw [smul_tmul', smul_eq_mul, mul_one, ← smul_tmul]
  congr 1
  ext <;> simp

/-- The `ε`-coefficient is linear over the constants of `R[ε]`. -/
theorem dualNumberTensorEpsCoeff_inl_smul (r : R) (x : R[ε] ⊗[R] A) :
    dualNumberTensorEpsCoeff R A ((TrivSqZeroExt.inl r : R[ε]) • x) =
      r • dualNumberTensorEpsCoeff R A x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [TensorProduct.smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul t a =>
    rw [smul_tmul', dualNumberTensorEpsCoeff_tmul, dualNumberTensorEpsCoeff_tmul, smul_eq_mul,
      ← smul_assoc]
    simp

variable (R A)

/-- **The infinitesimal automorphisms** of an `R`-algebra `A`: the `R[ε]`-algebra automorphisms
of its trivial first-order deformation `R[ε] ⊗[R] A` that reduce to the identity modulo `ε`. -/
def infinitesimalAlgAut : Subgroup (R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A) where
  carrier := {σ | ∀ x, dualNumberTensorReduce R A (σ x) = dualNumberTensorReduce R A x}
  mul_mem' hσ hτ x := by rw [AlgEquiv.mul_apply, hσ, hτ]
  one_mem' x := rfl
  inv_mem' {σ} hσ x := by
    rw [← hσ, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

variable {R A}

theorem mem_infinitesimalAlgAut {σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A} :
    σ ∈ infinitesimalAlgAut R A ↔
      ∀ x, dualNumberTensorReduce R A (σ x) = dualNumberTensorReduce R A x :=
  Iff.rfl

/-- An infinitesimal automorphism sends `1 ⊗ a` to `1 ⊗ a + ε ⊗ y`, where `y` is the
`ε`-coefficient of the image. -/
theorem infinitesimalAlgAut_apply_one_tmul {σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A}
    (hσ : σ ∈ infinitesimalAlgAut R A) (a : A) :
    σ (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a + ε ⊗ₜ[R] dualNumberTensorEpsCoeff R A (σ (1 ⊗ₜ[R] a)) := by
  conv_lhs => rw [dualNumberTensor_eq (σ (1 ⊗ₜ[R] a))]
  rw [hσ, dualNumberTensorReduce_tmul]
  simp

namespace derivationLieAlgebra

/-- The first-order automorphism `1 + ε D` of the extension of a derivation `D` to
`R[ε] ⊗[R] A`. -/
noncomputable abbrev dualNumberAlgEquiv (D : derivationLieAlgebra R A) :
    R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A :=
  firstOrderAlgEquiv (ε : R[ε]) DualNumber.eps_mul_eps (baseChange R[ε] D)

/-- The automorphism `1 + ε D` sends `1 ⊗ a` to `1 ⊗ a + ε ⊗ D a`. -/
theorem dualNumberAlgEquiv_one_tmul (D : derivationLieAlgebra R A) (a : A) :
    dualNumberAlgEquiv D (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a + ε ⊗ₜ[R] (D : Module.End R A) a := by
  rw [firstOrderAlgEquiv_apply, baseChange_tmul, smul_tmul', smul_eq_mul, mul_one]

/-- The automorphism `1 + ε D` reduces to the identity modulo `ε`. -/
theorem dualNumberAlgEquiv_mem_infinitesimalAlgAut (D : derivationLieAlgebra R A) :
    dualNumberAlgEquiv D ∈ infinitesimalAlgAut R A := fun x => by
  rw [firstOrderAlgEquiv_apply, map_add, dualNumberTensorReduce_smul, DualNumber.fst_eps,
    zero_smul, add_zero]

/-- The derivation underlying an infinitesimal automorphism `σ`: `a` goes to the `ε`-coefficient
of `σ (1 ⊗ a)`. -/
noncomputable def ofInfinitesimalAlgAut (σ : infinitesimalAlgAut R A) :
    derivationLieAlgebra R A :=
  ⟨{ toFun := fun a => dualNumberTensorEpsCoeff R A
         ((σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A) (1 ⊗ₜ[R] a))
     map_add' := fun a b => by rw [tmul_add, map_add, map_add]
     map_smul' := fun r a => by
       rw [one_tmul_smul_eq_inl_smul, map_smul, dualNumberTensorEpsCoeff_inl_smul,
         RingHom.id_apply] },
    mem_derivationLieAlgebra.2 fun x y => by
      have hx := infinitesimalAlgAut_apply_one_tmul σ.property x
      have hy := infinitesimalAlgAut_apply_one_tmul σ.property y
      have hxy : (σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A) (1 ⊗ₜ[R] (x * y)) =
          (σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A) (1 ⊗ₜ[R] x) *
            (σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A) (1 ⊗ₜ[R] y) := by
        rw [← map_mul]
        congr 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      change dualNumberTensorEpsCoeff R A _ = dualNumberTensorEpsCoeff R A _ * y +
        x * dualNumberTensorEpsCoeff R A _
      rw [hxy]
      conv_lhs => rw [hx, hy]
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        DualNumber.eps_mul_eps, zero_tmul, add_zero, map_add, dualNumberTensorEpsCoeff_tmul,
        TrivSqZeroExt.snd_one, DualNumber.snd_eps, zero_smul, one_smul, zero_add]⟩

/-- The derivation of `σ` sends `a` to the `ε`-coefficient of `σ (1 ⊗ a)`. -/
theorem ofInfinitesimalAlgAut_apply (σ : infinitesimalAlgAut R A) (a : A) :
    (ofInfinitesimalAlgAut σ : Module.End R A) a =
      dualNumberTensorEpsCoeff R A ((σ : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A) (1 ⊗ₜ[R] a)) :=
  (rfl)

/-- **Infinitesimal automorphisms are derivations**: `D ↦ 1 + ε D` is an isomorphism from the
additive group of derivations of the `R`-algebra `A` onto the group of `R[ε]`-algebra
automorphisms of `R[ε] ⊗[R] A` that reduce to the identity modulo `ε`. -/
noncomputable def infinitesimalAlgAutEquiv :
    Multiplicative (derivationLieAlgebra R A) ≃* infinitesimalAlgAut R A where
  toFun D := ⟨dualNumberAlgEquiv D.toAdd, dualNumberAlgEquiv_mem_infinitesimalAlgAut _⟩
  invFun σ := Multiplicative.ofAdd (ofInfinitesimalAlgAut σ)
  left_inv D := by
    refine congrArg Multiplicative.ofAdd (ext fun a => ?_)
    rw [ofInfinitesimalAlgAut_apply]
    simp only [dualNumberAlgEquiv_one_tmul, dualNumberTensorEpsCoeff_one_tmul_add_eps_tmul]
    rfl
  right_inv σ := by
    refine Subtype.ext (AlgEquiv.ext fun x => ?_)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s a =>
      have hs : s ⊗ₜ[R] a = s • (1 : R[ε]) ⊗ₜ[R] a := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, dualNumberAlgEquiv_one_tmul, toAdd_ofAdd,
        ofInfinitesimalAlgAut_apply,
        ← infinitesimalAlgAut_apply_one_tmul σ.property]
  map_mul' D E := Subtype.ext <| by
    simp only [dualNumberAlgEquiv, toAdd_mul, baseChange_add, firstOrderAlgEquiv_add]
    rfl

/-- The infinitesimal automorphism attached to `D` sends `1 ⊗ a` to `1 ⊗ a + ε ⊗ D a`. -/
theorem infinitesimalAlgAutEquiv_apply_tmul (D : derivationLieAlgebra R A) (a : A) :
    (infinitesimalAlgAutEquiv (Multiplicative.ofAdd D) : R[ε] ⊗[R] A ≃ₐ[R[ε]] R[ε] ⊗[R] A)
      (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a + ε ⊗ₜ[R] (D : Module.End R A) a :=
  dualNumberAlgEquiv_one_tmul D a

end derivationLieAlgebra

end TauCeti
