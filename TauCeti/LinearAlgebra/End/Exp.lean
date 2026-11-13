/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Exponentials of nilpotent linear endomorphisms

A nilpotent linear endomorphism satisfying the associative Leibniz rule exponentiates to an
algebra automorphism, with inverse the exponential of its negative. The algebra may be
noncommutative. Exponentiation also commutes with restriction of scalars. This packages
Mathlib's `Module.End.exp_mul_of_derivation` and
`IsNilpotent.isUnit_exp`; scalar restriction uses `IsNilpotent.map_exp`, and the
fixed-vector formula uses `IsNilpotent.exp_smul_eq_sum`.

A bilinear pairing satisfying the Leibniz rule for three endomorphisms also
intertwines their nilpotent exponentials. This extends the tensor-product
argument of `Module.End.exp_mul_of_derivation` to three different modules,
using exponential intertwining and commuting nilpotent endomorphisms.

Adapted from `Mei/LinearAlgebra/End/Exp.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace Module.End

section RestrictScalars

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommGroup M]
  [Module R M] [Module S M] [Module ℚ M] [SMul R S] [IsScalarTower R S M]

/-- Restricting the scalars of a nilpotent endomorphism commutes with its exponential. -/
@[simp]
theorem exp_restrictScalars (D : Module.End S M) (hD : IsNilpotent D) :
    (IsNilpotent.exp D).restrictScalars R = IsNilpotent.exp (D.restrictScalars R) := by
  let f : Module.End S M →+* Module.End R M :=
    { toFun := LinearMap.restrictScalars R
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  exact hD.map_exp f

end RestrictScalars

/-! ### Invariant submodules

The finite exponential of a nilpotent endomorphism preserves every submodule
stable under that endomorphism.
-/

/-- The finite exponential preserves every submodule stable under its endomorphism. -/
theorem exp_apply_mem_of_forall_mem {R M : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] [Module ℚ M] [Algebra ℚ R] [IsScalarTower ℚ R M]
    (D : Module.End R M) (hD : IsNilpotent D) (S : Submodule R M)
    (hS : ∀ x ∈ S, D x ∈ S) {x : M} (hx : x ∈ S) :
    IsNilpotent.exp D x ∈ S := by
  obtain ⟨k, hk⟩ := hD
  rw [IsNilpotent.exp_eq_sum hk, LinearMap.sum_apply]
  exact S.sum_mem fun n _ => S.smul_of_tower_mem _
    (Module.End.pow_apply_mem_of_forall_mem (f' := D) n hS x hx)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module ℚ M]

/-- Exponentiating a nilpotent endomorphism fixes every vector in its kernel. -/
theorem exp_apply_eq_self (D : Module.End R M) (hD : IsNilpotent D) {m : M}
    (hm : D m = 0) : IsNilpotent.exp D m = m := by
  have h : (D ^ 1) • m = 0 := by simpa using hm
  simpa using IsNilpotent.exp_smul_eq_sum h hD

variable {A : Type*} [Ring A] [Algebra R A] [Module ℚ A]

/-- The exponential of a nilpotent associative derivation is an algebra automorphism. -/
noncomputable def expAlgEquiv (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) :
    A ≃ₐ[R] A :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (IsNilpotent.exp D)
      (exp_apply_eq_self D hD (by simpa using hder 1 1))
      (exp_mul_of_derivation R A D hder hD))
    ((Module.End.isUnit_iff _).mp hD.isUnit_exp)

/-- The automorphism acts by Mathlib's finite exponential. -/
@[simp]
theorem expAlgEquiv_apply (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) (a : A) :
    D.expAlgEquiv hder hD a = IsNilpotent.exp D a := (rfl)

/-- The inverse acts by the finite exponential of the negative endomorphism. -/
@[simp]
theorem expAlgEquiv_symm_apply (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) (a : A) :
    (D.expAlgEquiv hder hD).symm a = IsNilpotent.exp (-D) a := by
  apply (D.expAlgEquiv hder hD).injective
  simp only [AlgEquiv.apply_symm_apply, expAlgEquiv_apply]
  exact (LinearMap.congr_fun hD.exp_mul_exp_neg_self a).symm

end Module.End

section BilinearPairings

namespace LinearMap

open IsNilpotent TensorProduct

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module ℚ M]
  [AddCommGroup N] [Module R N] [Module ℚ N]
  [AddCommGroup P] [Module R P] [Module ℚ P]

/-- A Leibniz-compatible bilinear pairing intertwines nilpotent exponentials. -/
theorem exp_bilinear_of_leibniz
    (f : M →ₗ[R] N →ₗ[R] P)
    (D₁ : Module.End R M) (D₂ : Module.End R N) (D₃ : Module.End R P)
    (h : ∀ x y, D₃ (f x y) = f x (D₂ y) + f (D₁ x) y)
    (h₁ : IsNilpotent D₁) (h₂ : IsNilpotent D₂) (h₃ : IsNilpotent D₃)
    (x : M) (y : N) :
    exp D₃ (f x y) = f (exp D₁ x) (exp D₂ y) := by
  let DL : Module.End R (M ⊗[R] N) := D₂.lTensor M
  let DR : Module.End R (M ⊗[R] N) := D₁.rTensor N
  have h_nilL : IsNilpotent DL := h₂.map <| Module.End.lTensorAlgHom R N M
  have h_nilR : IsNilpotent DR := h₁.map <| Module.End.rTensorAlgHom R M N
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift f
  have hc : exp D₃ ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    apply Module.End.commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) h₃
    ext
    simp [DL, DR, m, h]
  have hl : exp DL = (exp D₂).lTensor M :=
    (h₂.map_exp (Module.End.lTensorAlgHom R N M)).symm
  have hr : exp DR = (exp D₁).rTensor N :=
    (h₁.map_exp (Module.End.rTensorAlgHom R M N)).symm
  have he := LinearMap.congr_fun hc (x ⊗ₜ[R] y)
  simpa [exp_add_of_commute h_comm h_nilL h_nilR, hl, hr, m] using he

end LinearMap

end BilinearPairings
