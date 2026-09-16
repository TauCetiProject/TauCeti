/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Algebra.Module.Injective.SelfInjective

/-!
# Frobenius functionals

Let `A` be an algebra over a commutative ring `k`. A linear functional `φ : A →ₗ[k] k` is a
**Frobenius functional** when the bilinear form `(a, b) ↦ φ (a * b)` is nondegenerate, and a
**symmetric Frobenius functional** when moreover `φ (a * b) = φ (b * a)`. A finite-dimensional
algebra over a field carrying a Frobenius functional is a Frobenius algebra; carrying a symmetric
one, a symmetric algebra. Frobenius algebras are the basic examples of self-injective algebras,
whose stable module categories are the first examples of stable categories of Frobenius exact
categories.

For `A` finite-dimensional over a field this file proves the standard characterizations.

* Nondegeneracy on one side already implies nondegeneracy on the other, and a Frobenius functional
  makes `(a, b) ↦ φ (a * b)` a perfect pairing.
* The existence of a Frobenius functional is equivalent to an isomorphism of right `A`-modules
  `A ≅ A⁺` between the regular module and the `k`-dual `A⁺ = Module.Dual k A`, on which `A` acts on
  the right by `(ψ · c) b = ψ (c * b)`. That right action is written with Mathlib's domain action
  `DomMulAct.mk c • ψ`. The isomorphism attached to `φ` is `a ↦ φ (a * ·)`, and conversely an
  isomorphism `e` recovers the functional `e 1`. These two constructions are inverse to each other,
  so Frobenius functionals and such isomorphisms correspond one to one.
* A Frobenius functional determines its **Nakayama automorphism** `ν`, the unique map with
  `φ (a * b) = φ (b * ν a)`; it is a `k`-algebra automorphism, and it is the identity exactly when
  `φ` is symmetric.
* A Frobenius algebra is self-injective on both sides: `A` is injective as a left and as a right
  module over itself.

The trace of square matrices is the basic example; see `TauCeti.Algebra.Algebra.Frobenius.Matrix`.

## Main definitions

* `LinearMap.IsFrobeniusFunctional`: the form `(a, b) ↦ φ (a * b)` is nondegenerate.
* `LinearMap.IsSymmetricFrobeniusFunctional`: a Frobenius functional with `φ (a * b) = φ (b * a)`.
* `LinearMap.IsFrobeniusFunctional.toDualEquiv`: the isomorphism `A ≅ A⁺` of right `A`-modules
  attached to a Frobenius functional on a finite-dimensional algebra.
* `TauCeti.frobeniusFunctionalEquivDualEquiv`: the resulting bijection between Frobenius
  functionals and isomorphisms `A ≅ A⁺` of right `A`-modules.
* `LinearMap.IsFrobeniusFunctional.nakayamaAut`: the Nakayama automorphism of a Frobenius
  functional on a finite-dimensional algebra.

## Main results

* `LinearMap.IsFrobeniusFunctional.of_left`, `LinearMap.IsFrobeniusFunctional.of_right`: in finite
  dimension one-sided nondegeneracy suffices.
* `LinearMap.exists_isFrobeniusFunctional_iff`: a Frobenius functional exists if and only if the
  regular right module is isomorphic to the dual.
* `LinearMap.IsFrobeniusFunctional.apply_mul_nakayamaAut` and
  `LinearMap.IsFrobeniusFunctional.coe_nakayamaAut_eq`: the defining identity of the Nakayama
  automorphism and its uniqueness.
* `LinearMap.IsFrobeniusFunctional.nakayamaAut_eq_refl_iff`: the Nakayama automorphism is trivial
  if and only if the functional is symmetric.
* `LinearMap.IsFrobeniusFunctional.moduleInjective_self` and
  `LinearMap.IsFrobeniusFunctional.moduleInjective_op_self`: a Frobenius algebra is left and right
  self-injective.

## References

* T. Y. Lam, *Lectures on modules and rings*, Section 16 (Frobenius and symmetric algebras, the
  Nakayama automorphism, self-injectivity).
* A. Skowroński, K. Yamagata, *Frobenius algebras I*, Chapter IV, Section 2.
-/

public section

namespace TauCeti

open Function

universe u v

section CommSemiring

variable {k : Type v} [CommSemiring k] {A : Type u} [Semiring A] [Algebra k A]
  {φ : A →ₗ[k] k}

/-- A linear functional `φ` on a `k`-algebra `A` is a **Frobenius functional** when the bilinear
form `(a, b) ↦ φ (a * b)` is nondegenerate: `φ (a * b) = 0` for all `b` forces `a = 0`, and
`φ (a * b) = 0` for all `a` forces `b = 0`. -/
def _root_.LinearMap.IsFrobeniusFunctional (φ : A →ₗ[k] k) : Prop :=
  ((LinearMap.mul k A).compr₂ φ).Nondegenerate

/-- An isomorphism of right `A`-modules from `A` to its dual is determined by its value at `1`. -/
theorem dualEquiv_apply_apply {e : A ≃ₗ[k] Module.Dual k A}
    (he : ∀ a c : A, e (a * c) = DomMulAct.mk c • e a) (a b : A) : e a b = e 1 (a * b) := by
  simpa [DomMulAct.smul_linearMap_apply] using LinearMap.congr_fun (he 1 a) b

end CommSemiring

section CommRing

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {φ : A →ₗ[k] k}

/-- A **symmetric Frobenius functional** is a Frobenius functional `φ` with
`φ (a * b) = φ (b * a)` for all `a` and `b`. -/
structure _root_.LinearMap.IsSymmetricFrobeniusFunctional (φ : A →ₗ[k] k) : Prop where
  /-- The functional is a Frobenius functional. -/
  isFrobeniusFunctional : φ.IsFrobeniusFunctional
  /-- The functional is symmetric in the factors of a product. -/
  apply_mul_comm : ∀ a b : A, φ (a * b) = φ (b * a)

/-- Unfolding the nondegeneracy of `(a, b) ↦ φ (a * b)` into its two separating conditions. -/
theorem _root_.LinearMap.isFrobeniusFunctional_iff :
    φ.IsFrobeniusFunctional ↔
      (∀ a : A, (∀ b, φ (a * b) = 0) → a = 0) ∧ ∀ b : A, (∀ a, φ (a * b) = 0) → b = 0 := by
  simp [LinearMap.IsFrobeniusFunctional, LinearMap.Nondegenerate, LinearMap.SeparatingLeft,
    LinearMap.SeparatingRight]

section Nondegenerate

/-- An element pairing to zero from the left against a Frobenius functional is zero. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.eq_zero_of_forall_left
    (hφ : φ.IsFrobeniusFunctional) {a : A} (h : ∀ b, φ (a * b) = 0) : a = 0 :=
  (LinearMap.isFrobeniusFunctional_iff.mp hφ).1 a h

/-- An element pairing to zero from the right against a Frobenius functional is zero. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.eq_zero_of_forall_right
    (hφ : φ.IsFrobeniusFunctional) {b : A} (h : ∀ a, φ (a * b) = 0) : b = 0 :=
  (LinearMap.isFrobeniusFunctional_iff.mp hφ).2 b h

/-- Two elements pairing identically from the right against a Frobenius functional are equal. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.eq_of_forall_apply_mul_eq
    (hφ : φ.IsFrobeniusFunctional) {x y : A} (h : ∀ b, φ (b * x) = φ (b * y)) : x = y :=
  sub_eq_zero.mp <| hφ.eq_zero_of_forall_right fun b => by rw [mul_sub, map_sub, h, sub_self]

/-- A Frobenius functional on `A` is a Frobenius functional on `Aᵐᵒᵖ`, through `unop`. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.op (hφ : φ.IsFrobeniusFunctional) :
    (φ ∘ₗ (MulOpposite.opLinearEquiv k (M := A)).symm.toLinearMap).IsFrobeniusFunctional := by
  refine LinearMap.isFrobeniusFunctional_iff.mpr ⟨fun a h => ?_, fun b h => ?_⟩
  · refine MulOpposite.unop_injective (hφ.eq_zero_of_forall_right fun c => ?_)
    simpa using h (MulOpposite.op c)
  · refine MulOpposite.unop_injective (hφ.eq_zero_of_forall_left fun c => ?_)
    simpa using h (MulOpposite.op c)

end Nondegenerate

end CommRing

section Projective

variable {k : Type v} [CommSemiring k] {A : Type u} [Semiring A] [Algebra k A]
  [Module.Projective k A]

/-- The value at `1` of an isomorphism of right `A`-modules from `A` to its dual is a Frobenius
functional. -/
theorem _root_.LinearMap.isFrobeniusFunctional_apply_one {e : A ≃ₗ[k] Module.Dual k A}
    (he : ∀ a c : A, e (a * c) = DomMulAct.mk c • e a) : (e 1).IsFrobeniusFunctional := by
  constructor
  · intro a ha
    apply e.injective
    apply LinearMap.ext
    intro b
    rw [map_zero, LinearMap.zero_apply, dualEquiv_apply_apply he]
    exact ha b
  · intro b hb
    exact (Module.forall_dual_apply_eq_zero_iff k b).mp fun f => by
      rw [← e.apply_symm_apply f, dualEquiv_apply_apply he]
      exact hb _

end Projective

/-! ### Finite-dimensional algebras -/

section FiniteDimensional

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
  {φ : A →ₗ[k] k}

/-- In finite dimension, nondegeneracy of `(a, b) ↦ φ (a * b)` in the first variable suffices. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.of_left
    (h : ∀ a : A, (∀ b, φ (a * b) = 0) → a = 0) : φ.IsFrobeniusFunctional :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun a ha => h a fun b => by simpa using ha b

/-- In finite dimension, nondegeneracy of `(a, b) ↦ φ (a * b)` in the second variable suffices. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.of_right
    (h : ∀ b : A, (∀ a, φ (a * b) = 0) → b = 0) : φ.IsFrobeniusFunctional :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingRight fun b hb => h b fun a => by simpa using hb a

/-- A Frobenius functional on a finite-dimensional algebra makes `(a, b) ↦ φ (a * b)` a perfect
pairing. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.isPerfPair (hφ : φ.IsFrobeniusFunctional) :
    ((LinearMap.mul k A).compr₂ φ).IsPerfPair :=
  .of_injective (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hφ.1))
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hφ.2))

/-- On a finite-dimensional algebra, `φ` is a Frobenius functional if and only if
`a ↦ φ (a * ·)` is a bijection from `A` onto its dual. -/
theorem _root_.LinearMap.isFrobeniusFunctional_iff_bijective :
    φ.IsFrobeniusFunctional ↔ Bijective ((LinearMap.mul k A).compr₂ φ) :=
  ⟨fun hφ => hφ.isPerfPair.bijective_left,
    fun h => .of_left fun a ha => h.injective (LinearMap.ext fun b => by simpa using ha b)⟩

/-! ### Frobenius functionals and the dual module -/

/-- The isomorphism of right `A`-modules `A ≃ₗ[k] Module.Dual k A` attached to a Frobenius
functional `φ` on a finite-dimensional algebra: it sends `a` to `b ↦ φ (a * b)`. Its
right-linearity is `LinearMap.IsFrobeniusFunctional.toDualEquiv_mul`. -/
noncomputable def _root_.LinearMap.IsFrobeniusFunctional.toDualEquiv
    (hφ : φ.IsFrobeniusFunctional) : A ≃ₗ[k] Module.Dual k A :=
  have := hφ.isPerfPair
  ((LinearMap.mul k A).compr₂ φ).toPerfPair

@[simp]
theorem _root_.LinearMap.IsFrobeniusFunctional.toDualEquiv_apply_apply
    (hφ : φ.IsFrobeniusFunctional) (a b : A) : hφ.toDualEquiv a b = φ (a * b) := by
  simp [LinearMap.IsFrobeniusFunctional.toDualEquiv]

/-- The isomorphism attached to a Frobenius functional is an isomorphism of right `A`-modules,
where `c : A` acts on the right of a functional `ψ` by `b ↦ ψ (c * b)`, that is by
`DomMulAct.mk c • ψ`. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.toDualEquiv_mul (hφ : φ.IsFrobeniusFunctional)
    (a c : A) : hφ.toDualEquiv (a * c) = DomMulAct.mk c • hφ.toDualEquiv a := by
  ext b
  simp [DomMulAct.smul_linearMap_apply, mul_assoc]

/-- The isomorphism attached to a Frobenius functional gives it back at `1`. -/
@[simp]
theorem _root_.LinearMap.IsFrobeniusFunctional.toDualEquiv_one (hφ : φ.IsFrobeniusFunctional) :
    hφ.toDualEquiv 1 = φ := by
  ext b
  simp

/-- **Frobenius functionals and the dual module.** A finite-dimensional algebra carries a Frobenius
functional if and only if its regular right module is isomorphic to the dual `Module.Dual k A`,
where `c : A` acts on the right of a functional `ψ` by `b ↦ ψ (c * b)`, that is by
`DomMulAct.mk c • ψ`. The two constructions are inverse to each other, see
`TauCeti.frobeniusFunctionalEquivDualEquiv`. -/
theorem _root_.LinearMap.exists_isFrobeniusFunctional_iff :
    (∃ φ : A →ₗ[k] k, φ.IsFrobeniusFunctional) ↔
      ∃ e : A ≃ₗ[k] Module.Dual k A, ∀ a c : A, e (a * c) = DomMulAct.mk c • e a :=
  ⟨fun ⟨_, hφ⟩ => ⟨hφ.toDualEquiv, hφ.toDualEquiv_mul⟩,
    fun ⟨_, he⟩ => ⟨_, LinearMap.isFrobeniusFunctional_apply_one he⟩⟩

/-- The isomorphism attached to the Frobenius functional recovered from an isomorphism of right
`A`-modules is that isomorphism again. -/
theorem toDualEquiv_isFrobeniusFunctional_apply_one {e : A ≃ₗ[k] Module.Dual k A}
    (he : ∀ a c : A, e (a * c) = DomMulAct.mk c • e a) :
    (LinearMap.isFrobeniusFunctional_apply_one he).toDualEquiv = e :=
  LinearEquiv.ext fun a => LinearMap.ext fun b => by
    rw [LinearMap.IsFrobeniusFunctional.toDualEquiv_apply_apply]
    exact (dualEquiv_apply_apply he a b).symm

variable (k A) in
/-- **Frobenius functionals are the isomorphisms `A ≅ A⁺` of right modules.** The pointwise form of
`LinearMap.exists_isFrobeniusFunctional_iff`: a Frobenius functional `φ` on a finite-dimensional
algebra goes to the isomorphism `a ↦ φ (a * ·)` of the regular right module with the dual, an
isomorphism `e` goes back to the functional `e 1`, and these are inverse to each other. -/
noncomputable def frobeniusFunctionalEquivDualEquiv :
    {φ : A →ₗ[k] k // φ.IsFrobeniusFunctional} ≃
      {e : A ≃ₗ[k] Module.Dual k A // ∀ a c : A, e (a * c) = DomMulAct.mk c • e a} where
  toFun φ := ⟨φ.2.toDualEquiv, φ.2.toDualEquiv_mul⟩
  invFun e := ⟨e.1 1, LinearMap.isFrobeniusFunctional_apply_one e.2⟩
  left_inv φ := Subtype.ext φ.2.toDualEquiv_one
  right_inv e := Subtype.ext (toDualEquiv_isFrobeniusFunctional_apply_one e.2)

@[simp]
theorem frobeniusFunctionalEquivDualEquiv_apply_coe
    (φ : {φ : A →ₗ[k] k // φ.IsFrobeniusFunctional}) :
    (frobeniusFunctionalEquivDualEquiv k A φ : A ≃ₗ[k] Module.Dual k A) =
      φ.2.toDualEquiv := (rfl)

@[simp]
theorem frobeniusFunctionalEquivDualEquiv_symm_apply_coe
    (e : {e : A ≃ₗ[k] Module.Dual k A // ∀ a c : A, e (a * c) = DomMulAct.mk c • e a}) :
    ((frobeniusFunctionalEquivDualEquiv k A).symm e : A →ₗ[k] k) = e.1 1 := (rfl)

/-! ### The Nakayama automorphism -/

section Nakayama

variable (hφ : φ.IsFrobeniusFunctional)
include hφ

/-- The Nakayama map as a linear map: `a` goes to the element pairing from the right as `a` pairs
from the left. -/
private noncomputable def nakayamaLinearMap : A →ₗ[k] A :=
  (LinearEquiv.ofBijective _ hφ.isPerfPair.bijective_right).symm.toLinearMap ∘ₗ
    (LinearMap.mul k A).compr₂ φ

private theorem apply_mul_nakayamaLinearMap (a b : A) :
    φ (b * nakayamaLinearMap hφ a) = φ (a * b) := by
  have h := LinearMap.congr_fun
    ((LinearEquiv.ofBijective _ hφ.isPerfPair.bijective_right).apply_symm_apply
      ((LinearMap.mul k A).compr₂ φ a)) b
  rw [LinearEquiv.ofBijective_apply] at h
  simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.mul_apply'] at h
  exact h

/-- The **Nakayama automorphism** of a Frobenius functional `φ` on a finite-dimensional algebra:
the unique map `ν` with `φ (a * b) = φ (b * ν a)` for all `a` and `b`
(`LinearMap.IsFrobeniusFunctional.apply_mul_nakayamaAut`,
`LinearMap.IsFrobeniusFunctional.coe_nakayamaAut_eq`). It is a `k`-algebra automorphism. -/
noncomputable def _root_.LinearMap.IsFrobeniusFunctional.nakayamaAut : A ≃ₐ[k] A :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (nakayamaLinearMap hφ)
      (hφ.eq_of_forall_apply_mul_eq fun b => by
        rw [apply_mul_nakayamaLinearMap, one_mul, mul_one])
      fun x y => hφ.eq_of_forall_apply_mul_eq fun b => by
        -- `φ (b * ν (x * y)) = φ (x * (y * b)) = φ (b * (ν x * ν y))`, moving one factor at a time.
        rw [apply_mul_nakayamaLinearMap, ← mul_assoc, apply_mul_nakayamaLinearMap, ← mul_assoc,
          apply_mul_nakayamaLinearMap, mul_assoc])
    (by
      have hinj : Injective (nakayamaLinearMap hφ) := fun x y hxy =>
        sub_eq_zero.mp <| hφ.eq_zero_of_forall_left fun b => by
          rw [sub_mul, map_sub, ← apply_mul_nakayamaLinearMap hφ x,
            ← apply_mul_nakayamaLinearMap hφ y, hxy, sub_self]
      exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩)

/-- The defining identity of the Nakayama automorphism: `φ (b * ν a) = φ (a * b)`. -/
@[simp]
theorem _root_.LinearMap.IsFrobeniusFunctional.apply_mul_nakayamaAut (a b : A) :
    φ (b * hφ.nakayamaAut a) = φ (a * b) :=
  apply_mul_nakayamaLinearMap hφ a b

/-- A Frobenius functional is invariant under its Nakayama automorphism. -/
@[simp]
theorem _root_.LinearMap.IsFrobeniusFunctional.apply_nakayamaAut (a : A) :
    φ (hφ.nakayamaAut a) = φ a := by
  simpa using hφ.apply_mul_nakayamaAut a 1

/-- **Uniqueness of the Nakayama automorphism.** Any map `σ` with `φ (b * σ a) = φ (a * b)` is the
Nakayama automorphism. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.coe_nakayamaAut_eq {σ : A → A}
    (hσ : ∀ a b, φ (b * σ a) = φ (a * b)) : ⇑hφ.nakayamaAut = σ :=
  funext fun a => hφ.eq_of_forall_apply_mul_eq fun b => by rw [hφ.apply_mul_nakayamaAut, hσ]

/-- The Nakayama automorphism of a Frobenius functional is the identity if and only if the
functional is symmetric. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.nakayamaAut_eq_refl_iff :
    hφ.nakayamaAut = AlgEquiv.refl ↔ ∀ a b : A, φ (a * b) = φ (b * a) := by
  refine ⟨fun h a b => ?_, fun h => AlgEquiv.ext fun a => ?_⟩
  · have hab := hφ.apply_mul_nakayamaAut a b
    rw [h, AlgEquiv.coe_refl, id_eq] at hab
    exact hab.symm
  · exact congrFun (hφ.coe_nakayamaAut_eq (σ := id) fun a b => (h a b).symm) a

omit hφ in
/-- The Nakayama automorphism of a symmetric Frobenius functional is the identity. -/
@[simp]
theorem _root_.LinearMap.IsSymmetricFrobeniusFunctional.nakayamaAut_eq_refl
    (hφ : φ.IsSymmetricFrobeniusFunctional) :
    hφ.isFrobeniusFunctional.nakayamaAut = AlgEquiv.refl :=
  (hφ.isFrobeniusFunctional.nakayamaAut_eq_refl_iff).mpr hφ.apply_mul_comm

end Nakayama

/-! ### Self-injectivity -/

section SelfInjective

/-- **A Frobenius algebra is left self-injective**: it is an injective left module over itself. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.moduleInjective_self
    (hφ : φ.IsFrobeniusFunctional) : Module.Injective A A :=
  Function.Bijective.moduleInjective_self hφ.isPerfPair.bijective_right fun x y z => by
    simp [mul_assoc]

/-- **A Frobenius algebra is right self-injective**: it is an injective right module over itself,
that is an injective module over `Aᵐᵒᵖ`. -/
theorem _root_.LinearMap.IsFrobeniusFunctional.moduleInjective_op_self
    (hφ : φ.IsFrobeniusFunctional) : Module.Injective Aᵐᵒᵖ A := by
  have hB : Module.Baer Aᵐᵒᵖ Aᵐᵒᵖ :=
    Function.Bijective.moduleBaer_self hφ.op.isPerfPair.bijective_right fun x y z => by
      simp [mul_assoc]
  -- The regular left `Aᵐᵒᵖ`-module is the regular right `A`-module, through `unop`: Mathlib's
  -- module structure on `Aᵐᵒᵖ` induced from the right action on `A` is the regular one.
  exact (hB.of_equiv (MulOpposite.opLinearEquiv Aᵐᵒᵖ (M := A)).symm).injective

end SelfInjective

end FiniteDimensional

end TauCeti
