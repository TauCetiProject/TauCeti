/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# An abelian group with an automorphism, as a Laurent module

A module over `ℤ[T;T⁻¹]` is the same thing as an abelian group together with an automorphism,
the action of `T`.  For an additive automorphism `σ` of an abelian group `G`, the type
`TauCeti.LaurentAEval σ` is `G` with the `ℤ[T;T⁻¹]`-module structure in which `T` acts by `σ`.
It is the Laurent counterpart of Mathlib's `Module.AEval'`, which turns a single endomorphism into
a module over the polynomial ring; here the endomorphism is invertible, so `T⁻¹` acts too.

The action is evaluation `TauCeti.laurentEval` of a Laurent polynomial at `σ`, viewed as a unit of
the endomorphism ring of `G`.  Its defining property is `TauCeti.LaurentAEval.T_smul_of`: `Tⁿ`
acts by `n • σ`, the `n`-th power of `σ` in the additive group `AddAut G`, whose addition is
composition.

The universal property `TauCeti.LaurentAEval.liftEquiv` identifies the `ℤ[T;T⁻¹]`-linear maps out
of `LaurentAEval σ` into a `ℤ[T;T⁻¹]`-module `N` with the additive maps `f : G →+ N` satisfying
`f (σ x) = T • f x`.

Graded exact and graded triangulated `K₀` become modules over `ℤ[q,q⁻¹]` in this way,
`TauCeti.LaurentK0` and `TauCeti.LaurentTriangulatedK0`, with `σ` the automorphism induced by the
grading shift.

## Main definitions

* `TauCeti.LaurentAEval`: the group `G` as a `ℤ[T;T⁻¹]`-module, with `T` acting by `σ`.
* `TauCeti.LaurentAEval.of`: the additive equivalence `G ≃+ LaurentAEval σ`.
* `TauCeti.LaurentAEval.lift`: the `ℤ[T;T⁻¹]`-linear map induced by an additive map turning `σ`
  into multiplication by `T`.
* `TauCeti.LaurentAEval.liftEquiv`: the universal property.

## Main results

* `TauCeti.LaurentAEval.T_smul_of`: `Tⁿ • x = (n • σ) x`, with the generating cases
  `TauCeti.LaurentAEval.T_one_smul_of` and `TauCeti.LaurentAEval.T_neg_one_smul_of`.
* `TauCeti.LaurentAEval.hom_ext`: a `ℤ[T;T⁻¹]`-linear map out of `LaurentAEval σ` is determined by
  the underlying additive map out of `G`.
-/

public section

open LaurentPolynomial

namespace TauCeti

variable {G : Type*} [AddCommGroup G]

/-- **An abelian group with an automorphism, as a `ℤ[T;T⁻¹]`-module.**  This is a copy of `G`,
and the Laurent variable `T` acts by the automorphism `σ`.  Use `TauCeti.LaurentAEval.of` to
move elements of `G` into it. -/
structure LaurentAEval (σ : AddAut G) where
  /-- An element of `G`, viewed in `TauCeti.LaurentAEval σ`; prefer `TauCeti.LaurentAEval.of`. -/
  mk ::
  /-- The underlying element of `G`; prefer `(TauCeti.LaurentAEval.of σ).symm`. -/
  val : G

namespace LaurentAEval

variable (σ : AddAut G)

instance : AddCommGroup (LaurentAEval σ) :=
  Equiv.addCommGroup ⟨val, mk, fun _ => rfl, fun _ => rfl⟩

/-- The identification of `G` with the underlying group of `TauCeti.LaurentAEval σ`. -/
def of : G ≃+ LaurentAEval σ where
  toFun := mk
  invFun := val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The automorphism `σ` as a unit of the endomorphism ring of `TauCeti.LaurentAEval σ`. -/
private noncomputable def unit : (Module.End ℤ (LaurentAEval σ))ˣ :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((of σ).symm.trans (σ.trans (of σ))).toIntLinearEquiv

/-- **`ℤ[T;T⁻¹]` acts on `TauCeti.LaurentAEval σ`** by evaluating a Laurent polynomial at `σ`. -/
noncomputable instance : Module (LaurentPolynomial ℤ) (LaurentAEval σ) :=
  Module.compHom (LaurentAEval σ)
    (laurentEval (LinearMap.GeneralLinearGroup.ofLinearEquiv
      ((of σ).symm.trans (σ.trans (of σ))).toIntLinearEquiv)).toRingHom

private lemma smul_def (p : LaurentPolynomial ℤ) (x : LaurentAEval σ) :
    p • x = laurentEval (unit σ) p x :=
  (rfl)

private lemma unit_zpow_apply (n : ℤ) (x : G) :
    ((unit σ ^ n : (Module.End ℤ (LaurentAEval σ))ˣ) : Module.End ℤ (LaurentAEval σ)) (of σ x) =
      of σ ((n • σ) x) := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih =>
      rw [zpow_add_one, Units.val_mul, mul_apply_eq_comp, add_zsmul, one_zsmul,
        AddAut.add_apply]
      exact ih (σ x)
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, mul_apply_eq_comp, sub_zsmul, one_zsmul,
        AddAut.add_apply, AddAut.neg_apply]
      exact ih (σ.symm x)

/-- **`Tⁿ` acts by the `n`-th power of `σ`.**  This is the defining property of the module
structure, and it determines it. -/
@[simp]
theorem T_smul_of (n : ℤ) (x : G) :
    (T n : LaurentPolynomial ℤ) • of σ x = of σ ((n • σ) x) := by
  rw [smul_def, laurentEval_T, unit_zpow_apply]

/-- **`T` acts by `σ`.** -/
theorem T_one_smul_of (x : G) : (T 1 : LaurentPolynomial ℤ) • of σ x = of σ (σ x) := by
  simp

/-- **`T⁻¹` acts by the inverse of `σ`.** -/
theorem T_neg_one_smul_of (x : G) :
    (T (-1) : LaurentPolynomial ℤ) • of σ x = of σ (σ.symm x) := by
  simp

variable {σ} {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]

/-- **A `ℤ[T;T⁻¹]`-linear map out of `TauCeti.LaurentAEval σ` is determined by the underlying
additive map out of `G`.** -/
theorem hom_ext {f g : LaurentAEval σ →ₗ[LaurentPolynomial ℤ] N}
    (h : f.toAddMonoidHom.comp (of σ).toAddMonoidHom =
      g.toAddMonoidHom.comp (of σ).toAddMonoidHom) :
    f = g :=
  LinearMap.ext fun x => by simpa using DFunLike.congr_fun h ((of σ).symm x)

/-- **The `ℤ[T;T⁻¹]`-linear map induced by an additive map turning `σ` into multiplication
by `T`.** -/
noncomputable def lift (f : G →+ N) (hf : ∀ x, f (σ x) = (T 1 : LaurentPolynomial ℤ) • f x) :
    LaurentAEval σ →ₗ[LaurentPolynomial ℤ] N where
  toFun x := f ((of σ).symm x)
  map_add' x y := by simp
  map_smul' p x := by
    let g : LaurentAEval σ →ₗ[ℤ] N := (f.comp (of σ).symm.toAddMonoidHom).toIntLinearMap
    have hg : ∀ y, g ((T 1 : LaurentPolynomial ℤ) • y) =
        ((genericUnit ℤ : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) • g y := fun y => by
      obtain ⟨z, rfl⟩ := (of σ).surjective y
      simpa [g, genericUnit_val] using hf z
    have hid : laurentEval (genericUnit ℤ) = AlgHom.id ℤ (LaurentPolynomial ℤ) :=
      (laurentEval_unique _ _ (by simp [genericUnit_val])).symm
    simpa [g, hid] using map_smul_eq_laurentEval_smul (genericUnit ℤ) g hg p x

@[simp]
lemma lift_of (f : G →+ N) (hf : ∀ x, f (σ x) = (T 1 : LaurentPolynomial ℤ) • f x) (x : G) :
    lift f hf (of σ x) = f x :=
  congrArg f ((of σ).symm_apply_apply x)

variable (σ N) in
/-- **The universal property of `TauCeti.LaurentAEval σ`**: its `ℤ[T;T⁻¹]`-linear maps to `N` are
the additive maps out of `G` which turn `σ` into multiplication by `T`. -/
noncomputable def liftEquiv :
    {f : G →+ N // ∀ x, f (σ x) = (T 1 : LaurentPolynomial ℤ) • f x} ≃
      (LaurentAEval σ →ₗ[LaurentPolynomial ℤ] N) where
  toFun f := lift f.1 f.2
  invFun g := ⟨g.toAddMonoidHom.comp (of σ).toAddMonoidHom, fun x => by
    simpa using map_smul g (T 1 : LaurentPolynomial ℤ) (of σ x)⟩
  left_inv f := Subtype.ext <| AddMonoidHom.ext fun x => by simp
  right_inv g := hom_ext <| AddMonoidHom.ext fun x => by simp

@[simp]
lemma liftEquiv_apply (f : {f : G →+ N // ∀ x, f (σ x) = (T 1 : LaurentPolynomial ℤ) • f x}) :
    liftEquiv σ N f = lift f.1 f.2 :=
  (rfl)

@[simp]
lemma liftEquiv_symm_apply_coe (g : LaurentAEval σ →ₗ[LaurentPolynomial ℤ] N) :
    ((liftEquiv σ N).symm g : G →+ N) = g.toAddMonoidHom.comp (of σ).toAddMonoidHom :=
  (rfl)

end LaurentAEval

end TauCeti
