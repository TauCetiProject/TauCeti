/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Handle elements, transport, and tensor products of Frobenius coalgebras

This file develops basic structural properties of algebras carrying a coalgebra structure that
satisfies the Frobenius law `Coalgebra.IsFrobenius`:

* **Perfect pairing**: for a unital Frobenius coalgebra, the Frobenius bilinear form
  `(a, b) ↦ counit (a * b)` is a perfect pairing on both sides (`isPerfPair_compr₂_mul_counit`).
* **Handle element**: the element `TauCeti.Coalgebra.handle R A = m (Δ 1)` is central in any
  associative unital Frobenius coalgebra, and the handle operator `m ∘ Δ` acts as multiplication by
  it; iterating `g` times acts as multiplication by `handle ^ g`.
* **Transport**: the handle element is preserved by non-unital algebra homomorphisms that preserve
  `comul 1`, and the Frobenius law descends along surjective non-unital algebra homomorphisms that
  commute with comultiplication.
* **Tensor products and scalar extension**: if `A` is an `S`-Frobenius algebra and `B` is an
  `R`-Frobenius algebra for a commutative `R`-algebra `S`, then `A ⊗[R] B` is an `S`-Frobenius
  algebra with handle `handle S A ⊗ₜ handle R B`. Taking `S = R` gives tensor products over `R`;
  taking `A = S` gives scalar extension `S ⊗[R] B` with handle `1 ⊗ₜ handle R B`.

## Main definitions and results

* `TauCeti.Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit`: `(a, b) ↦ counit (a * b)` is a
  perfect pairing for every unital Frobenius coalgebra.
* `TauCeti.Coalgebra.handle`: the handle element `m (Δ 1)` of an algebra with a coalgebra
  structure.
* `TauCeti.Coalgebra.IsFrobenius.mul'_comul_eq_handle_mul`,
  `TauCeti.Coalgebra.IsFrobenius.mul'_comul_eq_mul_handle`,
  `TauCeti.Coalgebra.IsFrobenius.commute_handle`: the handle operator `m ∘ Δ` is left and right
  multiplication by `TauCeti.Coalgebra.handle`, which is therefore central.
* `TauCeti.Coalgebra.map_handle`, `TauCeti.Coalgebra.IsFrobenius.of_surjective`: transport of the
  handle element and of the Frobenius law.
* `TauCeti.Coalgebra.IsFrobenius.instTensorProduct`, `TauCeti.Coalgebra.handle_tensorProduct`,
  `TauCeti.Coalgebra.handle_baseChange`: tensor products and scalar extensions of Frobenius
  coalgebras.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Coalgebra

namespace IsFrobenius

section PerfPair

variable {R A : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A] [_root_.Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [_root_.Coalgebra.IsFrobenius R A]

/-- In a unital Frobenius coalgebra, `(a, b) ↦ counit (a * b)` is a perfect pairing. -/
instance isPerfPair_compr₂_mul_counit :
    ((LinearMap.mul R A).compr₂ (CoalgebraStruct.counit (R := R))).IsPerfPair :=
  LinearMap.IsPerfPair.of_bijective _ _root_.Coalgebra.IsFrobenius.compr₂_mul_counit_bijective

/-- The flipped Frobenius form `b ↦ (a ↦ counit (a * b))` of a unital Frobenius coalgebra is
bijective. -/
theorem compr₂_mul_counit_flip_bijective :
    Function.Bijective (((LinearMap.mul R A).compr₂ (CoalgebraStruct.counit (R := R))).flip) :=
  LinearMap.IsPerfPair.bijective_right _

end PerfPair

end IsFrobenius

section Handle

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [CoalgebraStruct R A]

/-- The **handle element** (or Euler element) `m (Δ 1)` of an algebra with a coalgebra structure:
the image of the unit under comultiplication followed by multiplication. -/
noncomputable def handle : A :=
  LinearMap.mul' R A (CoalgebraStruct.comul (R := R) (1 : A))

/-- Unfolding `TauCeti.Coalgebra.handle` as `m (Δ 1)`. -/
theorem handle_def :
    handle R A = LinearMap.mul' R A (CoalgebraStruct.comul (R := R) (1 : A)) := (rfl)

/-- The handle element of a commutative semiring over itself is `1`. -/
@[simp]
theorem handle_self : handle R R = 1 := by
  simp [handle_def]

end Handle

namespace IsFrobenius

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [_root_.Coalgebra R A] [_root_.Coalgebra.IsFrobenius R A]

/-- Comultiplication followed by multiplication acts as left multiplication by the handle
element. -/
theorem mul'_comul_eq_handle_mul (a : A) :
    LinearMap.mul' R A (CoalgebraStruct.comul (R := R) a) = handle R A * a := by
  have h1 : CoalgebraStruct.comul (R := R) a =
      _root_.Coalgebra.IsFrobenius.left R A (1 ⊗ₜ[R] a) := by
    simp [_root_.Coalgebra.IsFrobenius.left_eq_comul_comp_mul']
  rw [h1, _root_.Coalgebra.IsFrobenius.left_def, handle_def]
  simp only [comp_apply, rTensor_tmul]
  generalize CoalgebraStruct.comul (R := R) (1 : A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add t u ht hu => simp_all [add_tmul, add_mul]

/-- Comultiplication followed by multiplication acts as right multiplication by the handle
element. -/
theorem mul'_comul_eq_mul_handle (a : A) :
    LinearMap.mul' R A (CoalgebraStruct.comul (R := R) a) = a * handle R A := by
  have h1 : CoalgebraStruct.comul (R := R) a =
      _root_.Coalgebra.IsFrobenius.right R A (a ⊗ₜ[R] 1) := by
    simp [_root_.Coalgebra.IsFrobenius.right_eq_comul_comp_mul']
  rw [h1, _root_.Coalgebra.IsFrobenius.right_def, handle_def]
  simp only [comp_apply, lTensor_tmul]
  generalize CoalgebraStruct.comul (R := R) (1 : A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add t u ht hu => simp_all [tmul_add, mul_add]

/-- The handle element of an associative unital Frobenius coalgebra is central. -/
theorem commute_handle (a : A) : Commute (handle R A) a := by
  rw [Commute, SemiconjBy, ← mul'_comul_eq_handle_mul, ← mul'_comul_eq_mul_handle]

/-- Operator form of `mul'_comul_eq_handle_mul`: the handle operator `m ∘ Δ` is left multiplication
by `TauCeti.Coalgebra.handle`. -/
theorem mul'_comp_comul_eq_mulLeft_handle :
    LinearMap.mul' R A ∘ₗ CoalgebraStruct.comul (R := R) =
      LinearMap.mulLeft R (handle R A) := by
  ext a
  exact mul'_comul_eq_handle_mul a

/-- Operator form of `mul'_comul_eq_mul_handle`: the handle operator `m ∘ Δ` is right multiplication
by `TauCeti.Coalgebra.handle`. -/
theorem mul'_comp_comul_eq_mulRight_handle :
    LinearMap.mul' R A ∘ₗ CoalgebraStruct.comul (R := R) =
      LinearMap.mulRight R (handle R A) := by
  ext a
  exact mul'_comul_eq_mul_handle a

/-- Iterating the handle operator `m ∘ Δ` `g` times multiplies on the left by `handle ^ g`. -/
theorem mul'_comp_comul_pow_apply (g : ℕ) (a : A) :
    ((LinearMap.mul' R A ∘ₗ CoalgebraStruct.comul (R := R)) ^ g) a = handle R A ^ g * a := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, LinearMap.comp_apply, mul'_comul_eq_handle_mul,
      ← mul_assoc, ← pow_succ']

end IsFrobenius

/-- A non-unital algebra homomorphism that sends `comul 1` to `(f ⊗ f) (comul 1)` maps the handle
element of `A` to the handle element of `B`. -/
theorem map_handle {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [CoalgebraStruct R A] [CoalgebraStruct R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F)
    (hcomul : CoalgebraStruct.comul (R := R) (1 : B) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) (CoalgebraStruct.comul (R := R) (1 : A))) :
    f (handle R A) = handle R B := by
  rw [handle_def, handle_def, hcomul]
  exact congr($((f : A →ₙₐ[R] B).comp_mul') (CoalgebraStruct.comul (R := R) (1 : A)))

namespace IsFrobenius

/-- A surjective image of a Frobenius coalgebra under a map that preserves both multiplication and
comultiplication is again a Frobenius coalgebra. -/
theorem of_surjective {R A B F : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [Module R A] [Module R B] [SMulCommClass R A A] [IsScalarTower R A A]
    [SMulCommClass R B B] [IsScalarTower R B B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [_root_.Coalgebra.IsFrobenius R A] (f : F) (hf : Function.Surjective f)
    (hcomul : ∀ x, CoalgebraStruct.comul (R := R) (f x) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) (CoalgebraStruct.comul (R := R) x)) :
    _root_.Coalgebra.IsFrobenius R B := by
  refine ⟨TensorProduct.ext' fun b₁ b₂ ↦ ?_⟩
  obtain ⟨a₁, rfl⟩ := hf b₁
  obtain ⟨a₂, rfl⟩ := hf b₂
  have hL : _root_.Coalgebra.IsFrobenius.left R B (f a₁ ⊗ₜ[R] f a₂) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)
        (_root_.Coalgebra.IsFrobenius.left R A (a₁ ⊗ₜ[R] a₂)) := by
    simp only [_root_.Coalgebra.IsFrobenius.left_def, comp_apply, rTensor_tmul, hcomul]
    generalize CoalgebraStruct.comul (R := R) a₁ = t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add t u ht hu => simp only [add_tmul, map_add, ht, hu]
  have hR : _root_.Coalgebra.IsFrobenius.right R B (f a₁ ⊗ₜ[R] f a₂) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)
        (_root_.Coalgebra.IsFrobenius.right R A (a₁ ⊗ₜ[R] a₂)) := by
    simp only [_root_.Coalgebra.IsFrobenius.right_def, comp_apply, lTensor_tmul, hcomul]
    generalize CoalgebraStruct.comul (R := R) a₂ = t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add t u ht hu => simp only [tmul_add, map_add, ht, hu]
  rw [hL, hR, _root_.Coalgebra.IsFrobenius.left_eq_right]

/-- The tensor product `A ⊗[R] B` of an `S`-Frobenius algebra `A` and an `R`-Frobenius algebra `B`
is an `S`-Frobenius algebra. Taking `S = R` gives tensor products of Frobenius algebras over `R`;
taking `A = S` gives scalar extension `S ⊗[R] B`. -/
instance instTensorProduct {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [Module S A] [SMulCommClass S A A] [IsScalarTower S A A] [IsScalarTower R S A]
    [CoalgebraStruct S A]
    [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    [CoalgebraStruct R B]
    [_root_.Coalgebra.IsFrobenius S A] [_root_.Coalgebra.IsFrobenius R B] :
    _root_.Coalgebra.IsFrobenius S (A ⊗[R] B) := by
  let F := AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B
  have hL (a₁ a₂ : A) (b₁ b₂ : B) :
      _root_.Coalgebra.IsFrobenius.left S (A ⊗[R] B) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
        F (_root_.Coalgebra.IsFrobenius.left S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
          _root_.Coalgebra.IsFrobenius.left R B (b₁ ⊗ₜ[R] b₂)) := by
    simp only [_root_.Coalgebra.IsFrobenius.left_def, comp_apply, rTensor_tmul,
      TensorProduct.comul_tmul]
    generalize CoalgebraStruct.comul (R := S) a₁ = tA
    generalize CoalgebraStruct.comul (R := R) b₁ = tB
    induction tA using TensorProduct.inductionOn with
    | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
    | tmul x₁ x₂ =>
      induction tB using TensorProduct.inductionOn with
      | add u v hu hv => simp only [tmul_add, add_tmul, map_add, hu, hv]
      | tmul y₁ y₂ => simp [F]
  have hR (a₁ a₂ : A) (b₁ b₂ : B) :
      _root_.Coalgebra.IsFrobenius.right S (A ⊗[R] B) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
        F (_root_.Coalgebra.IsFrobenius.right S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
          _root_.Coalgebra.IsFrobenius.right R B (b₁ ⊗ₜ[R] b₂)) := by
    simp only [_root_.Coalgebra.IsFrobenius.right_def, comp_apply, lTensor_tmul,
      TensorProduct.comul_tmul]
    generalize CoalgebraStruct.comul (R := S) a₂ = tA
    generalize CoalgebraStruct.comul (R := R) b₂ = tB
    induction tA using TensorProduct.inductionOn with
    | add u v hu hv => simp only [add_tmul, tmul_add, map_add, hu, hv]
    | tmul x₁ x₂ =>
      induction tB using TensorProduct.inductionOn with
      | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
      | tmul y₁ y₂ => simp [F]
  refine ⟨TensorProduct.ext' fun z₁ z₂ ↦ ?_⟩
  induction z₁ using TensorProduct.inductionOn with
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
  | tmul a₁ b₁ =>
    induction z₂ using TensorProduct.inductionOn with
    | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
    | tmul a₂ b₂ =>
      rw [hL, hR, _root_.Coalgebra.IsFrobenius.left_eq_right,
        _root_.Coalgebra.IsFrobenius.left_eq_right]

end IsFrobenius

section TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [CoalgebraStruct S A]
  [Semiring B] [Algebra R B] [CoalgebraStruct R B]

/-- The handle element of `A ⊗[R] B` is the pure tensor of the handle elements of `A` and `B`. -/
@[simp]
theorem handle_tensorProduct :
    handle S (A ⊗[R] B) = handle S A ⊗ₜ[R] handle R B := by
  simp only [handle_def, Algebra.TensorProduct.one_def, TensorProduct.comul_tmul]
  generalize CoalgebraStruct.comul (R := S) (1 : A) = tA
  generalize CoalgebraStruct.comul (R := R) (1 : B) = tB
  induction tA using TensorProduct.inductionOn with
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
  | tmul x₁ x₂ =>
    induction tB using TensorProduct.inductionOn with
    | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
    | tmul y₁ y₂ => simp

/-- Extending scalars along `R → S` sends the handle element `h` of `B` to `1 ⊗ₜ h`. -/
theorem handle_baseChange :
    handle S (S ⊗[R] B) = 1 ⊗ₜ[R] handle R B := by
  rw [handle_tensorProduct, handle_self]

end TensorProduct

end TauCeti.Coalgebra
