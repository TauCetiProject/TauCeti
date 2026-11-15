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
* **Handle element**: the element `Coalgebra.handle R A = m (Δ 1)` is central in any associative
  unital Frobenius coalgebra, and the handle operator `m ∘ Δ` acts as multiplication by it;
  iterating `g` times acts as multiplication by `handle ^ g`.
* **Transport**: the handle element is preserved by maps that are simultaneously algebra and
  coalgebra homomorphisms, and the Frobenius law descends along surjective non-unital algebra and
  coalgebra homomorphisms.
* **Tensor products and scalar extension**: if `A` is an `S`-Frobenius algebra and `B` is an
  `R`-Frobenius algebra for a commutative `R`-algebra `S`, then `A ⊗[R] B` is an `S`-Frobenius
  algebra with handle `handle S A ⊗ₜ handle R B`. Taking `S = R` gives tensor products over `R`;
  taking `A = S` gives scalar extension `S ⊗[R] B` with handle `1 ⊗ₜ handle R B`.

## Main definitions and results

* `Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit`: `(a, b) ↦ counit (a * b)` is a perfect
  pairing for every unital Frobenius coalgebra.
* `Coalgebra.handle`: the handle element `m (Δ 1)` of an algebra with a coalgebra structure.
* `Coalgebra.IsFrobenius.mul'_comul_eq_handle_mul`,
  `Coalgebra.IsFrobenius.mul'_comul_eq_mul_handle`,
  `Coalgebra.IsFrobenius.commute_handle`: the handle operator `m ∘ Δ` is left and right
  multiplication by `Coalgebra.handle`, which is therefore central.
* `TauCeti.Coalgebra.map_handle`, `TauCeti.Coalgebra.IsFrobenius.of_surjective`: transport of the
  handle element and of the Frobenius law.
* `TensorProduct.instIsFrobenius`, `Coalgebra.handle_tensorProduct`,
  `Coalgebra.handle_baseChange`: tensor products and scalar extensions of Frobenius coalgebras.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

open TensorProduct LinearMap

namespace Coalgebra.IsFrobenius

section PerfPair

variable {R A : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [IsFrobenius R A]

/-- The flipped Frobenius form `b ↦ (a ↦ counit (a * b))` of a unital Frobenius coalgebra is
bijective. -/
theorem compr₂_mul_counit_flip_bijective :
    Function.Bijective (((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R))).flip) := by
  obtain ⟨S, hS⟩ := exists_finset (R := R) (Coalgebra.comul (R := R) (1 : A))
  have hleft (a : A) : ∑ x ∈ S, Coalgebra.counit (R := R) (a * x.1) • x.2 = a := by
    simpa [hS, tmul_sum, right_def] using
      congr(TensorProduct.lid R A
        (rTensor A (Coalgebra.counit (R := R))
          ($(right_eq_comul_comp_mul' (R := R) (A := A)) (a ⊗ₜ[R] 1))))
  have hright (a : A) : ∑ x ∈ S, Coalgebra.counit (R := R) (x.2 * a) • x.1 = a := by
    simpa [hS, sum_tmul, left_def] using
      congr(_root_.TensorProduct.rid R A
        (lTensor A (Coalgebra.counit (R := R))
          ($(left_eq_comul_comp_mul' (R := R) (A := A)) (1 ⊗ₜ[R] a))))
  refine ⟨fun b₁ b₂ h ↦ ?_, fun f ↦ ⟨∑ x ∈ S, f x.2 • x.1, LinearMap.ext fun a ↦ ?_⟩⟩
  · rw [← hright b₁, ← hright b₂]
    simp only [LinearMap.ext_iff, flip_apply, compr₂_apply, mul_apply_apply] at h
    simp [h]
  · rw [map_sum, LinearMap.sum_apply]
    calc
      ∑ x ∈ S, ((((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R))).flip) (f x.2 • x.1)) a =
          ∑ x ∈ S, Coalgebra.counit (R := R) (a * x.1) • f x.2 := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp [mul_comm]
      _ = f a := by simp only [← map_smul, ← map_sum, hleft]

/-- In a unital Frobenius coalgebra, `(a, b) ↦ counit (a * b)` is a perfect pairing. -/
instance isPerfPair_compr₂_mul_counit :
    ((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R))).IsPerfPair :=
  ⟨compr₂_mul_counit_bijective, compr₂_mul_counit_flip_bijective⟩

end PerfPair

end Coalgebra.IsFrobenius

namespace Coalgebra

section Handle

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [CoalgebraStruct R A]

/-- The **handle element** (or Euler element) `m (Δ 1)` of an algebra with a coalgebra structure:
the image of the unit under comultiplication followed by multiplication. -/
noncomputable def handle : A :=
  LinearMap.mul' R A (Coalgebra.comul (R := R) (1 : A))

/-- Unfolding `Coalgebra.handle` as `m (Δ 1)`. -/
theorem handle_def :
    Coalgebra.handle R A = LinearMap.mul' R A (Coalgebra.comul (R := R) (1 : A)) := (rfl)

/-- The handle element of a commutative semiring over itself is `1`. -/
@[simp]
theorem handle_self : Coalgebra.handle R R = 1 := by
  simp [handle_def]

end Handle

namespace IsFrobenius

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A] [IsFrobenius R A]

/-- Comultiplication followed by multiplication acts as left multiplication by the handle
element. -/
theorem mul'_comul_eq_handle_mul (a : A) :
    LinearMap.mul' R A (Coalgebra.comul (R := R) a) = Coalgebra.handle R A * a := by
  have h1 : Coalgebra.comul (R := R) a = left R A (1 ⊗ₜ[R] a) := by
    simp [left_eq_comul_comp_mul']
  rw [h1, left_def, handle_def]
  simp only [comp_apply, rTensor_tmul]
  generalize Coalgebra.comul (R := R) (1 : A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add t u ht hu => simp_all [add_tmul, add_mul]

/-- Comultiplication followed by multiplication acts as right multiplication by the handle
element. -/
theorem mul'_comul_eq_mul_handle (a : A) :
    LinearMap.mul' R A (Coalgebra.comul (R := R) a) = a * Coalgebra.handle R A := by
  have h1 : Coalgebra.comul (R := R) a = right R A (a ⊗ₜ[R] 1) := by
    simp [right_eq_comul_comp_mul']
  rw [h1, right_def, handle_def]
  simp only [comp_apply, lTensor_tmul]
  generalize Coalgebra.comul (R := R) (1 : A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add t u ht hu => simp_all [tmul_add, mul_add]

/-- The handle element of an associative unital Frobenius coalgebra is central. -/
theorem commute_handle (a : A) : Commute (Coalgebra.handle R A) a := by
  rw [Commute, SemiconjBy, ← mul'_comul_eq_handle_mul, ← mul'_comul_eq_mul_handle]

/-- Operator form of `mul'_comul_eq_handle_mul`: the handle operator `m ∘ Δ` is left multiplication
by `Coalgebra.handle`. -/
theorem mul'_comp_comul_eq_mulLeft_handle :
    LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) =
      LinearMap.mulLeft R (Coalgebra.handle R A) := by
  ext a
  exact mul'_comul_eq_handle_mul a

/-- Operator form of `mul'_comul_eq_mul_handle`: the handle operator `m ∘ Δ` is right multiplication
by `Coalgebra.handle`. -/
theorem mul'_comp_comul_eq_mulRight_handle :
    LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) =
      LinearMap.mulRight R (Coalgebra.handle R A) := by
  ext a
  exact mul'_comul_eq_mul_handle a

/-- Iterating the handle operator `m ∘ Δ` `g` times multiplies on the left by `handle ^ g`. -/
theorem mul'_comp_comul_pow_apply (g : ℕ) (a : A) :
    ((LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R)) ^ g) a = Coalgebra.handle R A ^ g * a := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, LinearMap.comp_apply, mul'_comul_eq_handle_mul,
      ← mul_assoc, ← pow_succ']

end IsFrobenius

end Coalgebra

namespace TauCeti.Coalgebra

/-- A map that is simultaneously an algebra homomorphism and a coalgebra homomorphism preserves the
handle element. -/
theorem map_handle {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [_root_.Coalgebra R A] [_root_.Coalgebra R B]
    [FunLike F A B] [AlgHomClass F R A B] [CoalgHomClass F R A B] (f : F) :
    f (_root_.Coalgebra.handle R A) = _root_.Coalgebra.handle R B := by
  have hcomul : CoalgebraStruct.comul (R := R) (1 : B) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)
        (CoalgebraStruct.comul (R := R) (1 : A)) := by
    rw [← map_one f, ← CoalgHomClass.map_comp_comul_apply]
  rw [_root_.Coalgebra.handle_def, _root_.Coalgebra.handle_def, hcomul]
  generalize CoalgebraStruct.comul (R := R) (1 : A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add t u ht hu => simp_all

namespace IsFrobenius

/-- A surjective image of a Frobenius coalgebra under a map that preserves both multiplication and
comultiplication is again a Frobenius coalgebra. -/
theorem of_surjective {R A B F : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [Module R A] [Module R B] [SMulCommClass R A A] [IsScalarTower R A A]
    [SMulCommClass R B B] [IsScalarTower R B B]
    [_root_.Coalgebra R A] [_root_.Coalgebra R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] [CoalgHomClass F R A B]
    [_root_.Coalgebra.IsFrobenius R A] (f : F) (hf : Function.Surjective f) :
    _root_.Coalgebra.IsFrobenius R B := by
  have hcomul (x : A) : CoalgebraStruct.comul (R := R) (f x) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) (CoalgebraStruct.comul (R := R) x) :=
    (CoalgHomClass.map_comp_comul_apply f x).symm
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

end IsFrobenius

end TauCeti.Coalgebra

section TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Coalgebra S A]
  [Semiring B] [Algebra R B] [Coalgebra R B]

/-- The tensor product `A ⊗[R] B` of an `S`-Frobenius algebra `A` and an `R`-Frobenius algebra `B`
is an `S`-Frobenius algebra. Taking `S = R` gives tensor products of Frobenius algebras over `R`;
taking `A = S` gives scalar extension `S ⊗[R] B`. -/
instance TensorProduct.instIsFrobenius [Coalgebra.IsFrobenius S A] [Coalgebra.IsFrobenius R B] :
    Coalgebra.IsFrobenius S (A ⊗[R] B) := by
  let F := AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B
  have hL (a₁ a₂ : A) (b₁ b₂ : B) :
      Coalgebra.IsFrobenius.left S (A ⊗[R] B) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
        F (Coalgebra.IsFrobenius.left S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
          Coalgebra.IsFrobenius.left R B (b₁ ⊗ₜ[R] b₂)) := by
    simp only [Coalgebra.IsFrobenius.left_def, comp_apply, rTensor_tmul, TensorProduct.comul_tmul]
    generalize Coalgebra.comul (R := S) a₁ = tA
    generalize Coalgebra.comul (R := R) b₁ = tB
    induction tA using TensorProduct.inductionOn with
    | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
    | tmul x₁ x₂ =>
      induction tB using TensorProduct.inductionOn with
      | add u v hu hv => simp only [tmul_add, add_tmul, map_add, hu, hv]
      | tmul y₁ y₂ => simp [F]
  have hR (a₁ a₂ : A) (b₁ b₂ : B) :
      Coalgebra.IsFrobenius.right S (A ⊗[R] B) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
        F (Coalgebra.IsFrobenius.right S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
          Coalgebra.IsFrobenius.right R B (b₁ ⊗ₜ[R] b₂)) := by
    simp only [Coalgebra.IsFrobenius.right_def, comp_apply, lTensor_tmul, TensorProduct.comul_tmul]
    generalize Coalgebra.comul (R := S) a₂ = tA
    generalize Coalgebra.comul (R := R) b₂ = tB
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
      rw [hL, hR, Coalgebra.IsFrobenius.left_eq_right, Coalgebra.IsFrobenius.left_eq_right]

/-- The handle element of `A ⊗[R] B` is the pure tensor of the handle elements of `A` and `B`. -/
@[simp]
theorem Coalgebra.handle_tensorProduct :
    Coalgebra.handle S (A ⊗[R] B) = Coalgebra.handle S A ⊗ₜ[R] Coalgebra.handle R B := by
  simp only [Coalgebra.handle_def, Algebra.TensorProduct.one_def, TensorProduct.comul_tmul]
  generalize Coalgebra.comul (R := S) (1 : A) = tA
  generalize Coalgebra.comul (R := R) (1 : B) = tB
  induction tA using TensorProduct.inductionOn with
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
  | tmul x₁ x₂ =>
    induction tB using TensorProduct.inductionOn with
    | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
    | tmul y₁ y₂ => simp

/-- Extending scalars along `R → S` sends the handle element `h` of `B` to `1 ⊗ₜ h`. -/
theorem Coalgebra.handle_baseChange :
    Coalgebra.handle S (S ⊗[R] B) = 1 ⊗ₜ[R] Coalgebra.handle R B := by
  rw [Coalgebra.handle_tensorProduct, Coalgebra.handle_self]

end TensorProduct
