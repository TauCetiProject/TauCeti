/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Maps between tensor products of algebras

The base change `Algebra.TensorProduct.map (AlgHom.id R S) f : S ⊗[R] B → S ⊗[R] C` of an
algebra map `f : B →ₐ[R] C` agrees with `LinearMap.lTensor S` applied to the underlying linear
map of `f`. This lets results about base change of linear maps, such as flatness preserving
injectivity and exactness, be applied to base change of algebra maps.

For an `S`-algebra `B` over `R` which need not be commutative, the multiplication maps
`S ⊗[R] B → B` and `B ⊗[R] S → B` are `S`-algebra maps, because `S` acts through its central
image in `B`. Mathlib's `Algebra.TensorProduct.lmul''` and `Algebra.TensorProduct.productMap`
require a commutative target.

## Main declarations

* `AlgHom.lTensor_toLinearMap_apply`: `f.toLinearMap.lTensor S` is
  `Algebra.TensorProduct.map (AlgHom.id R S) f`.
* `Algebra.TensorProduct.mulLeft`, `Algebra.TensorProduct.mulRight`: the
  multiplication maps `s ⊗ b ↦ s • b` and `b ⊗ t ↦ b * t`.
* `Algebra.TensorProduct.mulLeft_map`, `Algebra.TensorProduct.mulLeft_map_includeRight`:
  naturality of tensor multiplication and cancellation of an inserted middle factor `1`.
* `Algebra.TensorProduct.map_assoc_tmul_one`: applying `f : B ⊗[R] C → D` after
  reassociating `y ⊗ 1` is the base change of `b ↦ f (b ⊗ 1)`.
* `AlgHom.sectionBaseChange`: the base change `T ⊗[A] B →ₐ[T] T` of an `A`-algebra map
  `s : B →ₐ[A] A`, that is, the pullback to `Spec T` of the section of `Spec B → Spec A` given by
  `s`, with its value `AlgHom.sectionBaseChange_sum_tmul` on sums of pure tensors, its
  naturality `AlgHom.sectionBaseChange_rTensor` in `T`, and its transitivity
  `AlgHom.sectionBaseChange_sectionBaseChange` along `A → A' → T`.
-/

public section

open TensorProduct

/-- Base change of the underlying linear map of an algebra map is the base change of the
algebra map. -/
theorem AlgHom.lTensor_toLinearMap_apply {R B C : Type*} (S : Type*) [CommRing R] [Ring S]
    [Algebra R S] [Ring B] [Algebra R B] [Ring C] [Algebra R C] (f : B →ₐ[R] C)
    (x : S ⊗[R] B) :
    f.toLinearMap.lTensor S x = Algebra.TensorProduct.map (AlgHom.id R S) f x := by
  induction x using TensorProduct.inductionOn with
  | tmul s b => simp
  | add x y hx hy => simp [hx, hy]

namespace Algebra.TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]

/-- Reassociating `y ⊗ 1 ∈ (A ⊗[R] B) ⊗[R] C` and applying `f : B ⊗[R] C → D` to the last two
factors is the base change of `b ↦ f (b ⊗ 1)`. -/
theorem map_assoc_tmul_one {C D : Type*} [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]
    (f : B ⊗[R] C →ₐ[R] D) (y : A ⊗[R] B) :
    map (AlgHom.id R A) f (Algebra.TensorProduct.assoc R R R A B C (y ⊗ₜ 1)) =
      map (AlgHom.id R A) (f.comp includeLeft) y := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

variable [Algebra S B]

/-- The image of `S` in the right factor is central in `A ⊗[R] B`. -/
theorem commute_one_tmul_algebraMap (x : A ⊗[R] B) (t : S) :
    Commute x (1 ⊗ₜ algebraMap S B t) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact (Commute.one_right a).tmul (Algebra.commute_algebraMap_right t b)
  | add x y hx hy => exact hx.add_left hy

variable [Algebra R S] [IsScalarTower R S B]

/-- The multiplication map `S ⊗[R] B →ₐ[S] B`, `s ⊗ b ↦ s • b`, for an `S`-algebra `B` which
need not be commutative. -/
noncomputable def mulLeft : S ⊗[R] B →ₐ[S] B :=
  lift (Algebra.ofId S B) (AlgHom.id R B)
    (fun s b ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _)

@[simp]
theorem mulLeft_tmul (s : S) (b : B) :
    (mulLeft (s ⊗ₜ[R] b) : B) = algebraMap S B s * b := by
  simp [mulLeft]

/-- Tensor multiplication commutes with an algebra map over `S`. -/
@[simp]
theorem mulLeft_map {C : Type*} [Semiring C] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] (f : B →ₐ[S] C) (x : S ⊗[R] B) :
    mulLeft (map (AlgHom.id R S) (f.restrictScalars R) x) = f (mulLeft x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Algebra S B] [IsScalarTower R S B] in
/-- Multiplying the first two factors cancels insertion of `1` in the middle factor. -/
@[simp]
theorem mulLeft_map_includeRight (x : S ⊗[R] B) :
    mulLeft (map (AlgHom.id R S) (includeRight : B →ₐ[R] S ⊗[R] B) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s b => simp [algebraMap_apply, tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The multiplication map `B ⊗[R] S →ₐ[S] B`, `b ⊗ t ↦ b * t`, for an `S`-algebra `B` which
need not be commutative. -/
noncomputable def mulRight : B ⊗[R] S →ₐ[S] B :=
  lift (AlgHom.id S B) (IsScalarTower.toAlgHom R S B)
    (fun b t ↦ by rw [IsScalarTower.coe_toAlgHom']; exact Algebra.commute_algebraMap_right t b)

@[simp]
theorem mulRight_tmul (b : B) (t : S) :
    (mulRight (b ⊗ₜ[R] t) : B) = b * algebraMap S B t := by
  simp [mulRight]

end Algebra.TensorProduct

namespace AlgHom

variable {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]

/-- The base change `T ⊗[A] B →ₐ[T] T`, `t ⊗ b ↦ t * s b`, of an `A`-algebra map
`s : B →ₐ[A] A`. Geometrically, `s` is a section of `Spec B → Spec A`, and this is its pullback
along `Spec T → Spec A`. -/
noncomputable def sectionBaseChange (s : B →ₐ[A] A) (T : Type*) [CommSemiring T] [Algebra A T] :
    T ⊗[A] B →ₐ[T] T :=
  Algebra.TensorProduct.productLeftAlgHom (AlgHom.id T T) ((Algebra.ofId A T).comp s)

@[simp]
theorem sectionBaseChange_tmul (s : B →ₐ[A] A) {T : Type*} [CommSemiring T] [Algebra A T] (t : T)
    (b : B) : s.sectionBaseChange T (t ⊗ₜ b) = t * algebraMap A T (s b) := by
  simp [sectionBaseChange]

/-- The base change of a section `s` takes `∑ j ∈ u, tⱼ ⊗ bⱼ` to `∑ j ∈ u, s(bⱼ) • tⱼ`; for
`tⱼ = Xⱼ` and a basis `b`, the generic element goes to the linear form with coefficients
`s(bⱼ)`. -/
theorem sectionBaseChange_sum_tmul (s : B →ₐ[A] A) {T : Type*} [CommSemiring T] [Algebra A T]
    {κ : Type*} (u : Finset κ) (t : κ → T) (b : κ → B) :
    s.sectionBaseChange T (∑ j ∈ u, t j ⊗ₜ b j) = ∑ j ∈ u, s (b j) • t j := by
  simp [Algebra.smul_def, mul_comm]

/-- The base change of a section is natural in the base: it commutes with
`Algebra.TensorProduct.rTensor B φ` for an `A`-algebra map `φ : T →ₐ[A] T'`. -/
@[simp]
theorem sectionBaseChange_rTensor (s : B →ₐ[A] A) {T T' : Type*} [CommSemiring T] [Algebra A T]
    [CommSemiring T'] [Algebra A T'] (φ : T →ₐ[A] T') (x : T ⊗[A] B) :
    s.sectionBaseChange T' (Algebra.TensorProduct.rTensor B φ x) = φ (s.sectionBaseChange T x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Base change of a section is transitive: along `A → A' → T`, base changing `s` to `A'` and
then to `T` is base changing `s` to `T`, through the identification
`T ⊗[A'] (A' ⊗[A] B) ≃ T ⊗[A] B`. -/
@[simp]
theorem sectionBaseChange_sectionBaseChange {B : Type*} [CommSemiring B] [Algebra A B]
    (s : B →ₐ[A] A) {A' T : Type*} [CommSemiring A'] [Algebra A A'] [CommSemiring T]
    [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] (x : T ⊗[A'] (A' ⊗[A] B)) :
    (s.sectionBaseChange A').sectionBaseChange T x =
      s.sectionBaseChange T (Algebra.TensorProduct.cancelBaseChange A A' T T B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t y =>
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [sectionBaseChange_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.smul_def, IsScalarTower.algebraMap_apply A A' T, map_mul]
      ac_rfl
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgHom
