/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Maps between tensor products of algebras

The base change `Algebra.TensorProduct.map (AlgHom.id R S) f : S ⊗[R] B → S ⊗[R] C` of an
algebra map `f : B →ₐ[R] C` agrees with `LinearMap.lTensor S` applied to the underlying
linear map of `f`, and similarly on the right with `LinearMap.rTensor S`. This lets results
about base change of linear maps, such as flatness preserving injectivity and exactness, be
applied to base change of algebra maps.

For an `S`-algebra `B` over `R` which need not be commutative, the multiplication maps
`S ⊗[R] B → B` and `B ⊗[R] S → B` are `S`-algebra maps, because `S` acts through its central
image in `B`. Mathlib's `Algebra.TensorProduct.lmul''` and `Algebra.TensorProduct.productMap`
require a commutative target.

For commutative `R`-algebras `A` and `B`, the tensor product `A ⊗[R] B` is the pushout of
`A ← R → B` in commutative semirings. Mathlib's `Algebra.TensorProduct.productMap` expresses this
universal property for algebra homomorphisms into an `R`-algebra, and
`Algebra.TensorProduct.ringHom_ext` is its uniqueness half for ring homomorphisms.
`Algebra.TensorProduct.liftRingHom` is the existence half for ring homomorphisms: ring
homomorphisms `x : A →+* T` and `y : B →+* T` into a commutative semiring `T` which agree on `R`
induce `a ⊗ b ↦ x a * y b`, even for noncommutative `A` and `B`, with no `R`-algebra structure
on `T` involved. This is the form needed when `T` already carries an `R`-algebra structure which
`x` and `y` do not respect, for instance when `T` is itself a tensor product over `R` and `x`
twists the first factor by a ring automorphism.

Mathlib's `LinearMap.tensorProduct` and `LinearMap.tensorProductEnd` send `a ⊗ f` to `a` times the
base change of `f`, but their generated computation lemmas unfold to `TensorProduct.liftAux`; this
file records their values on pure tensors as `simp` lemmas of higher priority than the generated
ones, so the public `LinearMap.baseChange` API applies.

## Main declarations

* `AlgHom.lTensor_toLinearMap_apply`: `f.toLinearMap.lTensor S` is
  `Algebra.TensorProduct.map (AlgHom.id R S) f`.
* `AlgHom.rTensor_toLinearMap_apply`: `f.toLinearMap.rTensor S` is
  `Algebra.TensorProduct.map f (AlgHom.id R S)`.
* `LinearMap.tensorProduct_tmul`, `LinearMap.tensorProductEnd_tmul`: the extension of linear maps
  and of endomorphisms sends `a ⊗ f` to `a • f.baseChange A`.
* `Algebra.TensorProduct.mulLeft`, `Algebra.TensorProduct.mulRight`: the
  multiplication maps `s ⊗ b ↦ s • b` and `b ⊗ t ↦ b * t`.
* `Algebra.TensorProduct.liftRingHom x y h`: the ring homomorphism `a ⊗ b ↦ x a * y b`.
* `Algebra.TensorProduct.map_productMap_eq_zero_of_comp_eq`: if `p : T → U` equalizes
  `f, g : S → T`, then `p` kills `productMap f g e` (`s ⊗ t ↦ f s * g t`) for every `e` in the
  kernel of multiplication `S ⊗[R] S → S`.
* `Algebra.TensorProduct.productMap_mem_of_comp_eq`: if `f, g` agree modulo an ideal `J` of `T`,
  then `productMap f g e ∈ J` for every such `e`.
* `Algebra.TensorProduct.mulLeft_map`, `Algebra.TensorProduct.mulLeft_map_includeRight`:
  naturality of tensor multiplication and cancellation of an inserted middle factor `1`.
* `Algebra.TensorProduct.map_assoc_tmul_one`: applying `f : B ⊗[R] C → D` after
  reassociating `y ⊗ 1` is the base change of `b ↦ f (b ⊗ 1)`.
* `Algebra.TensorProduct.assoc_comp_includeLeft_comp_includeLeft`,
  `Algebra.TensorProduct.assoc_comp_includeLeft_comp_includeRight`,
  `Algebra.TensorProduct.assoc_comp_includeRight`: the associator restricted to each of the three
  tensor factors.
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
theorem AlgHom.lTensor_toLinearMap_apply {R B C : Type*} (S : Type*) [CommSemiring R]
    [Semiring S] [Algebra R S] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (f : B →ₐ[R] C) (x : S ⊗[R] B) :
    f.toLinearMap.lTensor S x = Algebra.TensorProduct.map (AlgHom.id R S) f x := by
  induction x using TensorProduct.inductionOn with
  | tmul s b => simp
  | add x y hx hy => simp [hx, hy]

/-- Right base change of the underlying linear map of an algebra map is the right base change of
the algebra map. -/
theorem AlgHom.rTensor_toLinearMap_apply {R B C : Type*} (S : Type*) [CommSemiring R]
    [Semiring S] [Algebra R S] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (f : B →ₐ[R] C) (x : B ⊗[R] S) :
    f.toLinearMap.rTensor S x = Algebra.TensorProduct.map f (AlgHom.id R S) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b s => simp
  | add x y hx hy => simp [hx, hy]

/-- The natural map `A ⊗[R] (M →ₗ[R] N) → (A ⊗[R] M →ₗ[A] A ⊗[R] N)` sends `a ⊗ f` to
`a • f.baseChange A`, so that `LinearMap.baseChange_tmul` computes its values on pure tensors. -/
@[simp high]
theorem LinearMap.tensorProduct_tmul {R A M N : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (a : A)
    (f : M →ₗ[R] N) : LinearMap.tensorProduct R A M N (a ⊗ₜ f) = a • f.baseChange A := by
  simp only [LinearMap.tensorProduct_apply, TensorProduct.liftAux_tmul,
    LinearMap.coe_restrictScalars, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.baseChangeHom_apply]

/-- The natural algebra map `A ⊗[R] Module.End R M → Module.End A (A ⊗[R] M)` sends `a ⊗ f` to
`a • f.baseChange A`. -/
@[simp high]
theorem LinearMap.tensorProductEnd_tmul {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] (a : A) (f : Module.End R M) :
    LinearMap.tensorProductEnd R A M (a ⊗ₜ f) = a • f.baseChange A :=
  LinearMap.tensorProduct_tmul a f

namespace Algebra.TensorProduct

section LiftRingHom

variable {R A B T : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [CommSemiring T]

/-- The ring homomorphism `A ⊗[R] B →+* T`, `a ⊗ b ↦ x a * y b`, induced by ring homomorphisms
`x : A →+* T` and `y : B →+* T` which agree on `R`. The sources `A` and `B` need not be
commutative, and no `R`-algebra structure on `T` is involved. -/
noncomputable def liftRingHom (x : A →+* T) (y : B →+* T)
    (h : x.comp (algebraMap R A) = y.comp (algebraMap R B)) : A ⊗[R] B →+* T :=
  letI : Algebra R T := (x.comp (algebraMap R A)).toAlgebra
  (productMap (R := R) { x with commutes' := fun _ ↦ rfl }
    { y with commutes' := fun r ↦ congr($h r).symm }).toRingHom

variable (x : A →+* T) (y : B →+* T) (h : x.comp (algebraMap R A) = y.comp (algebraMap R B))

@[simp]
theorem liftRingHom_tmul (a : A) (b : B) : liftRingHom x y h (a ⊗ₜ b) = x a * y b := by
  simp [liftRingHom]

@[simp]
theorem liftRingHom_comp_includeLeftRingHom :
    (liftRingHom x y h).comp includeLeftRingHom = x := by
  ext a
  simp

@[simp]
theorem liftRingHom_comp_includeRight :
    (liftRingHom x y h).comp (includeRight : B →ₐ[R] A ⊗[R] B) = y := by
  ext b
  simp

end LiftRingHom

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

section AssocInclude

variable {C : Type*} [Semiring C] [Algebra R C]

/-- Restricting the associator `(A ⊗[R] B) ⊗[R] C ≃ A ⊗[R] (B ⊗[R] C)` to the left factor `A`
gives the inclusion of the left factor. -/
theorem assoc_comp_includeLeft_comp_includeLeft :
    (((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeLeft).comp includeLeft :
      A →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeLeft :=
  AlgHom.ext fun _ ↦ rfl

/-- Restricting the associator `(A ⊗[R] B) ⊗[R] C ≃ A ⊗[R] (B ⊗[R] C)` to the middle factor `B`
gives the inclusion of `B` into the left factor of `B ⊗[R] C`. -/
theorem assoc_comp_includeLeft_comp_includeRight :
    (((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeLeft).comp includeRight :
      B →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeRight.comp includeLeft :=
  AlgHom.ext fun _ ↦ rfl

/-- Restricting the associator `(A ⊗[R] B) ⊗[R] C ≃ A ⊗[R] (B ⊗[R] C)` to the right factor `C`
gives the inclusion of `C` into the right factor of `B ⊗[R] C`. -/
theorem assoc_comp_includeRight :
    ((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeRight :
      C →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeRight.comp includeRight :=
  AlgHom.ext fun _ ↦ rfl

end AssocInclude

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

section Product

/-- If two algebra maps `f, g : S → T` agree after composing with `p : T → U`, then `p` kills
`productMap f g e` (the map `s ⊗ t ↦ f s * g t` applied to `e`) for every element `e` of the
kernel of multiplication `S ⊗[R] S → S`. -/
theorem map_productMap_eq_zero_of_comp_eq {R S T U : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [Semiring U] [Algebra R S] [Algebra R T] [Algebra R U]
    {e : S ⊗[R] S} (he : lmul' R e = 0)
    {f g : S →ₐ[R] T} (p : T →ₐ[R] U) (hfg : p.comp f = p.comp g) :
    p (productMap f g e) = 0 := by
  have hp : p.comp (productMap f g) =
      (p.comp f).comp (lmul' R) := by
    ext s
    · simp
    · simpa using DFunLike.congr_fun hfg.symm s
  simpa only [AlgHom.comp_apply, he, map_zero] using DFunLike.congr_fun hp e

/-- If two algebra maps `f, g : S → T` agree modulo an ideal `J` of `T`, then `productMap f g`
(the map `s ⊗ t ↦ f s * g t`) sends every element of the kernel of multiplication
`S ⊗[R] S → S` into `J`. -/
theorem productMap_mem_of_comp_eq {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommRing T]
    [Algebra R S] [Algebra R T]
    {e : S ⊗[R] S} (he : lmul' R e = 0) (J : Ideal T)
    {f g : S →ₐ[R] T}
    (hfg : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) :
    productMap f g e ∈ J :=
  Ideal.Quotient.eq_zero_iff_mem.mp
    (map_productMap_eq_zero_of_comp_eq he (Ideal.Quotient.mkₐ R J) hfg)

end Product

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
