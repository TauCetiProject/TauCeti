/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The smash product of a left module algebra

Given an `R`-bialgebra `H` and a left `H`-module algebra `A` (`TauCeti.LeftModuleAlgebra R H A`),
the smash product `A # H` (`TauCeti.LeftModuleAlgebra.SmashProduct`) is the `R`-module `A ⊗[R] H`
endowed with the multiplication determined on pure tensors by

`(a # h) * (b # k) = ∑ a (h₁ · b) # (h₂ k)`

and with unit `1 # 1`. Associativity and the unit laws are proved without choosing a Sweedler
representation of the coproduct by realizing `A # H` faithfully inside `Module.End R (A ⊗[R] H)`:
`A` acts by left multiplication on the first tensor factor, `H` acts diagonally via its coproduct,
and the module-algebra axioms express the covariance relation between these two actions.

## Main definitions

* `TauCeti.LeftModuleAlgebra.SmashProduct`: the carrier of the smash product `A # H`, equipped
  with `Semiring`, `Ring` (when `A` is a ring), and `Algebra R` instances.
* `TauCeti.LeftModuleAlgebra.tensorEquiv`: the canonical `R`-linear equivalence
  `μ.SmashProduct ≃ₗ[R] A ⊗[R] H`.
* `TauCeti.LeftModuleAlgebra.smash`: the pure element `a # h` in `μ.SmashProduct`.
* `TauCeti.LeftModuleAlgebra.smashMulPure`: the representation-free product formula on pure
  tensors, valued in `A ⊗[R] H`.
* `TauCeti.LeftModuleAlgebra.includeA` and `TauCeti.LeftModuleAlgebra.includeH`: the canonical
  `R`-algebra homomorphisms `a ↦ a # 1` and `h ↦ 1 # h`.
* `TauCeti.LeftModuleAlgebra.SmashCompatible`: the covariance relation
  `fH h * fA a = ∑ fA (h₁ · a) * fH h₂` for pairs of `R`-algebra maps out of `A` and `H`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.lift` and
  `TauCeti.LeftModuleAlgebra.SmashProduct.liftEquiv`: the universal property of `A # H` for
  covariant pairs of algebra homomorphisms.
* `TauCeti.LeftModuleAlgebra.SmashProduct.map`, `mapHom`, `mapRestrict`, and `congr`:
  functoriality of `A # H` in equivariant algebra homomorphisms and bialgebra homomorphisms.
* `TauCeti.LeftModuleAlgebra.SmashProduct.trivialAlgEquiv` and `baseAlgEquiv`: the `R`-algebra
  isomorphisms `A # H ≃ₐ[R] A ⊗[R] H` for the trivial action and `R # H ≃ₐ[R] H` for `A = R`.

## Main results

* `TauCeti.LeftModuleAlgebra.SmashProduct.algHom_ext`: `R`-algebra homomorphisms out of `A # H`
  are determined by their restrictions along `includeA` and `includeH`.
* `TauCeti.LeftModuleAlgebra.includeA_injective`: `a ↦ a # 1` is unconditionally injective.
* `TauCeti.LeftModuleAlgebra.ker_includeH_eq_top`,
  `TauCeti.LeftModuleAlgebra.includeH_injective_of_apply_one_eq_one`, and
  `TauCeti.LeftModuleAlgebra.includeH_injective`: `h ↦ 1 # h` has kernel `⊤` when `A` is
  subsingleton, is injective whenever `1 : A` admits an `R`-linear retraction to `1 : R`, and in
  particular is injective over any field when `A` is nontrivial.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace LeftModuleAlgebra

universe u v w x

section Semiring

variable {R : Type u} {H : Type v} {A : Type w}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-- The smash product `A # H` of a left `H`-module algebra `A` with the bialgebra `H`.
Its underlying `R`-module is `A ⊗[R] H`, wrapped in a structure so that its twisted
multiplication does not conflict with the componentwise algebra structure on `A ⊗[R] H`. -/
structure SmashProduct (_μ : LeftModuleAlgebra R H A) : Type (max v w) where
  /-- Construct an element of `A # H` from its underlying tensor in `A ⊗[R] H`. -/
  ofTensor ::
  /-- The underlying tensor in `A ⊗[R] H` of an element of `A # H`. -/
  toTensor : A ⊗[R] H

section Carrier

variable (μ : LeftModuleAlgebra R H A)

/-- `SmashProduct.toTensor` is injective. -/
theorem SmashProduct.toTensor_injective :
    Function.Injective (SmashProduct.toTensor (R := R) (H := H) (A := A) (_μ := μ)) :=
  fun ⟨_⟩ ⟨_⟩ h => congrArg SmashProduct.ofTensor h

instance SmashProduct.instZero : Zero μ.SmashProduct := ⟨⟨0⟩⟩

instance SmashProduct.instAdd : Add μ.SmashProduct := ⟨fun x y => ⟨x.toTensor + y.toTensor⟩⟩

instance SmashProduct.instSMulNat : SMul ℕ μ.SmashProduct := ⟨fun n x => ⟨n • x.toTensor⟩⟩

instance SmashProduct.instSMul : SMul R μ.SmashProduct := ⟨fun r x => ⟨r • x.toTensor⟩⟩

instance SmashProduct.instAddCommMonoid : AddCommMonoid μ.SmashProduct :=
  (SmashProduct.toTensor_injective μ).addCommMonoid SmashProduct.toTensor rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

instance SmashProduct.instModule : Module R μ.SmashProduct :=
  (SmashProduct.toTensor_injective μ).module R
    { toFun := SmashProduct.toTensor, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ => rfl)

/-- The canonical `R`-linear equivalence between `A # H` and `A ⊗[R] H`. -/
@[expose]
def tensorEquiv : μ.SmashProduct ≃ₗ[R] A ⊗[R] H where
  toFun := SmashProduct.toTensor
  invFun := SmashProduct.ofTensor
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance SmashProduct.instModuleFinite [Module.Finite R A] [Module.Finite R H] :
    Module.Finite R μ.SmashProduct :=
  Module.Finite.of_surjective μ.tensorEquiv.symm.toLinearMap μ.tensorEquiv.symm.surjective

instance SmashProduct.instSubsingleton [Subsingleton A] : Subsingleton μ.SmashProduct :=
  μ.tensorEquiv.injective.subsingleton

/-- The pure element `a # h` of the smash product `A # H`. -/
@[expose]
def smash (a : A) (h : H) : μ.SmashProduct := ⟨a ⊗ₜ[R] h⟩

/-- The bilinear map sending `(a, h)` to the pure smash element `a # h`. -/
def smashBilinear : A →ₗ[R] H →ₗ[R] μ.SmashProduct :=
  LinearMap.compr₂ (TensorProduct.mk R A H) μ.tensorEquiv.symm.toLinearMap

variable {μ}

@[simp] theorem smashBilinear_apply (a : A) (h : H) : μ.smashBilinear a h = μ.smash a h := (rfl)

@[simp] theorem tensorEquiv_smash (a : A) (h : H) : μ.tensorEquiv (μ.smash a h) = a ⊗ₜ[R] h := (rfl)

@[simp]
theorem tensorEquiv_symm_tmul (a : A) (h : H) : μ.tensorEquiv.symm (a ⊗ₜ[R] h) = μ.smash a h :=
  (rfl)

@[simp] theorem smash_zero (a : A) : μ.smash a 0 = 0 := map_zero (μ.smashBilinear a)

@[simp] theorem zero_smash (h : H) : μ.smash 0 h = 0 := map_zero (μ.smashBilinear.flip h)

theorem smash_add (a : A) (h k : H) : μ.smash a (h + k) = μ.smash a h + μ.smash a k :=
  map_add (μ.smashBilinear a) h k

theorem add_smash (a b : A) (h : H) : μ.smash (a + b) h = μ.smash a h + μ.smash b h :=
  map_add (μ.smashBilinear.flip h) a b

@[simp] theorem smul_smash (r : R) (a : A) (h : H) : μ.smash (r • a) h = r • μ.smash a h :=
  map_smul (μ.smashBilinear.flip h) r a

@[simp] theorem smash_smul (a : A) (r : R) (h : H) : μ.smash a (r • h) = r • μ.smash a h :=
  map_smul (μ.smashBilinear a) r h

theorem sum_smash {ι : Type*} (s : Finset ι) (f : ι → A) (h : H) :
    μ.smash (∑ i ∈ s, f i) h = ∑ i ∈ s, μ.smash (f i) h :=
  map_sum (μ.smashBilinear.flip h) f s

theorem smash_sum {ι : Type*} (a : A) (s : Finset ι) (g : ι → H) :
    μ.smash a (∑ i ∈ s, g i) = ∑ i ∈ s, μ.smash a (g i) :=
  map_sum (μ.smashBilinear a) g s

/-- Induction principle for elements of `A # H`. -/
@[elab_as_elim]
theorem SmashProduct.inductionOn {motive : μ.SmashProduct → Prop} (z : μ.SmashProduct)
    (smash : ∀ a h, motive (μ.smash a h))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.inductionOn (motive := fun t => motive ⟨t⟩) z.toTensor smash
    fun x y hx hy => add ⟨x⟩ ⟨y⟩ hx hy

/-- Two `R`-linear maps out of `A # H` agree when they agree on pure elements `a # h`. -/
@[ext]
theorem SmashProduct.lhom_ext {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : μ.SmashProduct →ₗ[R] M} (h : ∀ a x, f (μ.smash a x) = g (μ.smash a x)) : f = g := by
  ext z
  induction z using SmashProduct.inductionOn with
  | smash a x => exact h a x
  | add x y hx hy => simp [hx, hy]

end Carrier

/-! ### Smash multiplication and algebra structure -/

/-- The smash-product formula `(a # h) * (b # k) = ∑ a (h₁ · b) ⊗ (h₂ k)` on pure tensors,
valued in `A ⊗[R] H` and defined without choosing a coproduct representation. -/
noncomputable def smashMulPure (μ : LeftModuleAlgebra R H A) (a b : A) (h k : H) : A ⊗[R] H :=
  TensorProduct.map (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b)
    (LinearMap.mulRight R k) (Coalgebra.comul (R := R) h)

/-- `smashMulPure` expressed in any finite representation of `comul h`. -/
theorem smashMulPure_eq_sum (μ : LeftModuleAlgebra R H A) {h : H} {ι : Type*}
    (r : Coalgebra.Repr R h ι) (a b : A) (k : H) :
    μ.smashMulPure a b h k =
      ∑ i ∈ r.index, (a * μ.action (r.left i) b) ⊗ₜ[R] (r.right i * k) := by
  rw [smashMulPure, ← r.eq, map_sum]
  rfl

/-- Compatibility of algebra maps `fA : A →ₐ[R] C` and `fH : H →ₐ[R] C` for descending to
the smash product `A # H`: for every `h : H` and `a : A`,
`fH h * fA a = ∑ fA (h₁ · a) * fH h₂`. -/
def SmashCompatible (μ : LeftModuleAlgebra R H A) {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) : Prop :=
  ∀ h a, fH h * fA a =
    LinearMap.mul' R C
      (TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip a) fH.toLinearMap
        (Coalgebra.comul (R := R) h))

/-- The covariance relation in any finite representation of `comul h`. -/
theorem SmashCompatible.mul_eq_sum {μ : LeftModuleAlgebra R H A} {C : Type*}
    [Semiring C] [Algebra R C] {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hf : μ.SmashCompatible fA fH) {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) :
    fH h * fA a = ∑ i ∈ r.index, fA (μ.action (r.left i) a) * fH (r.right i) := by
  rw [hf h a, ← r.eq, map_sum, map_sum]
  simp

/-- Characterization of `SmashCompatible` using a family of finite coproduct representations. -/
theorem smashCompatible_iff_sum (μ : LeftModuleAlgebra R H A) {C : Type*}
    [Semiring C] [Algebra R C] (fA : A →ₐ[R] C) (fH : H →ₐ[R] C)
    {ι : H → Type*} (r : ∀ h, Coalgebra.Repr R h (ι h)) :
    μ.SmashCompatible fA fH ↔ ∀ h a,
      fH h * fA a = ∑ i ∈ (r h).index, fA (μ.action ((r h).left i) a) * fH ((r h).right i) := by
  refine ⟨fun hf h a => hf.mul_eq_sum (r h) a, fun hf h a => ?_⟩
  rw [hf h a, ← (r h).eq, map_sum, map_sum]
  simp

namespace SmashProduct

section AlgebraConstruction

/-- Left multiplication of `A` on the first factor of `A ⊗[R] H`. -/
private noncomputable def leftMulA (R : Type u) (H : Type v) (A : Type w)
    [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A] :
    A →ₐ[R] Module.End R (A ⊗[R] H) :=
  (Module.endTensorEndAlgHom (R := R) (S := R) (A := R) (M := A) (N := H)).comp
    (Algebra.TensorProduct.includeLeft.comp (Algebra.lsmul R R A))

variable (μ : LeftModuleAlgebra R H A)

/-- Diagonal left action of `H` on `A ⊗[R] H` via `μ.action` and left multiplication in `H`. -/
private noncomputable def leftMulH : H →ₐ[R] Module.End R (A ⊗[R] H) :=
  ((Module.endTensorEndAlgHom (R := R) (S := R) (A := R) (M := A) (N := H)).comp
    (Algebra.TensorProduct.map μ.action (Algebra.lsmul R R H))).comp
    (Bialgebra.comulAlgHom R H)

private theorem leftMulA_tmul (a b : A) (k : H) :
    leftMulA R H A a (b ⊗ₜ[R] k) = (a * b) ⊗ₜ[R] k := by
  simp [leftMulA, Module.endTensorEndAlgHom_apply]

private theorem leftMulH_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (b : A) (k : H) :
    leftMulH μ h (b ⊗ₜ[R] k) = ∑ i ∈ r.index, μ.action (r.left i) b ⊗ₜ[R] (r.right i * k) := by
  simp [leftMulH, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← r.eq, map_sum,
    LinearMap.sum_apply, Module.endTensorEndAlgHom_apply]

/-- Covariance of `leftMulA` and `leftMulH` in `Module.End R (A ⊗[R] H)`, deduced from
`μ.action_mul` and coassociativity of `H`. -/
private theorem smashCompatible_leftMul : μ.SmashCompatible (leftMulA R H A) (leftMulH μ) := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  refine TensorProduct.ext' fun b k => ?_
  let r := ℛ R h
  let r₁ := fun i => ℛ R (r.left i)
  let r₂ := fun i => ℛ R (r.right i)
  let Φ : H ⊗[R] (H ⊗[R] H) →ₗ[R] A ⊗[R] H :=
    (LinearMap.mul' R A).rTensor H ∘ₗ (TensorProduct.assoc R A A H).symm.toLinearMap ∘ₗ
      TensorProduct.map (μ.action.toLinearMap.flip a)
        (TensorProduct.map (μ.action.toLinearMap.flip b) (LinearMap.mulRight R k))
  have hco := congrArg Φ (Coalgebra.sum_tmul_tmul_eq r r₁ r₂)
  simp only [Φ, map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.flip_apply,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.mulRight_apply] at hco
  calc (leftMulH μ h * leftMulA R H A a) (b ⊗ₜ[R] k)
      = ∑ i ∈ r.index, μ.action (r.left i) (a * b) ⊗ₜ[R] (r.right i * k) := by
          rw [mul_apply_eq_comp, leftMulA_tmul, leftMulH_tmul μ r]
    _ = ∑ i ∈ r.index, ∑ j ∈ (r₁ i).index,
          (μ.action ((r₁ i).left j) a * μ.action ((r₁ i).right j) b) ⊗ₜ[R] (r.right i * k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [μ.action_mul_eq_sum (r₁ i), TensorProduct.sum_tmul]
    _ = ∑ i ∈ r.index, ∑ j ∈ (r₂ i).index,
          (μ.action (r.left i) a * μ.action ((r₂ i).left j) b) ⊗ₜ[R] ((r₂ i).right j * k) := hco
    _ = (∑ i ∈ r.index, leftMulA R H A (μ.action (r.left i) a) * leftMulH μ (r.right i))
          (b ⊗ₜ[R] k) := by
          rw [LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_apply_eq_comp, leftMulH_tmul μ (r₂ i), map_sum]
          exact Finset.sum_congr rfl fun j _ => (leftMulA_tmul _ _ _).symm

/-- The `R`-linear map `A ⊗[R] H →ₗ[R] C` sending `a ⊗ h` to `fA a * fH h`. -/
private noncomputable def bilinLift {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) : A ⊗[R] H →ₗ[R] C :=
  LinearMap.mul' R C ∘ₗ TensorProduct.map fA.toLinearMap fH.toLinearMap

private theorem bilinLift_tmul {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (a : A) (h : H) :
    bilinLift fA fH (a ⊗ₜ[R] h) = fA a * fH h :=
  rfl

/-- Left regular representation `a ⊗ h ↦ leftMulA a * leftMulH h` of `A # H` on `A ⊗[R] H`. -/
private noncomputable def toEnd : A ⊗[R] H →ₗ[R] Module.End R (A ⊗[R] H) :=
  bilinLift (leftMulA R H A) (leftMulH μ)

private theorem toEnd_tmul_tmul (a b : A) (h k : H) :
    toEnd μ (a ⊗ₜ[R] h) (b ⊗ₜ[R] k) = μ.smashMulPure a b h k := by
  rw [toEnd, bilinLift_tmul, mul_apply_eq_comp, leftMulH_tmul μ (ℛ R h), map_sum,
    μ.smashMulPure_eq_sum (ℛ R h)]
  exact Finset.sum_congr rfl fun i _ => leftMulA_tmul _ _ _

private theorem toEnd_apply_one (x : A ⊗[R] H) : toEnd μ x (1 ⊗ₜ[R] 1) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a h =>
    rw [toEnd_tmul_tmul, μ.smashMulPure_eq_sum (ℛ R h)]
    simp only [μ.action_one, mul_one, Algebra.mul_smul_comm, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sum, sum_counit_smul]
  | add x y hx hy => simp [hx, hy]

/-- Any covariant pair `(fA, fH)` turns `toEnd μ x y` into the product of `bilinLift` values. -/
private theorem bilinLift_toEnd_apply {μ : LeftModuleAlgebra R H A} {C : Type*}
    [Semiring C] [Algebra R C] {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hf : μ.SmashCompatible fA fH) (x y : A ⊗[R] H) :
    bilinLift fA fH (toEnd μ x y) = bilinLift fA fH x * bilinLift fA fH y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, add_mul]
  | tmul a h =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂, mul_add]
    | tmul b k =>
      rw [toEnd_tmul_tmul, μ.smashMulPure_eq_sum (ℛ R h), map_sum, bilinLift_tmul, bilinLift_tmul,
        show (fA a * fH h) * (fA b * fH k) = fA a * (fH h * fA b) * fH k by simp [mul_assoc],
        hf.mul_eq_sum (ℛ R h) b, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [bilinLift_tmul, map_mul, mul_assoc]

private theorem toEnd_mul (x y : A ⊗[R] H) :
    toEnd μ (toEnd μ x y) = toEnd μ x * toEnd μ y :=
  bilinLift_toEnd_apply (smashCompatible_leftMul μ) x y

/-- The bilinear smash multiplication on `A # H`. -/
noncomputable def mulLinear :
    μ.SmashProduct →ₗ[R] μ.SmashProduct →ₗ[R] μ.SmashProduct :=
  LinearMap.compl₂
    (LinearMap.compr₂ (toEnd μ ∘ₗ μ.tensorEquiv.toLinearMap) μ.tensorEquiv.symm.toLinearMap)
    μ.tensorEquiv.toLinearMap

private theorem mulLinear_apply (x y : μ.SmashProduct) :
    mulLinear μ x y = μ.tensorEquiv.symm (toEnd μ (μ.tensorEquiv x) (μ.tensorEquiv y)) :=
  rfl

noncomputable instance instSemiring : Semiring μ.SmashProduct where
  toAddCommMonoid := instAddCommMonoid μ
  mul x y := mulLinear μ x y
  one := μ.smash 1 1
  left_distrib x y z := map_add (mulLinear μ x) y z
  right_distrib x y z := LinearMap.add_apply (mulLinear μ x) (mulLinear μ y) z ▸
    congrArg (· z) (map_add (mulLinear μ) x y)
  zero_mul x := by
    change mulLinear μ 0 x = 0
    rw [map_zero, LinearMap.zero_apply]
  mul_zero x := map_zero (mulLinear μ x)
  mul_assoc x y z := by
    change mulLinear μ (mulLinear μ x y) z = mulLinear μ x (mulLinear μ y z)
    simp only [mulLinear_apply, LinearEquiv.apply_symm_apply, toEnd_mul, mul_apply_eq_comp]
  one_mul x := by
    change mulLinear μ (μ.smash 1 1) x = x
    simp only [mulLinear_apply, tensorEquiv_smash, toEnd, bilinLift_tmul, map_one, mul_one,
      one_apply_eq_self, LinearEquiv.symm_apply_apply]
  mul_one x := by
    change mulLinear μ x (μ.smash 1 1) = x
    rw [mulLinear_apply, tensorEquiv_smash, toEnd_apply_one, LinearEquiv.symm_apply_apply]
  natCast n := μ.smash n 1
  natCast_zero := by rw [Nat.cast_zero, zero_smash]
  natCast_succ n := by rw [Nat.cast_succ, add_smash]; rfl

-- Verify there is no `AddCommMonoid` diamond with `instSemiring`.
example : (instSemiring μ).toAddCommMonoid = instAddCommMonoid μ := rfl

theorem one_def : (1 : μ.SmashProduct) = μ.smash 1 1 := (rfl)

theorem smash_mul_smash (a b : A) (h k : H) :
    μ.smash a h * μ.smash b k = μ.tensorEquiv.symm (μ.smashMulPure a b h k) := by
  change mulLinear μ (μ.smash a h) (μ.smash b k) = _
  rw [mulLinear_apply, tensorEquiv_smash, tensorEquiv_smash, toEnd_tmul_tmul]

@[simp] theorem tensorEquiv_one : μ.tensorEquiv 1 = 1 ⊗ₜ[R] 1 := (rfl)

theorem tensorEquiv_smash_mul_smash (a b : A) (h k : H) :
    μ.tensorEquiv (μ.smash a h * μ.smash b k) = μ.smashMulPure a b h k := by
  rw [smash_mul_smash, LinearEquiv.apply_symm_apply]

/-- Product of pure smash elements in any finite representation of `comul h`. -/
theorem smash_mul_smash_eq_sum {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι)
    (a b : A) (k : H) :
    μ.smash a h * μ.smash b k =
      ∑ i ∈ r.index, μ.smash (a * μ.action (r.left i) b) (r.right i * k) := by
  rw [smash_mul_smash μ, μ.smashMulPure_eq_sum r, map_sum]
  rfl

@[simp]
theorem smash_one_mul_smash (a b : A) (k : H) :
    μ.smash a 1 * μ.smash b k = μ.smash (a * b) k := by
  change mulLinear μ (μ.smash a 1) (μ.smash b k) = μ.smash (a * b) k
  rw [mulLinear_apply, tensorEquiv_smash, tensorEquiv_smash, toEnd, bilinLift_tmul, map_one,
    mul_one, leftMulA_tmul, tensorEquiv_symm_tmul]

@[simp]
theorem smash_mul_one_smash (a : A) (h k : H) :
    μ.smash a h * μ.smash 1 k = μ.smash a (h * k) := by
  rw [smash_mul_smash_eq_sum μ (ℛ R h)]
  simp only [μ.action_one, Algebra.mul_smul_comm, mul_one, smul_smash, ← smash_smul,
    ← Algebra.smul_mul_assoc, ← smash_sum, ← Finset.sum_mul, sum_counit_smul]

theorem one_smash_mul_smash_one {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (b : A) :
    μ.smash 1 h * μ.smash b 1 = ∑ i ∈ r.index, μ.smash (μ.action (r.left i) b) (r.right i) := by
  simpa using smash_mul_smash_eq_sum μ r 1 b 1

instance instSMulCommClass : SMulCommClass R μ.SmashProduct μ.SmashProduct where
  smul_comm r x y := (map_smul (mulLinear μ x) r y).symm

instance instIsScalarTower : IsScalarTower R μ.SmashProduct μ.SmashProduct where
  smul_assoc r x y := by
    change mulLinear μ (r • x) y = r • mulLinear μ x y
    rw [map_smul, LinearMap.smul_apply]

/-- Ring homomorphism `A →+* A # H` sending `a` to `a # 1`. -/
@[expose]
noncomputable def includeARingHom : A →+* μ.SmashProduct where
  toFun a := μ.smash a 1
  map_one' := rfl
  map_mul' a b := (smash_one_mul_smash μ a b 1).symm
  map_zero' := zero_smash 1
  map_add' a b := add_smash a b 1

noncomputable instance instAlgebra : Algebra R μ.SmashProduct where
  smul := (· • ·)
  algebraMap := (includeARingHom μ).comp (algebraMap R A)
  commutes' r x := by
    change μ.smash (algebraMap R A r) 1 * x = x * μ.smash (algebraMap R A r) 1
    rw [Algebra.algebraMap_eq_smul_one, smul_smash, ← one_def, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one]
  smul_def' r x := by
    change r • x = μ.smash (algebraMap R A r) 1 * x
    rw [Algebra.algebraMap_eq_smul_one, smul_smash, ← one_def, smul_mul_assoc, one_mul]

-- Verify there is no `Module R` or `Algebra ℕ` diamond.
example : (instAlgebra μ).toModule = instModule μ := rfl
example {B : Type v} [Semiring B] [Bialgebra ℕ B] {C : Type w} [Semiring C]
    (ν : LeftModuleAlgebra ℕ B C) :
    (Semiring.toNatAlgebra : Algebra ℕ ν.SmashProduct) = instAlgebra ν := rfl

@[simp] theorem algebraMap_apply (r : R) :
    algebraMap R μ.SmashProduct r = μ.smash (algebraMap R A r) 1 := (rfl)

theorem algebraMap_apply' (r : R) :
    algebraMap R μ.SmashProduct r = μ.smash 1 (algebraMap R H r) := by
  rw [algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    smul_smash, smash_smul]

end AlgebraConstruction

end SmashProduct

/-! ### Canonical inclusions of `A` and `H` -/

section Inclusions

variable (μ : LeftModuleAlgebra R H A)

/-- The canonical `R`-algebra homomorphism `A →ₐ[R] A # H` sending `a` to `a # 1`. -/
noncomputable def includeA : A →ₐ[R] μ.SmashProduct where
  __ := SmashProduct.includeARingHom μ
  commutes' _ := rfl

/-- The canonical `R`-algebra homomorphism `H →ₐ[R] A # H` sending `h` to `1 # h`. -/
noncomputable def includeH : H →ₐ[R] μ.SmashProduct where
  toFun h := μ.smash 1 h
  map_one' := rfl
  map_mul' h k := (SmashProduct.smash_mul_one_smash μ 1 h k).symm
  map_zero' := smash_zero 1
  map_add' h k := smash_add 1 h k
  commutes' r := (SmashProduct.algebraMap_apply' μ r).symm

variable {μ}

@[simp] theorem includeA_apply (a : A) : μ.includeA a = μ.smash a 1 := (rfl)

@[simp] theorem includeH_apply (h : H) : μ.includeH h = μ.smash 1 h := (rfl)

theorem includeA_mul_includeH (a : A) (h : H) :
    μ.includeA a * μ.includeH h = μ.smash a h :=
  (SmashProduct.smash_one_mul_smash μ a 1 h).trans (by rw [mul_one])

theorem includeH_mul_includeA_eq_sum (μ : LeftModuleAlgebra R H A) {h : H} {ι : Type*}
    (r : Coalgebra.Repr R h ι) (a : A) :
    μ.includeH h * μ.includeA a =
      ∑ i ∈ r.index, μ.includeA (μ.action (r.left i) a) * μ.includeH (r.right i) := by
  simpa using SmashProduct.one_smash_mul_smash_one μ r a

/-- The canonical inclusions `includeA` and `includeH` form a `SmashCompatible` pair. -/
theorem smashCompatible_includeA_includeH (μ : LeftModuleAlgebra R H A) :
    μ.SmashCompatible μ.includeA μ.includeH :=
  (μ.smashCompatible_iff_sum _ _ (ℛ R)).2 fun h a => μ.includeH_mul_includeA_eq_sum (ℛ R h) a

/-- Two `R`-algebra homomorphisms out of `A # H` agree if and only if they agree on `includeA`
and `includeH`. -/
@[ext]
theorem SmashProduct.algHom_ext {C : Type*} [Semiring C] [Algebra R C]
    {f g : μ.SmashProduct →ₐ[R] C}
    (hA : f.comp μ.includeA = g.comp μ.includeA)
    (hH : f.comp μ.includeH = g.comp μ.includeH) : f = g := by
  refine AlgHom.toLinearMap_injective (SmashProduct.lhom_ext fun a h => ?_)
  have hA' := AlgHom.congr_fun hA a
  have hH' := AlgHom.congr_fun hH h
  simp only [AlgHom.comp_apply] at hA' hH'
  change f (μ.smash a h) = g (μ.smash a h)
  rw [← μ.includeA_mul_includeH, map_mul, map_mul, hA', hH']

end Inclusions

/-! ### Retractions, injectivity, and degeneracy -/

section Embeddings

variable (μ : LeftModuleAlgebra R H A)

/-- The `R`-linear retraction `A # H →ₗ[R] A` sending `a # h` to `counit h • a`. -/
noncomputable def retractA : μ.SmashProduct →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := H)).lTensor A ∘ₗ μ.tensorEquiv.toLinearMap

@[simp]
theorem retractA_smash (a : A) (h : H) :
    μ.retractA (μ.smash a h) = counit (R := R) h • a := by
  simp [retractA]

theorem retractA_includeA (a : A) : μ.retractA (μ.includeA a) = a := by simp

@[simp]
theorem retractA_comp_includeA : μ.retractA.comp μ.includeA.toLinearMap = LinearMap.id :=
  LinearMap.ext μ.retractA_includeA

/-- The canonical map `includeA : A →ₐ[R] A # H` (`a ↦ a # 1`) is unconditionally injective. -/
theorem includeA_injective : Function.Injective μ.includeA :=
  Function.LeftInverse.injective μ.retractA_includeA

/-- When `A` is subsingleton, `includeH : H →ₐ[R] A # H` has kernel `⊤`. -/
@[simp]
theorem ker_includeH_eq_top [Subsingleton A] :
    RingHom.ker (μ.includeH : H →+* μ.SmashProduct) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (RingHom.mem_ker.2 (Subsingleton.elim _ _))

/-- The `R`-linear map `A # H →ₗ[R] H` induced by a linear functional `φ : A →ₗ[R] R`,
sending `a # h` to `φ a • h`. -/
noncomputable def retractH (φ : A →ₗ[R] R) : μ.SmashProduct →ₗ[R] H :=
  (TensorProduct.lid R H).toLinearMap ∘ₗ φ.rTensor H ∘ₗ μ.tensorEquiv.toLinearMap

@[simp]
theorem retractH_smash (φ : A →ₗ[R] R) (a : A) (h : H) :
    μ.retractH φ (μ.smash a h) = φ a • h := by
  simp [retractH]

theorem retractH_includeH {φ : A →ₗ[R] R} (hφ : φ 1 = 1) (h : H) :
    μ.retractH φ (μ.includeH h) = h := by
  simp [hφ]

/-- If `1 : A` admits an `R`-linear functional sending it to `1 : R`, then
`includeH : H →ₐ[R] A # H` (`h ↦ 1 # h`) is injective. -/
theorem includeH_injective_of_apply_one_eq_one (φ : A →ₗ[R] R) (hφ : φ 1 = 1) :
    Function.Injective μ.includeH :=
  Function.LeftInverse.injective (μ.retractH_includeH hφ)

end Embeddings

section FieldEmbedding

variable {K : Type u} {H : Type v} {A : Type w}
  [Field K] [Semiring H] [Bialgebra K H] [Semiring A] [Algebra K A]

/-- Over a field, `includeH : H →ₐ[K] A # H` is injective whenever `A` is nontrivial. -/
theorem includeH_injective (μ : LeftModuleAlgebra K H A) [Nontrivial A] :
    Function.Injective μ.includeH := by
  let _ := Module.addCommMonoidToAddCommGroup K (M := A)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : A) ≠ 0)
  exact μ.includeH_injective_of_apply_one_eq_one φ hφ

end FieldEmbedding

/-! ### Universal property -/

namespace SmashProduct

section Lift

variable {μ : LeftModuleAlgebra R H A} {C : Type x} [Semiring C] [Algebra R C]

/-- Universal property of the smash product: a `SmashCompatible` pair of `R`-algebra
homomorphisms `fA : A →ₐ[R] C` and `fH : H →ₐ[R] C` descends to an `R`-algebra homomorphism
`A # H →ₐ[R] C` sending `a # h` to `fA a * fH h`. -/
noncomputable def lift (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH) :
    μ.SmashProduct →ₐ[R] C :=
  AlgHom.ofLinearMap
    (bilinLift fA fH ∘ₗ μ.tensorEquiv.toLinearMap)
    (by simp [bilinLift_tmul])
    (fun x y => by
      simp only [LinearMap.comp_apply]
      change bilinLift fA fH (μ.tensorEquiv (mulLinear μ x y)) = _
      rw [mulLinear_apply, LinearEquiv.apply_symm_apply]
      exact bilinLift_toEnd_apply hf (μ.tensorEquiv x) (μ.tensorEquiv y))

@[simp]
theorem lift_smash (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH)
    (a : A) (h : H) : lift fA fH hf (μ.smash a h) = fA a * fH h := by
  change bilinLift fA fH (μ.tensorEquiv (μ.smash a h)) = fA a * fH h
  rw [tensorEquiv_smash, bilinLift_tmul]

theorem lift_includeA (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH) (a : A) :
    lift fA fH hf (μ.includeA a) = fA a := by
  simp

theorem lift_includeH (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH) (h : H) :
    lift fA fH hf (μ.includeH h) = fH h := by
  simp

@[simp]
theorem lift_comp_includeA (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH) :
    (lift fA fH hf).comp μ.includeA = fA :=
  AlgHom.ext (lift_includeA fA fH hf)

@[simp]
theorem lift_comp_includeH (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH) :
    (lift fA fH hf).comp μ.includeH = fH :=
  AlgHom.ext (lift_includeH fA fH hf)

@[simp]
theorem lift_includeA_includeH :
    lift μ.includeA μ.includeH μ.smashCompatible_includeA_includeH =
      AlgHom.id R μ.SmashProduct := by
  ext <;> simp

/-- Every `R`-algebra homomorphism out of `A # H` restricts along `includeA` and `includeH` to a
`SmashCompatible` pair. -/
theorem smashCompatible_comp (F : μ.SmashProduct →ₐ[R] C) :
    μ.SmashCompatible (F.comp μ.includeA) (F.comp μ.includeH) := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  calc (F.comp μ.includeH) h * (F.comp μ.includeA) a
      = F (μ.includeH h * μ.includeA a) := (map_mul F _ _).symm
    _ = F (∑ i ∈ (ℛ R h).index,
          μ.includeA (μ.action ((ℛ R h).left i) a) * μ.includeH ((ℛ R h).right i)) := by
          rw [μ.includeH_mul_includeA_eq_sum (ℛ R h) a]
    _ = ∑ i ∈ (ℛ R h).index,
          (F.comp μ.includeA) (μ.action ((ℛ R h).left i) a) *
            (F.comp μ.includeH) ((ℛ R h).right i) := by
          simp only [map_sum, map_mul, AlgHom.comp_apply]

/-- Existence and uniqueness form of the universal property of `A # H`. -/
theorem lift_unique (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hf : μ.SmashCompatible fA fH) :
    ∃! F : μ.SmashProduct →ₐ[R] C, F.comp μ.includeA = fA ∧ F.comp μ.includeH = fH :=
  ⟨lift fA fH hf, ⟨lift_comp_includeA fA fH hf, lift_comp_includeH fA fH hf⟩,
    fun _ ⟨hA, hH⟩ => algHom_ext (hA.trans (lift_comp_includeA fA fH hf).symm)
      (hH.trans (lift_comp_includeH fA fH hf).symm)⟩

variable (μ C) in
/-- `R`-algebra homomorphisms out of `A # H` correspond bijectively to `SmashCompatible` pairs
of `R`-algebra homomorphisms out of `A` and `H`. -/
noncomputable def liftEquiv :
    (μ.SmashProduct →ₐ[R] C) ≃
      { p : (A →ₐ[R] C) × (H →ₐ[R] C) // μ.SmashCompatible p.1 p.2 } where
  toFun F := ⟨(F.comp μ.includeA, F.comp μ.includeH), smashCompatible_comp F⟩
  invFun p := lift p.1.1 p.1.2 p.2
  left_inv _ := by ext <;> simp
  right_inv p := Subtype.ext <| Prod.ext (lift_comp_includeA ..) (lift_comp_includeH ..)

@[simp]
theorem liftEquiv_apply_fst (F : μ.SmashProduct →ₐ[R] C) :
    ((liftEquiv μ C F).1).1 = F.comp μ.includeA :=
  (rfl)

@[simp]
theorem liftEquiv_apply_snd (F : μ.SmashProduct →ₐ[R] C) :
    ((liftEquiv μ C F).1).2 = F.comp μ.includeH :=
  (rfl)

@[simp]
theorem liftEquiv_symm_apply
    (p : { p : (A →ₐ[R] C) × (H →ₐ[R] C) // μ.SmashCompatible p.1 p.2 }) :
    (liftEquiv μ C).symm p = lift p.1.1 p.1.2 p.2 :=
  (rfl)

end Lift

/-! ### Trivial action and base-ring isomorphisms -/

section Comparison

variable (R H A)

/-- For the trivial module-algebra action, the smash product `A # H` is canonically isomorphic
as an `R`-algebra to the ordinary tensor-product algebra `A ⊗[R] H`. -/
noncomputable def trivialAlgEquiv :
    (trivial (R := R) (H := H) (A := A)).SmashProduct ≃ₐ[R] A ⊗[R] H :=
  AlgEquiv.ofLinearEquiv
    (trivial (R := R) (H := H) (A := A)).tensorEquiv
    rfl
    (fun x y => by
      let μ₀ := trivial (R := R) (H := H) (A := A)
      induction x using SmashProduct.inductionOn with
      | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
      | smash a h =>
        induction y using SmashProduct.inductionOn with
        | add y₁ y₂ hy₁ hy₂ => simp [mul_add, hy₁, hy₂]
        | smash b k =>
          change μ₀.tensorEquiv (μ₀.smash a h * μ₀.smash b k) = (a ⊗ₜ[R] h) * (b ⊗ₜ[R] k)
          rw [tensorEquiv_smash_mul_smash, μ₀.smashMulPure_eq_sum (ℛ R h)]
          simp only [μ₀, trivial_action, Algebra.mul_smul_comm, TensorProduct.smul_tmul]
          simp only [← Algebra.smul_mul_assoc, ← TensorProduct.tmul_sum, ← Finset.sum_mul,
            sum_counit_smul, Algebra.TensorProduct.tmul_mul_tmul])

@[simp]
theorem trivialAlgEquiv_smash (a : A) (h : H) :
    trivialAlgEquiv R H A ((trivial (R := R) (H := H) (A := A)).smash a h) = a ⊗ₜ[R] h :=
  (rfl)

@[simp]
theorem trivialAlgEquiv_symm_tmul (a : A) (h : H) :
    (trivialAlgEquiv R H A).symm (a ⊗ₜ[R] h) =
      (trivial (R := R) (H := H) (A := A)).smash a h :=
  (rfl)

/-- For the base ring `A = R` with the trivial action, `R # H` is canonically isomorphic as an
`R`-algebra to `H`, with inverse `includeH` (`h ↦ 1 # h`). -/
noncomputable def baseAlgEquiv :
    (trivial (R := R) (H := H) (A := R)).SmashProduct ≃ₐ[R] H :=
  (trivialAlgEquiv R H R).trans (Algebra.TensorProduct.lid R H)

@[simp]
theorem baseAlgEquiv_smash (r : R) (h : H) :
    baseAlgEquiv R H ((trivial (R := R) (H := H) (A := R)).smash r h) = r • h :=
  Algebra.TensorProduct.lid_tmul r h

@[simp]
theorem baseAlgEquiv_symm_apply (h : H) :
    (baseAlgEquiv R H).symm h = (trivial (R := R) (H := H) (A := R)).includeH h :=
  (rfl)

end Comparison

/-! ### Functoriality -/

section Functoriality

variable {K L : Type*} [Semiring K] [Bialgebra R K] [Semiring L] [Bialgebra R L]
  {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- Joint functoriality of the smash product: a bialgebra homomorphism `g : K →ₐc[R] H` and an
equivariant algebra homomorphism `f : Hom μ (ν.restrict g)` induce an `R`-algebra homomorphism
`A # K →ₐ[R] B # H` sending `a # k` to `f a # g k`. -/
noncomputable def map {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    μ.SmashProduct →ₐ[R] ν.SmashProduct :=
  lift (ν.includeA.comp f.toAlgHom) (ν.includeH.comp g.toAlgHom) <| by
    rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
    intro k a
    have hcomul : Coalgebra.comul (R := R) (g k) =
        ∑ i ∈ (ℛ R k).index, g ((ℛ R k).left i) ⊗ₜ[R] g ((ℛ R k).right i) := by
      simpa [← (ℛ R k).eq, map_sum] using (CoalgHomClass.map_comp_comul_apply g k).symm
    let rg : Coalgebra.Repr R (g k) _ :=
      { index := (ℛ R k).index
        left := fun i => g ((ℛ R k).left i)
        right := fun i => g ((ℛ R k).right i)
        eq := hcomul.symm }
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, ν.includeH_mul_includeA_eq_sum rg]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ν.includeA (ν.action (g ((ℛ R k).left i)) (f a)) *
        ν.includeH (g ((ℛ R k).right i)) =
      ν.includeA (f (μ.action ((ℛ R k).left i) a)) * ν.includeH (g ((ℛ R k).right i))
    rw [← ν.restrict_action g, ← f.map_action]

@[simp]
theorem map_smash {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) (a : A) (k : K) :
    map g f (μ.smash a k) = ν.smash (f a) (g k) := by
  simp [map]

@[simp]
theorem map_comp_includeA {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (map g f).comp μ.includeA = ν.includeA.comp f.toAlgHom :=
  lift_comp_includeA ..

@[simp]
theorem map_comp_includeH {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (map g f).comp μ.includeH = ν.includeH.comp g.toAlgHom :=
  lift_comp_includeH ..

theorem toLinearMap_map {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (map g f).toLinearMap =
      ν.tensorEquiv.symm.toLinearMap ∘ₗ
        TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap ∘ₗ
        μ.tensorEquiv.toLinearMap :=
  lhom_ext fun a k => by simp [AlgHom.toLinearMap_apply]

/-- Functoriality of `A # H` in an equivariant algebra homomorphism over a fixed bialgebra `H`. -/
noncomputable def mapHom {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) : μ.SmashProduct →ₐ[R] ν.SmashProduct :=
  map (BialgHom.id R H) ⟨f.toAlgHom, fun h a => by simp [f.map_action]⟩

@[simp]
theorem mapHom_smash {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) (a : A) (h : H) : mapHom f (μ.smash a h) = ν.smash (f a) h :=
  map_smash (BialgHom.id R H) _ a h

@[simp]
theorem mapHom_comp_includeA {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) : (mapHom f).comp μ.includeA = ν.includeA.comp f.toAlgHom :=
  map_comp_includeA ..

@[simp]
theorem mapHom_comp_includeH {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) : (mapHom f).comp μ.includeH = ν.includeH :=
  map_comp_includeH ..

@[simp]
theorem mapHom_id (μ : LeftModuleAlgebra R H A) :
    mapHom (Hom.id μ) = AlgHom.id R μ.SmashProduct := by
  ext <;> simp

@[simp]
theorem mapHom_comp {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    {ξ : LeftModuleAlgebra R H C} (g : Hom ν ξ) (f : Hom μ ν) :
    mapHom (g.comp f) = (mapHom g).comp (mapHom f) := by
  ext <;> simp

/-- Functoriality of `A # H` along a bialgebra homomorphism `g : K →ₐc[R] H`. -/
noncomputable def mapRestrict (μ : LeftModuleAlgebra R H A) (g : K →ₐc[R] H) :
    (μ.restrict g).SmashProduct →ₐ[R] μ.SmashProduct :=
  map g (Hom.id (μ.restrict g))

@[simp]
theorem mapRestrict_smash (μ : LeftModuleAlgebra R H A) (g : K →ₐc[R] H) (a : A) (k : K) :
    mapRestrict μ g ((μ.restrict g).smash a k) = μ.smash a (g k) := by
  simp [mapRestrict]

@[simp]
theorem mapRestrict_comp_includeA (μ : LeftModuleAlgebra R H A) (g : K →ₐc[R] H) :
    (mapRestrict μ g).comp (μ.restrict g).includeA = μ.includeA := by
  ext a
  simp [mapRestrict]

@[simp]
theorem mapRestrict_comp_includeH (μ : LeftModuleAlgebra R H A) (g : K →ₐc[R] H) :
    (mapRestrict μ g).comp (μ.restrict g).includeH = μ.includeH.comp g.toAlgHom :=
  map_comp_includeH ..

@[simp]
theorem map_comp {μ : LeftModuleAlgebra R L A} {ν : LeftModuleAlgebra R K B}
    {ξ : LeftModuleAlgebra R H C} (g₂ : K →ₐc[R] H) (g₁ : L →ₐc[R] K)
    (f₂ : Hom ν (ξ.restrict g₂)) (f₁ : Hom μ (ν.restrict g₁)) :
    (map g₂ f₂).comp (map g₁ f₁) =
      map (g₂.comp g₁) ⟨f₂.toAlgHom.comp f₁.toAlgHom, fun _ _ => by simp⟩ := by
  ext <;> simp

/-- Algebra equivalence `A # K ≃ₐ[R] B # H` induced by a bialgebra equivalence `g : K ≃ₐc[R] H`
and an equivariant algebra equivalence `f : A ≃ₐ[R] B`. -/
noncomputable def congr {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a)) :
    μ.SmashProduct ≃ₐ[R] ν.SmashProduct :=
  AlgEquiv.ofAlgHom
    (map (g : K →ₐc[R] H) ⟨f.toAlgHom, fun k a => by simp [hf]⟩)
    (map (g.symm : H →ₐc[R] K) ⟨f.symm.toAlgHom, fun _ _ => f.injective (by simp [hf])⟩)
    (by ext <;> simp)
    (by ext <;> simp)

@[simp]
theorem congr_smash {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (a : A) (k : K) :
    congr g f hf (μ.smash a k) = ν.smash (f a) (g k) :=
  map_smash (g : K →ₐc[R] H) ⟨f.toAlgHom, fun k' a' => by simp [hf]⟩ a k

end Functoriality

end SmashProduct

end Semiring

/-! ### Ring structure when `A` is a ring -/

section Ring

variable {R : Type u} {H : Type v} {A : Type w}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Ring A] [Algebra R A]

instance SmashProduct.instNeg (μ : LeftModuleAlgebra R H A) : Neg μ.SmashProduct :=
  ⟨fun x => ⟨-x.toTensor⟩⟩

instance SmashProduct.instSub (μ : LeftModuleAlgebra R H A) : Sub μ.SmashProduct :=
  ⟨fun x y => ⟨x.toTensor - y.toTensor⟩⟩

instance SmashProduct.instSMulInt (μ : LeftModuleAlgebra R H A) : SMul ℤ μ.SmashProduct :=
  ⟨fun z x => ⟨z • x.toTensor⟩⟩

instance SmashProduct.instAddCommGroup (μ : LeftModuleAlgebra R H A) :
    AddCommGroup μ.SmashProduct :=
  (SmashProduct.toTensor_injective μ).addCommGroup SmashProduct.toTensor
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

noncomputable instance SmashProduct.instRing (μ : LeftModuleAlgebra R H A) :
    Ring μ.SmashProduct where
  toSemiring := SmashProduct.instSemiring μ
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg x y := SmashProduct.toTensor_injective μ (sub_eq_add_neg x.toTensor y.toTensor)
  zsmul := (· • ·)
  zsmul_zero' x := SmashProduct.toTensor_injective μ (zero_smul ℤ x.toTensor)
  zsmul_succ' n x := SmashProduct.toTensor_injective μ (SubNegMonoid.zsmul_succ' n x.toTensor)
  zsmul_neg' n x := SmashProduct.toTensor_injective μ (SubNegMonoid.zsmul_neg' n x.toTensor)
  neg_add_cancel x := SmashProduct.toTensor_injective μ (neg_add_cancel x.toTensor)
  intCast z := μ.smash z 1
  intCast_ofNat n := by rw [Int.cast_natCast]; rfl
  intCast_negSucc n := by
    change μ.smash (Int.negSucc n : A) 1 = -μ.smash ((n + 1 : ℕ) : A) 1
    rw [Int.cast_negSucc]
    exact SmashProduct.toTensor_injective μ (TensorProduct.neg_tmul _ _)

-- Verify there are no `AddCommGroup`, `Semiring`, or `Algebra ℤ` diamonds.
example (μ : LeftModuleAlgebra R H A) :
    (SmashProduct.instRing μ).toAddCommGroup = SmashProduct.instAddCommGroup μ := rfl
example (μ : LeftModuleAlgebra R H A) :
    (SmashProduct.instRing μ).toSemiring = SmashProduct.instSemiring μ := rfl
example {B : Type v} [Semiring B] [Bialgebra ℤ B] {C : Type w} [Ring C]
    (ν : LeftModuleAlgebra ℤ B C) :
    (Ring.toIntAlgebra ν.SmashProduct : Algebra ℤ ν.SmashProduct) = SmashProduct.instAlgebra ν :=
  rfl

@[simp]
theorem neg_smash (μ : LeftModuleAlgebra R H A) (a : A) (h : H) :
    μ.smash (-a) h = -μ.smash a h :=
  SmashProduct.toTensor_injective μ (TensorProduct.neg_tmul a h)

theorem sub_smash (μ : LeftModuleAlgebra R H A) (a b : A) (h : H) :
    μ.smash (a - b) h = μ.smash a h - μ.smash b h :=
  map_sub (μ.smashBilinear.flip h) a b

@[simp]
theorem smash_neg {K : Type v} [Ring K] [Bialgebra R K]
    (μ : LeftModuleAlgebra R K A) (a : A) (k : K) :
    μ.smash a (-k) = -μ.smash a k :=
  map_neg (μ.smashBilinear a) k

theorem smash_sub {K : Type v} [Ring K] [Bialgebra R K]
    (μ : LeftModuleAlgebra R K A) (a : A) (k₁ k₂ : K) :
    μ.smash a (k₁ - k₂) = μ.smash a k₁ - μ.smash a k₂ :=
  map_sub (μ.smashBilinear a) k₁ k₂

end Ring

end LeftModuleAlgebra

end TauCeti
