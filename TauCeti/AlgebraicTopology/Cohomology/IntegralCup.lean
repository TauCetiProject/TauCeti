/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The integral cup product

Write `Hⁿ(X; ℤ)` for the singular cohomology of a space `X` with integral coefficients in the
convention of `TauCeti.HomologicalOrientation.evalFundamentalClass`, which pairs it with
fundamental classes: singular chains with coefficients in `ULift ℤ` and cochains with values in
`ℤ`. The singular cup product
`TopCat.singularCup` needs a diagonal of the chain coefficients and a pairing of the cochain
values. Taking the diagonal `n ↦ n (1 ⊗ 1)` of `ULift ℤ` and the multiplication of `ℤ` gives the
**integral cup product** `TopCat.integralCup : Hᵖ(X; ℤ) × H^q(X; ℤ) → Hⁿ(X; ℤ)`, `p + q = n`.

The diagonal is coassociative and cocommutative and the multiplication associative and
commutative, so the general laws of the singular cup product specialize: the integral cup product
is associative and graded commutative, `b ⌣ a = (-1)^(p q) a ⌣ b`, with unit the class
`1 ∈ H⁰(X; ℤ)` of the constant cocycle. Consequently the cup square of a class of odd degree has
order at most two, and degree-one classes anticommute in iterated products,
`a ⌣ (b ⌣ c) = -(b ⌣ (a ⌣ c))`.

## Main definitions

* `TopCat.integralCohomology`: integral singular cohomology `Hⁿ(X; ℤ)`.
* `TopCat.integralCup`: the integral cup product `Hᵖ(X; ℤ) × H^q(X; ℤ) → Hⁿ(X; ℤ)`.
* `TopCat.integralCohomologyOne`: the unit class `1 ∈ H⁰(X; ℤ)`.

## Main results

* `TopCat.integralCup_naturality`: `f^* a ⌣ f^* b = f^* (a ⌣ b)`.
* `TopCat.integralCup_assoc`: `(a ⌣ b) ⌣ c = a ⌣ (b ⌣ c)`.
* `TopCat.integralCup_gradedComm`: `b ⌣ a = (-1)^(p q) a ⌣ b`.
* `TopCat.integralCup_integralCohomologyOne`: `1 ⌣ b = b`.
* `TopCat.integralCup_self_add_self_eq_zero`: `a ⌣ a + a ⌣ a = 0` for `a` of odd degree.
* `TopCat.integralCup_left_anticomm`: `a ⌣ (b ⌣ c) = -(b ⌣ (a ⌣ c))` for `a`, `b` of degree
  one.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

namespace TopCat

/-- **Integral singular cohomology** `Hⁿ(X; ℤ)`, with singular chain coefficients `ULift ℤ` and
cochain values `ℤ`, as paired with fundamental classes by
`TauCeti.HomologicalOrientation.evalFundamentalClass`. -/
abbrev integralCohomology (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ) n

/-- Mathlib's `MonoidalLinear ℤ` instance on `ModuleCat ℤ` is stated for its `ℤ`-linear structure
as a category of modules, while instance search finds the `ℤ`-linear structure of a preadditive
category; whiskering commutes with the integer multiples of the latter as well. -/
local instance : MonoidalLinear ℤ (ModuleCat.{0} ℤ) where
  whiskerLeft_smul X _ _ r f := whiskerLeft_zsmul r X f
  smul_whiskerRight r _ _ f X := zsmul_whiskerRight r f X

/-- The diagonal `n ↦ n (1 ⊗ 1)` of the integral chain coefficients `ULift ℤ`. -/
def integralCoeffComul : ModuleCat.of ℤ (ULift.{0} ℤ) ⟶
    ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ) :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ _ ((⟨1⟩ : ULift ℤ) ⊗ₜ (⟨1⟩ : ULift ℤ))).comp
    ULift.moduleEquiv.toLinearMap)

/-- The multiplication `ℤ ⊗ ℤ → ℤ` of the integral cochain values. -/
def integralCoeffMul : ModuleCat.of ℤ ℤ ⊗ ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom (LinearMap.mul' ℤ ℤ)

/-- The diagonal of the chain coefficients sends `n` to `n (1 ⊗ 1)`. -/
theorem integralCoeffComul_apply (n : ModuleCat.of ℤ (ULift.{0} ℤ)) :
    integralCoeffComul.hom n = n.down • ((⟨1⟩ : ULift ℤ) ⊗ₜ (⟨1⟩ : ULift ℤ)) :=
  (rfl)

/-- The multiplication of the cochain values on pure tensors. -/
theorem integralCoeffMul_apply (a b : ModuleCat.of ℤ ℤ) :
    integralCoeffMul.hom (a ⊗ₜ b) = (a * b : ℤ) :=
  (rfl)

/-- The diagonal of the chain coefficients is cocommutative. -/
theorem integralCoeffComul_comm :
    integralCoeffComul ≫ (β_ _ _).hom = integralCoeffComul := by
  ext n
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, integralCoeffComul_apply, map_smul,
    ModuleCat.MonoidalCategory.braiding_hom_apply]

/-- The diagonal of the chain coefficients is coassociative. -/
theorem integralCoeffComul_coassoc :
    integralCoeffComul ≫ integralCoeffComul ▷ _ ≫ (α_ _ _ _).hom =
      integralCoeffComul ≫ _ ◁ integralCoeffComul := by
  ext n
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, integralCoeffComul_apply, map_smul, map_smul,
    map_smul, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, integralCoeffComul_apply]
  exact congrArg (n.down • ·) (ModuleCat.MonoidalCategory.associator_hom_apply _ _ _)

/-- The multiplication of the cochain values is commutative. -/
theorem integralCoeffMul_comm : (β_ _ _).hom ≫ integralCoeffMul = integralCoeffMul := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.braiding_hom_apply,
    integralCoeffMul_apply, integralCoeffMul_apply, mul_comm]

/-- The multiplication of the cochain values is associative. -/
theorem integralCoeffMul_assoc :
    integralCoeffMul ▷ _ ≫ integralCoeffMul =
      (α_ _ _ _).hom ≫ _ ◁ integralCoeffMul ≫ integralCoeffMul := by
  refine ModuleCat.MonoidalCategory.tensor_ext₃' fun a b c ↦ ?_
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  -- Both sides are `integralCoeffMul` on pure tensors, that is products (`integralCoeffMul_apply`).
  exact mul_assoc a b c

variable (X : TopCat.{0})

/-- **The integral cup product** `Hᵖ(X; ℤ) × H^q(X; ℤ) → Hⁿ(X; ℤ)` for `p + q = n`: the singular
cup product along the diagonal `n ↦ n (1 ⊗ 1)` of the chain coefficients `ULift ℤ` and the
multiplication of the cochain values `ℤ`. -/
-- The type is left to elaboration: written out, instance search would equip the inner space of
-- linear maps with the `ℤ`-module structure of an additive group rather than `LinearMap.module`.
def integralCup (p q n : ℕ) (h : p + q = n) :=
  X.singularCup ℤ integralCoeffComul integralCoeffMul p q n h

/-- The integral cup product is the singular cup product along the integral coefficient maps. -/
theorem integralCup_def (p q n : ℕ) (h : p + q = n) :
    X.integralCup p q n h = X.singularCup ℤ integralCoeffComul integralCoeffMul p q n h :=
  (rfl)

/-- **Naturality of the integral cup product**: pulling back along `f : X ⟶ Y` commutes with
the cup product. -/
theorem integralCup_naturality {Y : TopCat.{0}} (f : X ⟶ Y) (p q n : ℕ) (h : p + q = n)
    (a : Y.integralCohomology p) (b : Y.integralCohomology q) :
    X.integralCup p q n h (TopCat.singularCohomologyMap f p a)
        (TopCat.singularCohomologyMap f q b) =
      TopCat.singularCohomologyMap f n (Y.integralCup p q n h a b) :=
  singularCup_naturality f ℤ integralCoeffComul integralCoeffMul p q n h a b

/-- **Associativity of the integral cup product**, `(a ⌣ b) ⌣ c = a ⌣ (b ⌣ c)`. -/
theorem integralCup_assoc {p q r m m' n : ℕ} (h₁₂ : p + q = m) (h : m + r = n)
    (h₂₃ : q + r = m') (h' : p + m' = n) (a : X.integralCohomology p)
    (b : X.integralCohomology q) (c : X.integralCohomology r) :
    X.integralCup m r n h (X.integralCup p q m h₁₂ a b) c =
      X.integralCup p m' n h' a (X.integralCup q r m' h₂₃ b c) :=
  X.singularCup_assoc ℤ integralCoeffComul_coassoc integralCoeffMul_assoc h₁₂ h h₂₃ h' a b c

/-- **Graded commutativity of the integral cup product**, `b ⌣ a = (-1)^(p q) a ⌣ b`. -/
theorem integralCup_gradedComm {p q n : ℕ} (h : p + q = n) (h' : q + p = n)
    (a : X.integralCohomology p) (b : X.integralCohomology q) :
    X.integralCup q p n h' b a = ((-1 : ℤ) ^ (p * q)) • X.integralCup p q n h a b :=
  X.singularCup_gradedComm ℤ integralCoeffComul_comm integralCoeffMul_comm h a b

/-- The cup square of a class of odd degree has order at most two, `a ⌣ a + a ⌣ a = 0`. -/
theorem integralCup_self_add_self_eq_zero {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (a : X.integralCohomology p) :
    X.integralCup p p n h a a + X.integralCup p p n h a a = 0 := by
  have hc := X.integralCup_gradedComm h h a a
  rw [(hp.mul hp).neg_one_pow] at hc
  rw [neg_one_zsmul] at hc
  nth_rw 1 [hc]
  exact neg_add_cancel _

/-- **Degree-one classes anticommute**: `a ⌣ (b ⌣ c) = -(b ⌣ (a ⌣ c))` for `a` and `b` of
degree one. -/
theorem integralCup_left_anticomm {q m n : ℕ} (hm : 1 + q = m) (hn : 1 + m = n)
    (a b : X.integralCohomology 1) (c : X.integralCohomology q) :
    X.integralCup 1 m n hn a (X.integralCup 1 q m hm b c) =
      -X.integralCup 1 m n hn b (X.integralCup 1 q m hm a c) := by
  rw [← X.integralCup_assoc rfl (by omega) hm hn, ← X.integralCup_assoc rfl (by omega) hm hn,
    X.integralCup_gradedComm rfl rfl b a]
  simp

/-- For `a` of degree one, `a ⌣ (a ⌣ c)` has order at most two. -/
theorem integralCup_integralCup_self_add_self_eq_zero {q m n : ℕ} (hm : 1 + q = m)
    (hn : 1 + m = n) (a : X.integralCohomology 1) (c : X.integralCohomology q) :
    X.integralCup 1 m n hn a (X.integralCup 1 q m hm a c) +
      X.integralCup 1 m n hn a (X.integralCup 1 q m hm a c) = 0 := by
  rw [← X.integralCup_assoc rfl (by omega) hm hn, ← LinearMap.add_apply, ← map_add,
    X.integralCup_self_add_self_eq_zero odd_one rfl, map_zero, LinearMap.zero_apply]

/-- The unit class `1 ∈ H⁰(X; ℤ)`, the class of the constant `0`-cocycle with value `1`. -/
def integralCohomologyOne : X.integralCohomology 0 :=
  (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ)).homologyπ 0
    (X.constSingularCocycle ℤ (ModuleCat.ofHom ULift.moduleEquiv.toLinearMap))

/-- The unit class is a left unit for the integral cup product, `1 ⌣ b = b`. -/
@[simp]
theorem integralCup_integralCohomologyOne (q : ℕ) (b : X.integralCohomology q) :
    X.integralCup 0 q q (zero_add q) X.integralCohomologyOne b = b := by
  refine X.singularCup_constSingularCocycle_left ℤ (η := 𝟙 _) ?_ ?_ (zero_add q) b
  · rw [id_whiskerRight, Category.comp_id]
    ext n
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, integralCoeffComul_apply, map_smul,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ← TensorProduct.tmul_smul]
    congr 1
    ext
    simp
  · rw [id_whiskerRight, Category.id_comp]
    refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
    rw [integralCoeffMul_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, smul_eq_mul]

end TopCat
