/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Steinberg pairings and the degree-two symbol group

A **Steinberg pairing** on the unit group `Rˣ` of a semiring `R` with values in an additive monoid
`A` is a bimultiplicative map `c : Rˣ → Rˣ → A` that vanishes on complementary units, i.e.,
`c a b = 0` whenever `(a : R) + b = 1`. Over a field `F`, the Steinberg relation forces the
classical integral symbol identities: `c a (-a) = 0`, skew-symmetry `c a b = -c b a`, the diagonal
relation `c a a = c a (-1)`, and hence `2 • c a a = 0` (with `c a a = 0` in characteristic `2`).

For a commutative semiring `R`, the quotient
`TauCeti.SymbolGroup R := (Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R`
is the universal target of Steinberg pairings out of `Rˣ × Rˣ` into abelian groups. It models
Milnor's `K₂ᴹ(R)` directly as a quotient of the tensor square.

## Main definitions

* `TauCeti.IsSteinbergPairing`: predicate on `c : Rˣ → Rˣ → A` asserting bimultiplicativity and
  vanishing on complementary units `a + b = 1`.
* `TauCeti.steinbergRelations`: the `ℤ`-submodule of `Additive Rˣ ⊗[ℤ] Additive Rˣ` spanned by
  tensors `a ⊗ b` with `(a : R) + b = 1`.
* `TauCeti.SymbolGroup`: the degree-two symbol group
  `(Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R`.
* `TauCeti.symbol`: the universal Steinberg pairing `Rˣ → Rˣ → SymbolGroup R`.
* `TauCeti.SymbolGroup.lift`, `TauCeti.SymbolGroup.liftEquiv`: the universal property identifying
  additive homomorphisms out of `SymbolGroup R` with Steinberg pairings.
* `TauCeti.SymbolGroup.map`: functoriality of `SymbolGroup` along ring homomorphisms.

## Main results

* `TauCeti.IsSteinbergPairing.map_neg_self`, `TauCeti.IsSteinbergPairing.map_swap`,
  `TauCeti.IsSteinbergPairing.map_self`, `TauCeti.IsSteinbergPairing.two_nsmul_map_self`,
  `TauCeti.IsSteinbergPairing.map_self_of_charTwo`: integral symbol identities for every Steinberg
  pairing on a field.
* `TauCeti.isSteinbergPairing_symbol`: `TauCeti.symbol` is a Steinberg pairing.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Ch. III, §6.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

/-- A **Steinberg pairing** on the units of a semiring `R` with values in an additive monoid `A`
is a bimultiplicative map vanishing on `1` and on pairs of units that sum to `1` in `R`. -/
structure IsSteinbergPairing {R : Type u} [Semiring R] {A : Type v} [AddMonoid A]
    (c : Rˣ → Rˣ → A) : Prop where
  /-- Multiplicativity in the first argument. -/
  map_mul_left : ∀ a₁ a₂ b : Rˣ, c (a₁ * a₂) b = c a₁ b + c a₂ b
  /-- Multiplicativity in the second argument. -/
  map_mul_right : ∀ a b₁ b₂ : Rˣ, c a (b₁ * b₂) = c a b₁ + c a b₂
  /-- Vanishing when the first argument is `1`. -/
  map_one_left : ∀ b : Rˣ, c 1 b = 0
  /-- Vanishing when the second argument is `1`. -/
  map_one_right : ∀ a : Rˣ, c a 1 = 0
  /-- The Steinberg relation: complementary units pair to zero. -/
  map_add_eq_one : ∀ a b : Rˣ, (a : R) + b = 1 → c a b = 0

namespace IsSteinbergPairing

section Semiring

variable {R : Type u} [Semiring R] {A : Type v} [AddMonoid A]

/-- The zero pairing is a Steinberg pairing. -/
theorem zero : IsSteinbergPairing (fun _ _ : Rˣ ↦ (0 : A)) where
  map_mul_left _ _ _ := (add_zero 0).symm
  map_mul_right _ _ _ := (add_zero 0).symm
  map_one_left _ := rfl
  map_one_right _ := rfl
  map_add_eq_one _ _ _ := rfl

/-- Postcomposing a Steinberg pairing with an additive monoid homomorphism yields a Steinberg
pairing. -/
theorem comp_addMonoidHom {B : Type w} [AddMonoid B] {c : Rˣ → Rˣ → A}
    (hc : IsSteinbergPairing c) (f : A →+ B) :
    IsSteinbergPairing (fun a b ↦ f (c a b)) where
  map_mul_left a₁ a₂ b := by rw [hc.map_mul_left, map_add]
  map_mul_right a b₁ b₂ := by rw [hc.map_mul_right, map_add]
  map_one_left b := by rw [hc.map_one_left, map_zero]
  map_one_right a := by rw [hc.map_one_right, map_zero]
  map_add_eq_one a b h := by rw [hc.map_add_eq_one a b h, map_zero]

/-- Pulling back a Steinberg pairing along a ring homomorphism yields a Steinberg pairing. -/
theorem comp_ringHom {S : Type w} [Semiring S] {c : Sˣ → Sˣ → A}
    (hc : IsSteinbergPairing c) (f : R →+* S) :
    IsSteinbergPairing
      (fun a b : Rˣ ↦ c (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)) where
  map_mul_left a₁ a₂ b := by rw [map_mul, hc.map_mul_left]
  map_mul_right a b₁ b₂ := by rw [map_mul, hc.map_mul_right]
  map_one_left b := by rw [map_one, hc.map_one_left]
  map_one_right a := by rw [map_one, hc.map_one_right]
  map_add_eq_one a b h := hc.map_add_eq_one _ _ (by simp [← map_add, h])

end Semiring

section Ring

variable {R : Type u} [Ring R] {A : Type v} [AddMonoid A] {c : Rˣ → Rˣ → A}

/-- Pairing with `-1` on the right gives a `2`-torsion value. -/
theorem two_nsmul_map_neg_one_right (hc : IsSteinbergPairing c) (a : Rˣ) :
    2 • c a (-1) = 0 := by
  rw [two_nsmul, ← hc.map_mul_right, neg_mul_neg, one_mul, hc.map_one_right]

end Ring

section AddGroup

variable {R : Type u} [Semiring R] {A : Type v} [AddGroup A] {c : Rˣ → Rˣ → A}

/-- Inverting the first argument of a Steinberg pairing negates its value. -/
theorem map_inv_left (hc : IsSteinbergPairing c) (a b : Rˣ) : c a⁻¹ b = -c a b :=
  eq_neg_of_add_eq_zero_left (by rw [← hc.map_mul_left, inv_mul_cancel, hc.map_one_left])

/-- Inverting the second argument of a Steinberg pairing negates its value. -/
theorem map_inv_right (hc : IsSteinbergPairing c) (a b : Rˣ) : c a b⁻¹ = -c a b :=
  eq_neg_of_add_eq_zero_left (by rw [← hc.map_mul_right, inv_mul_cancel, hc.map_one_right])

/-- Raising the first argument to a natural power scales the pairing. -/
theorem map_pow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) :
    c (a ^ n) b = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_left]
  | succ n ih => rw [pow_succ, hc.map_mul_left, ih, succ_nsmul]

/-- Raising the second argument to a natural power scales the pairing. -/
theorem map_pow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) :
    c a (b ^ n) = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_right]
  | succ n ih => rw [pow_succ, hc.map_mul_right, ih, succ_nsmul]

/-- Raising the first argument to an integer power scales the pairing. -/
theorem map_zpow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c (a ^ n) b = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_left a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_left, hc.map_pow_left, negSucc_zsmul]

/-- Raising the second argument to an integer power scales the pairing. -/
theorem map_zpow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c a (b ^ n) = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_right a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_right, hc.map_pow_right, negSucc_zsmul]

end AddGroup

section Field

variable {F : Type u} [Field F] {A : Type v} [AddGroup A] {c : Fˣ → Fˣ → A}

/-- **Steinberg identity `c(a, -a) = 0`.** For any unit `a` of a field, a Steinberg pairing kills
`(a, -a)`. -/
theorem map_neg_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a (-a) = 0 := by
  by_cases ha : a = 1
  · subst ha; exact hc.map_one_left _
  · let u : Fˣ := Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr fun h ↦ ha (Units.ext h.symm))
    let v : Fˣ := Units.mk0 (1 - ((a⁻¹ : Fˣ) : F))
      (sub_ne_zero.mpr fun h ↦ ha (inv_eq_one.mp (Units.ext h.symm)))
    -- The complementary units satisfy `u = (-a) * v`, since `(-a) * (1 - a⁻¹) = 1 - a`.
    have huv : u = -a * v := Units.ext (by
      simp only [u, v, Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]
      rw [mul_sub, mul_one, neg_mul, mul_inv_cancel₀ (Units.ne_zero a), sub_neg_eq_add, add_comm,
        sub_eq_add_neg])
    have hcu : c a u = 0 := hc.map_add_eq_one a u (by simp [u])
    have hcv : c a v = 0 := neg_eq_zero.mp <| by
      rw [← hc.map_inv_left]; exact hc.map_add_eq_one a⁻¹ v (by simp [v])
    rwa [huv, hc.map_mul_right, hcv, add_zero] at hcu

/-- For any unit `a` of a field, a Steinberg pairing kills `(-a, a)`. -/
theorem map_neg_self_left (hc : IsSteinbergPairing c) (a : Fˣ) : c (-a) a = 0 := by
  simpa only [neg_neg] using hc.map_neg_self (-a)

/-- **Skew-symmetry of Steinberg pairings.** Over a field, swapping the two arguments negates the
value of any Steinberg pairing. -/
theorem map_swap (hc : IsSteinbergPairing c) (a b : Fˣ) : c a b = -c b a := by
  have h : c a b + c b a = 0 := by
    calc c a b + c b a
        = (c a (-a) + c a b) + (c b a + c b (-b)) := by
          rw [hc.map_neg_self, hc.map_neg_self, zero_add, add_zero]
      _ = c a (-a * b) + c b (a * -b) := by
          rw [← hc.map_mul_right, ← hc.map_mul_right]
      _ = c a (-(a * b)) + c b (-(a * b)) := by
          rw [neg_mul, mul_neg]
      _ = c (a * b) (-(a * b)) := (hc.map_mul_left a b _).symm
      _ = 0 := hc.map_neg_self (a * b)
  exact eq_neg_of_add_eq_zero_left h

/-- **Diagonal identity `c(a, a) = c(a, -1)`.** Over a field, pairing a unit with itself equals
pairing it with `-1`. -/
theorem map_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a a = c a (-1) := by
  have hneg : c a (-1) + c a a = 0 := by
    rw [← hc.map_mul_right, neg_one_mul, hc.map_neg_self]
  have htwo := hc.two_nsmul_map_neg_one_right a
  rw [two_nsmul] at htwo
  exact add_left_cancel (hneg.trans htwo.symm)

/-- The diagonal value `c(a, a)` of a Steinberg pairing on a field is `2`-torsion. -/
theorem two_nsmul_map_self (hc : IsSteinbergPairing c) (a : Fˣ) : 2 • c a a = 0 := by
  rw [hc.map_self, hc.two_nsmul_map_neg_one_right]

/-- Pairing `-1` on the left equals pairing `-1` on the right. -/
theorem map_neg_one_left (hc : IsSteinbergPairing c) (a : Fˣ) : c (-1) a = c a (-1) := by
  have htwo := hc.two_nsmul_map_neg_one_right a
  rw [two_nsmul] at htwo
  rw [hc.map_swap, ← eq_neg_of_add_eq_zero_left htwo]

/-- In characteristic `2`, every Steinberg pairing is alternating: `c(a, a) = 0`. -/
theorem map_self_of_charTwo [CharP F 2] (hc : IsSteinbergPairing c) (a : Fˣ) : c a a = 0 := by
  have hneg : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [hc.map_self, hneg, hc.map_one_right]

end Field

end IsSteinbergPairing

section SymbolGroup

variable (R : Type u) [CommSemiring R]

/-- The `ℤ`-submodule of `Additive Rˣ ⊗[ℤ] Additive Rˣ` spanned by the Steinberg relations
`a ⊗ b` with `(a : R) + b = 1`. -/
def steinbergRelations : Submodule ℤ (Additive Rˣ ⊗[ℤ] Additive Rˣ) :=
  Submodule.span ℤ {x | ∃ a b : Rˣ, (a : R) + b = 1 ∧ x = Additive.ofMul a ⊗ₜ Additive.ofMul b}

/-- Unfolding lemma for `steinbergRelations R`. -/
theorem steinbergRelations_eq_span :
    steinbergRelations R =
      Submodule.span ℤ
        {x | ∃ a b : Rˣ, (a : R) + b = 1 ∧ x = Additive.ofMul a ⊗ₜ Additive.ofMul b} := by
  rfl

/-- The degree-two symbol group `(Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R`, the
universal target of Steinberg pairings on `Rˣ`; it is canonically isomorphic to `K₂ᴹ(R)`. -/
abbrev SymbolGroup : Type u := (Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R

variable {R}

/-- The universal symbol `{a, b}` in `SymbolGroup R`, the quotient class of `a ⊗ b`. -/
def symbol (a b : Rˣ) : SymbolGroup R :=
  Submodule.Quotient.mk (Additive.ofMul a ⊗ₜ Additive.ofMul b)

/-- Unfolding lemma expressing `symbol a b` as the quotient class of `ofMul a ⊗ₜ ofMul b`. -/
theorem symbol_def (a b : Rˣ) :
    symbol a b = Submodule.Quotient.mk (Additive.ofMul a ⊗ₜ Additive.ofMul b) := by
  rfl

/-- `TauCeti.symbol` is a Steinberg pairing. -/
theorem isSteinbergPairing_symbol : IsSteinbergPairing (symbol (R := R)) where
  map_mul_left a₁ a₂ b := by
    simp only [symbol_def, ofMul_mul, TensorProduct.add_tmul, Submodule.Quotient.mk_add]
  map_mul_right a b₁ b₂ := by
    simp only [symbol_def, ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]
  map_one_left b := by simp [symbol_def]
  map_one_right a := by simp [symbol_def]
  map_add_eq_one a b h :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨a, b, h, rfl⟩)

/-- Multiplicativity of `symbol` in the first entry. -/
theorem symbol_mul_left (a₁ a₂ b : Rˣ) : symbol (a₁ * a₂) b = symbol a₁ b + symbol a₂ b :=
  isSteinbergPairing_symbol.map_mul_left a₁ a₂ b

/-- Multiplicativity of `symbol` in the second entry. -/
theorem symbol_mul_right (a b₁ b₂ : Rˣ) : symbol a (b₁ * b₂) = symbol a b₁ + symbol a b₂ :=
  isSteinbergPairing_symbol.map_mul_right a b₁ b₂

/-- The Steinberg relation for `symbol`: complementary units give zero. -/
theorem symbol_add_eq_one {a b : Rˣ} (h : (a : R) + b = 1) : symbol a b = 0 :=
  isSteinbergPairing_symbol.map_add_eq_one a b h

/-- The symbol `{1, b}` vanishes. -/
@[simp]
theorem symbol_one_left (b : Rˣ) : symbol 1 b = 0 :=
  isSteinbergPairing_symbol.map_one_left b

/-- The symbol `{a, 1}` vanishes. -/
@[simp]
theorem symbol_one_right (a : Rˣ) : symbol a 1 = 0 :=
  isSteinbergPairing_symbol.map_one_right a

/-- Inverting the first entry negates the symbol. -/
@[simp]
theorem symbol_inv_left (a b : Rˣ) : symbol a⁻¹ b = -symbol a b :=
  isSteinbergPairing_symbol.map_inv_left a b

/-- Inverting the second entry negates the symbol. -/
@[simp]
theorem symbol_inv_right (a b : Rˣ) : symbol a b⁻¹ = -symbol a b :=
  isSteinbergPairing_symbol.map_inv_right a b

/-- Raising the first entry to a natural power scales the symbol. -/
theorem symbol_pow_left (a b : Rˣ) (n : ℕ) : symbol (a ^ n) b = n • symbol a b :=
  isSteinbergPairing_symbol.map_pow_left a b n

/-- Raising the second entry to a natural power scales the symbol. -/
theorem symbol_pow_right (a b : Rˣ) (n : ℕ) : symbol a (b ^ n) = n • symbol a b :=
  isSteinbergPairing_symbol.map_pow_right a b n

/-- Raising the first entry to an integer power scales the symbol. -/
theorem symbol_zpow_left (a b : Rˣ) (n : ℤ) : symbol (a ^ n) b = n • symbol a b :=
  isSteinbergPairing_symbol.map_zpow_left a b n

/-- Raising the second entry to an integer power scales the symbol. -/
theorem symbol_zpow_right (a b : Rˣ) (n : ℤ) : symbol a (b ^ n) = n • symbol a b :=
  isSteinbergPairing_symbol.map_zpow_right a b n

section FieldSymbols

variable {F : Type u} [Field F]

/-- Over a field, `{a, -a} = 0`. -/
@[simp]
theorem symbol_neg_self (a : Fˣ) : symbol a (-a) = 0 :=
  isSteinbergPairing_symbol.map_neg_self a

/-- Over a field, `{-a, a} = 0`. -/
@[simp]
theorem symbol_neg_self_left (a : Fˣ) : symbol (-a) a = 0 :=
  isSteinbergPairing_symbol.map_neg_self_left a

/-- Over a field, symbols are skew-symmetric: `{a, b} = -{b, a}`. -/
theorem symbol_swap (a b : Fˣ) : symbol a b = -symbol b a :=
  isSteinbergPairing_symbol.map_swap a b

/-- Over a field, `{a, a} = {a, -1}`. -/
theorem symbol_self (a : Fˣ) : symbol a a = symbol a (-1) :=
  isSteinbergPairing_symbol.map_self a

/-- Over a field, `2 • {a, a} = 0`. -/
theorem two_nsmul_symbol_self (a : Fˣ) : 2 • symbol a a = 0 :=
  isSteinbergPairing_symbol.two_nsmul_map_self a

/-- Over a field of characteristic `2`, `{a, a} = 0`. -/
@[simp]
theorem symbol_self_of_charTwo [CharP F 2] (a : Fˣ) : symbol a a = 0 :=
  isSteinbergPairing_symbol.map_self_of_charTwo a

end FieldSymbols

namespace SymbolGroup

/-- Induction principle for `SymbolGroup R`: it is additively generated by symbols `symbol a b`. -/
@[elab_as_elim]
theorem induction_on {P : SymbolGroup R → Prop} (x : SymbolGroup R)
    (symbol : ∀ a b : Rˣ, P (symbol a b))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using Submodule.Quotient.induction_on with | _ t =>
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact symbol (Additive.toMul a) (Additive.toMul b)
  | add x y hx hy => simpa using add _ _ hx hy

/-- Two `ℤ`-linear maps out of `SymbolGroup R` agree if they agree on all symbols. -/
theorem linearMap_ext {A : Type v} [AddCommGroup A] {f g : SymbolGroup R →ₗ[ℤ] A}
    (h : ∀ a b : Rˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using SymbolGroup.induction_on with
  | symbol a b => exact h a b
  | add x y hx hy => simp [hx, hy]

/-- Two additive homomorphisms out of `SymbolGroup R` agree if they agree on all symbols. -/
theorem addMonoidHom_ext {A : Type v} [AddCommGroup A] {f g : SymbolGroup R →+ A}
    (h : ∀ a b : Rˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  refine AddMonoidHom.ext fun x ↦ ?_
  induction x using SymbolGroup.induction_on with
  | symbol a b => exact h a b
  | add x y hx hy => simp [hx, hy]

/-- The `ℤ`-bilinear map on `Additive Rˣ` associated to a Steinberg pairing. -/
private def pairingBilin {A : Type v} [AddCommGroup A] (c : Rˣ → Rˣ → A)
    (hc : IsSteinbergPairing c) : Additive Rˣ →ₗ[ℤ] Additive Rˣ →ₗ[ℤ] A :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun a ↦ AddMonoidHom.toIntLinearMap
        { toFun := fun b ↦ c (Additive.toMul a) (Additive.toMul b)
          map_zero' := hc.map_one_right _
          map_add' := fun _ _ ↦ hc.map_mul_right _ _ _ }
      map_zero' := LinearMap.ext fun _ ↦ hc.map_one_left _
      map_add' := fun _ _ ↦ LinearMap.ext fun _ ↦ hc.map_mul_left _ _ _ }

/-- **Universal property of `SymbolGroup R`.** Any Steinberg pairing `c : Rˣ → Rˣ → A` into an
abelian group factors uniquely through a `ℤ`-linear map `SymbolGroup R →ₗ[ℤ] A`. -/
noncomputable def lift {A : Type v} [AddCommGroup A] (c : Rˣ → Rˣ → A)
    (hc : IsSteinbergPairing c) : SymbolGroup R →ₗ[ℤ] A :=
  Submodule.liftQ (steinbergRelations R) (TensorProduct.lift (pairingBilin c hc)) (by
    rw [steinbergRelations, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    exact hc.map_add_eq_one a b hab)

/-- Evaluating `SymbolGroup.lift c hc` on `symbol a b` recovers `c a b`. -/
@[simp]
theorem lift_symbol {A : Type v} [AddCommGroup A] (c : Rˣ → Rˣ → A)
    (hc : IsSteinbergPairing c) (a b : Rˣ) :
    lift c hc (symbol a b) = c a b := by
  rw [symbol_def]
  exact (Submodule.liftQ_apply (steinbergRelations R) (TensorProduct.lift (pairingBilin c hc))
    (Additive.ofMul a ⊗ₜ Additive.ofMul b)).trans
    (TensorProduct.lift.tmul (f' := pairingBilin c hc) (Additive.ofMul a) (Additive.ofMul b))

/-- Additive homomorphisms `SymbolGroup R →+ A` are in canonical bijection with Steinberg pairings
`Rˣ → Rˣ → A`. -/
noncomputable def liftEquiv {A : Type v} [AddCommGroup A] :
    (SymbolGroup R →+ A) ≃ {c : Rˣ → Rˣ → A // IsSteinbergPairing c} where
  toFun f := ⟨fun a b ↦ f (symbol a b), isSteinbergPairing_symbol.comp_addMonoidHom f⟩
  invFun c := (lift c.val c.property).toAddMonoidHom
  left_inv f := addMonoidHom_ext fun a b ↦
    lift_symbol (fun a b ↦ f (symbol a b)) (isSteinbergPairing_symbol.comp_addMonoidHom f) a b
  right_inv c := Subtype.ext (funext₂ fun a b ↦ lift_symbol c.val c.property a b)

/-- Evaluating `liftEquiv f` on `(a, b)` returns `f (symbol a b)`. -/
@[simp]
theorem liftEquiv_apply {A : Type v} [AddCommGroup A] (f : SymbolGroup R →+ A) (a b : Rˣ) :
    (liftEquiv f).val a b = f (symbol a b) := by
  rfl

/-- Evaluating the inverse of `liftEquiv` on a symbol returns the pairing value. -/
@[simp]
theorem liftEquiv_symm_symbol {A : Type v} [AddCommGroup A]
    (c : {c : Rˣ → Rˣ → A // IsSteinbergPairing c}) (a b : Rˣ) :
    liftEquiv.symm c (symbol a b) = c.val a b :=
  lift_symbol c.val c.property a b

/-- Functoriality of `SymbolGroup`: a ring homomorphism `f : R →+* S` induces a `ℤ`-linear map
`SymbolGroup R →ₗ[ℤ] SymbolGroup S` sending `{a, b}` to `{f(a), f(b)}`. -/
noncomputable def map {S : Type w} [CommSemiring S] (f : R →+* S) :
    SymbolGroup R →ₗ[ℤ] SymbolGroup S :=
  lift (fun a b ↦ symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b))
    (isSteinbergPairing_symbol.comp_ringHom f)

/-- `SymbolGroup.map f` sends `{a, b}` to `{f(a), f(b)}`. -/
@[simp]
theorem map_symbol {S : Type w} [CommSemiring S] (f : R →+* S) (a b : Rˣ) :
    map f (symbol a b) = symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) :=
  lift_symbol _ _ a b

/-- The identity ring homomorphism induces the identity on `SymbolGroup`. -/
@[simp]
theorem map_id : map (RingHom.id R) = LinearMap.id :=
  linearMap_ext fun a b ↦ by simp

/-- `SymbolGroup.map` respects composition of ring homomorphisms. -/
theorem map_comp {S : Type v} {T : Type w} [CommSemiring S] [CommSemiring T]
    (g : S →+* T) (f : R →+* S) :
    map (g.comp f) = (map g).comp (map f) :=
  linearMap_ext fun a b ↦ by
    simp only [map_symbol, LinearMap.comp_apply]
    rfl

end SymbolGroup

end SymbolGroup

end TauCeti
