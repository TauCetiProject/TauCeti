/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.FieldTheory.MilnorK.SteinbergPairing

/-!
# The universal degree-two symbol group

This file defines `TauCeti.steinbergRelations`, `TauCeti.SymbolGroup`, and
`TauCeti.SymbolGroup.symbol`, establishes the universal property identifying `ℤ`-linear maps out
of `SymbolGroup R` with Steinberg pairings on `R`, develops functoriality and field identities, and
proves that `SymbolGroup F` is trivial for every finite field `F`.

## Main definitions

* `TauCeti.steinbergRelations`: the `ℤ`-submodule of `Additive Rˣ ⊗[ℤ] Additive Rˣ` spanned by
  `Additive.ofMul a ⊗ₜ Additive.ofMul b` with `(a : R) + b = 1`.
* `TauCeti.SymbolGroup`: the quotient `(Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R`.
* `TauCeti.SymbolGroup.symbol`: the universal symbol `{a, b}` in `SymbolGroup R`.
* `TauCeti.SymbolGroup.lift` and `TauCeti.SymbolGroup.liftEquiv`: universal property of
  `SymbolGroup R` with respect to Steinberg pairings.
* `TauCeti.SymbolGroup.map`: functorial `ℤ`-linear map induced by a ring homomorphism.

## Main results

* `TauCeti.SymbolGroup.isSteinbergPairing_symbol`: `SymbolGroup.symbol` is a Steinberg pairing.
* `TauCeti.SymbolGroup.subsingleton_of_finite`: `SymbolGroup F` is subsingleton for any finite
  field `F`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.6.1, Corollary III.6.1.1.
-/

public section

namespace TauCeti

open scoped TensorProduct

section Defs

variable (R : Type u) [CommSemiring R]

/-- The span of the tensors `a ⊗ b` with `a + b = 1` in `Additive Rˣ ⊗[ℤ] Additive Rˣ`. -/
def steinbergRelations : Submodule ℤ (Additive Rˣ ⊗[ℤ] Additive Rˣ) :=
  Submodule.span ℤ {x | ∃ a b : Rˣ, (a : R) + b = 1 ∧ x = Additive.ofMul a ⊗ₜ Additive.ofMul b}

/-- Definitional unfolding of `steinbergRelations`. -/
theorem steinbergRelations_def :
    steinbergRelations R = Submodule.span ℤ
      {x | ∃ a b : Rˣ, (a : R) + b = 1 ∧ x = Additive.ofMul a ⊗ₜ Additive.ofMul b} := (rfl)

/-- The degree-two symbol group `(Rˣ ⊗ Rˣ) / ⟨a ⊗ b : a + b = 1⟩`, the universal target of
Steinberg pairings on `R`. -/
abbrev SymbolGroup : Type u := (Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R

end Defs

namespace SymbolGroup

section Basic

variable {R : Type u} [CommSemiring R]

/-- The class `{a, b}` of `Additive.ofMul a ⊗ₜ Additive.ofMul b` in `SymbolGroup R`. -/
def symbol (a b : Rˣ) : SymbolGroup R :=
  Submodule.Quotient.mk (Additive.ofMul a ⊗ₜ Additive.ofMul b)

/-- Definitional unfolding of `SymbolGroup.symbol`. -/
theorem symbol_def (a b : Rˣ) :
    symbol a b = Submodule.Quotient.mk (Additive.ofMul a ⊗ₜ Additive.ofMul b) := (rfl)

/-- `symbol` is multiplicative in the left unit argument. -/
theorem symbol_mul_left (a₁ a₂ b : Rˣ) : symbol (a₁ * a₂) b = symbol a₁ b + symbol a₂ b := by
  simp only [symbol_def, ofMul_mul, TensorProduct.add_tmul, Submodule.Quotient.mk_add]

/-- `symbol` is multiplicative in the right unit argument. -/
theorem symbol_mul_right (a b₁ b₂ : Rˣ) : symbol a (b₁ * b₂) = symbol a b₁ + symbol a b₂ := by
  simp only [symbol_def, ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

/-- The Steinberg relation holds for `symbol`. -/
theorem symbol_eq_zero_of_add_eq_one {a b : Rˣ} (h : (a : R) + b = 1) : symbol a b = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr <| Submodule.subset_span ⟨a, b, h, rfl⟩

/-- `symbol` is a Steinberg pairing on `R`. -/
theorem isSteinbergPairing_symbol : IsSteinbergPairing (symbol (R := R)) where
  map_mul_left := symbol_mul_left
  map_mul_right := symbol_mul_right
  steinberg := symbol_eq_zero_of_add_eq_one

/-- `symbol 1 b = 0`. -/
@[simp]
theorem symbol_one_left (b : Rˣ) : symbol (1 : Rˣ) b = 0 :=
  isSteinbergPairing_symbol.map_one_left b

/-- `symbol a 1 = 0`. -/
@[simp]
theorem symbol_one_right (a : Rˣ) : symbol a (1 : Rˣ) = 0 :=
  isSteinbergPairing_symbol.map_one_right a

/-- `symbol a⁻¹ b = -symbol a b`. -/
theorem symbol_inv_left (a b : Rˣ) : symbol a⁻¹ b = -symbol a b :=
  isSteinbergPairing_symbol.map_inv_left a b

/-- `symbol a b⁻¹ = -symbol a b`. -/
theorem symbol_inv_right (a b : Rˣ) : symbol a b⁻¹ = -symbol a b :=
  isSteinbergPairing_symbol.map_inv_right a b

/-- `symbol (a ^ n) b = n • symbol a b`. -/
theorem symbol_pow_left (a b : Rˣ) (n : ℕ) : symbol (a ^ n) b = n • symbol a b :=
  isSteinbergPairing_symbol.map_pow_left a b n

/-- `symbol a (b ^ n) = n • symbol a b`. -/
theorem symbol_pow_right (a b : Rˣ) (n : ℕ) : symbol a (b ^ n) = n • symbol a b :=
  isSteinbergPairing_symbol.map_pow_right a b n

/-- `symbol (a ^ n) b = n • symbol a b` for `n : ℤ`. -/
theorem symbol_zpow_left (a b : Rˣ) (n : ℤ) : symbol (a ^ n) b = n • symbol a b :=
  isSteinbergPairing_symbol.map_zpow_left a b n

/-- `symbol a (b ^ n) = n • symbol a b` for `n : ℤ`. -/
theorem symbol_zpow_right (a b : Rˣ) (n : ℤ) : symbol a (b ^ n) = n • symbol a b :=
  isSteinbergPairing_symbol.map_zpow_right a b n

end Basic

section Universal

variable {R : Type u} [CommSemiring R] {A : Type*} [AddCommGroup A]

/-- Induction principle for `SymbolGroup R` generated by symbols `{a, b}`. -/
@[elab_as_elim]
theorem inductionOn {motive : SymbolGroup R → Prop} (x : SymbolGroup R)
    (symbol : ∀ a b : Rˣ, motive (symbol a b))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  induction x using Submodule.Quotient.induction_on with | _ t =>
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    simpa only [SymbolGroup.symbol_def, ofMul_toMul] using
      symbol (Additive.toMul u) (Additive.toMul v)
  | add _ _ ht₁ ht₂ => rw [Submodule.Quotient.mk_add]; exact add _ _ ht₁ ht₂

/-- Two `ℤ`-linear maps out of `SymbolGroup R` agreeing on every symbol are equal. -/
@[ext]
theorem linearMap_ext {f g : SymbolGroup R →ₗ[ℤ] A}
    (h : ∀ a b : Rˣ, f (symbol a b) = g (symbol a b)) : f = g :=
  LinearMap.ext fun x ↦ by
    induction x using SymbolGroup.inductionOn with
    | symbol a b => exact h a b
    | add _ _ hx hy => rw [map_add, map_add, hx, hy]

/-- Two additive homomorphisms out of `SymbolGroup R` agreeing on every symbol are equal. -/
theorem addMonoidHom_ext {f g : SymbolGroup R →+ A}
    (h : ∀ a b : Rˣ, f (symbol a b) = g (symbol a b)) : f = g :=
  AddMonoidHom.ext fun x ↦ by
    induction x using SymbolGroup.inductionOn with
    | symbol a b => exact h a b
    | add _ _ hx hy => rw [map_add, map_add, hx, hy]

private def liftB (c : Rˣ → Rˣ → A) (hc : IsSteinbergPairing c) :
    Additive Rˣ →ₗ[ℤ] Additive Rˣ →ₗ[ℤ] A where
  toFun u :=
    (AddMonoidHom.mk' (fun v : Additive Rˣ ↦ c (Additive.toMul u) (Additive.toMul v))
      fun v₁ v₂ ↦ by simp only [toMul_add, hc.map_mul_right]).toIntLinearMap
  map_add' u₁ u₂ := LinearMap.ext fun v ↦ hc.map_mul_left _ _ _
  map_smul' k u := LinearMap.ext fun v ↦ by
    simpa [toMul_zsmul] using hc.map_zpow_left (Additive.toMul u) (Additive.toMul v) k

/-- Lift a Steinberg pairing `c : Rˣ → Rˣ → A` to a `ℤ`-linear map `SymbolGroup R →ₗ[ℤ] A`. -/
def lift (c : Rˣ → Rˣ → A) (hc : IsSteinbergPairing c) : SymbolGroup R →ₗ[ℤ] A :=
  Submodule.liftQ (steinbergRelations R)
    (TensorProduct.lift (liftB c hc)).toAddMonoidHom.toIntLinearMap <| by
    rw [steinbergRelations_def, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap,
      LinearMap.toAddMonoidHom_coe, TensorProduct.lift.tmul]
    simpa [liftB] using hc.steinberg hab

/-- On generators, `SymbolGroup.lift c hc` evaluates `c`. -/
@[simp]
theorem lift_symbol (c : Rˣ → Rˣ → A) (hc : IsSteinbergPairing c) (a b : Rˣ) :
    lift c hc (symbol a b) = c a b := by
  rw [lift, symbol_def, Submodule.liftQ_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.toAddMonoidHom_coe, TensorProduct.lift.tmul]
  simp [liftB]

/-- The universal equivalence between `ℤ`-linear maps `SymbolGroup R →ₗ[ℤ] A` and Steinberg
pairings `Rˣ → Rˣ → A`. -/
def liftEquiv : (SymbolGroup R →ₗ[ℤ] A) ≃ {c : Rˣ → Rˣ → A // IsSteinbergPairing c} where
  toFun f :=
    ⟨fun a b ↦ f (symbol a b), isSteinbergPairing_symbol.comp_addMonoidHom f.toAddMonoidHom⟩
  invFun c := lift c.val c.property
  left_inv _ := linearMap_ext fun a b ↦ lift_symbol _ _ a b
  right_inv c := Subtype.ext <| funext fun a ↦ funext fun b ↦ lift_symbol c.val c.property a b

end Universal

section Functoriality

variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S] {T : Type w} [CommSemiring T]

/-- Functorial `ℤ`-linear map `SymbolGroup R →ₗ[ℤ] SymbolGroup S` induced by `f : R →+* S`. -/
def map (f : R →+* S) : SymbolGroup R →ₗ[ℤ] SymbolGroup S :=
  lift (fun a b ↦ symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b))
    (isSteinbergPairing_symbol.comp_ringHom f)

/-- `SymbolGroup.map f` sends `{a, b}` to `{f a, f b}`. -/
@[simp]
theorem map_symbol (f : R →+* S) (a b : Rˣ) :
    map f (symbol a b) = symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) :=
  lift_symbol _ _ a b

/-- `SymbolGroup.map` preserves the identity ring homomorphism. -/
@[simp]
theorem map_id : map (RingHom.id R) = LinearMap.id := linearMap_ext fun _ _ ↦ by simp

/-- `SymbolGroup.map` preserves composition of ring homomorphisms. -/
theorem map_comp (g : S →+* T) (f : R →+* S) : map (g.comp f) = (map g).comp (map f) :=
  linearMap_ext fun a b ↦ by simp only [map_symbol, LinearMap.comp_apply]; congr 1

end Functoriality

section Field

variable {F : Type u} [Field F]

/-- Over a field, `symbol a (-a) = 0`. -/
theorem symbol_neg_self (a : Fˣ) : symbol a (-a) = 0 := isSteinbergPairing_symbol.map_neg_self a

/-- Over a field, `symbol a a = symbol a (-1)`. -/
theorem symbol_self (a : Fˣ) : symbol a a = symbol a (-1 : Fˣ) :=
  isSteinbergPairing_symbol.map_self a

/-- Over a field, `symbol` is skew-symmetric. -/
theorem symbol_anticomm (a b : Fˣ) : symbol a b = -symbol b a :=
  isSteinbergPairing_symbol.map_anticomm a b

/-- Over a field, `2 • symbol a a = 0`. -/
theorem two_nsmul_symbol_self (a : Fˣ) : 2 • symbol a a = 0 :=
  isSteinbergPairing_symbol.two_nsmul_map_self a

/-- In characteristic `2`, `symbol a a = 0`. -/
theorem symbol_self_of_charTwo [CharP F 2] (a : Fˣ) : symbol a a = 0 :=
  isSteinbergPairing_symbol.map_self_of_charTwo a

/-- For a field with cyclic unit group and positive characteristic, `SymbolGroup F` is trivial. -/
theorem subsingleton_of_isCyclic_of_ringChar_ne_zero [IsCyclic Fˣ] (hchar : ringChar F ≠ 0) :
    Subsingleton (SymbolGroup F) :=
  subsingleton_iff_forall_eq 0 |>.mpr fun x ↦ by
    induction x using SymbolGroup.inductionOn with
    | symbol a b =>
      exact isSteinbergPairing_symbol.eq_zero_of_isCyclic_of_ringChar_ne_zero hchar a b
    | add _ _ hx hy => rw [hx, hy, add_zero]

/-- For every finite field `F`, `SymbolGroup F` vanishes. -/
theorem subsingleton_of_finite [Finite F] : Subsingleton (SymbolGroup F) :=
  subsingleton_of_isCyclic_of_ringChar_ne_zero (CharP.ringChar_ne_zero_of_finite F)

end Field

end SymbolGroup

end TauCeti
