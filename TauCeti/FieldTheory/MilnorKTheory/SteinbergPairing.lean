/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Bilinear Steinberg pairings and the degree-two symbol group

A **Steinberg pairing** (`TauCeti.IsSteinbergPairing`) on a semiring `R` with values in an additive
commutative monoid `A` is a bimultiplicative map `c : Rˣ → Rˣ → A` vanishing whenever
`(a : R) + b = 1`. Over a field `F`, every Steinberg pairing into an additive commutative group
satisfies `c a (-a) = 0`, `c a b = -c b a`, `c a a = c a (-1)`, and `2 • c a a = 0`, plus
`c a a = 0` in characteristic two.

For any commutative semiring `R`, the quotient `TauCeti.SymbolGroup R` of
`Additive Rˣ ⊗[ℤ] Additive Rˣ` by `TauCeti.steinbergRelations R` is the universal target of
Steinberg pairings (`SymbolGroup.lift`, `liftEquiv`, `liftAddMonoidHomEquiv`) and is functorial
via `SymbolGroup.map`.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §§6.1 and 7.1.
* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*, Ann. Sci.
  École Norm. Sup. (4) **2** (1969), §5.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

/-! ### Bilinear Steinberg pairings -/

/-- A map `c : Rˣ → Rˣ → A` is a **Steinberg pairing** if it is bimultiplicative and vanishes
on pairs of units whose ambient values sum to `1`. -/
structure IsSteinbergPairing {R : Type u} {A : Type v} [Semiring R] [AddCommMonoid A]
    (c : Rˣ → Rˣ → A) : Prop where
  /-- Multiplicativity in the first argument. -/
  map_mul_left (a b d : Rˣ) : c (a * b) d = c a d + c b d
  /-- Multiplicativity in the second argument. -/
  map_mul_right (a b d : Rˣ) : c a (b * d) = c a b + c a d
  /-- The Steinberg relation on pairs of units summing to `1`. -/
  steinberg (a b : Rˣ) : (a : R) + b = 1 → c a b = 0

namespace IsSteinbergPairing

section Semiring

variable {R S A B : Type*} [Semiring R] [Semiring S] [AddCommMonoid A] [AddCommMonoid B]

/-- The zero map is a Steinberg pairing. -/
theorem zero : IsSteinbergPairing (fun _ _ : Rˣ => (0 : A)) where
  map_mul_left _ _ _ := (add_zero 0).symm
  map_mul_right _ _ _ := (add_zero 0).symm
  steinberg _ _ _ := rfl

/-- Post-composing a Steinberg pairing with an additive homomorphism gives a Steinberg pairing. -/
theorem comp_addMonoidHom {c : Rˣ → Rˣ → A} (hc : IsSteinbergPairing c) (f : A →+ B) :
    IsSteinbergPairing (fun a b => f (c a b)) where
  map_mul_left _ _ _ := by rw [hc.map_mul_left, map_add]
  map_mul_right _ _ _ := by rw [hc.map_mul_right, map_add]
  steinberg _ _ h := by rw [hc.steinberg _ _ h, map_zero]

/-- Pulling back a Steinberg pairing along a ring homomorphism gives a Steinberg pairing. -/
theorem comp_ringHom {c : Sˣ → Sˣ → A} (hc : IsSteinbergPairing c) (f : R →+* S) :
    IsSteinbergPairing (fun a b => c (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)) where
  map_mul_left _ _ _ := by rw [map_mul, hc.map_mul_left]
  map_mul_right _ _ _ := by rw [map_mul, hc.map_mul_right]
  steinberg _ _ h := hc.steinberg _ _ (by simp [← map_add, h])

variable [IsLeftCancelAdd A] {c : Rˣ → Rˣ → A}

theorem map_one_left (hc : IsSteinbergPairing c) (b : Rˣ) : c 1 b = 0 :=
  add_left_cancel ((hc.map_mul_left 1 1 b).symm.trans (by simp))
theorem map_one_right (hc : IsSteinbergPairing c) (a : Rˣ) : c a 1 = 0 :=
  add_left_cancel ((hc.map_mul_right a 1 1).symm.trans (by simp))
theorem map_pow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) : c (a ^ n) b = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_left]
  | succ n ih => rw [pow_succ, hc.map_mul_left, ih, succ_nsmul]
theorem map_pow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) : c a (b ^ n) = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_right]
  | succ n ih => rw [pow_succ, hc.map_mul_right, ih, succ_nsmul]

end Semiring

section AddCommGroup

variable {R A : Type*} [Semiring R] [AddCommGroup A] {c : Rˣ → Rˣ → A}

theorem map_inv_left (hc : IsSteinbergPairing c) (a b : Rˣ) : c a⁻¹ b = -c a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← hc.map_mul_left, inv_mul_cancel, hc.map_one_left]
theorem map_inv_right (hc : IsSteinbergPairing c) (a b : Rˣ) : c a b⁻¹ = -c a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← hc.map_mul_right, inv_mul_cancel, hc.map_one_right]
theorem map_zpow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) : c (a ^ n) b = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_left a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_left, hc.map_pow_left, negSucc_zsmul]
theorem map_zpow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c a (b ^ n) = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_right a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_right, hc.map_pow_right, negSucc_zsmul]

end AddCommGroup

/-! ### Integral symbol identities over a field -/

section Field

variable {F A : Type*} [Field F] [AddCommGroup A] {c : Fˣ → Fˣ → A}

/-- **Steinberg's sign identity**: `c(a, -a) = 0` for every unit `a` of a field. -/
theorem map_neg_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a (-a) = 0 := by
  by_cases ha : (a : F) = 1
  · obtain rfl : a = 1 := Units.ext ha
    exact hc.map_one_left (-1)
  · let u : Fˣ := Units.mk0 (1 - a) (sub_ne_zero.mpr (Ne.symm ha))
    let v : Fˣ := (-a)⁻¹ * u
    have hav : (a⁻¹ : Fˣ) + (v : F) = 1 := by
      simp only [v, u, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_mk0]
      rw [inv_neg, neg_mul, mul_sub, mul_one, inv_mul_cancel₀ (Units.ne_zero a), neg_sub,
        add_sub_cancel]
    have h2 : c a v = 0 := neg_eq_zero.mp (hc.map_inv_left a v ▸ hc.steinberg a⁻¹ v hav)
    have huv : (-a) * v = u := by simp [v]
    have h3 : c a (-a) + c a v = 0 := by
      rw [← hc.map_mul_right, huv, hc.steinberg a u (by simp [u])]
    rwa [h2, add_zero] at h3

/-- **Skew-symmetry** of Steinberg pairings over a field: `c(a, b) = -c(b, a)`. -/
theorem map_swap (hc : IsSteinbergPairing c) (a b : Fˣ) : c a b = -c b a := by
  have h := hc.map_neg_self (a * b)
  rw [hc.map_mul_left, ← neg_mul a b, hc.map_mul_right, hc.map_neg_self, zero_add,
    neg_mul a b, ← mul_neg a b, hc.map_mul_right, hc.map_neg_self, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **Diagonal identity** over a field: `c(a, a) = c(a, -1)`. -/
theorem map_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a a = c a (-1) := by
  have haa : (-a) * (-1) = a := by simp
  conv_lhs => arg 2; rw [← haa]
  rw [hc.map_mul_right, hc.map_neg_self, zero_add]

/-- Every diagonal value `c(a, a)` of a Steinberg pairing over a field is `2`-torsion. -/
theorem two_nsmul_map_self (hc : IsSteinbergPairing c) (a : Fˣ) : 2 • c a a = 0 := by
  rw [two_nsmul]; exact add_eq_zero_iff_eq_neg.mpr (hc.map_swap a a)

/-- In characteristic two, every Steinberg pairing is alternating: `c(a, a) = 0`. -/
theorem map_self_eq_zero_of_charTwo [CharP F 2] (hc : IsSteinbergPairing c) (a : Fˣ) :
    c a a = 0 := by
  have hneg1 : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [hc.map_self, hneg1, hc.map_one_right]

end Field

end IsSteinbergPairing

/-! ### Universal degree-two symbol group -/

section SymbolGroup

variable (R : Type u) [CommSemiring R]

/-- The `ℤ`-submodule of `Additive Rˣ ⊗[ℤ] Additive Rˣ` spanned by the Steinberg tensors
`a ⊗ b` with `(a : R) + b = 1`. -/
def steinbergRelations : Submodule ℤ (Additive Rˣ ⊗[ℤ] Additive Rˣ) :=
  Submodule.span ℤ {x | ∃ a b : Rˣ, (a : R) + b = 1 ∧ x = Additive.ofMul a ⊗ₜ Additive.ofMul b}
/-- Unfolding lemma for `TauCeti.steinbergRelations`. -/
theorem steinbergRelations_def : steinbergRelations R = Submodule.span ℤ
    {x | ∃ a b : Rˣ, (a : R) + b = 1 ∧ x = Additive.ofMul a ⊗ₜ Additive.ofMul b} := by rfl

/-- The universal degree-two symbol group
`(Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R` (Weibel, III.6.1 and III.7.1). -/
abbrev SymbolGroup : Type u := (Additive Rˣ ⊗[ℤ] Additive Rˣ) ⧸ steinbergRelations R

variable {R}

/-- The symbol class `{a, b}` of `Additive.ofMul a ⊗ₜ Additive.ofMul b` in `SymbolGroup R`. -/
def symbol (a b : Rˣ) : SymbolGroup R :=
  Submodule.Quotient.mk (Additive.ofMul a ⊗ₜ Additive.ofMul b)
/-- Unfolding lemma for `TauCeti.symbol`. -/
theorem symbol_def (a b : Rˣ) :
    symbol a b = Submodule.Quotient.mk (Additive.ofMul a ⊗ₜ Additive.ofMul b) := by rfl

/-- The canonical pairing `(a, b) ↦ symbol a b` is a Steinberg pairing. -/
theorem isSteinbergPairing_symbol : IsSteinbergPairing (symbol (R := R)) where
  map_mul_left _ _ _ := by simp [symbol_def, TensorProduct.add_tmul]
  map_mul_right _ _ _ := by simp [symbol_def, TensorProduct.tmul_add]
  steinberg a b h := (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨a, b, h, rfl⟩)

theorem symbol_mul_left (a b d : Rˣ) : symbol (a * b) d = symbol a d + symbol b d :=
  isSteinbergPairing_symbol.map_mul_left a b d
theorem symbol_mul_right (a b d : Rˣ) : symbol a (b * d) = symbol a b + symbol a d :=
  isSteinbergPairing_symbol.map_mul_right a b d
theorem symbol_eq_zero_of_add_eq_one {a b : Rˣ} (h : (a : R) + b = 1) : symbol a b = 0 :=
  isSteinbergPairing_symbol.steinberg a b h
@[simp] theorem symbol_one_left (b : Rˣ) : symbol (1 : Rˣ) b = 0 :=
  isSteinbergPairing_symbol.map_one_left b
@[simp] theorem symbol_one_right (a : Rˣ) : symbol a (1 : Rˣ) = 0 :=
  isSteinbergPairing_symbol.map_one_right a
@[simp] theorem symbol_inv_left (a b : Rˣ) : symbol a⁻¹ b = -symbol a b :=
  isSteinbergPairing_symbol.map_inv_left a b
@[simp] theorem symbol_inv_right (a b : Rˣ) : symbol a b⁻¹ = -symbol a b :=
  isSteinbergPairing_symbol.map_inv_right a b
theorem symbol_pow_left (a b : Rˣ) (n : ℕ) : symbol (a ^ n) b = n • symbol a b :=
  isSteinbergPairing_symbol.map_pow_left a b n
theorem symbol_pow_right (a b : Rˣ) (n : ℕ) : symbol a (b ^ n) = n • symbol a b :=
  isSteinbergPairing_symbol.map_pow_right a b n
theorem symbol_zpow_left (a b : Rˣ) (n : ℤ) : symbol (a ^ n) b = n • symbol a b :=
  isSteinbergPairing_symbol.map_zpow_left a b n
theorem symbol_zpow_right (a b : Rˣ) (n : ℤ) : symbol a (b ^ n) = n • symbol a b :=
  isSteinbergPairing_symbol.map_zpow_right a b n

section FieldSymbols
variable {F : Type u} [Field F]
@[simp] theorem symbol_neg_self (a : Fˣ) : symbol a (-a) = 0 :=
  isSteinbergPairing_symbol.map_neg_self a
theorem symbol_swap (a b : Fˣ) : symbol a b = -symbol b a := isSteinbergPairing_symbol.map_swap a b
theorem symbol_self (a : Fˣ) : symbol a a = symbol a (-1) := isSteinbergPairing_symbol.map_self a
theorem two_nsmul_symbol_self (a : Fˣ) : 2 • symbol a a = 0 :=
  isSteinbergPairing_symbol.two_nsmul_map_self a
theorem symbol_self_eq_zero_of_charTwo [CharP F 2] (a : Fˣ) : symbol a a = 0 :=
  isSteinbergPairing_symbol.map_self_eq_zero_of_charTwo a
end FieldSymbols

namespace SymbolGroup

/-- Induction principle on `SymbolGroup R` generated by the symbols `symbol a b`. -/
@[elab_as_elim]
theorem induction_on {P : SymbolGroup R → Prop} (x : SymbolGroup R)
    (symbol : ∀ a b : Rˣ, P (TauCeti.symbol a b)) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using Submodule.Quotient.induction_on with
  | H t =>
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      simpa only [symbol_def, ofMul_toMul] using symbol (Additive.toMul u) (Additive.toMul v)
    | add _ _ h₁ h₂ => simpa only [Submodule.Quotient.mk_add] using add _ _ h₁ h₂

section Universal

variable {A : Type*} [AddCommGroup A]

/-- Two `ℤ`-linear maps out of `SymbolGroup R` agree if they agree on all symbols. -/
@[ext 1100] theorem hom_ext {f g : SymbolGroup R →ₗ[ℤ] A}
    (h : ∀ a b : Rˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  apply Submodule.linearMap_qext; apply TensorProduct.ext'; intro u v
  have huv := h (Additive.toMul u) (Additive.toMul v)
  rwa [symbol_def, ofMul_toMul, ofMul_toMul] at huv

/-- Two additive homomorphisms out of `SymbolGroup R` agree if they agree on all symbols. -/
@[ext 1100] theorem addMonoidHom_ext {f g : SymbolGroup R →+ A}
    (h : ∀ a b : Rˣ, f (symbol a b) = g (symbol a b)) : f = g :=
  AddMonoidHom.toIntLinearMap_injective (hom_ext h)

section Lift
variable (c : Rˣ → Rˣ → A) (hc : IsSteinbergPairing c)

/-- Universal property of `SymbolGroup R`: a Steinberg pairing `c : Rˣ → Rˣ → A` into an
additive commutative group descends to a `ℤ`-linear map `SymbolGroup R →ₗ[ℤ] A`. -/
def lift : SymbolGroup R →ₗ[ℤ] A :=
  let bilin : Additive Rˣ →ₗ[ℤ] Additive Rˣ →ₗ[ℤ] A :=
    AddMonoidHom.toIntLinearMap
      { toFun := fun u => AddMonoidHom.toIntLinearMap
          { toFun := fun v => c (Additive.toMul u) (Additive.toMul v)
            map_zero' := hc.map_one_right _
            map_add' := fun _ _ => hc.map_mul_right _ _ _ }
        map_zero' := LinearMap.ext fun _ => hc.map_one_left _
        map_add' := fun _ _ => LinearMap.ext fun _ => hc.map_mul_left _ _ _ }
  (steinbergRelations R).liftQ (TensorProduct.lift bilin) <| by
    rw [steinbergRelations, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩; exact hc.steinberg a b hab

@[simp] theorem lift_symbol (a b : Rˣ) : lift c hc (symbol a b) = c a b := by rfl
theorem lift_unique (f : SymbolGroup R →ₗ[ℤ] A) (hf : ∀ a b : Rˣ, f (symbol a b) = c a b) :
    f = lift c hc := hom_ext fun a b => (hf a b).trans (lift_symbol c hc a b).symm
theorem lift_toAddMonoidHom_unique (f : SymbolGroup R →+ A)
    (hf : ∀ a b : Rˣ, f (symbol a b) = c a b) : f = (lift c hc).toAddMonoidHom :=
  addMonoidHom_ext fun a b => (hf a b).trans (lift_symbol c hc a b).symm
end Lift

/-- Equivalence between Steinberg pairings `Rˣ → Rˣ → A` and `ℤ`-linear maps
`SymbolGroup R →ₗ[ℤ] A`. -/
def liftEquiv : {c : Rˣ → Rˣ → A // IsSteinbergPairing c} ≃ (SymbolGroup R →ₗ[ℤ] A) where
  toFun c := lift c.1 c.2
  invFun f :=
    ⟨fun a b => f (symbol a b), isSteinbergPairing_symbol.comp_addMonoidHom f.toAddMonoidHom⟩
  left_inv c := Subtype.ext (funext fun a => funext fun b => lift_symbol c.1 c.2 a b)
  right_inv f := (lift_unique _ _ f fun _ _ => rfl).symm

@[simp] theorem liftEquiv_apply (c : {c : Rˣ → Rˣ → A // IsSteinbergPairing c}) :
    liftEquiv c = lift c.1 c.2 := by rfl
@[simp] theorem liftEquiv_symm_apply_val (f : SymbolGroup R →ₗ[ℤ] A) (a b : Rˣ) :
    (liftEquiv.symm f).1 a b = f (symbol a b) := by rfl

/-- Equivalence between Steinberg pairings `Rˣ → Rˣ → A` and additive homomorphisms
`SymbolGroup R →+ A`. -/
def liftAddMonoidHomEquiv : {c : Rˣ → Rˣ → A // IsSteinbergPairing c} ≃ (SymbolGroup R →+ A) where
  toFun c := (lift c.1 c.2).toAddMonoidHom
  invFun f := ⟨fun a b => f (symbol a b), isSteinbergPairing_symbol.comp_addMonoidHom f⟩
  left_inv c := Subtype.ext (funext fun a => funext fun b => lift_symbol c.1 c.2 a b)
  right_inv f := (lift_toAddMonoidHom_unique _ _ f fun _ _ => rfl).symm

@[simp] theorem liftAddMonoidHomEquiv_apply (c : {c : Rˣ → Rˣ → A // IsSteinbergPairing c}) :
    liftAddMonoidHomEquiv c = (lift c.1 c.2).toAddMonoidHom := by rfl
@[simp] theorem liftAddMonoidHomEquiv_symm_apply_val (f : SymbolGroup R →+ A) (a b : Rˣ) :
    (liftAddMonoidHomEquiv.symm f).1 a b = f (symbol a b) := by rfl

end Universal

/-- Functorial map on `SymbolGroup` induced by a ring homomorphism `f : R →+* S`. -/
def map {S : Type*} [CommSemiring S] (f : R →+* S) : SymbolGroup R →ₗ[ℤ] SymbolGroup S :=
  lift (fun a b => symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b))
    (isSteinbergPairing_symbol.comp_ringHom f)

@[simp] theorem map_symbol {S : Type*} [CommSemiring S] (f : R →+* S) (a b : Rˣ) :
    map f (symbol a b) = symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by rfl
@[simp] theorem map_id : map (RingHom.id R) = LinearMap.id := hom_ext fun _ _ => by simp
@[simp] theorem map_comp {S T : Type*} [CommSemiring S] [CommSemiring T] (g : S →+* T)
    (f : R →+* S) : map (g.comp f) = (map g).comp (map f) := hom_ext fun _ _ => rfl

end SymbolGroup

end SymbolGroup

end TauCeti
