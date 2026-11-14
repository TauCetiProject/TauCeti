/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fintype.Fin

/-!
# Exchange polynomials

In cluster algebras with polynomial exchange relations, each mutable direction carries a formal
polynomial `H(T) = ∑_{l=0}^r h_l T^l` of specified positive degree `r` whose constant and leading
coefficients `h_0` and `h_r` are units. Reversal `T^r H(T⁻¹)`, variable dilation `H(κ T)`, and unit
scaling `e H` use only the multiplication of `𝕂`, which is therefore taken to be an arbitrary
`CommMonoidWithZero`. Recording `r` explicitly keeps `h_r` well-defined even when `𝕂` is trivial.

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014 (2014), §2.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  §2.
-/

public section

namespace TauCeti

/-- An *exchange polynomial* over a commutative monoid with zero `𝕂`: a specified positive degree
`r` together with coefficients `h_0, …, h_r ∈ 𝕂` whose endpoint coefficients `h_0` and `h_r` are
units. -/
structure ExchangePolynomial (𝕂 : Type*) [CommMonoidWithZero 𝕂] where
  /-- The formal degree `r` of the exchange polynomial. -/
  degree : ℕ
  /-- The formal degree is strictly positive. -/
  degree_pos : 0 < degree
  /-- The coefficients `h_0, …, h_r` indexed by `Fin (degree + 1)`. -/
  coeff : Fin (degree + 1) → 𝕂
  /-- The constant coefficient `h_0` is a unit. -/
  isUnit_coeff_zero : IsUnit (coeff 0)
  /-- The leading coefficient `h_r` is a unit. -/
  isUnit_coeff_last : IsUnit (coeff (Fin.last degree))

namespace ExchangePolynomial

variable {𝕂 𝕂' 𝕂'' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂'']

@[ext (iff := false)]
theorem ext {H₁ H₂ : ExchangePolynomial 𝕂} (hd : H₁.degree = H₂.degree)
    (hc : ∀ l : Fin (H₁.degree + 1), H₁.coeff l = H₂.coeff (l.cast (congrArg (· + 1) hd))) :
    H₁ = H₂ := by
  obtain ⟨d₁, _, c₁, _, _⟩ := H₁
  obtain ⟨d₂, _, c₂, _, _⟩ := H₂
  dsimp only at hd hc
  subst hd
  congr
  exact funext hc

theorem coeff_eq_of_eq {H₁ H₂ : ExchangePolynomial 𝕂} (h : H₁ = H₂)
    (l : Fin (H₁.degree + 1)) :
    H₁.coeff l = H₂.coeff (l.cast (congrArg (· + 1) (congrArg degree h))) := by
  subst h; rfl

theorem coeff_zero_ne_zero [Nontrivial 𝕂] (H : ExchangePolynomial 𝕂) : H.coeff 0 ≠ 0 :=
  H.isUnit_coeff_zero.ne_zero

/-! ### Reversal, dilation, and scaling -/

/-- The reciprocal polynomial `T^r H(T⁻¹)`, obtained by reversing the coefficient tuple. -/
def reverse (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := H.coeff l.rev
  isUnit_coeff_zero := by simpa using H.isUnit_coeff_last
  isUnit_coeff_last := by simpa using H.isUnit_coeff_zero

@[simp] theorem reverse_degree (H : ExchangePolynomial 𝕂) : H.reverse.degree = H.degree := (rfl)

@[simp]
theorem reverse_coeff (H : ExchangePolynomial 𝕂) (l : Fin (H.reverse.degree + 1)) :
    H.reverse.coeff l = H.coeff (l.cast (by rw [reverse_degree])).rev := (rfl)

@[simp]
theorem reverse_reverse (H : ExchangePolynomial 𝕂) : H.reverse.reverse = H := by
  ext l <;> simp [Fin.cast_rev]

theorem unit_reverse_zero (H : ExchangePolynomial 𝕂) :
    H.reverse.isUnit_coeff_zero.unit = H.isUnit_coeff_last.unit := Units.ext (by simp)

theorem unit_reverse_last (H : ExchangePolynomial 𝕂) :
    H.reverse.isUnit_coeff_last.unit = H.isUnit_coeff_zero.unit := Units.ext (by simp)

/-- Variable dilation `H(κ T)` by a unit `κ : 𝕂ˣ`, multiplying the `l`-th coefficient by `κ ^ l`. -/
def dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := H.coeff l * ((κ ^ l.val : 𝕂ˣ) : 𝕂)
  isUnit_coeff_zero := H.isUnit_coeff_zero.mul (Units.isUnit _)
  isUnit_coeff_last := H.isUnit_coeff_last.mul (Units.isUnit _)

@[simp]
theorem dilate_degree (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) : (H.dilate κ).degree = H.degree := (rfl)

@[simp]
theorem dilate_coeff (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) (l : Fin ((H.dilate κ).degree + 1)) :
    (H.dilate κ).coeff l = H.coeff (l.cast (by rw [dilate_degree])) * ((κ ^ l.val : 𝕂ˣ) : 𝕂) :=
  (rfl)

@[simp] theorem dilate_one (H : ExchangePolynomial 𝕂) : H.dilate 1 = H := by ext l <;> simp

@[simp]
theorem dilate_dilate (H : ExchangePolynomial 𝕂) (κ₁ κ₂ : 𝕂ˣ) :
    (H.dilate κ₁).dilate κ₂ = H.dilate (κ₁ * κ₂) := by ext l <;> simp [mul_assoc, mul_pow]

theorem unit_dilate_zero (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).isUnit_coeff_zero.unit = H.isUnit_coeff_zero.unit := Units.ext (by simp)

@[simp]
theorem unit_dilate_last (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).isUnit_coeff_last.unit = H.isUnit_coeff_last.unit * κ ^ H.degree :=
  Units.ext (by simp)

/-- Scalar multiplication `e H` of an exchange polynomial by a unit `e : 𝕂ˣ`. -/
def scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := (e : 𝕂) * H.coeff l
  isUnit_coeff_zero := (Units.isUnit e).mul H.isUnit_coeff_zero
  isUnit_coeff_last := (Units.isUnit e).mul H.isUnit_coeff_last

@[simp]
theorem scale_degree (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : (H.scale e).degree = H.degree := (rfl)

@[simp]
theorem scale_coeff (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (l : Fin ((H.scale e).degree + 1)) :
    (H.scale e).coeff l = (e : 𝕂) * H.coeff (l.cast (by rw [scale_degree])) := (rfl)

@[simp] theorem scale_one (H : ExchangePolynomial 𝕂) : H.scale 1 = H := by ext l <;> simp

@[simp]
theorem scale_scale (H : ExchangePolynomial 𝕂) (e₁ e₂ : 𝕂ˣ) :
    (H.scale e₁).scale e₂ = H.scale (e₂ * e₁) := by ext l <;> simp [mul_assoc]

@[simp]
theorem unit_scale_zero (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).isUnit_coeff_zero.unit = e * H.isUnit_coeff_zero.unit := Units.ext (by simp)

@[simp]
theorem unit_scale_last (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).isUnit_coeff_last.unit = e * H.isUnit_coeff_last.unit := Units.ext (by simp)

/-- Unit scaling acts freely on exchange polynomials because the constant coefficient is a unit. -/
theorem scale_right_injective (H : ExchangePolynomial 𝕂) : Function.Injective H.scale := by
  intro e₁ e₂ h
  simpa only [unit_scale_zero, mul_left_inj] using
    congrArg (fun P ↦ P.isUnit_coeff_zero.unit) h

@[simp]
theorem scale_inj (H : ExchangePolynomial 𝕂) {e₁ e₂ : 𝕂ˣ} : H.scale e₁ = H.scale e₂ ↔ e₁ = e₂ :=
  (scale_right_injective H).eq_iff

@[simp]
theorem scale_eq_self_iff (H : ExchangePolynomial 𝕂) {e : 𝕂ˣ} : H.scale e = H ↔ e = 1 :=
  ⟨fun h ↦ H.scale_inj.mp (h.trans H.scale_one.symm), fun h ↦ h ▸ H.scale_one⟩

theorem scale_dilate (H : ExchangePolynomial 𝕂) (e κ : 𝕂ˣ) :
    (H.scale e).dilate κ = (H.dilate κ).scale e := by ext l <;> simp [mul_assoc]

@[simp]
theorem reverse_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).reverse = H.reverse.scale e := by ext l <;> simp [Fin.cast_rev]

/-- Reversing `H(κ T)` yields `κ^r` times the dilation of `H.reverse` by `κ⁻¹`. -/
theorem reverse_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).reverse = (H.reverse.dilate κ⁻¹).scale (κ ^ H.degree) := by
  ext l; · simp
  have hl : l.val ≤ H.degree := Nat.lt_succ_iff.mp (by simpa using l.isLt)
  have hκ : κ ^ (H.degree - l.val) = κ ^ H.degree * (κ⁻¹) ^ l.val := by
    rw [← Nat.add_sub_of_le hl, pow_add, inv_pow, mul_comm (κ ^ l.val), mul_inv_cancel_right,
      Nat.add_sub_cancel_left]
  simp [Fin.cast_rev, Fin.val_rev, Nat.add_sub_add_right, hκ, mul_assoc, mul_comm]

/-! ### Dilation factors -/

/-- The unit `h_r^{b⁺} h_0^{-b⁻}` by which mutation at a direction carrying `H` dilates an
adjacent exchange polynomial whose divided matrix entry is `b`. -/
noncomputable def dilationFactor (H : ExchangePolynomial 𝕂) (b : ℤ) : 𝕂ˣ :=
  H.isUnit_coeff_last.unit ^ b⁺ * H.isUnit_coeff_zero.unit ^ (-b⁻)

theorem dilationFactor_def (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.dilationFactor b = H.isUnit_coeff_last.unit ^ b⁺ * H.isUnit_coeff_zero.unit ^ (-b⁻) := (rfl)

@[simp]
theorem dilationFactor_zero (H : ExchangePolynomial 𝕂) : H.dilationFactor 0 = 1 := by
  simp [dilationFactor]

/-- Reversing `H` and negating `b` inverts the dilation factor. -/
@[simp]
theorem dilationFactor_reverse (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.reverse.dilationFactor b = (H.dilationFactor (-b))⁻¹ := by
  rw [dilationFactor_def, dilationFactor_def, unit_reverse_last, unit_reverse_zero,
    posPart_neg, negPart_neg, mul_inv, ← zpow_neg, ← zpow_neg, neg_neg, mul_comm]

/-- Scaling `H` by `e` multiplies its dilation factor at `b` by `e ^ b`. -/
@[simp]
theorem dilationFactor_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (b : ℤ) :
    (H.scale e).dilationFactor b = e ^ b * H.dilationFactor b := by
  rw [dilationFactor_def, dilationFactor_def, unit_scale_last, unit_scale_zero, mul_zpow, mul_zpow,
    mul_mul_mul_comm, ← zpow_add, ← sub_eq_add_neg, posPart_sub_negPart]

/-! ### Endpoint-one and degree-one polynomials -/

/-- An exchange polynomial has endpoint coefficients equal to `1` when `h_0 = 1` and `h_r = 1`. -/
def IsEndpointOne (H : ExchangePolynomial 𝕂) : Prop :=
  H.coeff 0 = 1 ∧ H.coeff (Fin.last H.degree) = 1

protected theorem IsEndpointOne.reverse {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.reverse.IsEndpointOne := ⟨by simp [h.2], by simp [h.1]⟩

protected theorem IsEndpointOne.dilationFactor {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne)
    (b : ℤ) : H.dilationFactor b = 1 := by
  have h0 : H.isUnit_coeff_zero.unit = 1 := Units.ext (by simp [h.1])
  have hr : H.isUnit_coeff_last.unit = 1 := Units.ext (by simp [h.2])
  rw [dilationFactor_def, h0, hr]
  simp

/-- The binary exchange polynomial `1 + T` of degree `1`. -/
def binary : ExchangePolynomial 𝕂 := ⟨1, Nat.one_pos, fun _ ↦ 1, isUnit_one, isUnit_one⟩

@[simp] theorem binary_degree : (binary : ExchangePolynomial 𝕂).degree = 1 := (rfl)

@[simp]
theorem binary_coeff (l : Fin ((binary : ExchangePolynomial 𝕂).degree + 1)) :
    (binary : ExchangePolynomial 𝕂).coeff l = 1 := (rfl)

@[simp]
theorem reverse_binary : (binary : ExchangePolynomial 𝕂).reverse = binary := by ext l <;> simp

theorem isEndpointOne_binary : (binary : ExchangePolynomial 𝕂).IsEndpointOne := ⟨rfl, rfl⟩

@[simp]
theorem dilationFactor_binary (b : ℤ) : (binary : ExchangePolynomial 𝕂).dilationFactor b = 1 :=
  isEndpointOne_binary.dilationFactor b

/-- The degree-one binomial `1 + y T` associated with a unit `y : 𝕂ˣ`. -/
def binomial (y : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := 1
  degree_pos := Nat.one_pos
  coeff l := if l.val = 0 then 1 else (y : 𝕂)
  isUnit_coeff_zero := isUnit_one
  isUnit_coeff_last := Units.isUnit y

@[simp] theorem binomial_degree (y : 𝕂ˣ) : (binomial y).degree = 1 := (rfl)

@[simp]
theorem binomial_coeff (y : 𝕂ˣ) (l : Fin ((binomial y).degree + 1)) :
    (binomial y).coeff l = if l.val = 0 then 1 else (y : 𝕂) := (rfl)

@[simp] theorem binomial_one : binomial (1 : 𝕂ˣ) = binary := by ext l <;> simp

theorem reverse_binomial (y : 𝕂ˣ) : (binomial y).reverse = (binomial y⁻¹).scale y := by
  ext l; · simp
  match l with | ⟨0, _⟩ | ⟨1, _⟩ => simp [Fin.val_rev]

@[simp]
theorem dilate_binomial (y κ : 𝕂ˣ) : (binomial y).dilate κ = binomial (y * κ) := by
  ext l; · simp
  match l with | ⟨0, _⟩ | ⟨1, _⟩ => simp

@[simp]
theorem dilationFactor_binomial (y : 𝕂ˣ) (b : ℤ) : (binomial y).dilationFactor b = y ^ b⁺ := by
  have h0 : (binomial y).isUnit_coeff_zero.unit = 1 := Units.ext (by simp)
  have h1 : (binomial y).isUnit_coeff_last.unit = y := Units.ext (by simp)
  rw [dilationFactor_def, h0, h1]
  simp

/-! ### Functoriality and coefficient sums -/

/-- Transport an exchange polynomial coefficientwise along a morphism of monoids with zero. -/
def map (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂' where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := f (H.coeff l)
  isUnit_coeff_zero := H.isUnit_coeff_zero.map f
  isUnit_coeff_last := H.isUnit_coeff_last.map f

@[simp]
theorem map_degree (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) : (H.map f).degree = H.degree := (rfl)

@[simp]
theorem map_coeff (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (l : Fin ((H.map f).degree + 1)) :
    (H.map f).coeff l = f (H.coeff (l.cast (by rw [map_degree]))) := (rfl)

@[simp]
theorem map_id (H : ExchangePolynomial 𝕂) : H.map (MonoidWithZeroHom.id 𝕂) = H := by ext l <;> simp

@[simp]
theorem map_map (g : 𝕂' →*₀ 𝕂'') (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) :
    (H.map f).map g = H.map (g.comp f) := by ext l <;> simp

@[simp]
theorem map_reverse (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) :
    H.reverse.map f = (H.map f).reverse := by ext l <;> simp [Fin.cast_rev]

@[simp]
theorem map_scale (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).map f = (H.map f).scale (Units.map f.toMonoidHom e) := by ext l <;> simp

@[simp]
theorem map_dilate (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).map f = (H.map f).dilate (Units.map f.toMonoidHom κ) := by
  ext l <;> simp [← map_pow]

@[simp]
theorem map_dilationFactor (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (b : ℤ) :
    (H.map f).dilationFactor b = Units.map f.toMonoidHom (H.dilationFactor b) := by
  have h0 : (H.map f).isUnit_coeff_zero.unit = Units.map f.toMonoidHom H.isUnit_coeff_zero.unit :=
    Units.ext (by simp)
  have hr : (H.map f).isUnit_coeff_last.unit = Units.map f.toMonoidHom H.isUnit_coeff_last.unit :=
    Units.ext (by simp)
  rw [dilationFactor_def, dilationFactor_def, h0, hr, map_mul, map_zpow, map_zpow]

@[simp]
theorem map_binary (f : 𝕂 →*₀ 𝕂') : (binary : ExchangePolynomial 𝕂).map f = binary := by
  ext l <;> simp

@[simp]
theorem map_binomial (f : 𝕂 →*₀ 𝕂') (y : 𝕂ˣ) :
    (binomial y).map f = binomial (Units.map f.toMonoidHom y) := by
  ext l; · simp
  match l with | ⟨0, _⟩ | ⟨1, _⟩ => simp

theorem sum_reverse_coeff {M : Type*} [AddCommMonoid M] (H : ExchangePolynomial 𝕂) (g : 𝕂 → M) :
    ∑ l, g (H.reverse.coeff l) = ∑ l, g (H.coeff l) := by
  let e : Fin (H.reverse.degree + 1) ≃ Fin (H.degree + 1) :=
    (finCongr (by rw [reverse_degree])).trans Fin.revPerm
  simpa [e] using Equiv.sum_comp e fun l ↦ g (H.coeff l)

theorem sum_scale_coeff {M : Type*} [AddCommMonoid M] (H : ExchangePolynomial 𝕂)
    (u : 𝕂ˣ) (g : 𝕂 → M) :
    ∑ l, g ((H.scale u).coeff l) = ∑ l, g ((u : 𝕂) * H.coeff l) := by
  let e : Fin ((H.scale u).degree + 1) ≃ Fin (H.degree + 1) := finCongr (by rw [scale_degree])
  simpa [e] using Equiv.sum_comp e fun l ↦ g ((u : 𝕂) * H.coeff l)

theorem sum_dilate_coeff {M : Type*} [AddCommMonoid M] (H : ExchangePolynomial 𝕂)
    (κ : 𝕂ˣ) (g : 𝕂 → M) :
    ∑ l, g ((H.dilate κ).coeff l) = ∑ l, g ((κ : 𝕂) ^ l.val * H.coeff l) := by
  let e : Fin ((H.dilate κ).degree + 1) ≃ Fin (H.degree + 1) := finCongr (by rw [dilate_degree])
  simpa [e, mul_comm] using Equiv.sum_comp e fun l ↦ g ((κ : 𝕂) ^ l.val * H.coeff l)

theorem sum_map_coeff {M : Type*} [AddCommMonoid M] (f : 𝕂 →*₀ 𝕂')
    (H : ExchangePolynomial 𝕂) (g : 𝕂' → M) :
    ∑ l, g ((H.map f).coeff l) = ∑ l, g (f (H.coeff l)) := by
  let e : Fin ((H.map f).degree + 1) ≃ Fin (H.degree + 1) := finCongr (by rw [map_degree])
  simpa [e] using Equiv.sum_comp e fun l ↦ g (f (H.coeff l))

end ExchangePolynomial

end TauCeti
