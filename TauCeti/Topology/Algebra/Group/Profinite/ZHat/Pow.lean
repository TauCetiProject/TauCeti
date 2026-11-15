/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition

/-!
# Profinite powers

An element `x` of a profinite group `G` can be raised to a profinite integer `a ∈ ℤ̂`: the
universal property of `ℤ̂ = zHat` gives a unique continuous homomorphism `zHat.lift x` from `ℤ̂`
to `G` sending the generator to `x`, and `x ^ᶻ a` is its value at `a`, read multiplicatively
(`TauCeti.zpowHat`). There is no integer representative of `a` in general, so this power is
defined by the universal property and not by a formula.

The power extends the integer powers, and the ring structure of `Additive zHat` is exactly what
makes it a ring of exponents: `x ^ᶻ (a + b) = x ^ᶻ a * x ^ᶻ b`, and
`(x ^ᶻ a) ^ᶻ b = x ^ᶻ (a * b)` for the ring product. Continuous homomorphisms preserve it, so in
particular it commutes with conjugation, and it is jointly continuous in the base and the
exponent. On an element of finite order dividing `n`, the power only sees the residue of the
exponent modulo `n`.

On a pro-`ℓ` group, Tau Ceti's `ℓ`-adic power `TauCeti.IsProP.padicPow` is the same operation
seen through the `ℓ`-adic component of the exponent: `x ^ᶻ a` is the `ℓ`-adic power of `x` by
`zHat.component ℓ a` (`TauCeti.zpowHat_eq_padicPow_component`). In particular, on the additive
group of `ℤ_[ℓ]` itself, written multiplicatively, the profinite power by `a` is multiplication by
`zHat.component ℓ a`, and on the product `∏ ℓ, ℤ_[ℓ]` it is multiplication by the image of `a`
under the decomposition `zHat.ringEquivPiPadicInt : ℤ̂ ≃+* ∏ ℓ, ℤ_[ℓ]`.

## Main definitions

* `TauCeti.zpowHat`: the profinite power `x ^ᶻ a` of an element of a profinite group by a
  profinite integer, with the notation `x ^ᶻ a` scoped in `TauCeti.zHat`.

## Main results

* `TauCeti.zpowHat_one`, `TauCeti.zpowHat_intCast`, `TauCeti.zpowHat_natCast`: the power is
  pinned by `x ^ᶻ 1 = x` and extends the integer powers.
* `TauCeti.zpowHat_add`, `TauCeti.zpowHat_neg`, `TauCeti.zpowHat_mul`: the exponent laws, the
  last one for the ring product of `Additive zHat`.
* `TauCeti.map_zpowHat`, `TauCeti.conj_zpowHat`, `TauCeti.inv_zpowHat`: continuous homomorphisms
  preserve profinite powers.
* `TauCeti.mul_zpowHat`, `Commute.zpowHat_left`, `Commute.zpowHat_zpowHat_self`: powers of
  commuting elements.
* `TauCeti.continuous_zpowHat`, `TauCeti.continuous_zpowHat_prod`: continuity in the exponent,
  and joint continuity.
* `TauCeti.toMul_zpowHat`: on `ℤ̂` itself the profinite power is the ring product.
* `TauCeti.eq_zpowHat_of_continuous`: the profinite power is the unique continuous extension of
  the integer powers.
* `TauCeti.zpowHat_mem`: a closed subgroup containing `x` contains all its profinite powers.
* `TauCeti.zpowHat_eq_pow_val_toZMod`: on an element killed by `n`, the profinite power is the
  natural power by the residue of the exponent modulo `n`.
* `TauCeti.zpowHat_eq_padicPow_component`: on a pro-`ℓ` group the profinite power is the
  `ℓ`-adic power by the `ℓ`-adic component of the exponent.
* `TauCeti.ofAdd_zpowHat_padicInt`, `TauCeti.ofAdd_zpowHat_pi_padicInt`: on `ℤ_[ℓ]` and on
  `∏ ℓ, ℤ_[ℓ]`, the profinite power is multiplication by the `ℓ`-adic component of the exponent,
  respectively by its image in `∏ ℓ, ℤ_[ℓ]`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.1.
-/

public section

namespace TauCeti

universe u v w

open Additive

section Group

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The profinite power** `x ^ᶻ a` of an element `x` of a profinite group by a profinite integer
`a`: the value at `a`, read multiplicatively, of the continuous homomorphism `zHat.lift x` from
the profinite integers to `G` that sends the generator to `x`. -/
noncomputable def zpowHat (x : G) (a : Additive zHat.{u}) : G :=
  zHat.lift x a.toMul

@[inherit_doc] scoped[TauCeti.zHat] infixl:75 " ^ᶻ " => TauCeti.zpowHat

open scoped zHat

/-- The profinite power by `a` is the lift of `x` evaluated at `a`, read multiplicatively. -/
theorem zpowHat_def (x : G) (a : Additive zHat.{u}) : x ^ᶻ a = zHat.lift x a.toMul :=
  (rfl)

/-- Raising to the profinite integer `1` is the identity. -/
@[simp]
theorem zpowHat_one (x : G) : x ^ᶻ (1 : Additive zHat.{u}) = x := by
  rw [zpowHat_def, zHat.toMul_one, zHat.lift_gen]

/-- Raising to the profinite integer `0` gives `1`. -/
@[simp]
theorem zpowHat_zero (x : G) : x ^ᶻ (0 : Additive zHat.{u}) = 1 :=
  map_one (zHat.lift x)

/-- The profinite power agrees with the integer power on the integers. -/
@[simp]
theorem zpowHat_intCast (x : G) (n : ℤ) : x ^ᶻ (n : Additive zHat.{u}) = x ^ n := by
  rw [zpowHat_def, zHat.toMul_intCast, map_zpow, zHat.lift_gen]

/-- The profinite power agrees with the natural power on the natural numbers. -/
@[simp]
theorem zpowHat_natCast (x : G) (n : ℕ) : x ^ᶻ (n : Additive zHat.{u}) = x ^ n := by
  rw [← Int.cast_natCast, zpowHat_intCast, zpow_natCast]

/-- The profinite power by a numeral is the corresponding natural power. -/
@[simp]
theorem zpowHat_ofNat (x : G) (n : ℕ) [n.AtLeastTwo] :
    x ^ᶻ (ofNat(n) : Additive zHat.{u}) = x ^ OfNat.ofNat n := by
  simpa using zpowHat_natCast x (OfNat.ofNat n)

/-- Every profinite power of `1` is `1`. -/
@[simp]
theorem one_zpowHat (a : Additive zHat.{u}) : (1 : G) ^ᶻ a = 1 :=
  zHat.lift_one_apply a.toMul

/-- **The additive law.** -/
@[simp]
theorem zpowHat_add (x : G) (a b : Additive zHat.{u}) : x ^ᶻ (a + b) = x ^ᶻ a * x ^ᶻ b :=
  map_mul (zHat.lift x) a.toMul b.toMul

/-- Raising to `-a` inverts the power by `a`. -/
@[simp]
theorem zpowHat_neg (x : G) (a : Additive zHat.{u}) : x ^ᶻ (-a) = (x ^ᶻ a)⁻¹ :=
  map_inv (zHat.lift x) a.toMul

/-- Raising to `a - b` is the power by `a` times the inverse of the power by `b`. -/
theorem zpowHat_sub (x : G) (a b : Additive zHat.{u}) : x ^ᶻ (a - b) = x ^ᶻ a * (x ^ᶻ b)⁻¹ := by
  rw [sub_eq_add_neg, zpowHat_add, zpowHat_neg]

/-- **The multiplicative law**, for the ring product of the profinite integers: raising to `a`
and then to `b` is raising to `a * b`. -/
@[simp]
theorem zpowHat_mul (x : G) (a b : Additive zHat.{u}) : x ^ᶻ (a * b) = (x ^ᶻ a) ^ᶻ b := by
  simp only [zpowHat_def, zHat.toMul_mul, zHat.map_lift]

/-- On the profinite integers themselves, the profinite power is the ring product:
`toMul b ^ᶻ a` is `b * a`, read multiplicatively. -/
theorem toMul_zpowHat (b a : Additive zHat.{u}) : b.toMul ^ᶻ a = (b * a).toMul := by
  rw [zpowHat_def, zHat.toMul_mul]

section Map

variable {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

/-- **Naturality.** A continuous homomorphism of profinite groups preserves profinite powers. -/
@[simp]
theorem map_zpowHat {F : Type*} [FunLike F G H] [MonoidHomClass F G H] [ContinuousMapClass F G H]
    (f : F) (x : G) (a : Additive zHat.{u}) : f (x ^ᶻ a) = f x ^ᶻ a :=
  zHat.map_lift (f : G →ₜ* H) x a.toMul

end Map

/-- A continuous action by group endomorphisms commutes with profinite powers. -/
@[simp]
theorem smul_zpowHat {Γ : Type*} [Monoid Γ] [MulDistribMulAction Γ G]
    [ContinuousConstSMul Γ G] (γ : Γ) (x : G) (a : Additive zHat.{u}) :
    γ • x ^ᶻ a = (γ • x) ^ᶻ a :=
  map_zpowHat
    (⟨MulDistribMulAction.toMonoidHom G γ, continuous_const_smul γ⟩ : G →ₜ* G) x a

/-- Profinite powers commute with conjugation. -/
@[simp]
theorem conj_zpowHat (g x : G) (a : Additive zHat.{u}) :
    (g * x * g⁻¹) ^ᶻ a = g * x ^ᶻ a * g⁻¹ :=
  (map_zpowHat (⟨(MulAut.conj g).toMonoidHom, IsTopologicalGroup.continuous_conj g⟩ : G →ₜ* G)
    x a).symm

/-- Profinite powers commute with conjugation by an inverse. -/
@[simp]
theorem conj_inv_zpowHat (c x : G) (a : Additive zHat.{u}) :
    (c⁻¹ * x * c) ^ᶻ a = c⁻¹ * x ^ᶻ a * c := by
  simpa only [inv_inv] using conj_zpowHat c⁻¹ x a

/-- The profinite power of an inverse is the inverse of the profinite power. -/
@[simp]
theorem inv_zpowHat (x : G) (a : Additive zHat.{u}) : x⁻¹ ^ᶻ a = (x ^ᶻ a)⁻¹ := by
  simpa only [zpowHat_def, zpow_neg_one] using zHat.lift_zpow_apply x (-1) a.toMul

/-- The profinite power is multiplicative on commuting base elements. -/
@[simp]
theorem mul_zpowHat {x y : G} (h : Commute x y) (a : Additive zHat.{u}) :
    (x * y) ^ᶻ a = x ^ᶻ a * y ^ᶻ a :=
  zHat.lift_mul_apply x y h a.toMul

/-- A profinite power of an element commuting with `y` commutes with `y`. -/
theorem _root_.Commute.zpowHat_left {x y : G} (h : Commute x y) (a : Additive zHat.{u}) :
    Commute (x ^ᶻ a) y := by
  have hl := conj_zpowHat y x a
  rw [← h.eq, mul_inv_cancel_right] at hl
  exact (mul_inv_eq_iff_eq_mul.mp hl.symm).symm

/-- An element commuting with `y` commutes with every profinite power of `y`. -/
theorem _root_.Commute.zpowHat_right {x y : G} (h : Commute x y) (a : Additive zHat.{u}) :
    Commute x (y ^ᶻ a) :=
  (h.symm.zpowHat_left a).symm

/-- Profinite powers of commuting elements commute. -/
theorem _root_.Commute.zpowHat_zpowHat {x y : G} (h : Commute x y) (a b : Additive zHat.{u}) :
    Commute (x ^ᶻ a) (y ^ᶻ b) :=
  (h.zpowHat_left a).zpowHat_right b

/-- Two profinite powers of the same element commute. -/
theorem _root_.Commute.zpowHat_zpowHat_self (x : G) (a b : Additive zHat.{u}) :
    Commute (x ^ᶻ a) (x ^ᶻ b) :=
  (Commute.refl x).zpowHat_zpowHat a b

/-- Two profinite powers of the same element commute under multiplication. -/
theorem zpowHat_comm (x : G) (a b : Additive zHat.{u}) :
    x ^ᶻ a * x ^ᶻ b = x ^ᶻ b * x ^ᶻ a :=
  (Commute.zpowHat_zpowHat_self x a b).eq

/-- The profinite powers of `x` depend continuously on the exponent. -/
theorem continuous_zpowHat (x : G) : Continuous fun a : Additive zHat.{u} ↦ x ^ᶻ a :=
  (zHat.lift x).continuous.comp continuous_toMul

/-- **Joint continuity.** The profinite power `(x, a) ↦ x ^ᶻ a` is continuous on `G × ℤ̂`. -/
theorem continuous_zpowHat_prod : Continuous fun q : G × Additive zHat.{u} ↦ q.1 ^ᶻ q.2 :=
  zHat.continuous_lift.comp (continuous_id.prodMap continuous_toMul)

/-- A closed subgroup containing `x` contains every profinite power of `x`. -/
theorem zpowHat_mem {K : Subgroup G} (hK : IsClosed (K : Set G)) {x : G} (hx : x ∈ K)
    (a : Additive zHat.{u}) : x ^ᶻ a ∈ K :=
  -- The exponents `a` with `x ^ᶻ a ∈ K` form a closed set containing the dense integers.
  zHat.denseRange_intCast.induction_on a (hK.preimage (continuous_zpowHat x)) fun n ↦ by
    simpa only [Set.mem_preimage, zpowHat_intCast] using K.zpow_mem hx n

/-- **Uniqueness.** The profinite power is the unique continuous extension of the integer powers
of `x` along the dense inclusion of `ℤ` in `ℤ̂`. -/
theorem eq_zpowHat_of_continuous {x : G} {f : Additive zHat.{u} → G} (hf : Continuous f)
    (hint : ∀ n : ℤ, f n = x ^ n) (a : Additive zHat.{u}) : f a = x ^ᶻ a :=
  congrFun (zHat.denseRange_intCast.equalizer hf (continuous_zpowHat x)
    (funext fun n ↦ by rw [Function.comp_apply, Function.comp_apply, hint, zpowHat_intCast])) a

/-- **Powers of an element of finite order.** If `x ^ n = 1`, the profinite power `x ^ᶻ a` is the
natural power of `x` by the residue of `a` modulo `n`. -/
theorem zpowHat_eq_pow_val_toZMod {x : G} {n : ℕ+} (hx : x ^ (n : ℕ) = 1)
    (a : Additive zHat.{u}) : x ^ᶻ a = x ^ (zHat.toZMod n a).val := by
  -- The right side is continuous in `a`, since it factors through the discrete `ZMod n`.
  refine (eq_zpowHat_of_continuous ((continuous_of_discreteTopology
    (f := fun c : ZMod n ↦ x ^ c.val)).comp (zHat.continuous_toZMod n)) (fun m ↦ ?_) a).symm
  rw [Function.comp_apply, map_intCast, ← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' m hx).symm

/-- In a finite group, the profinite power depends only on the exponent modulo the group order. -/
theorem zpowHat_eq_pow_val_toZMod_natCard [Finite G] (x : G) (a : Additive zHat.{u}) :
    x ^ᶻ a = x ^ (zHat.toZMod ⟨Nat.card G, Nat.card_pos⟩ a).val :=
  zpowHat_eq_pow_val_toZMod pow_card_eq_one' a

/-- **The `ℓ`-adic comparison.** On a pro-`ℓ` group, the profinite power by `a` is Tau Ceti's
`ℓ`-adic power by the `ℓ`-adic component of `a`. -/
theorem zpowHat_eq_padicPow_component {ℓ : ℕ} [Fact ℓ.Prime] (hG : IsProP ℓ G) (x : G)
    (a : Additive zHat.{u}) : x ^ᶻ a = hG.padicPow x (zHat.component ℓ a) :=
  (eq_zpowHat_of_continuous (hG.continuous_padicPow.comp
    ((zHat.continuous_component ℓ).prodMk continuous_const))
    (fun n ↦ by simp only [Function.comp_apply, map_intCast, hG.padicPow_intCast]) a).symm

end Group

section PadicInt

open Multiplicative

open scoped zHat

/-- **Profinite powers in `ℤ_[ℓ]`.** In the additive group of `ℤ_[ℓ]`, written multiplicatively,
the profinite power by `a` is multiplication by the `ℓ`-adic component of `a`. -/
@[simp]
theorem ofAdd_zpowHat_padicInt {ℓ : ℕ} [Fact ℓ.Prime] (r : ℤ_[ℓ]) (a : Additive zHat.{u}) :
    ofAdd r ^ᶻ a = ofAdd (r * zHat.component ℓ a) := by
  have h := (isProP_multiplicative_padicInt ℓ).padicPow_ofAdd_apply_one (AddMonoidHom.mulLeft r)
    (continuous_const.mul continuous_id) (zHat.component ℓ a)
  rw [AddMonoidHom.coe_mulLeft, mul_one] at h
  rw [zpowHat_eq_padicPow_component (isProP_multiplicative_padicInt ℓ), h]

/-- **Profinite powers in `∏ ℓ, ℤ_[ℓ]`.** In the additive group of the product of the `ℓ`-adic
integers over all primes, written multiplicatively, the profinite power by `a` is multiplication by
the image of `a` under the decomposition `zHat.ringEquivPiPadicInt : ℤ̂ ≃+* ∏ ℓ, ℤ_[ℓ]`. -/
@[simp]
theorem ofAdd_zpowHat_pi_padicInt (r : ∀ ℓ : Nat.Primes, ℤ_[ℓ]) (a : Additive zHat.{u}) :
    ofAdd r ^ᶻ a = ofAdd (r * zHat.ringEquivPiPadicInt a) := by
  refine toAdd.injective (funext fun ℓ ↦ ?_)
  -- Each coordinate projection is a continuous homomorphism, so it preserves profinite powers.
  let f : Multiplicative (∀ ℓ : Nat.Primes, ℤ_[ℓ]) →ₜ* Multiplicative ℤ_[ℓ] :=
    ⟨AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun ℓ : Nat.Primes ↦ ℤ_[ℓ]) ℓ),
      continuous_ofAdd.comp ((continuous_apply ℓ).comp continuous_toAdd)⟩
  -- The values of `f`, unfolded once.
  have hf (y : Multiplicative (∀ ℓ : Nat.Primes, ℤ_[ℓ])) : (f y).toAdd = y.toAdd ℓ := rfl
  have hr : f (ofAdd r) = ofAdd (r ℓ) := rfl
  rw [← hf, map_zpowHat f, hr, ofAdd_zpowHat_padicInt]
  simp only [toAdd_ofAdd, Pi.mul_apply, zHat.ringEquivPiPadicInt_apply]

end PadicInt

end TauCeti
