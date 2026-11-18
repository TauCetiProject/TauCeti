/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.GradedObject.Twisted.Basic
import Mathlib.Algebra.CharP.Two
import TauCeti.Data.ZMod.Two

/-!
# Pointed braidings (abelian `3`-cocycles) and `ℤ/2` classification

For a commutative additive monoid `I` and a monoid `K`, a scalar braiding datum extending a
normalized `3`-cocycle `c : TauCeti.GradedObject.TwistingCocycle I K` is a function
`r : I → I → Kˣ` satisfying the two scalar hexagon identities with `c.ω`, i.e., an
Eilenberg–MacLane abelian `3`-cocycle extending `c` (Joyal–Street, §3; Quinn, §5).

* `TauCeti.GradedObject.PointedBraiding c`: scalar braiding data `r : I → I → Kˣ` extending `c`,
  with derived unit laws `r_zero_right` and `r_zero_left` and coefficient pushforward
  `PointedBraiding.map`.
* `TauCeti.GradedObject.PointedBraiding.zmod2` and `PointedBraiding.zmod2Equiv`: complete
  classification on `ZMod 2`, identifying pointed braidings on `TwistingCocycle.zmod2 u hu` with
  `{ r : Kˣ // r * r = u }` via `B ↦ B.r 1 1`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §8.4.
* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. **102** (1993), 20–78, §3.
* F. Quinn, *Group categories and their field theories*, Geom. Topol. Monogr. **2** (1999),
  407–453, §5.
-/

public section

namespace TauCeti.GradedObject

universe u v

/-- A scalar braiding datum `r : I → I → Kˣ` on a commutative additive monoid `I` compatible with
a normalized `3`-cocycle `c : TwistingCocycle I K`, i.e., an Eilenberg–MacLane abelian `3`-cocycle
extending `c` (Joyal–Street, *Braided tensor categories*, §3). -/
@[ext]
structure PointedBraiding {I : Type u} [AddCommMonoid I] {K : Type v} [Monoid K]
    (c : TwistingCocycle I K) where
  /-- The scalar braiding entries `r a b`. -/
  r : I → I → Kˣ
  /-- Forward scalar hexagon identity. -/
  hexagon_forward (a b c' : I) :
    (c.ω a b c')⁻¹ * r a (b + c') * (c.ω b c' a)⁻¹ = r a b * (c.ω b a c')⁻¹ * r a c'
  /-- Reverse scalar hexagon identity. -/
  hexagon_reverse (a b c' : I) :
    c.ω a b c' * r (a + b) c' * c.ω c' a b = r b c' * c.ω a c' b * r a c'

namespace PointedBraiding

section General

variable {I : Type u} [AddCommMonoid I] {K : Type v} [Monoid K] {c : TwistingCocycle I K}

@[simp] theorem r_zero_right (B : PointedBraiding c) (a : I) : B.r a 0 = 1 := by
  simpa using (B.hexagon_forward a 0 0).symm
@[simp] theorem r_zero_left (B : PointedBraiding c) (a : I) : B.r 0 a = 1 := by
  simpa using (B.hexagon_reverse 0 0 a).symm

/-- Push a pointed braiding forward along a monoid homomorphism `f : K →* L`. -/
def map {L : Type*} [Monoid L] (f : K →* L) (B : PointedBraiding c) :
    PointedBraiding (c.map f) where
  r a b := Units.map f (B.r a b)
  hexagon_forward a b c' := by
    simpa only [TwistingCocycle.map_ω, ← map_inv, ← map_mul] using
      congrArg (Units.map f) (B.hexagon_forward a b c')
  hexagon_reverse a b c' := by
    simpa only [TwistingCocycle.map_ω, ← map_mul] using
      congrArg (Units.map f) (B.hexagon_reverse a b c')

@[simp] theorem map_r {L : Type*} [Monoid L] (f : K →* L) (B : PointedBraiding c) (a b : I) :
    (B.map f).r a b = Units.map f (B.r a b) := (rfl)

end General

section ZMod2

variable {K : Type v} [Monoid K]

private theorem mul_mid_eq_one {u r : Kˣ} (hu : u * u = 1) (hr : r * r = u) : r * u * r = 1 := by
  rw [← hr, ← mul_assoc, mul_assoc (r * r), hr, hu]

/-- Pointed braiding on `TwistingCocycle.zmod2 u hu` with `r 1 1 = r` (`r * r = u`) and `1`
elsewhere. -/
def zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    PointedBraiding (TwistingCocycle.zmod2 u hu) where
  r a b := if a = 1 ∧ b = 1 then r else 1
  hexagon_forward a b c' := by
    rcases a.eq_zero_or_eq_one with rfl | rfl <;> rcases b.eq_zero_or_eq_one with rfl | rfl <;>
      rcases c'.eq_zero_or_eq_one with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero, inv_eq_of_mul_eq_one_right hu, hu, mul_mid_eq_one hu hr]
  hexagon_reverse a b c' := by
    rcases a.eq_zero_or_eq_one with rfl | rfl <;> rcases b.eq_zero_or_eq_one with rfl | rfl <;>
      rcases c'.eq_zero_or_eq_one with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero, hu, mul_mid_eq_one hu hr]

@[simp] theorem zmod2_r {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) (a b : ZMod 2) :
    (zmod2 hu r hr).r a b = if a = 1 ∧ b = 1 then r else 1 := (rfl)

/-- Pointed braidings on `TwistingCocycle.zmod2 u hu` are in bijection with
`{ r : Kˣ // r * r = u }` via `B ↦ B.r 1 1`. -/
def zmod2Equiv (u : Kˣ) (hu : u * u = 1) :
    PointedBraiding (TwistingCocycle.zmod2 u hu) ≃ { r : Kˣ // r * r = u } where
  toFun B := ⟨B.r 1 1, by
    have hhex := B.hexagon_forward 1 1 1
    rw [CharTwo.add_self_eq_zero (1 : ZMod 2), B.r_zero_right] at hhex
    simp only [TwistingCocycle.zmod2_ω, and_self, ↓reduceIte, inv_eq_of_mul_eq_one_right hu,
      mul_one] at hhex
    have h₁ : B.r 1 1 * u = (B.r 1 1)⁻¹ := mul_eq_one_iff_eq_inv.mp (hhex.symm.trans hu)
    have h₂ : (B.r 1 1)⁻¹ * u = B.r 1 1 := by rw [← h₁, mul_assoc, hu, mul_one]
    calc B.r 1 1 * B.r 1 1 = B.r 1 1 * ((B.r 1 1)⁻¹ * u) := by rw [h₂]
      _ = u := by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
  invFun r := zmod2 hu r.1 r.2
  left_inv B := by
    ext a b; rcases a.eq_zero_or_eq_one with rfl | rfl <;>
      rcases b.eq_zero_or_eq_one with rfl | rfl <;> simp
  right_inv := fun ⟨_, _⟩ ↦ by ext1; simp

@[simp] theorem coe_zmod2Equiv_apply (u : Kˣ) (hu : u * u = 1)
    (B : PointedBraiding (TwistingCocycle.zmod2 u hu)) :
    (zmod2Equiv u hu B : Kˣ) = B.r 1 1 := (rfl)
@[simp] theorem zmod2Equiv_symm_apply (u : Kˣ) (hu : u * u = 1) (r : { r : Kˣ // r * r = u }) :
    (zmod2Equiv u hu).symm r = zmod2 hu r.1 r.2 := (rfl)
@[simp] theorem zmod2Equiv_zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2Equiv u hu (zmod2 hu r hr) = ⟨r, hr⟩ := (zmod2Equiv u hu).apply_symm_apply ⟨r, hr⟩
@[simp] theorem zmod2_r_one_one {u : Kˣ} (hu : u * u = 1)
    (B : PointedBraiding (TwistingCocycle.zmod2 u hu)) (hr : B.r 1 1 * B.r 1 1 = u) :
    zmod2 hu (B.r 1 1) hr = B := (zmod2Equiv u hu).symm_apply_apply B
theorem zmod2_zmod2Equiv (u : Kˣ) (hu : u * u = 1)
    (B : PointedBraiding (TwistingCocycle.zmod2 u hu)) :
    zmod2 hu (zmod2Equiv u hu B).1 (zmod2Equiv u hu B).2 = B :=
  (zmod2Equiv u hu).symm_apply_apply B

end ZMod2

end PointedBraiding

end TauCeti.GradedObject
