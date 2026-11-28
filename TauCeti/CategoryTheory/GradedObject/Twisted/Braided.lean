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
# Scalar braiding data (abelian `3`-cocycles) and `ℤ/2` classification

For a commutative additive monoid `I` and a monoid `K`, a scalar braiding datum extending a
normalized `3`-cocycle `c : TauCeti.GradedObject.TwistingCocycle I K` is a function
`r : I → I → Kˣ` satisfying the two scalar hexagon identities with `c.ω`. When `I` is an abelian
group, this is an Eilenberg–MacLane abelian `3`-cocycle extending `c`, describing a braiding on the
pointed category of `I`-graded objects (Joyal–Street, §3; Quinn, §5); the structure
`PointedBraiding` records the same equations over any commutative additive monoid `I`.

* `TauCeti.GradedObject.PointedBraiding c`: scalar braiding data `r : I → I → Kˣ` extending `c`,
  with trivial braiding `1` on `c = 1`, derived unit laws `r_zero_right` and `r_zero_left`,
  transport `PointedBraiding.cast`, grading pullback `PointedBraiding.comap` and equivalence
  `PointedBraiding.comapEquiv`, and coefficient pushforward `PointedBraiding.map`.
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

/-- A scalar braiding datum `r : I → I → Kˣ` on a commutative additive monoid `I` compatible with
a normalized `3`-cocycle `c : TwistingCocycle I K`. When `I` is an abelian group, this is an
Eilenberg–MacLane abelian `3`-cocycle extending `c` (Joyal–Street, *Braided tensor categories*,
§3), parametrizing braidings in the pointed case. -/
@[ext]
structure PointedBraiding {I : Type*} [AddCommMonoid I] {K : Type*} [Monoid K]
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

variable {I : Type*} [AddCommMonoid I] {K : Type*} [Monoid K] {c : TwistingCocycle I K}

/-- The trivial scalar braiding datum `r _ _ = 1` on the trivial twisting cocycle `1`. -/
instance : One (PointedBraiding (1 : TwistingCocycle I K)) where
  one := ⟨fun _ _ ↦ 1, fun _ _ _ ↦ by simp, fun _ _ _ ↦ by simp⟩

@[simp] theorem one_r (a b : I) : (1 : PointedBraiding (1 : TwistingCocycle I K)).r a b = 1 := (rfl)

@[simp] theorem r_zero_right (B : PointedBraiding c) (a : I) : B.r a 0 = 1 := by
  simpa using (B.hexagon_forward a 0 0).symm
@[simp] theorem r_zero_left (B : PointedBraiding c) (a : I) : B.r 0 a = 1 := by
  simpa using (B.hexagon_reverse 0 0 a).symm

/-- Transport a scalar braiding datum along an equality of twisting cocycles. -/
def cast {c₁ c₂ : TwistingCocycle I K} (h : c₁ = c₂) (B : PointedBraiding c₁) :
    PointedBraiding c₂ :=
  h ▸ B

@[simp] theorem cast_r {c₁ c₂ : TwistingCocycle I K} (h : c₁ = c₂) (B : PointedBraiding c₁)
    (a b : I) : (B.cast h).r a b = B.r a b := by
  cases h; rfl

@[simp] theorem cast_rfl (B : PointedBraiding c) : B.cast rfl = B := (rfl)

@[simp] theorem cast_cast {c₁ c₂ c₃ : TwistingCocycle I K} (h₁ : c₁ = c₂) (h₂ : c₂ = c₃)
    (B : PointedBraiding c₁) : (B.cast h₁).cast h₂ = B.cast (h₁.trans h₂) := by
  cases h₁; cases h₂; rfl

/-- Pull a scalar braiding datum back along an additive monoid homomorphism `f : J →+ I`. -/
def comap {J : Type*} [AddCommMonoid J] (f : J →+ I) (B : PointedBraiding c) :
    PointedBraiding (c.comap f) where
  r j₁ j₂ := B.r (f j₁) (f j₂)
  hexagon_forward j₁ j₂ j₃ := by
    simpa only [TwistingCocycle.comap_ω, map_add] using B.hexagon_forward (f j₁) (f j₂) (f j₃)
  hexagon_reverse j₁ j₂ j₃ := by
    simpa only [TwistingCocycle.comap_ω, map_add] using B.hexagon_reverse (f j₁) (f j₂) (f j₃)

@[simp] theorem comap_r {J : Type*} [AddCommMonoid J] (f : J →+ I) (B : PointedBraiding c)
    (j₁ j₂ : J) : (B.comap f).r j₁ j₂ = B.r (f j₁) (f j₂) := (rfl)

@[simp] theorem comap_cast {J : Type*} [AddCommMonoid J] {c₁ c₂ : TwistingCocycle I K}
    (h : c₁ = c₂) (f : J →+ I) (B : PointedBraiding c₁) :
    (B.cast h).comap f = (B.comap f).cast (congrArg (TwistingCocycle.comap f) h) := by
  ext; simp

@[simp] theorem comap_id (B : PointedBraiding c) :
    B.comap (AddMonoidHom.id I) = B.cast c.comap_id.symm := by
  ext; simp

@[simp] theorem comap_comp {J M : Type*} [AddCommMonoid J] [AddCommMonoid M]
    (f : J →+ I) (g : M →+ J) (B : PointedBraiding c) :
    (B.comap f).comap g = (B.comap (f.comp g)).cast (c.comap_comp f g).symm := by
  ext; simp

@[simp] theorem comap_one {J : Type*} [AddCommMonoid J] (f : J →+ I) :
    (1 : PointedBraiding (1 : TwistingCocycle I K)).comap f =
      (1 : PointedBraiding (1 : TwistingCocycle J K)).cast (TwistingCocycle.comap_one f).symm := by
  ext; simp

/-- Equivalence of scalar braiding data induced by an additive isomorphism `e : J ≃+ I`. -/
def comapEquiv {J : Type*} [AddCommMonoid J] (e : J ≃+ I) (c : TwistingCocycle I K) :
    PointedBraiding (c.comap (e : J →+ I)) ≃ PointedBraiding c where
  toFun B := (B.comap (e.symm : I →+ J)).cast (c.comap_comap_symm e)
  invFun := comap (e : J →+ I)
  left_inv B := by ext; simp
  right_inv B := by ext; simp

@[simp] theorem comapEquiv_apply {J : Type*} [AddCommMonoid J] (e : J ≃+ I)
    (c : TwistingCocycle I K) (B : PointedBraiding (c.comap (e : J →+ I))) :
    comapEquiv e c B = (B.comap (e.symm : I →+ J)).cast (c.comap_comap_symm e) := (rfl)

@[simp] theorem comapEquiv_symm_apply {J : Type*} [AddCommMonoid J] (e : J ≃+ I)
    (c : TwistingCocycle I K) (B : PointedBraiding c) :
    (comapEquiv e c).symm B = B.comap (e : J →+ I) := (rfl)

/-- Push a scalar braiding datum forward along a monoid homomorphism `f : K →* L`. -/
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

@[simp] theorem map_cast {L : Type*} [Monoid L] {c₁ c₂ : TwistingCocycle I K}
    (h : c₁ = c₂) (f : K →* L) (B : PointedBraiding c₁) :
    (B.cast h).map f = (B.map f).cast (congrArg (TwistingCocycle.map f) h) := by
  ext; simp

@[simp] theorem map_id (B : PointedBraiding c) :
    B.map (MonoidHom.id K) = B.cast c.map_id.symm := by
  ext; simp

@[simp] theorem map_comp {L M : Type*} [Monoid L] [Monoid M]
    (f : K →* L) (g : L →* M) (B : PointedBraiding c) :
    (B.map f).map g = (B.map (g.comp f)).cast (c.map_comp f g).symm := by
  ext; simp

@[simp] protected theorem map_one {L : Type*} [Monoid L] (f : K →* L) :
    (1 : PointedBraiding (1 : TwistingCocycle I K)).map f =
      (1 : PointedBraiding (1 : TwistingCocycle I L)).cast (TwistingCocycle.map_one f).symm := by
  ext; simp

end General

section ZMod2

variable {K : Type*} [Monoid K]

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
  invFun r := zmod2 hu r.val r.property
  left_inv B := by
    ext a b; rcases a.eq_zero_or_eq_one with rfl | rfl <;>
      rcases b.eq_zero_or_eq_one with rfl | rfl <;> simp
  right_inv := fun ⟨_, _⟩ ↦ by ext1; simp

@[simp] theorem coe_zmod2Equiv_apply (u : Kˣ) (hu : u * u = 1)
    (B : PointedBraiding (TwistingCocycle.zmod2 u hu)) :
    (zmod2Equiv u hu B : Kˣ) = B.r 1 1 := (rfl)
@[simp] theorem zmod2Equiv_symm_apply (u : Kˣ) (hu : u * u = 1) (r : { r : Kˣ // r * r = u }) :
    (zmod2Equiv u hu).symm r = zmod2 hu r.val r.property := (rfl)
@[simp] theorem zmod2Equiv_zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2Equiv u hu (zmod2 hu r hr) = ⟨r, hr⟩ := (zmod2Equiv u hu).apply_symm_apply ⟨r, hr⟩
@[simp] theorem zmod2_r_eq_self {u : Kˣ} (hu : u * u = 1)
    (B : PointedBraiding (TwistingCocycle.zmod2 u hu)) (hr : B.r 1 1 * B.r 1 1 = u) :
    zmod2 hu (B.r 1 1) hr = B := (zmod2Equiv u hu).symm_apply_apply B

end ZMod2

end PointedBraiding

end TauCeti.GradedObject
