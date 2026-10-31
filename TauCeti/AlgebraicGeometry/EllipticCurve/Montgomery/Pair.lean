/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Raw projective pairs for Montgomery `x`-only arithmetic

Montgomery's `x`-only arithmetic on an elliptic curve works with *raw pairs* `(X, Z)` of ring
elements, standing for the projective `x`-coordinate `X / Z`, with `(1, 0)` standing for
infinity. Over a ring, and in particular over `ZMod n` for a composite `n`, such a pair need not
determine a point of the projective line: the doubling and differential-addition formulas may
output `(0, 0)`, and reducing a pair modulo a prime divisor of `n` may produce `(0, 0)` as well.
So pairs are kept as plain data, `TauCeti.Montgomery.Pair R`, and compared through the
**cross difference** `X₁ Z₂ - X₂ Z₁`.

Over a field, two nonzero pairs have vanishing cross difference exactly when one is a scalar
multiple of the other, that is, exactly when they define the same point of the projective line
`ℙ K (Fin 2 → K)`. The relation "the cross difference vanishes" is transitive through a nonzero
middle pair but not through `(0, 0)`, which has vanishing cross difference with every pair; this
is why `(0, 0)` never denotes a point.

## Main definitions

* `TauCeti.Montgomery.Pair R`: a raw pair `(X, Z)` of elements of `R`.
* `TauCeti.Montgomery.Pair.map`: apply a ring homomorphism to both fields.
* `TauCeti.Montgomery.Pair.cross`: the cross difference `X₁ Z₂ - X₂ Z₁` of two pairs.
* `TauCeti.Montgomery.Pair.toProj`: the point of `ℙ K (Fin 2 → K)` defined by a nonzero pair
  over a field.

## Main results

* `TauCeti.Montgomery.Pair.cross_eq_zero_trans`: over a domain, vanishing of the cross difference
  is transitive through a nonzero middle pair.
* `TauCeti.Montgomery.Pair.cross_eq_zero_iff_exists_smul`: over a field, two nonzero pairs have
  vanishing cross difference exactly when one is a scalar multiple of the other.
* `TauCeti.Montgomery.Pair.toProj_eq_toProj_iff`: two nonzero pairs define the same point of the
  projective line exactly when their cross difference vanishes.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1.
-/

public section

namespace TauCeti.Montgomery

open scoped LinearAlgebra.Projectivization

/-- A **raw pair** `(X, Z)` of elements of `R`, standing for the projective `x`-coordinate
`X / Z`; the pair `(1, 0)` stands for infinity. A pair denotes a point of the projective line
only when it is nonzero. -/
@[ext]
structure Pair (R : Type*) where
  /-- The first field `X` of a raw pair `(X, Z)`. -/
  x : R
  /-- The second field `Z` of a raw pair `(X, Z)`. -/
  z : R

namespace Pair

section Vec

variable {R : Type*}

/-- The coordinate vector `![X, Z]` of a pair `(X, Z)`, the form in which Mathlib's
`Projectivization` takes it. -/
def vec (p : Pair R) : Fin 2 → R := ![p.x, p.z]

@[simp] theorem vec_apply_zero (p : Pair R) : p.vec 0 = p.x := (rfl)
@[simp] theorem vec_apply_one (p : Pair R) : p.vec 1 = p.z := (rfl)

theorem vec_injective : Function.Injective (vec : Pair R → Fin 2 → R) := fun _ _ h ↦
  Pair.ext (congr_fun h 0) (congr_fun h 1)

@[simp]
theorem vec_inj {p q : Pair R} : p.vec = q.vec ↔ p = q := vec_injective.eq_iff

end Vec

section Zero

variable {R : Type*} [Zero R]

instance : Zero (Pair R) := ⟨⟨0, 0⟩⟩

@[simp] theorem zero_x : (0 : Pair R).x = 0 := (rfl)
@[simp] theorem zero_z : (0 : Pair R).z = 0 := (rfl)

/-- A pair is zero exactly when both of its fields are. -/
theorem eq_zero_iff {p : Pair R} : p = 0 ↔ p.x = 0 ∧ p.z = 0 := by
  rw [Pair.ext_iff, zero_x, zero_z]

/-- A pair is nonzero exactly when one of its fields is. -/
theorem ne_zero_iff {p : Pair R} : p ≠ 0 ↔ p.x ≠ 0 ∨ p.z ≠ 0 := by
  rw [Ne, eq_zero_iff, not_and_or]

@[simp]
theorem vec_eq_zero_iff {p : Pair R} : p.vec = 0 ↔ p = 0 := by
  simp [vec, eq_zero_iff]

end Zero

section SMul

variable {R : Type*} [Mul R]

/-- Scaling both fields of a pair by the same element. -/
instance : SMul R (Pair R) := ⟨fun c p ↦ ⟨c * p.x, c * p.z⟩⟩

@[simp] theorem smul_x (c : R) (p : Pair R) : (c • p).x = c * p.x := (rfl)
@[simp] theorem smul_z (c : R) (p : Pair R) : (c • p).z = c * p.z := (rfl)

@[simp]
theorem vec_smul (c : R) (p : Pair R) : (c • p).vec = c • p.vec := by
  ext i
  fin_cases i <;> simp [vec]

end SMul

section CommRing

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The image of a pair under a ring homomorphism, applied to both fields. -/
def map (f : R →+* S) (p : Pair R) : Pair S := ⟨f p.x, f p.z⟩

@[simp] theorem map_x (f : R →+* S) (p : Pair R) : (p.map f).x = f p.x := (rfl)
@[simp] theorem map_z (f : R →+* S) (p : Pair R) : (p.map f).z = f p.z := (rfl)

@[simp]
theorem map_id (p : Pair R) : p.map (RingHom.id R) = p := (rfl)

@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (p : Pair R) :
    (p.map f).map g = p.map (g.comp f) := (rfl)

@[simp]
theorem map_zero (f : R →+* S) : (0 : Pair R).map f = 0 := by
  ext <;> simp

@[simp]
theorem map_smul (f : R →+* S) (c : R) (p : Pair R) : (c • p).map f = f c • p.map f := by
  ext <;> simp

/-- The **cross difference** `X₁ Z₂ - X₂ Z₁` of two pairs `(X₁, Z₁)` and `(X₂, Z₂)`. Two nonzero
pairs over a field represent the same point of the projective line exactly when it vanishes. -/
def cross (p q : Pair R) : R := p.x * q.z - q.x * p.z

theorem cross_def (p q : Pair R) : p.cross q = p.x * q.z - q.x * p.z := (rfl)

@[simp]
theorem cross_self (p : Pair R) : p.cross p = 0 := sub_self _

/-- Exchanging the two pairs negates the cross difference. -/
theorem cross_anticomm (p q : Pair R) : -p.cross q = q.cross p := by
  simp only [cross_def]
  ring

theorem cross_eq_zero_comm {p q : Pair R} : p.cross q = 0 ↔ q.cross p = 0 := by
  rw [← cross_anticomm, neg_eq_zero]

@[simp]
theorem zero_cross (p : Pair R) : (0 : Pair R).cross p = 0 := by
  simp [cross_def]

@[simp]
theorem cross_zero (p : Pair R) : p.cross 0 = 0 := by
  simp [cross_def]

@[simp]
theorem smul_cross (c : R) (p q : Pair R) : (c • p).cross q = c * p.cross q := by
  simp only [cross_def, smul_x, smul_z]
  ring

@[simp]
theorem cross_smul (c : R) (p q : Pair R) : p.cross (c • q) = c * p.cross q := by
  simp only [cross_def, smul_x, smul_z]
  ring

/-- The cross difference commutes with ring homomorphisms. -/
@[simp]
theorem cross_map (f : R →+* S) (p q : Pair R) : (p.map f).cross (q.map f) = f (p.cross q) := by
  simp [cross_def]

/-- Over a commutative ring, scaling either pair by a unit does not change whether the cross
difference vanishes. -/
theorem smul_cross_eq_zero_iff {c : R} (hc : IsUnit c) {p q : Pair R} :
    (c • p).cross q = 0 ↔ p.cross q = 0 := by
  rw [smul_cross, hc.mul_right_eq_zero]

theorem cross_smul_eq_zero_iff {c : R} (hc : IsUnit c) {p q : Pair R} :
    p.cross (c • q) = 0 ↔ p.cross q = 0 := by
  rw [cross_smul, hc.mul_right_eq_zero]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- **Transitivity through a nonzero pair.** Over a domain, if the cross differences of `p` with
`q` and of `q` with `r` vanish and `q` is nonzero, then so does the cross difference of `p` with
`r`. The hypothesis `q ≠ 0` cannot be dropped, since `0` has vanishing cross difference with
every pair. -/
theorem cross_eq_zero_trans {p q r : Pair R} (hq : q ≠ 0) (hpq : p.cross q = 0)
    (hqr : q.cross r = 0) : p.cross r = 0 := by
  rw [cross_def, sub_eq_zero] at hpq hqr ⊢
  rcases ne_zero_iff.mp hq with hx | hz
  · refine mul_left_cancel₀ hx ?_
    linear_combination p.x * hqr + r.x * hpq
  · refine mul_left_cancel₀ hz ?_
    linear_combination r.z * hpq + p.z * hqr

end Domain

section Field

variable {K : Type*} [Field K]

/-- Over a field, a pair `p` has vanishing cross difference with a nonzero pair `q` exactly when
`p` is a scalar multiple of `q`. The scalar is then nonzero exactly when `p ≠ 0`. -/
theorem cross_eq_zero_iff_exists_smul {p q : Pair K} (hq : q ≠ 0) :
    p.cross q = 0 ↔ ∃ c : K, c • q = p := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ by simp [← hc]⟩
  rw [cross_def, sub_eq_zero] at h
  rcases ne_zero_iff.mp hq with hx | hz
  · refine ⟨p.x / q.x, Pair.ext (div_mul_cancel₀ _ hx) ?_⟩
    rw [smul_z, div_mul_eq_mul_div, div_eq_iff hx]
    linear_combination h
  · refine ⟨p.z / q.z, Pair.ext ?_ (div_mul_cancel₀ _ hz)⟩
    rw [smul_x, div_mul_eq_mul_div, div_eq_iff hz]
    linear_combination -h

/-- The point of the projective line `ℙ K (Fin 2 → K)` defined by a nonzero pair over a field. -/
def toProj (p : Pair K) (hp : p ≠ 0) : ℙ K (Fin 2 → K) :=
  .mk K p.vec (vec_eq_zero_iff.not.mpr hp)

theorem toProj_def (p : Pair K) (hp : p ≠ 0) :
    p.toProj hp = .mk K p.vec (vec_eq_zero_iff.not.mpr hp) := (rfl)

/-- **Two nonzero pairs define the same point of the projective line exactly when their cross
difference vanishes.** -/
theorem toProj_eq_toProj_iff {p q : Pair K} (hp : p ≠ 0) (hq : q ≠ 0) :
    p.toProj hp = q.toProj hq ↔ p.cross q = 0 := by
  rw [toProj_def, toProj_def, Projectivization.mk_eq_mk_iff', cross_eq_zero_iff_exists_smul hq]
  simp only [← vec_smul, vec_inj]

end Field

end Pair

end TauCeti.Montgomery
