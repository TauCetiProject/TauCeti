/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive additive characters

Mathlib's `AddChar.IsPrimitive` asks that every multiplicative shift of an additive character by a
nonzero element be nontrivial. Consumers that just need *some* nontrivial additive character —
character sums over a finite field, the cuspidal characters of `GL₂(F)` — want the weaker
statement that a primitive character differs from the trivial one, which is primitivity read at
the shift by `1`. Over a field the converse is Mathlib's `AddChar.IsPrimitive.of_ne_one`. Through
it, a nontrivial additive character of a finite field has vanishing character sum, and this file
records the punctured form of that sum, over the units of the field. Without a domain hypothesis,
the full character sum still vanishes when some value minus one is a non-zero-divisor.

The shift of a primitive character by `a` is trivial only for `a = 0`, by definition of
primitivity. A primitive character stays primitive under a shift by a unit, and on a finite ring
these are the only primitive shifts: Mathlib's `AddChar.not_isPrimitive_mulShift` rules out the
nonunits. This is what identifies the primitive characters among the shifts of one primitive
character.

## Main results

* `AddChar.IsPrimitive.ne_one`: a primitive additive character on a nontrivial ring is
  nontrivial.
* `AddChar.IsPrimitive.mulShift_eq_one_iff`: the shift of a primitive character by `a` is
  trivial if and only if `a = 0`.
* `AddChar.IsPrimitive.mulShift`: the shift of a primitive character by a unit is primitive.
* `AddChar.IsPrimitive.isPrimitive_mulShift_iff`: on a finite ring, the shift of a primitive
  character by `a` is primitive if and only if `a` is a unit.
* `AddChar.IsPrimitive.natCast_ne_zero`: the level of a primitive additive character of `ZMod n`
  with values in a domain is nonzero in that domain.
* `AddChar.sum_units_mul_eq_neg_one`: a nontrivial additive character of a finite field sums to
  `-1` over the nonzero elements, even after multiplication by a unit. This is the punctured form
  of Mathlib's `AddChar.sum_eq_zero_of_ne_one`, reindexed by `Fˣ`, which is the shape character
  computations over a finite field consume directly.
* `AddChar.sum_eq_zero_of_sub_one_mem_nonZeroDivisors`: the values of an additive character of a
  finite group sum to zero as soon as `φ b - 1` is a non-zero-divisor for one `b`. This drops the
  domain hypothesis of Mathlib's `AddChar.sum_eq_zero_of_ne_one`, which is the case where every
  nonzero `φ b - 1` qualifies.
* `TauCeti.traceAddChar`, `TauCeti.traceAddChar_apply`, `TauCeti.isPrimitive_traceAddChar`: the
  canonical additive character `t ↦ ζ ^ Tr(t)` on an algebra `F / ZMod p`, its evaluation lemma,
  and its primitivity when `p` is prime, `F` is a finite field, and `ζ` is a primitive `p`-th root
  of unity.
-/

public section

namespace AddChar

section Shift

variable {R R' : Type*} [CommRing R] [CommMonoid R'] {ψ : AddChar R R'}

/-- The shift of a primitive additive character by `a` is trivial exactly when `a = 0`. -/
@[simp]
theorem IsPrimitive.mulShift_eq_one_iff (hψ : ψ.IsPrimitive) {a : R} :
    ψ.mulShift a = 1 ↔ a = 0 :=
  ⟨fun h ↦ by_contra fun ha ↦ hψ ha h, fun h ↦ h ▸ mulShift_zero ψ⟩

/-- The shift of a primitive additive character by a unit is primitive. -/
theorem IsPrimitive.mulShift (hψ : ψ.IsPrimitive) {a : R} (ha : IsUnit a) :
    (ψ.mulShift a).IsPrimitive := fun b hb ↦ by
  rw [mulShift_mulShift]
  exact hψ (ha.mul_right_eq_zero.not.mpr hb)

/-- On a finite ring, the shift of a primitive additive character by `a` is primitive if and only
if `a` is a unit. -/
theorem IsPrimitive.isPrimitive_mulShift_iff [Finite R] (hψ : ψ.IsPrimitive) {a : R} :
    (ψ.mulShift a).IsPrimitive ↔ IsUnit a :=
  ⟨fun h ↦ by_contra fun ha ↦ not_isPrimitive_mulShift ψ ha h, hψ.mulShift⟩

end Shift

variable {R R' : Type*} [CommRing R] [Nontrivial R] [CommMonoid R']

/-- A primitive additive character on a nontrivial ring is nontrivial. -/
theorem IsPrimitive.ne_one {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) : ψ ≠ 1 := by
  simpa only [mulShift_one] using hψ one_ne_zero

/-- The level of a primitive additive character of `ZMod n` with values in a domain is nonzero in
that domain. This is the level hypothesis needed to show that Gauss sums against primitive
additive characters are nonzero. -/
theorem IsPrimitive.natCast_ne_zero {S : Type*} [CommRing S] [IsDomain S] {n : ℕ} [NeZero n]
    {e : AddChar (ZMod n) S} (he : e.IsPrimitive) : (n : S) ≠ 0 := by
  have hroot : IsPrimitiveRoot (e 1) n :=
    { pow_eq_one := by
        rw [← map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero_eq_one]
      dvd_of_pow_eq_one := fun l hl ↦ by
        rw [← map_nsmul_eq_pow, he.zmod_char_eq_one_iff n, nsmul_eq_mul, mul_one] at hl
        exact (ZMod.natCast_eq_zero_iff l n).1 hl }
  exact hroot.neZero'.out

/-- A nontrivial additive character of a finite field sums to `-1` over the units, even after
multiplication by a fixed unit. This is the punctured form of `AddChar.sum_eq_zero_of_ne_one`. -/
theorem sum_units_mul_eq_neg_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {S : Type*} [CommRing S] [IsDomain S] (ψ : AddChar F S) (hψ : ψ ≠ 1) (c : Fˣ) :
    ∑ d : Fˣ, ψ ((c : F) * (d : F)) = -1 := by
  -- the full sum over `F` vanishes, `ψ (c * ·)` being a nontrivial additive character
  have hsum : ∑ x : F, ψ ((c : F) * x) = 0 := by
    simpa [AddChar.mulShift_apply] using
      AddChar.sum_eq_zero_of_ne_one ((AddChar.IsPrimitive.of_ne_one hψ) c.ne_zero)
  -- split off the term at `0`, which is `ψ 0 = 1`, and reindex the nonzero terms by `Fˣ`
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, mul_zero, AddChar.map_zero_eq_one,
    ← Fintype.sum_equiv unitsEquivNeZero (fun d : Fˣ ↦ ψ ((c : F) * (d : F))) _
      fun d ↦ by rw [unitsEquivNeZero_apply_coe]] at hsum
  exact eq_neg_of_add_eq_zero_right hsum

/-- The values of an additive character of a finite group sum to zero as soon as `φ b - 1` is a
non-zero-divisor for some `b`. Over a domain this is `AddChar.sum_eq_zero_of_ne_one`; in general
it applies, for instance, when `φ b - 1` is a unit. -/
theorem sum_eq_zero_of_sub_one_mem_nonZeroDivisors {A S : Type*} [AddGroup A] [Fintype A]
    [CommRing S] {φ : AddChar A S} {b : A} (hb : φ b - 1 ∈ nonZeroDivisors S) :
    ∑ a, φ a = 0 := by
  have h : ∑ a, φ (b + a) = ∑ a, φ a := Fintype.sum_equiv (Equiv.addLeft b) _ _ fun _ ↦ rfl
  simp_rw [map_add_eq_mul, ← Finset.mul_sum] at h
  rw [← mul_left_mem_nonZeroDivisors_eq_zero_iff hb, sub_mul, one_mul, h, sub_self]

end AddChar

namespace TauCeti

/-- The canonical additive character `t ↦ ζ ^ Tr(t)` on an algebra `F / ZMod p` attached to a
`p`-th root of unity `ζ`. -/
noncomputable def traceAddChar (p : ℕ) [NeZero p] (F : Type*) {L : Type*} [CommRing F]
    [Algebra (ZMod p) F] [CommMonoid L] {ζ : L} (hζ : ζ ^ p = 1) :
    AddChar F L :=
  (AddChar.zmodChar p hζ).compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom

/-- Evaluation of `TauCeti.traceAddChar`. -/
@[simp]
theorem traceAddChar_apply (p : ℕ) [NeZero p] (F : Type*) {L : Type*} [CommRing F]
    [Algebra (ZMod p) F] [CommMonoid L] {ζ : L} (hζ : ζ ^ p = 1) (t : F) :
    traceAddChar p F hζ t = ζ ^ (Algebra.trace (ZMod p) F t).val := by
  simp [traceAddChar, AddChar.zmodChar_apply]

/-- For a prime `p` and a primitive `p`-th root of unity `ζ`, the trace character `t ↦ ζ ^ Tr(t)`
on a finite field of characteristic `p` is primitive. -/
theorem isPrimitive_traceAddChar {p : ℕ} [Fact p.Prime] (F : Type*) {L : Type*} [Field F]
    [Finite F] [Algebra (ZMod p) F] [CommMonoidWithZero L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ p) :
    (traceAddChar p F hζ.pow_eq_one).IsPrimitive := by
  refine AddChar.IsPrimitive.of_ne_one fun h ↦ ?_
  obtain ⟨t, ht⟩ := Algebra.trace_surjective (ZMod p) F 1
  have hval := traceAddChar_apply p F hζ.pow_eq_one t
  rw [h, one_apply, ht, ZMod.val_one, pow_one] at hval
  exact hζ.ne_one (Fact.out : p.Prime).one_lt hval.symm

end TauCeti
