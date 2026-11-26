/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.FundamentalIdeal

/-!
# Signature on Witt rings over ordered fields

The integer signature, the positive index minus the negative index, defines a ring homomorphism
from the Witt ring of an ordered field to `ℤ`. The hyperbolic plane has signature zero, while the
positive and negative unit lines have signatures `1` and `-1`. Over a real closed field, every
line is isometric to one of these unit lines, so every Witt class is an integer multiple of the
positive unit line.

The signature extends first to the Witt-Grothendieck ring and then descends through the
hyperbolic ideal. For an ordered real closed field, the resulting ring equivalence has integer cast
as its inverse.
In particular, two regular forms over such a field have the same Witt class exactly when their
integer signatures agree, and two regular forms of the same rank are isometric exactly when their
integer signatures agree. Taking `K = ℝ` gives the real Witt ring; the real closed instance is
available in `Mathlib.FieldTheory.IsRealClosed.Real`.

## Main definitions and results

* `WittGrothendieckRing.signature`: the signature of a virtual form over an ordered field.
* `WittRing.signature`: the integer signature on Witt classes over an ordered field.
* `WittRing.equivInt`: the signature isomorphism `W(K) ≃+* ℤ` for ordered real closed fields.
* `WittRing.signature_wittClass`: computes the signature from a regular-form class.
* `WittRing.intCast_signature`: reconstructs a Witt class from its signature.
* `wittClass_eq_iff_signature_eq`: Witt classes over ordered real closed fields are determined by
  the signature.
* `RegularFormClass.eq_iff_rank_eq_and_signature_eq`: Sylvester's law of inertia for isometry
  classes over ordered real closed fields.
* `WittRing.dimMod2_eq_intCast_signature` and `mem_fundamentalIdeal_iff_even_signature`: over any
  ordered field, dimension modulo two agrees with signature modulo two.
* `WittRing.signature_oneFoldPfisterClass`: over any ordered field, the signature of a one-fold
  Pfister class `⟨⟨a⟩⟩` is `0` for `a > 0` and `2` for `a < 0`.
* `mem_fundamentalIdeal_pow_iff_dvd_signature`: over an ordered real closed field, `I(K)^n`
  consists of the Witt classes whose signature is divisible by `2^n`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §3.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Invertible (2 : K)]

/-- The integer signature of a virtual form over an ordered field, extending the signature on
regular-form classes to their Grothendieck ring. -/
noncomputable def WittGrothendieckRing.signature : WittGrothendieckRing K →+* ℤ :=
  (Algebra.GrothendieckAddGroup.liftRingHom RegularFormClass.signatureHom).comp
    WittGrothendieckRing.equivGrothendieck.toRingHom

/-- The signature of the Grothendieck class of a regular form is its integer signature. -/
@[simp]
theorem WittGrothendieckRing.signature_toWittGrothendieck (x : RegularFormClass K) :
    signature (toWittGrothendieck x) = RegularFormClass.signature x := by
  rw [signature, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, toWittGrothendieck_apply,
    Algebra.GrothendieckAddGroup.liftRingHom_apply_of, RegularFormClass.signatureHom_apply]

/-- The integer signature of a Witt class over an ordered field. Signature vanishes on hyperbolic
forms, so it is well defined on the quotient. -/
noncomputable def WittRing.signature : WittRing K →+* ℤ :=
  WittRing.lift WittGrothendieckRing.signature <| by
    intro z hz
    rw [RingHom.mem_ker]
    obtain ⟨m, rfl⟩ := mem_hyperbolicIdeal_iff.mp hz
    rw [map_zsmul, WittGrothendieckRing.signature_toWittGrothendieck,
      RegularFormClass.signature_hyperbolicClass, smul_zero]

/-- Signature on the Witt ring agrees with signature on virtual forms. -/
@[simp]
theorem WittRing.signature_mk (x : WittGrothendieckRing K) :
    signature (WittRing.mk x) = WittGrothendieckRing.signature x :=
  DFunLike.congr_fun (WittRing.lift_comp_mk WittGrothendieckRing.signature _) x

/-- Signature on the Witt ring agrees with signature on regular-form classes. -/
@[simp]
theorem WittRing.signature_wittClass (x : RegularFormClass K) :
    signature (wittClass x) = RegularFormClass.signature x := by
  rw [wittClass_apply, signature_mk, WittGrothendieckRing.signature_toWittGrothendieck]

/-- The signature of a numeral `(ofNat(n) : WittRing K)` (`n ≥ 2`) is `n`. -/
@[simp]
theorem WittRing.signature_ofNat (n : ℕ) [n.AtLeastTwo] :
    signature (ofNat(n) : WittRing K) = ofNat(n) :=
  map_ofNat signature n

/-- Over any ordered field, the dimension modulo two of a Witt class equals its integer signature
modulo two, since `p + q` and `p - q` have the same parity. -/
theorem WittRing.dimMod2_eq_intCast_signature (x : WittRing K) :
    dimMod2 x = (signature x : ZMod 2) := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  rw [dimMod2_wittClass, signature_wittClass, ← RegularFormClass.sigPos_add_sigNeg_eq_rank,
    RegularFormClass.signature_eq_sigPos_sub_sigNeg]
  push_cast
  exact (CharTwo.sub_eq_add (q.sigPos : ZMod 2) (q.sigNeg : ZMod 2)).symm

/-- Over any ordered field, a Witt class lies in the fundamental ideal if and only if its integer
signature is even. -/
theorem mem_fundamentalIdeal_iff_even_signature {x : WittRing K} :
    x ∈ fundamentalIdeal K ↔ Even (WittRing.signature x) := by
  rw [mem_fundamentalIdeal_iff, WittRing.dimMod2_eq_intCast_signature,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat, even_iff_two_dvd]

/-- Over any ordered field, membership in `I(K)^n` forces `2^n` to divide the integer signature. -/
theorem dvd_signature_of_mem_fundamentalIdeal_pow {x : WittRing K} {n : ℕ}
    (hx : x ∈ fundamentalIdeal K ^ n) : (2 ^ n : ℤ) ∣ WittRing.signature x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu⟩ := even_iff_two_dvd.mp (mem_fundamentalIdeal_iff_even_signature.mp ha)
      obtain ⟨v, hv⟩ := ih hb
      refine ⟨u * v, ?_⟩
      rw [map_mul, hu, hv, pow_succ']
      ring
    · intro a b ha hb
      rw [map_add]
      exact dvd_add ha hb

/-- Over any ordered field, the signature of a one-fold Pfister class `⟨⟨a⟩⟩ = ⟨1, -a⟩` is `0` when
`a > 0` and `2` when `a < 0`. -/
@[simp]
theorem WittRing.signature_oneFoldPfisterClass (a : Kˣ) :
    signature (oneFoldPfisterClass a) = if 0 < (a : K) then 0 else 2 := by
  rw [oneFoldPfisterClass_eq, map_add, map_one, signature_wittClass,
    RegularFormClass.signature_mk_rankOne]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · simp [ha, ha.not_gt]
  · simp [ha, not_lt_of_gt ha]

variable [IsRealClosed K]

/-- Every Witt class over an ordered real closed field is its signature times the positive unit
line. -/
@[simp]
theorem WittRing.intCast_signature (x : WittRing K) : (signature x : WittRing K) = x := by
  obtain ⟨c, rfl⟩ := wittClass_surjective x
  rw [signature_wittClass]
  induction c using RegularFormClass.induction_on_rankOne with
  | zero => simp
  | add_rankOne c a ih =>
    rw [RegularFormClass.signature_add, Int.cast_add, map_add, ih]
    congr 1
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · rw [RegularFormClass.mk_rankOne_eq_mk_neg_one_of_neg ha,
        RegularFormClass.signature_mk_rankOne]
      norm_num
      simpa only [RegularFormClass.mk_rankOne_one, map_one] using
        (wittClass_rankOne_neg (1 : Kˣ)).symm
    · rw [RegularFormClass.mk_rankOne_eq_one_of_pos ha, RegularFormClass.signature_one]
      simp

/-- The Witt ring of an ordered real closed field is isomorphic to the integers by its signature.
Its inverse is integer cast, as characterized by Mathlib's `eq_intCast`;
`simp` simplifies inverse applications to integer casts. -/
noncomputable def WittRing.equivInt : WittRing K ≃+* ℤ :=
  RingEquiv.ofBijective signature ⟨
    Function.LeftInverse.injective intCast_signature,
    fun n => ⟨n, map_intCast signature n⟩⟩

/-- The real closed Witt-ring isomorphism evaluates by taking the integer signature. -/
@[simp]
theorem WittRing.equivInt_apply (x : WittRing K) : equivInt x = signature x :=
  RingEquiv.ofBijective_apply _ _ x

/-- **Witt classes over a real closed field.** Over an ordered real closed field, two regular-form
classes have the same Witt class exactly when their signatures agree. -/
theorem wittClass_eq_iff_signature_eq {x y : RegularFormClass K} :
    wittClass x = wittClass y ↔ RegularFormClass.signature x = RegularFormClass.signature y := by
  rw [← WittRing.equivInt.injective.eq_iff]
  simp [WittRing.equivInt_apply]

/-- **Sylvester's law of inertia for isometry classes.** Over an ordered real closed field, two
regular-form classes are equal exactly when they have the same rank and the same signature. -/
theorem RegularFormClass.eq_iff_rank_eq_and_signature_eq {x y : RegularFormClass K} :
    x = y ↔ x.rank = y.rank ∧ signature x = signature y := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hr, hs⟩ => ?_⟩
  -- Equal signatures give equal Witt classes, which differ by hyperbolic planes; equal ranks force
  -- the same number of planes on both sides, and Witt cancellation removes them.
  obtain ⟨a, b, h⟩ := wittClass_eq_iff_exists_nsmul.mp (wittClass_eq_iff_signature_eq.mpr hs)
  have hab : a = b := by
    have := congrArg rank h
    simp only [rank_add, rank_nsmul, hr, rank_hyperbolicClass] at this
    omega
  subst hab
  exact add_left_cancel h

/-- **Powers of the fundamental ideal over an ordered real closed field.** A Witt class lies in
`I(K)^n` if and only if its integer signature is divisible by `2^n`. -/
theorem mem_fundamentalIdeal_pow_iff_dvd_signature {x : WittRing K} (n : ℕ) :
    x ∈ fundamentalIdeal K ^ n ↔ (2 ^ n : ℤ) ∣ WittRing.signature x := by
  refine ⟨dvd_signature_of_mem_fundamentalIdeal_pow, fun ⟨k, hk⟩ => ?_⟩
  rw [← WittRing.intCast_signature x, hk]
  push_cast
  exact Ideal.mul_mem_right (k : WittRing K) (fundamentalIdeal K ^ n)
    (two_pow_mem_fundamentalIdeal_pow n)

end TauCeti
