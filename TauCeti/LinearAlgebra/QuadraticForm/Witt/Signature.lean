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
integer signatures agree. Taking `K = ℝ` gives the real Witt ring; the real closed instance is
available in `TauCeti.FieldTheory.IsRealClosed.Real`.

## Main definitions and results

* `WittGrothendieckRing.signature`: the signature of a virtual form over an ordered field.
* `WittRing.signature`: the integer signature on Witt classes over an ordered field.
* `WittRing.equivInt`: the signature isomorphism `W(K) ≃+* ℤ` for ordered real closed fields.
* `WittRing.signature_wittClass`: computes the signature from a regular-form class.
* `WittRing.intCast_signature`: reconstructs a Witt class from its signature.

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

end TauCeti
