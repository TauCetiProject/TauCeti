/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Ring

/-!
# The Witt ring of the real numbers

The integer signature, the positive index minus the negative index, identifies the Witt ring of
`ℝ` with `ℤ`. The hyperbolic plane has signature zero, while the positive and negative unit lines
have signatures `1` and `-1`. Every nonzero real coefficient has one of these two signs, so every
Witt class is an integer multiple of the positive unit line.

The signature extends first to the Witt-Grothendieck ring and then descends through the
hyperbolic ideal. The resulting ring equivalence has integer cast as its inverse. In particular,
two regular real forms have the same Witt class exactly when their integer signatures agree.

## Main definitions and results

* `WittGrothendieckRing.signature`: the signature of a virtual real form.
* `WittRing.signature`: the integer signature on real Witt classes.
* `WittRing.equivInt`: the signature isomorphism `W(ℝ) ≃+* ℤ`.
* `WittRing.signature_wittClass`: computes the signature from a regular-form class.
* `WittRing.intCast_signature`: reconstructs a Witt class from its signature.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §3.
-/

public section

namespace TauCeti

/-- The integer signature of a virtual real form, extending the signature on regular-form
classes to their Grothendieck ring. -/
noncomputable def WittGrothendieckRing.signature : WittGrothendieckRing ℝ →+* ℤ :=
  (Algebra.GrothendieckAddGroup.liftRingHom RegularFormClass.signatureHom).comp
    WittGrothendieckRing.equivGrothendieck.toRingHom

/-- The signature of the Grothendieck class of a regular real form is its integer signature. -/
@[simp]
theorem WittGrothendieckRing.signature_toWittGrothendieck (x : RegularFormClass ℝ) :
    signature (toWittGrothendieck x) = RegularFormClass.signature x := by
  rw [signature, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, toWittGrothendieck_apply,
    Algebra.GrothendieckAddGroup.liftRingHom_apply_of, RegularFormClass.signatureHom_apply]

/-- The integer signature of a real Witt class. Signature vanishes on hyperbolic forms, so it
is well defined on the quotient. -/
noncomputable def WittRing.signature : WittRing ℝ →+* ℤ :=
  WittRing.lift WittGrothendieckRing.signature <| by
    intro z hz
    rw [RingHom.mem_ker]
    obtain ⟨m, rfl⟩ := mem_hyperbolicIdeal_iff.mp hz
    rw [map_zsmul, WittGrothendieckRing.signature_toWittGrothendieck,
      RegularFormClass.signature_hyperbolicClass, smul_zero]

/-- Signature on the Witt ring agrees with signature on virtual forms. -/
@[simp]
theorem WittRing.signature_mk (x : WittGrothendieckRing ℝ) :
    signature (WittRing.mk x) = WittGrothendieckRing.signature x :=
  DFunLike.congr_fun (WittRing.lift_comp_mk WittGrothendieckRing.signature _) x

/-- Signature on the Witt ring agrees with signature on regular-form classes. -/
@[simp]
theorem WittRing.signature_wittClass (x : RegularFormClass ℝ) :
    signature (wittClass x) = RegularFormClass.signature x := by
  rw [wittClass_apply, signature_mk, WittGrothendieckRing.signature_toWittGrothendieck]

/-- Every real Witt class is its signature times the positive unit line. -/
@[simp]
theorem WittRing.intCast_signature (x : WittRing ℝ) : (signature x : WittRing ℝ) = x := by
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
      rw [eq_comm, eq_neg_iff_add_eq_zero, add_comm, ← map_one wittClass, ← map_add]
      simpa only [RegularFormClass.mk_rankOne_one, mul_one, wittClass_hyperbolicClass] using
        congrArg wittClass (RegularFormClass.mk_rankOne_add_neg_one_mul (1 : ℝˣ))
    · rw [RegularFormClass.mk_rankOne_eq_one_of_pos ha, RegularFormClass.signature_one]
      simp

/-- The real Witt ring is isomorphic to the integers by its signature. -/
noncomputable def WittRing.equivInt : WittRing ℝ ≃+* ℤ :=
  RingEquiv.ofBijective signature ⟨
    Function.LeftInverse.injective intCast_signature,
    fun n => ⟨n, map_intCast signature n⟩⟩

/-- The real Witt-ring isomorphism evaluates by taking the integer signature. -/
@[simp]
theorem WittRing.equivInt_apply (x : WittRing ℝ) : equivInt x = signature x :=
  RingEquiv.ofBijective_apply _ _ x

end TauCeti
