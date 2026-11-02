/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.SepClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange

/-!
# The Witt ring of a separably closed field

Over a separably closed field of characteristic different from two, rank classifies regular
quadratic forms. A hyperbolic plane has rank two, so rank modulo two classifies their Witt classes.
In particular, the Witt ring of `ℂ` is `ZMod 2`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §3.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [Invertible (2 : K)]

section

variable [IsSepClosed K]

/-- A Witt class over a separably closed field vanishes if its rank modulo two does. -/
theorem WittRing.eq_zero_of_dimMod2_eq_zero_of_isSepClosed {x : WittRing K}
    (h : WittRing.dimMod2 x = 0) : x = 0 := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  have heven : Even q.rank := by
    simpa only [WittRing.dimMod2_wittClass, ZMod.natCast_eq_zero_iff_even] using h
  obtain ⟨m, hm⟩ := heven
  have hq : q = m • hyperbolicClass K :=
    RegularFormClass.rank_injective_of_isSepClosed (by
      rw [rank_nsmul_hyperbolicClass, hm, two_mul])
  rw [hq, map_nsmul, wittClass_hyperbolicClass, smul_zero]

/-- Dimension modulo two is an isomorphism for the Witt ring of a separably closed field. -/
noncomputable def WittRing.equivZModTwoOfIsSepClosed : WittRing K ≃+* ZMod 2 :=
  RingEquiv.ofBijective WittRing.dimMod2 ⟨
    (injective_iff_map_eq_zero WittRing.dimMod2).2
      (fun _ => WittRing.eq_zero_of_dimMod2_eq_zero_of_isSepClosed),
    ZMod.ringHom_surjective WittRing.dimMod2⟩

@[simp]
theorem WittRing.equivZModTwoOfIsSepClosed_apply (x : WittRing K) :
    WittRing.equivZModTwoOfIsSepClosed x = WittRing.dimMod2 x := by
  unfold WittRing.equivZModTwoOfIsSepClosed
  exact RingEquiv.ofBijective_apply _ _ x

end

variable {L M : Type*} [Field L] [Field M] [Algebra K L]
variable [Invertible (2 : L)]

/-- Scalar extension to a separably closed field kills exactly the even-dimensional Witt classes. -/
theorem WittRing.baseChange_eq_zero_iff_dimMod2_eq_zero [IsSepClosed L] (x : WittRing K) :
    WittRing.baseChange (L := L) x = 0 ↔ WittRing.dimMod2 x = 0 := by
  constructor
  · exact WittRing.dimMod2_eq_zero_of_baseChange_eq_zero
  · intro h
    apply WittRing.eq_zero_of_dimMod2_eq_zero_of_isSepClosed
    simpa only [WittRing.dimMod2_baseChange] using h

/-- Equality after scalar extension implies equality after extension to any separably closed field.
No map between the two extension fields is required. -/
theorem WittRing.baseChange_eq_of_baseChange_eq_of_isSepClosed
    [Algebra K M] [Invertible (2 : M)] [IsSepClosed M] {x y : WittRing K}
    (h : WittRing.baseChange (L := L) x = WittRing.baseChange (L := L) y) :
    WittRing.baseChange (L := M) x = WittRing.baseChange (L := M) y := by
  have hsub : WittRing.baseChange (L := L) (x - y) = 0 := by simp [h]
  have hdim := WittRing.dimMod2_eq_zero_of_baseChange_eq_zero hsub
  have hc := (WittRing.baseChange_eq_zero_iff_dimMod2_eq_zero (L := M) (x - y)).mpr hdim
  simpa only [map_sub, sub_eq_zero] using hc

end TauCeti
