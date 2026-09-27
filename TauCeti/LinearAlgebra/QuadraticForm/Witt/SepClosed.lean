/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.SepClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Ring

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

variable {K : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]

/-- A Witt class over a separably closed field vanishes if its rank modulo two does. -/
theorem WittRing.eq_zero_of_dimMod2_eq_zero_of_isSepClosed {x : WittRing K}
    (h : WittRing.dimMod2 x = 0) : x = 0 := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  have heven : Even q.rank := by
    simpa only [WittRing.dimMod2_wittClass, ZMod.natCast_eq_zero_iff_even] using h
  obtain ⟨m, hm⟩ := heven
  have hq : q = m • hyperbolicClass K :=
    RegularFormClass.rank_injective_of_isSepClosed (by
      rw [← RegularFormClass.rankHom_apply (m • hyperbolicClass K), map_nsmul,
        RegularFormClass.rankHom_apply, rank_hyperbolicClass]
      simpa [hm, nsmul_eq_mul] using (Nat.mul_two m).symm)
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

end TauCeti
