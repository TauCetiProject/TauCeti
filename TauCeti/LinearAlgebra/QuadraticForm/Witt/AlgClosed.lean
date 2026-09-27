/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.AlgClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Ring

/-!
# The Witt ring of an algebraically closed field

Over an algebraically closed field of characteristic different from two, rank classifies regular
quadratic forms. A hyperbolic plane has rank two, so rank modulo two classifies their Witt classes.
In particular, the Witt ring of `ℂ` is `ZMod 2`.

The classification uses Mathlib's algebraically closed diagonalization through
`QuadraticForm.equivalent_of_finrank_eq_of_isAlgClosed`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)]

/-- A Witt class over an algebraically closed field vanishes if its rank modulo two does. -/
theorem WittRing.eq_zero_of_dimMod2_eq_zero_of_isAlgClosed {x : WittRing K}
    (h : WittRing.dimMod2 x = 0) : x = 0 := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  have heven : Even q.rank := by
    simpa only [WittRing.dimMod2_wittClass, ZMod.natCast_eq_zero_iff_even] using h
  obtain ⟨m, hm⟩ := heven
  have hq : q = m • hyperbolicClass K :=
    RegularFormClass.rank_injective_of_isAlgClosed (by
      rw [← RegularFormClass.rankHom_apply (m • hyperbolicClass K), map_nsmul,
        RegularFormClass.rankHom_apply, rank_hyperbolicClass]
      simpa [hm, nsmul_eq_mul] using (Nat.mul_two m).symm)
  rw [hq, map_nsmul, wittClass_hyperbolicClass, smul_zero]

/-- Dimension modulo two is an isomorphism for the Witt ring of an algebraically closed field. -/
noncomputable def WittRing.equivZModTwoOfIsAlgClosed : WittRing K ≃+* ZMod 2 :=
  RingEquiv.ofBijective WittRing.dimMod2 ⟨by
    intro x y h
    apply sub_eq_zero.mp
    apply WittRing.eq_zero_of_dimMod2_eq_zero_of_isAlgClosed
    simpa only [map_sub, sub_eq_zero] using h, by
    intro z
    fin_cases z
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, map_one _⟩⟩

@[simp]
theorem WittRing.equivZModTwoOfIsAlgClosed_apply (x : WittRing K) :
    WittRing.equivZModTwoOfIsAlgClosed x = WittRing.dimMod2 x := by
  unfold WittRing.equivZModTwoOfIsAlgClosed
  exact RingEquiv.ofBijective_apply _ _ x

end TauCeti
