/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Clifford
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Brauer
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Classification

/-!
# Witt classes over a nonarchimedean local field

Over a nonarchimedean local field `K` in which `2` is invertible, regular quadratic forms are
classified by their rank, plain discriminant and local Hasse invariant
(`TauCeti.RegularFormClass.eq_iff_rank_eq_and_discr_eq_and_localHasse_eq`). This file restates
that classification with invariants that only depend on the Witt class, and deduces that the
Witt class of a form over `K` is determined by three of them:

* the rank modulo two, `TauCeti.WittRing.dimMod2`;
* the signed discriminant `d±`, `TauCeti.WittRing.signedDiscr`;
* the Clifford invariant `c`, `TauCeti.WittRing.cliffordInvariant`.

None of the three changes when a hyperbolic plane is added, while the rank, the plain
discriminant and the local Hasse invariant can. At a fixed rank the signed discriminant
determines the plain one, and by Lam's comparison
(`TauCeti.RegularFormClass.cliffordInvariant_eq_hasseInvariant_mul`) the Clifford invariant
differs from the Brauer-valued Hasse invariant by a factor depending only on the rank and the
discriminant. Over a local field the Brauer-valued Hasse invariant determines the sign-valued one
(`TauCeti.RegularFormClass.quaternionSubgroupSignEquiv_apply_hasseInvariant`). So two classes of
equal rank with equal `d±` and `c` are equal. Two classes with the same `d±`, `c` and rank parity
become classes of equal rank after hyperbolic planes are added to the smaller one, so they have
the same Witt class.

Over a general field the three invariants do not determine the Witt class: over `ℝ` the sum of
eight squares has even rank, trivial signed discriminant and trivial Clifford invariant, but it is
positive definite, so its Witt class is not zero.

## Main results

* `TauCeti.RegularFormClass.eq_iff_rank_eq_and_signedDiscr_eq_and_cliffordInvariant_eq`: local
  classification by rank, signed discriminant and Clifford invariant.
* `TauCeti.wittClass_eq_iff_rank_modEq_and_signedDiscr_eq_and_cliffordInvariant_eq`: two regular
  forms have the same Witt class exactly when their ranks have the same parity and their signed
  discriminants and Clifford invariants agree.
* `TauCeti.WittRing.eq_iff_dimMod2_eq_and_signedDiscr_eq_and_cliffordInvariant_eq`: the same
  criterion for elements of the Witt ring.
* `WittRing.eq_zero_iff_dimMod2_eq_zero_and_signedDiscr_eq_zero_and_cliffordInvariant_eq_one`
  (in the namespace `TauCeti`): a Witt class vanishes exactly when its three invariants are trivial.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3, and Chapter VI, §2.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20.
-/

public section

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

namespace RegularFormClass

/-- **Local classification by Witt invariants.** Over a nonarchimedean local field, two regular
form classes of equal rank with equal signed discriminants and equal Clifford invariants are
equal. -/
theorem eq_of_rank_eq_of_signedDiscr_eq_of_cliffordInvariant_eq {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) (hd : signedDiscr x = signedDiscr y)
    (hc : cliffordInvariant x = cliffordInvariant y) : x = y := by
  have hdiscr : discr x = discr y := by
    rw [discr_eq_sign_add_signedDiscr, discr_eq_sign_add_signedDiscr, hrank, hd]
  -- Lam's comparison: the correction factor depends only on the rank and the discriminant.
  have hhasse : hasseInvariant x = hasseInvariant y := by
    rw [cliffordInvariant_eq_hasseInvariant_mul, cliffordInvariant_eq_hasseInvariant_mul, hrank,
      hdiscr] at hc
    exact mul_right_cancel (mul_right_cancel hc)
  refine eq_of_discr_eq_of_localHasse_eq hrank hdiscr ?_
  have hsub : (⟨hasseInvariant x, hasseInvariant_mem_quaternionSubgroup x⟩ :
      BrauerGroup.quaternionSubgroup K) =
      ⟨hasseInvariant y, hasseInvariant_mem_quaternionSubgroup y⟩ :=
    Subtype.ext hhasse
  rw [← quaternionSubgroupSignEquiv_apply_hasseInvariant, hsub,
    quaternionSubgroupSignEquiv_apply_hasseInvariant]

/-- **The local invariant criterion with Witt invariants.** Over a nonarchimedean local field, a
regular form class is determined by its rank, signed discriminant and Clifford invariant. -/
theorem eq_iff_rank_eq_and_signedDiscr_eq_and_cliffordInvariant_eq {x y : RegularFormClass K} :
    x = y ↔ x.rank = y.rank ∧ signedDiscr x = signedDiscr y ∧
      cliffordInvariant x = cliffordInvariant y :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩,
    fun ⟨hr, hd, hc⟩ => eq_of_rank_eq_of_signedDiscr_eq_of_cliffordInvariant_eq hr hd hc⟩

end RegularFormClass

/-- **Witt classes over a local field.** Over a nonarchimedean local field, two regular form
classes have the same Witt class exactly when their ranks have the same parity and their signed
discriminants and Clifford invariants agree. -/
theorem wittClass_eq_iff_rank_modEq_and_signedDiscr_eq_and_cliffordInvariant_eq
    {x y : RegularFormClass K} :
    wittClass x = wittClass y ↔ x.rank ≡ y.rank [MOD 2] ∧
      RegularFormClass.signedDiscr x = RegularFormClass.signedDiscr y ∧
      RegularFormClass.cliffordInvariant x = RegularFormClass.cliffordInvariant y := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, ?_⟩
  · have := congrArg WittRing.dimMod2 h
    rwa [WittRing.dimMod2_wittClass, WittRing.dimMod2_wittClass,
      ZMod.natCast_eq_natCast_iff] at this
  · simpa using congrArg WittRing.signedDiscr h
  · simpa using congrArg WittRing.cliffordInvariant h
  rintro ⟨hr, hd, hc⟩
  -- Add hyperbolic planes to the class of smaller rank until the ranks agree.
  wlog hle : y.rank ≤ x.rank generalizing x y
  · exact (this hr.symm hd.symm hc.symm (by omega)).symm
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hr.symm
  rw [← wittClass_nsmul_hyperbolicClass_add k y]
  congr 1
  refine RegularFormClass.eq_of_rank_eq_of_signedDiscr_eq_of_cliffordInvariant_eq ?_ ?_ ?_
  · rw [RegularFormClass.rank_add, rank_nsmul_hyperbolicClass]
    omega
  · rw [RegularFormClass.signedDiscr_nsmul_hyperbolicClass_add, hd]
  · rw [RegularFormClass.cliffordInvariant_nsmul_hyperbolicClass_add, hc]

namespace WittRing

/-- **The Witt ring of a local field is detected by three invariants.** Over a nonarchimedean
local field, two Witt classes are equal exactly when their dimensions modulo two, signed
discriminants and Clifford invariants agree. -/
theorem eq_iff_dimMod2_eq_and_signedDiscr_eq_and_cliffordInvariant_eq {a b : WittRing K} :
    a = b ↔ dimMod2 a = dimMod2 b ∧ signedDiscr a = signedDiscr b ∧
      cliffordInvariant a = cliffordInvariant b := by
  obtain ⟨x, rfl⟩ := wittClass_surjective a
  obtain ⟨y, rfl⟩ := wittClass_surjective b
  rw [wittClass_eq_iff_rank_modEq_and_signedDiscr_eq_and_cliffordInvariant_eq, dimMod2_wittClass,
    dimMod2_wittClass, signedDiscr_wittClass, signedDiscr_wittClass, cliffordInvariant_wittClass,
    cliffordInvariant_wittClass, ZMod.natCast_eq_natCast_iff]

/-- **Vanishing of a Witt class over a local field.** Over a nonarchimedean local field, a Witt
class is zero exactly when it has even dimension, trivial signed discriminant and trivial Clifford
invariant. -/
theorem eq_zero_iff_dimMod2_eq_zero_and_signedDiscr_eq_zero_and_cliffordInvariant_eq_one
    {a : WittRing K} :
    a = 0 ↔ dimMod2 a = 0 ∧ signedDiscr a = 0 ∧ cliffordInvariant a = 1 := by
  rw [eq_iff_dimMod2_eq_and_signedDiscr_eq_and_cliffordInvariant_eq, map_zero, signedDiscr_zero,
    cliffordInvariant_zero]

end WittRing

end TauCeti
