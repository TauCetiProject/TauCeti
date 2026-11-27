/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# The determinant-one part of an orthogonal subgroup

For any subgroup `U` of the orthogonal group of a nondegenerate form, its determinant-one
part has index one or two in `U`. The index is two exactly when `U` contains an isometry
of determinant minus one. This applies to lattice stabilizers as well as to the full
orthogonal group, without assuming that either group is finite.

The results are stated for finite free modules over integral domains. Left separation
of the polar form is the nondegeneracy hypothesis needed for the determinant to square
to one; no reflection in `U` is assumed. Only the index-two criterion excludes
characteristic two, where the two determinant signs coincide.

Under the same hypotheses every orthogonal determinant is `1` or `-1`
(`TauCeti.QuadraticMap.orthogonalDet_eq_one_or_eq_neg_one`). Consequently, if `U` contains an
isometry of determinant minus one, every isometry becomes proper after right multiplication by an
element of `U` (`Subgroup.exists_mem_mul_mem_specialOrthogonalWithin`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A.
-/

public section

open TauCeti.QuadraticMap QuadraticMap

variable {R M : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  {Q : QuadraticForm R M}

namespace TauCeti.QuadraticMap

/-- **The determinant of an isometry is `1` or `-1`** when the polar form is left-separating,
since it squares to one (`TauCeti.QuadraticMap.orthogonalDet_sq`). -/
theorem orthogonalDet_eq_one_or_eq_neg_one (hQ : Q.polarBilin.SeparatingLeft)
    (g : orthogonalGroup Q) : orthogonalDet Q g = 1 ∨ orthogonalDet Q g = -1 := by
  simpa only [Units.ext_iff, Units.val_one, Units.val_neg] using
    sq_eq_one_iff.mp (congrArg (fun u : Rˣ ↦ (u : R)) (orthogonalDet_sq hQ g))

end TauCeti.QuadraticMap

namespace Subgroup

/-- The determinant-one part of an orthogonal subgroup has index dividing two. -/
theorem relIndex_specialOrthogonalWithin_dvd_two (U : Subgroup (orthogonalGroup Q))
    (hQ : Q.polarBilin.SeparatingLeft) :
    (specialOrthogonalWithin Q).relIndex U ∣ 2 := by
  classical
  have hdet := orthogonalDet_eq_one_or_eq_neg_one hQ
  by_cases hU : U ≤ specialOrthogonalWithin Q
  · exact (relIndex_eq_one.mpr hU) ▸ one_dvd 2
  · obtain ⟨a, ha, ha'⟩ := IsConcreteLE.not_le_iff_exists.mp hU
    have hda : orthogonalDet Q a = -1 :=
      (hdet a).resolve_left fun h ↦ ha' (by
        simpa only [mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply] using h)
    apply (relIndex_dvd_two_iff).mpr
    refine ⟨a, ha, fun b _ ↦ ?_⟩
    rcases hdet b with hb | hb
    · exact Or.inr (by
        simpa only [mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply] using hb)
    · exact Or.inl (by
        simp only [mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply]
        simp [map_mul, hb, hda])

/-- The determinant-one part of an orthogonal subgroup has index two exactly when the
subgroup contains an isometry of determinant minus one. -/
theorem relIndex_specialOrthogonalWithin_eq_two_iff [NeZero (2 : R)]
    (U : Subgroup (orthogonalGroup Q))
    (hQ : Q.polarBilin.SeparatingLeft) :
    (specialOrthogonalWithin Q).relIndex U = 2 ↔
      ∃ g ∈ U, orthogonalDet Q g = -1 := by
  constructor
  · intro h
    obtain ⟨g, hg, hg', _⟩ := relIndex_eq_two_iff_exists_notMem_and.mp h
    refine ⟨g, hg, (orthogonalDet_eq_one_or_eq_neg_one hQ g).resolve_left fun h ↦ hg' ?_⟩
    simpa only [mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply] using h
  · rintro ⟨g, hg, hd⟩
    have hi := U.relIndex_specialOrthogonalWithin_dvd_two hQ
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
    · have hg' := relIndex_eq_one.mp hi hg
      have h1 : orthogonalDet Q g = 1 := by
        simpa only [mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply] using hg'
      have : (-1 : R) = 1 := congrArg (fun u : Rˣ ↦ (u : R)) (hd.symm.trans h1)
      exact (NeZero.ne (2 : R) (by
        simpa only [one_add_one_eq_two] using neg_eq_iff_add_eq_zero.mp this)).elim
    · exact hi

/-- **`O = SO · U` as soon as `U` is improper**: if the subgroup `U` of the orthogonal group
contains an isometry of determinant `-1`, then every isometry `g` becomes proper after right
multiplication by an element of `U`. -/
theorem exists_mem_mul_mem_specialOrthogonalWithin (U : Subgroup (orthogonalGroup Q))
    (hQ : Q.polarBilin.SeparatingLeft) (hU : ∃ k ∈ U, orthogonalDet Q k = -1)
    (g : orthogonalGroup Q) : ∃ k ∈ U, g * k ∈ specialOrthogonalWithin Q := by
  simp only [mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply, map_mul]
  rcases orthogonalDet_eq_one_or_eq_neg_one hQ g with hg | hg
  · exact ⟨1, one_mem U, by simp [hg]⟩
  · obtain ⟨k, hk, hkdet⟩ := hU
    exact ⟨k, hk, by simp [hg, hkdet]⟩

end Subgroup
