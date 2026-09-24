/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Quaternary.TernarySubspace
public import TauCeti.NumberTheory.QuadraticForm.Global.CompletionTower
public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant

/-!
# Local isotropy of quaternary forms over number fields

Let `Q` be a regular quadratic form of dimension four over a number field `K`. This file transfers
local isotropy of `Q` to the subforms of dimension three that the Hasse–Minkowski theorem
reduces to.

If the discriminant of `Q` is a square, then at every place the localization of `Q` has square
discriminant, so a form of dimension at least three represented by that localization is isotropic
as soon as `Q` is (O'Meara 42:12). Hence a form of dimension at least three locally represented by
`Q`, for instance the restriction of `Q` to a ternary subspace, is locally isotropic exactly when
`Q` is.

If the discriminant of `Q` is the class of `d`, then over any extension `L` of `K` containing a
square root of `d` the scalar extension of `Q` has square discriminant, and it is locally isotropic
when `Q` is, place by place through the completion tower. So every form of dimension at least three
locally represented by `Q ⊗ L` is locally isotropic. For `L = K(√d)` with `d` a nonsquare,
quaternary descent (`QuadraticForm.anisotropic_baseChange_iff_quaternary`) brings isotropy of
`Q ⊗ L` back to `Q`.

## Main results

* `QuadraticForm.LocallyRepresents.isLocallyIsotropic_iff_quaternary`: for `Q` regular quaternary
  of square discriminant, a form of dimension at least three locally represented by `Q` is locally
  isotropic exactly when `Q` is.
* `QuadraticForm.LocallyRepresents.isLocallyIsotropic_of_baseChange_quaternary`: for `Q` regular
  quaternary and locally isotropic, with discriminant the class of `d`, every form of dimension at
  least three locally represented by the scalar extension of `Q` to a number field containing a
  square root of `d` is locally isotropic.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 42:12 and 66:1, the case of
  dimension four.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- Let `Q` be a regular quaternary form over a number field with square discriminant. A form of
dimension at least three locally represented by `Q` is locally isotropic exactly when `Q` is. -/
theorem LocallyRepresents.isLocallyIsotropic_iff_quaternary {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hRQ : R.LocallyRepresents Q) (hQ : Q.Nondegenerate)
    (hrank : Module.finrank K V = 4) (hdiscr : RegularFormClass.discr (formClass Q hQ) = 0)
    (hR : 3 ≤ Module.finrank K W) :
    R.IsLocallyIsotropic ↔ Q.IsLocallyIsotropic := by
  refine ⟨hRQ.isLocallyIsotropic, fun hQloc ↦ ?_⟩
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨hRfin, hRreal⟩ := (locallyRepresents_iff R Q).mp hRQ
  obtain ⟨hQfin, hQreal⟩ := (isLocallyIsotropic_iff Q).mp hQloc
  refine (isLocallyIsotropic_iff R).mpr ⟨fun v ↦ ?_, fun w ↦ ?_⟩
  · let : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    refine QuadraticMap.Nondegenerate.not_anisotropic_of_isRepresentedBy_of_finrank_ge_three
      (Nondegenerate.atFinitePlace hQ v) (hRfin v) (by simpa using hR) (by simpa using hrank) ?_
      (hQfin v)
    rw [discr_atFinitePlace Q hQ v, hdiscr, map_zero]
  · refine QuadraticMap.Nondegenerate.not_anisotropic_of_isRepresentedBy_of_finrank_ge_three
      (Nondegenerate.atRealPlace hQ w) (hRreal w) (by simpa using hR) (by simpa using hrank) ?_
      (hQreal w)
    rw [discr_atRealPlace Q hQ w, hdiscr, map_zero]

/-- Let `Q` be a regular quaternary form over a number field `K` which is isotropic at every finite
and real place, and whose discriminant is the class of `d`. Let `L` be an extension of `K`
containing a square root `s` of `d`. Then every form of dimension at least three locally
represented by the scalar extension of `Q` to `L` is isotropic at every finite and real place of
`L`. -/
theorem LocallyRepresents.isLocallyIsotropic_of_baseChange_quaternary
    {L : Type*} [Field L] [NumberField L] [Algebra K L] {Q : _root_.QuadraticForm K V}
    {W : Type*} [AddCommGroup W] [Module L W] {R : _root_.QuadraticForm L W}
    (hRQ : R.LocallyRepresents (Q.baseChange L)) (hR : 3 ≤ Module.finrank L W)
    (hQloc : Q.IsLocallyIsotropic) (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 4)
    (d : Kˣ) (hd : RegularFormClass.discr (formClass Q hQ) = squareClass d) (s : L)
    (hs : s * s = algebraMap K L d) : R.IsLocallyIsotropic := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact d.ne_zero ((algebraMap K L).injective (by rw [← hs, zero_mul, map_zero]))
  refine (hRQ.isLocallyIsotropic_iff_quaternary (Nondegenerate.baseChange hQ)
    (by simpa using hrank) ?_ hR).mpr hQloc.baseChange
  -- Over `L` the discriminant of `Q` is the class of `d = s * s`, a square.
  rw [formClass_baseChange Q hQ, RegularFormClass.discr_baseChange, hd,
    RingHom.squareClassMap_apply, squareClass_eq_zero_iff]
  exact ⟨Units.mk0 s hs0, Units.ext (by simpa using hs.symm)⟩

end QuadraticForm
