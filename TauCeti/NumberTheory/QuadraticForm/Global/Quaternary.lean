/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Quaternary.TernarySubspace
public import TauCeti.NumberTheory.QuadraticForm.Global.CompletionTower
import TauCeti.LinearAlgebra.QuadraticForm.QuaternaryDescent
public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
import Mathlib.Algebra.QuadraticAlgebra.Basic
import TauCeti.Algebra.Group.Units.Basic

/-!
# The quaternary case of the Hasse–Minkowski theorem

Let `Q` be a regular quadratic form of dimension four over a number field `K`. This file transfers
local isotropy of `Q` to the subforms of dimension three, and deduces the Hasse–Minkowski theorem
for `Q` from the Hasse–Minkowski theorem for ternary forms.

If the discriminant of `Q` is a square, then at every place the localization of `Q` has square
discriminant, so a form of dimension at least three represented by that localization is isotropic
as soon as `Q` is (O'Meara 42:12). Hence a form of dimension at least three locally represented by
`Q`, for instance the restriction of `Q` to a ternary subspace, is locally isotropic exactly when
`Q` is. If moreover `Q` is locally isotropic, the ternary theorem makes such a subform, and hence
`Q`, isotropic over `K`.

If the discriminant of `Q` is the class of `d`, then over any extension `L` of `K` containing a
square root of `d` the scalar extension of `Q` has square discriminant, and it is locally isotropic
when `Q` is, place by place through the completion tower. So every form of dimension at least three
locally represented by `Q ⊗ L` is locally isotropic. For `L = K(√d)` with `d` a nonsquare, the
square-discriminant case makes `Q ⊗ L` isotropic, and quaternary descent
(`QuadraticForm.anisotropic_baseChange_iff_quaternary`) brings isotropy of `Q ⊗ L` back to `Q`.

The ternary theorem enters as a hypothesis, stated for diagonal forms. The quaternary case is not
proved by the finiteness argument used in rank at least five: a binary complement can be
anisotropic at infinitely many places.

## Main results

* `QuadraticForm.LocallyRepresents.isLocallyIsotropic_iff_quaternary`: for `Q` regular quaternary
  of square discriminant, a form of dimension at least three locally represented by `Q` is locally
  isotropic exactly when `Q` is.
* `QuadraticForm.LocallyRepresents.isLocallyIsotropic_of_baseChange_quaternary`: for `Q` regular
  quaternary and locally isotropic, with discriminant the class of `d`, every form of dimension at
  least three locally represented by the scalar extension of `Q` to a number field containing a
  square root of `d` is locally isotropic.
* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary_of_discr_eq_zero`: a locally
  isotropic regular quaternary form of square discriminant is isotropic, given the ternary theorem
  over `K`.
* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary`: a locally isotropic regular
  quaternary form is isotropic, given the ternary theorem over every number field.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 42:12, 58:7 and 66:1, the
  case of dimension four.
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
    (hs : s * s = algebraMap K L d) : R.IsLocallyIsotropic :=
  (hRQ.isLocallyIsotropic_iff_quaternary (Nondegenerate.baseChange hQ) (by simpa using hrank)
    (discr_formClass_baseChange_eq_zero Q hQ hd hs) hR).mpr hQloc.baseChange

/-- **The quaternary case of the Hasse–Minkowski theorem, square discriminant.** Let `Q` be a
regular quaternary form over a number field `K` whose discriminant is a square and which is
isotropic at every finite and real place. If every regular diagonal ternary form over `K` that is
isotropic at every finite and real place is isotropic over `K`, then `Q` is isotropic over `K`. -/
theorem not_anisotropic_of_isLocallyIsotropic_quaternary_of_discr_eq_zero
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 4)
    (hdiscr : RegularFormClass.discr (formClass Q hQ) = 0) (hloc : Q.IsLocallyIsotropic)
    (hternary : ∀ p : RegularFormPresentation K, p.1 = 3 →
      (presentedForm p).IsLocallyIsotropic → ¬(presentedForm p).Anisotropic) :
    ¬Q.Anisotropic := by
  obtain ⟨⟨n, w⟩, ⟨e⟩⟩ := exists_presentedForm_equivalent Q hQ
  obtain rfl : n = 4 := by simpa [hrank] using e.toLinearEquiv.finrank_eq.symm
  -- The diagonal ternary form `⟨w 1, w 2, w 3⟩` is an orthogonal summand of `Q`.
  have hrep : (presentedForm ⟨3, fun i ↦ w i.succ⟩).IsRepresentedBy Q := by
    exact (presentedForm_tail_isRepresentedBy w).trans
      (QuadraticMap.Equivalent.isRepresentedBy ⟨e.symm⟩)
  refine hrep.not_anisotropic (hternary _ rfl ?_)
  exact ((LocallyRepresents.of_isRepresentedBy hrep).isLocallyIsotropic_iff_quaternary hQ hrank
    hdiscr (by simp)).mpr hloc

/-- **The quaternary case of the Hasse–Minkowski theorem.** Let `Q` be a regular quaternary form
over a number field `K` which is isotropic at every finite and real place. If, over every number
field, every regular diagonal ternary form that is isotropic at every finite and real place is
isotropic, then `Q` is isotropic over `K`.

The ternary hypothesis is quantified over number fields because it is needed not only over `K` but
also over the quadratic field `K(√d)`, for `d` a nonsquare representative of the discriminant of
`Q`. -/
theorem not_anisotropic_of_isLocallyIsotropic_quaternary
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 4)
    (hloc : Q.IsLocallyIsotropic)
    (hternary : ∀ (L : Type u) [Field L] [NumberField L] (p : RegularFormPresentation L),
      p.1 = 3 → (presentedForm p).IsLocallyIsotropic → ¬(presentedForm p).Anisotropic) :
    ¬Q.Anisotropic := by
  obtain ⟨p, hQp⟩ := exists_presentedForm_equivalent Q hQ
  have hd := discr_formClass Q hQ p hQp
  by_cases hsq : IsSquare (∏ i, p.2 i)
  · exact not_anisotropic_of_isLocallyIsotropic_quaternary_of_discr_eq_zero hQ hrank
      (by rw [hd, squareClass_eq_zero_iff]; exact hsq) hloc (hternary K)
  -- Otherwise pass to the quadratic field `E = K(√d)`, where the discriminant becomes a square.
  set d := ∏ i, p.2 i
  have : Fact (¬IsSquare (d : K)) := ⟨by rwa [isSquare_units_val_iff]⟩
  let E := QuadraticAlgebra K (d : K) 0
  have : NumberField E := NumberField.of_module_finite K E
  have : Algebra.IsQuadraticExtension K E := ⟨QuadraticAlgebra.finrank_eq_two _ _⟩
  have hs : (QuadraticAlgebra.omega : E) * QuadraticAlgebra.omega = algebraMap K E d := by
    rw [QuadraticAlgebra.omega_mul_omega_eq_mk, QuadraticAlgebra.algebraMap_eq]
  rw [← anisotropic_baseChange_iff_quaternary Q hQ hrank d hd hsq _ hs]
  exact not_anisotropic_of_isLocallyIsotropic_quaternary_of_discr_eq_zero
    (Nondegenerate.baseChange hQ) (by simpa using hrank)
    (discr_formClass_baseChange_eq_zero Q hQ hd hs) hloc.baseChange (hternary E)

end QuadraticForm
