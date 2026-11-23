/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Realization.Basic
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Existence with prescribed local quadratic forms

A family of regular quadratic forms of fixed positive rank at all finite and real places of a
number field comes from one global form with discriminant `d` precisely when its discriminants
are the images of `d`, its finite Hasse signs have finite support, and its total Hasse product is
one. Here the real contribution is `(-1)^(q.choose 2)`, where `q` is the negative index.

The global discriminant is prescribed as a square class in the number field, not merely through
its local images. The forms at real places are prescribed up to isometry, so their full signatures
are retained, even when determinant and Hasse sign alone do not distinguish them.

The existence direction uses
`GlobalFormInvariants.IsAdmissible.exists_globalForm_equivalent_at_places`; the converse uses the
invariants of a global form and their compatibility with localization and isometry.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti
open TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open scoped Classical in
/-- **Existence with prescribed local behavior.** Regular forms of rank `n ≥ 1` at every finite
and real place are the localizations, up to isometry, of a regular global form with plain
discriminant `d` if and only if their discriminants come from `d`, their finite Hasse signs have
finite support, and the product of those signs and their real Hasse signs is one. -/
theorem exists_form_discr_eq_equivalent_at_all_places_iff (hn : 1 ≤ n)
    (d : SquareClassGroup K)
    (U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin n → v.adicCompletion K))
    (hU : ∀ v, (U v).Nondegenerate)
    (R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin n → ℝ))
    (hR : ∀ w, (R w).Nondegenerate) :
    (∃ (Q : _root_.QuadraticForm K (Fin n → K)) (hQ : Q.Nondegenerate),
      (letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero;
        RegularFormClass.discr (formClass Q hQ) = d) ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w)) ↔
    (∀ v, RegularFormClass.discr (formClass (U v) (hU v)) =
      (algebraMap K (v.adicCompletion K)).squareClassMap d) ∧
    (∀ w, RegularFormClass.discr (formClass (R w) (hR w)) =
      (embedding_of_isReal w.property).squareClassMap d) ∧
    (Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hU v))) ∧
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hU v))) *
        ∏ w, (-1 : ℤˣ) ^ (sigNeg (R w)).choose 2 = 1 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · rintro ⟨Q, hQ, hd, hfin, hreal⟩
    have hUd (v) : RegularFormClass.discr (formClass (U v) (hU v)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap d := by
      rw [← (formClass_eq_iff _ (_root_.QuadraticForm.Nondegenerate.atFinitePlace hQ v)
        _ (hU v)).mpr (hfin v)]
      have hv := _root_.QuadraticForm.discr_atFinitePlace Q hQ v
      rw [hd] at hv
      -- The two constructions of the inverse of two agree by subsingleton elimination.
      convert hv using 2 <;> congr 1 <;> exact Subsingleton.elim _ _
    have hL := isLocalRealization_ofLocalForms hU hUd hR
    have hQI := (hL.globalInvariants_eq_iff hQ).mpr ⟨hfin, hreal⟩
    have hI := hQI ▸ _root_.QuadraticForm.isAdmissible_globalInvariants Q hQ
      (by simpa using hn)
    refine ⟨hUd, fun w ↦ ?_, hL.hasFiniteMulSupport_localHasse hI,
      hL.finprod_localHasse_mul_prod_eq_one hI⟩
    rw [← (formClass_eq_iff _ (_root_.QuadraticForm.Nondegenerate.atRealPlace hQ w)
      _ (hR w)).mpr (hreal w), _root_.QuadraticForm.discr_atRealPlace Q hQ w, hd]
  · rintro ⟨hUd, hRd, hs, hp⟩
    have hI := isAdmissible_ofLocalForms hU hn hUd hR hRd hs hp
    obtain ⟨Q, hQ, hQI, hfin, hreal⟩ :=
      hI.exists_globalForm_equivalent_at_places (isLocalRealization_ofLocalForms hU hUd hR)
    have hd : RegularFormClass.discr (formClass Q hQ) = d := by
      rw [← _root_.QuadraticForm.globalInvariants_discr, hQI, ofLocalForms_discr]
    exact ⟨Q, hQ, hd, hfin, hreal⟩

end TauCeti.NumberField.QuadraticForm
