/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.ComplexPlaces
public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.LowRank

/-!
# Prescribed local behavior in rank one

A regular line is classified over any field of characteristic different from two by its plain
discriminant. Consequently, if regular lines at all finite and real places of a number field have
discriminants obtained from one global square class, the global line representing that class has
exactly the prescribed local isometry classes. Any regular complex line is automatically
isometric to its complex scalar extension. This is the rank-one case of existence with
prescribed local behavior; it needs no Hilbert-sign correction.

The proof uses the low-rank classification of regular form classes and the compatibility of
discriminants with scalar extension.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-- **Existence with prescribed local behavior for regular lines.** If every prescribed finite
and real local line has the image of one global discriminant class `d`, then a global line of
discriminant `d` localizes to those lines and to any prescribed regular complex line. -/
theorem exists_rankOne_form_equivalent_at_places (d : SquareClassGroup K)
    (U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin 1 → v.adicCompletion K))
    (R : ∀ _w : {w : InfinitePlace K // w.IsReal},
      _root_.QuadraticForm ℝ (Fin 1 → ℝ))
    (C : ∀ _w : InfinitePlace K, _root_.QuadraticForm ℂ (Fin 1 → ℂ))
    (hU : ∀ v, (U v).Nondegenerate) (hR : ∀ w, (R w).Nondegenerate)
    (hC : ∀ w, (C w).Nondegenerate)
    (hUd : ∀ (v : HeightOneSpectrum (𝓞 K)),
      letI : Invertible (2 : v.adicCompletion K) :=
        (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm;
      RegularFormClass.discr (formClass (U v) (hU v)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap d)
    (hRd : ∀ (w : {w : InfinitePlace K // w.IsReal}),
      RegularFormClass.discr (formClass (R w) (hR w)) =
      (embedding_of_isReal w.2).squareClassMap d) :
    ∃ Q : _root_.QuadraticForm K (Fin 1 → K), ∃ hQ : Q.Nondegenerate,
      (letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero;
        RegularFormClass.discr (formClass Q hQ) = d) ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      (∀ w, (Q.atRealPlace w).Equivalent (R w)) ∧
      ∀ w, (Q.atComplexEmbedding w).Equivalent (C w) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let a : Kˣ := Additive.toMul (Quotient.out d)
  let p : RegularFormPresentation K := ⟨1, fun _ => a⟩
  let Q : _root_.QuadraticForm K (Fin 1 → K) := presentedForm p
  let hQ : Q.Nondegenerate := nondegenerate_presentedForm p
  have hd : RegularFormClass.discr (formClass Q hQ) = d := by
    have hp : formClass Q hQ = Quotient.mk (regularFormSetoid K) p :=
      formClass_presentedForm p
    rw [hp, RegularFormClass.discr_mk]
    simp [p, a]
  refine ⟨Q, hQ, hd, ?_, ?_, ?_⟩
  · intro v
    let _ : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hQv := _root_.QuadraticForm.Nondegenerate.atFinitePlace hQ v
    apply (_root_.QuadraticForm.equivalent_iff_discr_eq_and_hasseInvariant_eq
      (Q.atFinitePlace v) hQv (hU v) (by simp) (by simp)).mpr
    constructor
    · rw [_root_.QuadraticForm.discr_atFinitePlace Q hQ v, hd, ← hUd v]
    · rw [RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp),
        RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp)]
  · intro w
    have hQw := _root_.QuadraticForm.Nondegenerate.atRealPlace hQ w
    apply (_root_.QuadraticForm.equivalent_iff_discr_eq_and_hasseInvariant_eq
      (Q.atRealPlace w) hQw (hR w) (by simp) (by simp)).mpr
    constructor
    · rw [_root_.QuadraticForm.discr_atRealPlace Q hQ w, hd, ← hRd w]
    · rw [RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp),
        RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp)]
  · intro w
    let _ : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
    exact (_root_.QuadraticForm.equivalent_iff_finrank_eq_of_isAlgClosed
      (Q.atComplexEmbedding w) (C w)
      (_root_.QuadraticForm.Nondegenerate.atComplexEmbedding hQ w) (hC w)).mpr (by simp)

end TauCeti.NumberField.QuadraticForm
