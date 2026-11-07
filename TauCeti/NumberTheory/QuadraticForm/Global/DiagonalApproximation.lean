/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass
import TauCeti.NumberTheory.NumberField.Global.Approximation.SquareClass

/-!
# Approximating local quadratic forms with a fixed discriminant

Given regular forms of the same positive rank at finitely many finite and real places of a
number field, with discriminants induced by one global square class, there is a regular global
form with that discriminant isometric to all the prescribed forms. There is no condition on
Hasse signs away from the selected places.

This is the initial approximation in the construction of a form with prescribed local behavior.
The global diagonal coefficients have product equal to a chosen representative of the
discriminant: the first coefficients are chosen in the prescribed local square classes, and the
last coefficient is determined by their product.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap

namespace NumberField.QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- A regular form of positive rank over an extension `L` of `K`, whose discriminant is induced by
the square class of a unit `d` of `K`, is equivalent to a diagonal form whose coefficient product
differs from the image of `d` by a square. -/
theorem exists_equivalent_weightedSumSquares_isSquare_div_prod {L : Type*} [Field L]
    [Invertible (2 : L)] {n : ℕ} (φ : K →+* L) (d : Kˣ)
    (Q : _root_.QuadraticForm L (Fin (n + 1) → L)) (hQ : Q.Nondegenerate)
    (hd : RegularFormClass.discr (formClass Q hQ) = φ.squareClassMap (squareClass d)) :
    ∃ a : Fin (n + 1) → Lˣ, Q.Equivalent (weightedSumSquares L a) ∧
      IsSquare (Units.map φ.toMonoidHom d / ∏ i, a i) := by
  classical
  obtain ⟨a, ha⟩ := by
    have h := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
      (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
    rw [Module.finrank_fin_fun] at h
    exact h
  refine ⟨a, ha, ?_⟩
  have h := discr_formClass Q hQ ⟨n + 1, a⟩
    (by simpa only [presentedForm_eq_weightedSumSquares] using ha)
  rw [hd, RingHom.squareClassMap_apply] at h
  have hs := (squareClass_eq_iff_isSquare_mul _ _).mp h
  simpa only [pow_two, mul_div_mul_right_eq_div] using hs.div (IsSquare.sq (∏ i, a i))

end NumberField.QuadraticForm

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-- Regular local forms of the same positive rank and with discriminants induced by one global
unit can be matched at finitely many places by a regular global form of that discriminant. -/
theorem exists_form_discr_eq_equivalent_at_places
    {n : ℕ} (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset {w : InfinitePlace K // w.IsReal}) (d : Kˣ)
    (U : ∀ v : S, _root_.QuadraticForm (v.1.adicCompletion K) (Fin n → v.1.adicCompletion K))
    (R : T → _root_.QuadraticForm ℝ (Fin n → ℝ))
    (hU : ∀ v, (U v).Nondegenerate) (hR : ∀ w, (R w).Nondegenerate)
    (hUd : ∀ v : S,
      let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
      let : Invertible (2 : v.1.adicCompletion K) :=
        (Invertible.map (algebraMap K (v.1.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
      RegularFormClass.discr (formClass (U v) (hU v)) =
        (algebraMap K (v.1.adicCompletion K)).squareClassMap (squareClass d))
    (hRd : ∀ w : T, RegularFormClass.discr (formClass (R w) (hR w)) =
      (embedding_of_isReal w.1.2).squareClassMap (squareClass d)) :
    ∃ Q : _root_.QuadraticForm K (Fin n → K), ∃ hQ : Q.Nondegenerate,
      (letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero;
        RegularFormClass.discr (formClass Q hQ) = squareClass d) ∧
      (∀ v : S, (Q.atFinitePlace v.1).Equivalent (U v)) ∧
      (∀ w : T, (Q.atRealPlace w.1).Equivalent (R w)) := by
  classical
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  cases n with
  | zero => omega
  | succ n =>
    let (v : S) : Invertible (2 : v.1.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.1.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    -- Diagonalize the prescribed local forms, tracking the square class of the coefficient product.
    choose a ha hprodU using fun v : S =>
      _root_.NumberField.QuadraticForm.exists_equivalent_weightedSumSquares_isSquare_div_prod
      (algebraMap K (v.1.adicCompletion K)) d (U v) (hU v) (hUd v)
    choose b hb hprodR using fun w : T =>
      _root_.NumberField.QuadraticForm.exists_equivalent_weightedSumSquares_isSquare_div_prod
      (embedding_of_isReal w.1.2) d (R w) (hR w) (hRd w)
    -- Approximate the coefficients, with the last one fixed by their global product.
    obtain ⟨c, hc, hcv, hcw⟩ :=
      GlobalNumberFields.exists_coefficients_prod_eq_isSquare_div_at_places S T d a b hprodU hprodR
    let Q := weightedSumSquares K c
    have hQ : Q.Nondegenerate := by
      dsimp only [Q]
      rw [weightedSumSquares_units]
      exact nondegenerate_weightedSumSquares (fun i => isRegular_iff_ne_zero.mpr (c i).ne_zero)
    -- Coordinatewise square rescaling gives actual isometries after localization.
    refine ⟨Q, hQ, ?_, ?_, ?_⟩
    · rw [discr_formClass Q hQ ⟨n + 1, c⟩ (by
        rw [presentedForm_eq_weightedSumSquares]; exact Equivalent.refl Q), hc]
    · intro v
      have he := equivalent_weightedSumSquares_of_isSquare_div (hcv v)
      rw [weightedSumSquares_units, weightedSumSquares_units] at he
      exact Equivalent.trans
        ⟨_root_.QuadraticForm.atFinitePlaceWeightedSumSquares v.1 (fun i => (c i : K))⟩
        (he.trans (by simpa only [weightedSumSquares_units] using (ha v).symm))
    · intro w
      have he := equivalent_weightedSumSquares_of_isSquare_div (hcw w)
      rw [weightedSumSquares_units, weightedSumSquares_units] at he
      exact Equivalent.trans
        ⟨_root_.QuadraticForm.atRealPlaceWeightedSumSquares w.1 (fun i => (c i : K))⟩
        (he.trans (by simpa only [weightedSumSquares_units] using (hb w).symm))

end TauCeti.NumberField.QuadraticForm
