/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The zero locus of a nonzero multivariate polynomial is null

A nonzero polynomial in finitely many variables over a measurable integral domain vanishes on a
null set of any finite product of σ-finite measures without atoms; in particular, a nonzero real
polynomial vanishes on a Lebesgue-null set. Determinants and minors are polynomials in the
entries of a matrix, so this shows that generic polynomial conditions, such as nonsingularity,
hold almost everywhere.

## Main declarations

* `MvPolynomial.measurable_eval` — evaluation is measurable in the coordinates.
* `MvPolynomial.measurableSet_setOfPred_eval_eq_zero` — the zero locus of a multivariate
  polynomial is measurable.
* `MvPolynomial.measure_pi_setOfPred_eval_eq_zero` — the zero locus of a nonzero multivariate
  polynomial is null for a finite product of σ-finite measures without atoms.
* `MvPolynomial.volume_setOfPred_eval_eq_zero` — the same for the product `volume`.
-/

public section

noncomputable section

open MeasureTheory

namespace MvPolynomial

section Measurable

variable {R ι : Type*} [CommSemiring R] [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R]

/-- Evaluating a multivariate polynomial is measurable in the coordinates: a polynomial is
built from finitely many coordinate projections by addition and multiplication. -/
theorem measurable_eval (P : MvPolynomial ι R) : Measurable fun x : ι → R => eval x P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add]; fun_prop
  | mul_X P i hP => simp only [map_mul, eval_X]; fun_prop

/-- The zero locus of a multivariate polynomial is measurable. -/
theorem measurableSet_setOfPred_eval_eq_zero [MeasurableSingletonClass R]
    (P : MvPolynomial ι R) : MeasurableSet {x : ι → R | eval x P = 0} :=
  measurable_eval P (measurableSet_singleton 0)

end Measurable

section Null

variable {R ι : Type*} [CommRing R] [IsDomain R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableAdd₂ R] [MeasurableMul₂ R]

/-- The zero locus of a nonzero polynomial in `n` variables is null for a product of σ-finite
measures without atoms. -/
private theorem measure_pi_setOfPred_eval_eq_zero_fin :
    ∀ (n : ℕ) (μ : Fin n → Measure R) [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)]
      (P : MvPolynomial (Fin n) R), P ≠ 0 → Measure.pi μ {x | eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro μ _ _ P hP
    obtain ⟨a, rfl⟩ := C_surjective (Fin 0) P
    simp_all
  | succ n ih =>
    intro μ _ _ P hP
    -- Split off the first coordinate: `P` becomes a polynomial `Q` in one variable whose
    -- coefficients are polynomials in the remaining `n` variables.
    set Q := finSuccEquiv R n P with hQdef
    have hQ : Q ≠ 0 := by simpa [hQdef] using hP
    have he := (measurePreserving_piFinSuccAbove μ 0).symm
    rw [← he.measure_preimage_equiv {x : Fin (n + 1) → R | eval x P = 0}]
    set T := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => R) 0).symm ⁻¹'
      {x : Fin (n + 1) → R | eval x P = 0} with hTdef
    have hT : MeasurableSet T :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => R) 0).symm.measurable
        (measurableSet_setOfPred_eval_eq_zero P)
    -- Each slice `{y | (y, s) ∈ T}` is the root set of `Q` with coefficients evaluated at `s`.
    have hslice : ∀ s : Fin n → R, ((fun y : R => (y, s)) ⁻¹' T) =
        {y : R | Polynomial.eval y (Polynomial.map (eval s) Q) = 0} := fun s => by
      ext y
      simp [hTdef, Fin.consEquiv, ← eval_eq_eval_mv_eval', hQdef]
    -- Off the null zero locus of the leading coefficient, the slice polynomial is nonzero, so
    -- the slice is finite and hence null.
    have hae : (fun s => μ 0 ((fun y : R => (y, s)) ⁻¹' T))
        =ᵐ[Measure.pi fun j => μ (Fin.succAbove 0 j)] 0 := by
      filter_upwards
        [compl_mem_ae_iff.2 (ih _ Q.leadingCoeff (Polynomial.leadingCoeff_ne_zero.2 hQ))]
        with s hs
      have hne : Polynomial.map (eval s) Q ≠ 0 := Polynomial.leadingCoeff_ne_zero.1 <| by
        rwa [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hs]
      rw [hslice s]
      exact (Polynomial.finite_setOfPred_isRoot hne).measure_zero _
    rw [Measure.prod_apply_symm hT, lintegral_congr_ae hae]
    simp

/-- The zero locus of a nonzero multivariate polynomial is null for a finite product of
σ-finite measures without atoms. -/
theorem measure_pi_setOfPred_eval_eq_zero [Fintype ι] (μ : ι → Measure R)
    [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)] (P : MvPolynomial ι R)
    (hP : P ≠ 0) : Measure.pi μ {x | eval x P = 0} = 0 := by
  have hφ := measurePreserving_piCongrLeft (α := fun _ : ι => R) μ (Fintype.equivFin ι).symm
  rw [← hφ.measure_preimage_equiv {x : ι → R | eval x P = 0}]
  have hpre : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => R) (Fintype.equivFin ι).symm) ⁻¹'
      {x : ι → R | eval x P = 0}) =
      {z : Fin (Fintype.card ι) → R | eval z (rename (Fintype.equivFin ι) P) = 0} := by
    ext z
    have happ : (MeasurableEquiv.piCongrLeft (fun _ : ι => R) (Fintype.equivFin ι).symm) z
        = fun i => z (Fintype.equivFin ι i) := by
      funext i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp [happ, eval_rename, Function.comp_def]
  rw [hpre]
  exact measure_pi_setOfPred_eval_eq_zero_fin _ _ _
    ((map_ne_zero_iff _ (rename_injective _ (Fintype.equivFin ι).injective)).2 hP)

end Null

/-- The zero locus of a nonzero multivariate polynomial is `volume`-null when `volume` is a
σ-finite measure without atoms; for instance, for real polynomials and Lebesgue measure. -/
theorem volume_setOfPred_eval_eq_zero {R ι : Type*} [CommRing R] [IsDomain R] [MeasureSpace R]
    [MeasurableSingletonClass R] [MeasurableAdd₂ R] [MeasurableMul₂ R]
    [SigmaFinite (volume : Measure R)] [NullSingletonClass (volume : Measure R)] [Fintype ι]
    (P : MvPolynomial ι R) (hP : P ≠ 0) : volume {x : ι → R | eval x P = 0} = 0 :=
  measure_pi_setOfPred_eval_eq_zero (fun _ => volume) P hP

end MvPolynomial
