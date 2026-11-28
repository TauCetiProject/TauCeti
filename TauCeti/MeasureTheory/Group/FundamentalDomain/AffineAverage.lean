/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Averaging affine lattice translates

Averaging the sum of a nonnegative kernel over lattice translates of a parameter in a fundamental
domain gives its full integral divided by the mass of the domain. An invertible linear change
of variables contributes the inverse absolute determinant, and a constant shift does not change
the integral. For an orbit covered by finitely many affine lattice cosets, the average of its
weights is bounded by charging each coset and a uniform allowance for each fibre.

The application is the lattice averaging step of `New.Filling.tsum_schurIntegral_le` in
`grh/src/New/Spanning/RemainingTerms/SchurOrbit.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open scoped ENNReal

namespace MeasureTheory.IsAddFundamentalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {L : AddSubgroup E} [Countable L] {D : Set E}

/-- Integrating a nonnegative kernel summed over a finite family of affine lattice translates
on a fundamental domain charges one full-space integral per coset, times the inverse absolute
determinant of the common linear part. Cosets may be repeated, in which case each copy counts. -/
theorem lintegral_sum_tsum_affine (hD : IsAddFundamentalDomain L D μ) {A : E →ₗ[ℝ] E}
    (hA : LinearMap.det A ≠ 0) {ι : Type*} [Fintype ι] (a : ι → E)
    {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x in D, (∑ i, ∑' v : L, f (A ((v : E) + x) + a i)) ∂μ =
      (Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal |(LinearMap.det A)⁻¹| * ∫⁻ x, f x ∂μ) := by
  have hAq := Measure.LinearMap.quasiMeasurePreserving μ A hA
  have hmeas (i : ι) (v : L) :
      AEMeasurable (fun x ↦ f (A ((v : E) + x) + a i)) (μ.restrict D) := by
    have h := hf.comp_quasiMeasurePreserving
      ((measurePreserving_add_right μ (a i)).quasiMeasurePreserving.comp
        (hAq.comp (measurePreserving_add_left μ (v : E)).quasiMeasurePreserving))
    exact h.restrict
  rw [lintegral_finsetSum' _ fun i _ ↦ AEMeasurable.tsum (hmeas i)]
  have hcoset (i : ι) :
      ∫⁻ x in D, (∑' v : L, f (A ((v : E) + x) + a i)) ∂μ =
        ENNReal.ofReal |(LinearMap.det A)⁻¹| * ∫⁻ x, f x ∂μ := by
    rw [lintegral_tsum (hmeas i)]
    calc
      _ = ∫⁻ x, f (A x + a i) ∂μ := (hD.lintegral_eq_tsum'' (fun x ↦ f (A x + a i))).symm
      _ = _ := by
        rw [lintegral_comp_linearMap μ hA (fun x ↦ f (x + a i)), lintegral_add_right_eq_self]
  simp only [hcoset, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Bound the average of nonnegative orbit weights assigned to finitely many affine lattice
cosets with representatives `a`. Label each term by a coset and a lattice vector using `c`.
It suffices to dominate the sum on each fibre of `c` by the corresponding shifted kernel
value times `C`; the individual weights need not be measurable. -/
theorem laverage_tsum_affine_le (hD : IsAddFundamentalDomain L D μ) {A : E →ₗ[ℝ] E}
    (hA : LinearMap.det A ≠ 0) {ι T : Type*} [Fintype ι] (a : ι → E) (c : T → ι × L)
    {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) (w : T → E → ℝ≥0∞) (C : ℝ≥0∞)
    (hw : ∀ᵐ x ∂μ.restrict D, ∀ p : ι × L,
      (∑' t : {t // c t = p}, w t x) ≤ C * f (A ((p.2 : E) + x) + a p.1)) :
    (⨍⁻ x in D, ∑' t, w t x ∂μ) ≤
      ((Fintype.card ι : ℝ≥0∞) * C * ENNReal.ofReal |(LinearMap.det A)⁻¹| *
        ∫⁻ x, f x ∂μ) / μ D := by
  rw [setLAverage_eq]
  gcongr 1
  -- Group the orbit weights by their labels before integrating the common majorant.
  have hmajor : ∀ᵐ x ∂μ.restrict D,
      (∑' t, w t x) ≤ ∑ i, ∑' v : L, C * f (A ((v : E) + x) + a i) := by
    filter_upwards [hw] with x hx
    calc
      _ = ∑' p : ι × L, ∑' t : {t // c t = p}, w t x := (tsum_fiberwise _ c).symm
      _ ≤ ∑' p : ι × L, C * f (A ((p.2 : E) + x) + a p.1) := tsum_le_tsum hx
      _ = _ := by rw [tsum_prod', tsum_fintype]
  calc
    _ ≤ ∫⁻ x in D, (∑ i, ∑' v : L, C * f (A ((v : E) + x) + a i)) ∂μ := lintegral_mono_ae hmajor
    _ = _ := by
      have hCf : AEMeasurable (fun x ↦ C * f x) μ := aemeasurable_const.mul hf
      rw [hD.lintegral_sum_tsum_affine hA a hCf, lintegral_const_mul'' _ hf]
      ac_rfl

end MeasureTheory.IsAddFundamentalDomain
