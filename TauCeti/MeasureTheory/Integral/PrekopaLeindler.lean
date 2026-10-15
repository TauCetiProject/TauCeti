/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Prékopa–Leindler tensorization

For a measure on a real module, `Measure.HasPrekopaLeindler θ` records the weighted
Prékopa–Leindler inequality for measurable `ℝ≥0∞`-valued functions.  Its pointwise hypothesis
is imposed on the chosen measurable representatives, rather than only almost everywhere, so it is
stable under taking sections.

The main result is tensorization: if two measures have the Prékopa–Leindler property at the same
weight, then their product measure has it as well.  Tonelli's theorem first applies the inequality
in the first variable and then applies it to the resulting marginal integrals in the second
variable.  Thus a one-dimensional proof can be iterated to obtain the inequality in finite product
spaces.

The property is also transported by measure-preserving measurable equivalences which preserve the
weighted affine combination.  This makes tensorization usable after changing linear coordinates.

## Main results

* `MeasureTheory.Measure.HasPrekopaLeindler`: the measurable extended-integral inequality.
* `MeasureTheory.Measure.HasPrekopaLeindler.prod`: tensorization over product measures.
* `MeasureTheory.Measure.HasPrekopaLeindler.map`: transport by a measure-preserving affine
  equivalence.

## References

* A. Prékopa, *Logarithmic concave measures with application to stochastic programming*, Acta
  Scientiarum Mathematicarum **32** (1971), 301–316.
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., AMS, 2001, Section 4.3.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- A measure has the **Prékopa–Leindler property** at weight `θ` if every three measurable
nonnegative extended-valued functions satisfying the pointwise weighted geometric-mean bound also
satisfy the corresponding bound on their integrals.

The pointwise bound is deliberately imposed on the supplied measurable representatives.  This is
the form which tensorizes without choosing new representatives on individual sections. -/
def HasPrekopaLeindler (mu : Measure E) (theta : ℝ) : Prop :=
  ∀ {f g h : E → ENNReal}, Measurable f → Measurable g → Measurable h →
    (∀ x y, (f x).rpow (1 - theta) * (g y).rpow theta ≤
      h ((1 - theta) • x + theta • y)) →
    (∫⁻ x, f x ∂mu).rpow (1 - theta) * (∫⁻ x, g x ∂mu).rpow theta ≤
      ∫⁻ x, h x ∂mu

/-- The Prékopa–Leindler property unfolded into its measurable-function formulation. -/
theorem hasPrekopaLeindler_def (mu : Measure E) (theta : ℝ) :
    mu.HasPrekopaLeindler theta ↔
      ∀ {f g h : E → ENNReal}, Measurable f → Measurable g → Measurable h →
        (∀ x y, (f x).rpow (1 - theta) * (g y).rpow theta ≤
          h ((1 - theta) • x + theta • y)) →
        (∫⁻ x, f x ∂mu).rpow (1 - theta) * (∫⁻ x, g x ∂mu).rpow theta ≤
          ∫⁻ x, h x ∂mu :=
  Iff.rfl

/-- A Dirac mass at the origin has the Prékopa–Leindler property at every weight. -/
theorem hasPrekopaLeindler_dirac_zero (theta : ℝ) :
    (Measure.dirac (0 : E)).HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  rw [lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hh]
  simpa using hfg 0 0

/-- Transport the Prékopa–Leindler property through a measure-preserving measurable equivalence
which preserves the weighted affine combination. -/
theorem HasPrekopaLeindler.map {mu : Measure E} {nu : Measure F} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (e : E ≃ᵐ F) (he : MeasurePreserving e mu nu)
    (haffine : ∀ x y, e ((1 - theta) • x + theta • y) =
      (1 - theta) • e x + theta • e y) :
    nu.HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  have hbound := hmu (hf.comp e.measurable) (hg.comp e.measurable) (hh.comp e.measurable)
    fun x y => by simpa only [Function.comp_apply, haffine] using hfg (e x) (e y)
  simpa only [Function.comp_apply, he.lintegral_comp hf, he.lintegral_comp hg,
    he.lintegral_comp hh] using hbound

/-- **Tensorization of Prékopa–Leindler.** If `mu` and `nu` satisfy the inequality at the same
weight, then so does their product measure. -/
theorem HasPrekopaLeindler.prod {mu : Measure E} {nu : Measure F} [SFinite mu] [SFinite nu]
    {theta : ℝ} (hmu : mu.HasPrekopaLeindler theta) (hnu : nu.HasPrekopaLeindler theta) :
    (mu.prod nu).HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  let fMarginal : F → ENNReal := fun y => ∫⁻ x, f (x, y) ∂mu
  let gMarginal : F → ENNReal := fun y => ∫⁻ x, g (x, y) ∂mu
  let hMarginal : F → ENNReal := fun y => ∫⁻ x, h (x, y) ∂mu
  have hfMarginal : Measurable fMarginal := hf.lintegral_prod_left'
  have hgMarginal : Measurable gMarginal := hg.lintegral_prod_left'
  have hhMarginal : Measurable hMarginal := hh.lintegral_prod_left'
  have hmarginal (x y : F) :
      (fMarginal x).rpow (1 - theta) * (gMarginal y).rpow theta ≤
        hMarginal ((1 - theta) • x + theta • y) := by
    apply hmu (hf.comp (measurable_id.prodMk measurable_const))
      (hg.comp (measurable_id.prodMk measurable_const))
      (hh.comp (measurable_id.prodMk measurable_const))
    intro a b
    simpa only [Function.comp_apply, id_eq, Prod.smul_mk, Prod.add_def] using hfg (a, x) (b, y)
  have hresult := hnu hfMarginal hgMarginal hhMarginal hmarginal
  rw [lintegral_prod_symm' f hf, lintegral_prod_symm' g hg, lintegral_prod_symm' h hh]
  exact hresult

end MeasureTheory.Measure
