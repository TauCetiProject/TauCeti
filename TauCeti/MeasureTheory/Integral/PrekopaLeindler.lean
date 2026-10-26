/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Analysis.Convex.LogConcave
-- Proof-only: weighted AM-GM, the minimum below a geometric mean, the layer-cake formula in
-- `ℝ≥0∞` and one-dimensional Brunn–Minkowski.
import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Real

/-!
# The Prékopa–Leindler inequality

For a measure on a real module, `Measure.HasPrekopaLeindler θ` records the weighted
Prékopa–Leindler inequality for measurable `ℝ≥0∞`-valued functions.  Its pointwise hypothesis
is imposed on the chosen measurable representatives, rather than only almost everywhere, so it is
stable under taking sections.

The property tensorizes: if two measures have the Prékopa–Leindler property at the same
weight, then their product measure has it as well.  Tonelli's theorem first applies the inequality
in the second variable and then applies it to the resulting marginal integrals in the first
variable, so only the second factor needs to be s-finite.  Iterating over the coordinates, a
finite product of σ-finite measures with the property has it as well.

The property is also transported by measure-preserving maps which preserve the weighted affine
combination.  This makes tensorization usable after changing linear coordinates or projecting to a
marginal.

Lebesgue measure on `ℝ` has the property for every weight `0 ≤ θ ≤ 1`; the endpoints are
monotonicity of the integral.  The interior case rests on a version of the inequality for the
minimum: if `f` and `g` have the same supremum and `min (f x) (g y) ≤ h (c * x + d * y)`, then
each superlevel set of `h` contains the weighted Minkowski sum of those of `f` and `g`, which are
nonempty below the common supremum, so one-dimensional Brunn–Minkowski and the layer-cake formula
give `c ∫ f + d ∫ g ≤ ∫ h`.  Normalizing the suprema of bounded `f` and `g` to one and applying
the weighted AM-GM inequality gives Prékopa–Leindler, and truncation removes the boundedness.
Tensorization then gives the inequality for Lebesgue measure on `ι → ℝ`, and linear isometries
transport it to every finite-dimensional real inner product space.

Applied once in the second variable, the inequality says that a marginal
`x ↦ ∫⁻ y, f (x, y) ∂ν` of a log-concave function `f` is log-concave. For the indicator of a
convex set this is Brunn's principle in log-concave form: the measures of the parallel slices of
a convex set form a log-concave function, so for a symmetric convex set the central slice is the
largest. This is the form in which Vaaler's cube-slicing theorem uses the inequality.

## Main results

* `MeasureTheory.Measure.HasPrekopaLeindler`: the measurable extended-integral inequality.
* `MeasureTheory.Measure.HasPrekopaLeindler.prod`: tensorization over product measures.
* `MeasureTheory.Measure.HasPrekopaLeindler.pi`: tensorization over finite products.
* `MeasureTheory.Measure.HasPrekopaLeindler.map`: transport by a measure-preserving affine map.
* `MeasureTheory.Measure.HasPrekopaLeindler.withDensity`,
  `MeasureTheory.Measure.HasPrekopaLeindler.restrict`: log-concave densities and restriction to
  convex sets preserve the property.
* `TauCeti.Real.mul_lintegral_add_mul_lintegral_le`: the inequality for the minimum on `ℝ`.
* `TauCeti.Real.hasPrekopaLeindler_volume`: the **Prékopa–Leindler inequality** on `ℝ`.
* `TauCeti.hasPrekopaLeindler_volume_pi`, `TauCeti.hasPrekopaLeindler_volume`: the inequality on
  `ι → ℝ` and on finite-dimensional real inner product spaces.
* `TauCeti.LogConcave.lintegral_prod_right`, `TauCeti.LogConcave.setLIntegral_prod_right`:
  marginals of log-concave functions are log-concave.
* `Convex.logConcave_measure_preimage_prodMk`: the slice measures of a convex set are
  log-concave.
* `Convex.measure_preimage_prodMk_le_measure_preimage_prodMk_zero`: the central slice of a
  symmetric convex set is the largest.

## References

* A. Prékopa, *Logarithmic concave measures with application to stochastic programming*, Acta
  Scientiarum Mathematicarum **32** (1971), 301–316.
* L. Leindler, *On a certain converse of Hölder's inequality II*, Acta Scientiarum Mathematicarum
  **33** (1972), 217–223.
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., AMS, 2001, Section 4.3.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for the one-dimensional level-set argument.
* Terence Tao, [The Brunn–Minkowski inequality for nilpotent groups]
  (https://terrytao.wordpress.com/2011/09/16/the-brunn-minkowski-inequality-for-nilpotent-groups/).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Lemma C.3.4, for marginals of log-concave functions. The statements and proofs of the marginal
  results are adapted from the Apache-2.0 formalization in `rwst/Subspace-Theorems` (files
  `ArithmeticHeights/LogConcave.lean` and `ArithmeticHeights/CubeSlicing.lean`), by Ralf Stephan.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

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

/-- A Dirac mass has the Prékopa–Leindler property at every weight. -/
theorem hasPrekopaLeindler_dirac (a : E) (theta : ℝ) :
    (Measure.dirac a).HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  rw [lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hh]
  simpa only [← add_smul, sub_add_cancel, one_smul] using hfg a a

/-- Transport the Prékopa–Leindler property through a measure-preserving map
which preserves the weighted affine combination. -/
theorem HasPrekopaLeindler.map {mu : Measure E} {nu : Measure F} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (e : E → F) (he : MeasurePreserving e mu nu)
    (haffine : ∀ x y, e ((1 - theta) • x + theta • y) =
      (1 - theta) • e x + theta • e y) :
    nu.HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  have hbound := hmu (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
    fun x y => by simpa only [Function.comp_apply, haffine] using hfg (e x) (e y)
  simpa only [Function.comp_apply, he.lintegral_comp hf, he.lintegral_comp hg,
    he.lintegral_comp hh] using hbound

/-- **Tensorization of Prékopa–Leindler.** If `mu` and `nu` satisfy the inequality at the same
weight, then so does their product measure. -/
theorem HasPrekopaLeindler.prod {mu : Measure E} {nu : Measure F} [SFinite nu]
    {theta : ℝ} (hmu : mu.HasPrekopaLeindler theta) (hnu : nu.HasPrekopaLeindler theta) :
    (mu.prod nu).HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  let fMarginal : E → ENNReal := fun x => ∫⁻ y, f (x, y) ∂nu
  let gMarginal : E → ENNReal := fun x => ∫⁻ y, g (x, y) ∂nu
  let hMarginal : E → ENNReal := fun x => ∫⁻ y, h (x, y) ∂nu
  have hfMarginal : Measurable fMarginal := hf.lintegral_prod_right'
  have hgMarginal : Measurable gMarginal := hg.lintegral_prod_right'
  have hhMarginal : Measurable hMarginal := hh.lintegral_prod_right'
  have hmarginal (x y : E) :
      (fMarginal x).rpow (1 - theta) * (gMarginal y).rpow theta ≤
        hMarginal ((1 - theta) • x + theta • y) := by
    apply hnu (hf.comp (measurable_const.prodMk measurable_id))
      (hg.comp (measurable_const.prodMk measurable_id))
      (hh.comp (measurable_const.prodMk measurable_id))
    intro a b
    simpa only [Function.comp_apply, id_eq, Prod.smul_mk, Prod.add_def] using hfg (x, a) (y, b)
  have hresult := hmu hfMarginal hgMarginal hhMarginal hmarginal
  rw [lintegral_prod f hf.aemeasurable, lintegral_prod g hg.aemeasurable,
    lintegral_prod h hh.aemeasurable]
  exact hresult

/-- Pull the Prékopa–Leindler property back along a measure-preserving measurable equivalence
whose forward map preserves the weighted affine combination. -/
theorem HasPrekopaLeindler.of_measurePreserving {mu : Measure E} {nu : Measure F} {theta : ℝ}
    (hnu : nu.HasPrekopaLeindler theta) (e : E ≃ᵐ F) (he : MeasurePreserving e mu nu)
    (haffine : ∀ x y, e ((1 - theta) • x + theta • y) = (1 - theta) • e x + theta • e y) :
    mu.HasPrekopaLeindler theta :=
  hnu.map e.symm he.symm fun x y ↦ e.injective <| by
    simp only [haffine, MeasurableEquiv.apply_symm_apply]

/-- **Tensorization of Prékopa–Leindler over finite products.** If σ-finite measures `μ i`
on finitely many real modules all satisfy the inequality at the same weight, then so does their
product measure. -/
theorem HasPrekopaLeindler.pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, AddCommMonoid (α i)] [∀ i, Module ℝ (α i)]
    {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)] {theta : ℝ}
    (h : ∀ i, (μ i).HasPrekopaLeindler theta) :
    (Measure.pi μ).HasPrekopaLeindler theta := by
  -- First treat the index types `Fin n`, splitting off the zeroth coordinate inductively.
  have hfin : ∀ (n : ℕ) (α : Fin n → Type _) [∀ i, MeasurableSpace (α i)]
      [∀ i, AddCommMonoid (α i)] [∀ i, Module ℝ (α i)] (μ : ∀ i, Measure (α i))
      [∀ i, SigmaFinite (μ i)], (∀ i, (μ i).HasPrekopaLeindler theta) →
      (Measure.pi μ).HasPrekopaLeindler theta := by
    intro n
    induction n with
    | zero =>
      intro α _ _ _ μ _ _
      rw [Measure.pi_of_empty μ isEmptyElim]
      exact hasPrekopaLeindler_dirac _ _
    | succ n ih =>
      intro α _ _ _ μ _ h f g k hf hg hk hfgk
      refine HasPrekopaLeindler.of_measurePreserving
        (HasPrekopaLeindler.prod (h 0) (ih _ (fun j ↦ μ (Fin.succAbove 0 j)) fun j ↦ h _))
        (MeasurableEquiv.piFinSuccAbove α 0) (measurePreserving_piFinSuccAbove μ 0)
        (fun x y ↦ ?_) hf hg hk hfgk
      -- Both components of `piFinSuccAbove` are coordinate evaluations, hence linear.
      ext j <;> rfl
  intro f g k hf hg hk hfgk
  let e := Fintype.equivFin ι
  refine HasPrekopaLeindler.map (hfin _ (fun j ↦ α (e.symm j)) (fun j ↦ μ (e.symm j)) fun j ↦ h _)
    (MeasurableEquiv.piCongrLeft α e.symm) (measurePreserving_piCongrLeft μ e.symm)
    (fun x y ↦ ?_) hf hg hk hfgk
  ext i
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  simp [MeasurableEquiv.piCongrLeft_apply_apply]

/-- **A log-concave density preserves Prékopa–Leindler.** If `mu` has the Prékopa–Leindler
property at a weight `0 ≤ θ ≤ 1` and `φ` is measurable and log-concave, then `mu.withDensity φ`
has it as well. For instance, the Gaussian density `exp (-π ‖x‖ ^ 2)` is log-concave. -/
theorem HasPrekopaLeindler.withDensity {mu : Measure E} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (hθ₀ : 0 ≤ theta) (hθ₁ : theta ≤ 1) {φ : E → ℝ≥0∞}
    (hφ : Measurable φ) (hlc : TauCeti.LogConcave φ) :
    (mu.withDensity φ).HasPrekopaLeindler theta := by
  intro f g h hf hg hh hfg
  simp only [lintegral_withDensity_eq_lintegral_mul _ hφ hf,
    lintegral_withDensity_eq_lintegral_mul _ hφ hg, lintegral_withDensity_eq_lintegral_mul _ hφ hh]
  refine hmu (hφ.mul hf) (hφ.mul hg) (hφ.mul hh) fun x y ↦ ?_
  have h1θ : 0 ≤ 1 - theta := by linarith
  simp only [Pi.mul_apply, ENNReal.rpow_eq_pow] at hfg ⊢
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ, ENNReal.mul_rpow_of_nonneg _ _ hθ₀]
  calc φ x ^ (1 - theta) * f x ^ (1 - theta) * (φ y ^ theta * g y ^ theta)
      = φ x ^ (1 - theta) * φ y ^ theta * (f x ^ (1 - theta) * g y ^ theta) := by ring
    _ ≤ _ := mul_le_mul' (hlc.rpow_mul_rpow_le h1θ hθ₀ (by ring)) (hfg x y)

/-- The restriction of a measure with the Prékopa–Leindler property at a weight `0 ≤ θ ≤ 1` to a
measurable convex set has the Prékopa–Leindler property as well. -/
theorem HasPrekopaLeindler.restrict {mu : Measure E} {theta : ℝ}
    (hmu : mu.HasPrekopaLeindler theta) (hθ₀ : 0 ≤ theta) (hθ₁ : theta ≤ 1) {s : Set E}
    (hs : MeasurableSet s) (hsc : Convex ℝ s) : (mu.restrict s).HasPrekopaLeindler theta := by
  rw [← withDensity_indicator_one hs]
  exact hmu.withDensity hθ₀ hθ₁ (measurable_one.indicator hs) (hsc.logConcave_indicator 1)

end MeasureTheory.Measure

namespace TauCeti.Real

/-- At each level `s`, the weighted volumes of the superlevel sets of `f` and `g` are bounded by
the volume of the superlevel set of `h`: below the common supremum the two sets are nonempty and
one-dimensional Brunn–Minkowski applies, and above it they are empty. -/
private theorem mul_volume_add_mul_volume_lt_le {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) (hfg : ⨆ x, f x = ⨆ y, g y) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hmin : ∀ x y, min (f x) (g y) ≤ h (c * x + d * y)) (s : ℝ≥0∞) :
    ENNReal.ofReal c * volume {x | s < f x} + ENNReal.ofReal d * volume {y | s < g y} ≤
      volume {z | s < h z} := by
  by_cases hs : s < ⨆ x, f x
  · obtain ⟨x, hx⟩ := lt_iSup_iff.1 hs
    obtain ⟨y, hy⟩ := lt_iSup_iff.1 (hfg ▸ hs)
    refine (mul_volume_add_mul_volume_le ⟨x, hx⟩ (hf.nullMeasurable measurableSet_Ioi)
      ⟨y, hy⟩ (hg.nullMeasurable measurableSet_Ioi) hc hd).trans (measure_mono ?_)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact (lt_min hx hy).trans_le (hmin x y)
  · have hf0 : {x | s < f x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hs (hx.trans_le (le_iSup f x))
    have hg0 : {y | s < g y} = ∅ :=
      eq_empty_of_forall_notMem fun y hy ↦ hs (hfg ▸ hy.trans_le (le_iSup g y))
    simp [hf0, hg0]

/-- **Prékopa–Leindler inequality for the minimum** on `ℝ`. If `f` and `g` have the same
supremum and `h (c * x + d * y)` dominates `min (f x) (g y)` for all `x` and `y`, then
`c ∫ f + d ∫ g ≤ ∫ h`. The coefficients may vanish, and the common supremum and the integrals may
be infinite. -/
theorem mul_lintegral_add_mul_lintegral_le {f g h : ℝ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) (hh : AEMeasurable h) (hfg : ⨆ x, f x = ⨆ y, g y) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hmin : ∀ x y, min (f x) (g y) ≤ h (c * x + d * y)) :
    ENNReal.ofReal c * (∫⁻ x, f x) + ENNReal.ofReal d * ∫⁻ y, g y ≤ ∫⁻ z, h z := by
  -- The layer-cake formula in `ℝ≥0∞`, at the exponent one.
  have hlayer {u : ℝ → ℝ≥0∞} (hu : AEMeasurable u) :
      ∫⁻ x, u x = ∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < u x} := by
    simpa using lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume hu one_pos
  rw [hlayer hf, hlayer hg, hlayer hh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (le_lintegral_add _ _).trans <| lintegral_mono fun t ↦
    mul_volume_add_mul_volume_lt_le hf hg hfg hc hd hmin _

/-- The one-dimensional Prékopa–Leindler inequality at an interior weight, for `f` and `g` with
finite suprema. -/
private theorem rpow_mul_rpow_le_of_iSup_ne_top {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hF : ⨆ x, f x ≠ ∞) (hG : ⨆ y, g y ≠ ∞)
    (hfgh : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ y, g y) ^ θ ≤ ∫⁻ z, h z := by
  set F := ⨆ x, f x
  set G := ⨆ y, g y
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  rcases eq_or_ne F 0 with hF0 | hF0
  · simp [ENNReal.iSup_eq_zero.1 hF0, ENNReal.zero_rpow_of_pos h1θ]
  rcases eq_or_ne G 0 with hG0 | hG0
  · simp [ENNReal.iSup_eq_zero.1 hG0, ENNReal.zero_rpow_of_pos hθ₀]
  -- Normalize the suprema of `f` and `g` to one, and scale `h` by the matching factor `K⁻¹`.
  set K := F ^ (1 - θ) * G ^ θ
  have hK0 : K ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hF0) hF).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hG0) hG).ne'
  have hKtop : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1θ.le hF)
    (ENNReal.rpow_ne_top_of_nonneg hθ₀.le hG)
  have hscale (a b : ℝ≥0∞) :
      (F⁻¹ * a) ^ (1 - θ) * (G⁻¹ * b) ^ θ = K⁻¹ * (a ^ (1 - θ) * b ^ θ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ₀.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, ENNReal.mul_inv (.inr (ENNReal.rpow_ne_top_of_nonneg
      hθ₀.le hG)) (.inl (ENNReal.rpow_ne_top_of_nonneg h1θ.le hF))]
    ring
  have hsup : ⨆ x, F⁻¹ * f x = ⨆ y, G⁻¹ * g y := by
    rw [← ENNReal.mul_iSup, ← ENNReal.mul_iSup, ENNReal.inv_mul_cancel hF0 hF,
      ENNReal.inv_mul_cancel hG0 hG]
  have key := mul_lintegral_add_mul_lintegral_le (hf.const_mul _).aemeasurable
    (hg.const_mul _).aemeasurable (hh.const_mul K⁻¹).aemeasurable hsup h1θ.le hθ₀.le
    fun x y ↦ (ENNReal.min_le_rpow_one_sub_mul_rpow _ _ hθ₀.le hθ₁.le).trans <| by
      rw [hscale]
      gcongr
      exact hfgh x y
  rw [lintegral_const_mul _ hf, lintegral_const_mul _ hg, lintegral_const_mul _ hh] at key
  have hamgm := ENNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal (1 - θ))
    (Real.toNNReal θ) (F⁻¹ * ∫⁻ x, f x) (G⁻¹ * ∫⁻ y, g y) (by
      rw [← Real.toNNReal_add h1θ.le hθ₀.le, sub_add_cancel, Real.toNNReal_one])
  rw [Real.coe_toNNReal _ h1θ.le, Real.coe_toNNReal _ hθ₀.le, hscale] at hamgm
  rw [← ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 hKtop) (ENNReal.inv_ne_top.2 hK0)]
  exact hamgm.trans key

/-- The **Prékopa–Leindler inequality** on `ℝ`: Lebesgue measure has the Prékopa–Leindler
property at every weight `0 ≤ θ ≤ 1`. -/
theorem hasPrekopaLeindler_volume {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (volume : Measure ℝ).HasPrekopaLeindler θ := by
  intro f g h hf hg hh hfgh
  simp only [ENNReal.rpow_eq_pow] at hfgh ⊢
  rcases hθ₀.eq_or_lt with rfl | hθ₀
  · simpa using lintegral_mono fun x ↦ by simpa using hfgh x x
  rcases hθ₁.eq_or_lt with rfl | hθ₁
  · simpa using lintegral_mono fun y ↦ by simpa using hfgh y y
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ₁
  -- Truncate `f` and `g` at finite heights and pass to the limit by monotone convergence.
  have htrunc {u : ℝ → ℝ≥0∞} (hu : Measurable u) :
      ∫⁻ x, u x = ⨆ n : ℕ, ∫⁻ x, min (u x) n := by
    rw [← lintegral_iSup (fun n ↦ hu.min measurable_const)
      fun m n hmn x ↦ min_le_min_left _ (Nat.cast_le.2 hmn)]
    simp [← inf_iSup_eq, ENNReal.iSup_natCast]
  have hbdd {u : ℝ → ℝ≥0∞} (n : ℕ) : ⨆ x, min (u x) n ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun _ ↦ min_le_right _ _)
  have key (m n : ℕ) :
      (∫⁻ x, min (f x) m) ^ (1 - θ) * (∫⁻ y, min (g y) n) ^ θ ≤ ∫⁻ z, h z :=
    rpow_mul_rpow_le_of_iSup_ne_top hθ₀ hθ₁ (hf.min measurable_const)
      (hg.min measurable_const) hh (hbdd m) (hbdd n) fun x y ↦
      (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) h1θ.le)
        (ENNReal.rpow_le_rpow (min_le_left _ _) hθ₀.le)).trans (hfgh x y)
  rw [htrunc hf, htrunc hg, ← ENNReal.orderIsoRpow_apply _ h1θ,
    ← ENNReal.orderIsoRpow_apply _ hθ₀, OrderIso.map_iSup, OrderIso.map_iSup, ENNReal.iSup_mul]
  exact iSup_le fun m ↦ by
    rw [ENNReal.mul_iSup]
    exact iSup_le fun n ↦ by simpa using key m n

end TauCeti.Real

namespace TauCeti

/-- The **Prékopa–Leindler inequality** on `ι → ℝ`: Lebesgue measure on a finite power of `ℝ` has
the Prékopa–Leindler property at every weight `0 ≤ θ ≤ 1`. -/
theorem hasPrekopaLeindler_volume_pi (ι : Type*) [Fintype ι] {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : (volume : Measure (ι → ℝ)).HasPrekopaLeindler θ := by
  intro f g h hf hg hh hfgh
  exact Measure.HasPrekopaLeindler.pi (fun _ ↦ Real.hasPrekopaLeindler_volume hθ₀ hθ₁)
    hf hg hh hfgh

/-- The **Prékopa–Leindler inequality** on a finite-dimensional real inner product space, such as
`EuclideanSpace ℝ (Fin n)`: its volume has the Prékopa–Leindler property at every weight
`0 ≤ θ ≤ 1`. -/
theorem hasPrekopaLeindler_volume (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : (volume : Measure E).HasPrekopaLeindler θ := by
  intro f g h hf hg hh hfgh
  let b := stdOrthonormalBasis ℝ E
  exact Measure.HasPrekopaLeindler.map (hasPrekopaLeindler_volume_pi (Fin _) hθ₀ hθ₁)
    (b.repr.symm ∘ WithLp.toLp 2)
    (b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp _))
    (fun x y ↦ by simp) hf hg hh hfgh

end TauCeti

/-! ### Marginals of log-concave functions -/

namespace TauCeti

section AddCommMonoid

variable {E F : Type*} [MeasurableSpace E] [AddCommMonoid E] [Module ℝ E]
  [MeasurableSpace F] [AddCommMonoid F] [Module ℝ F] {ν : Measure F}

/-- **Marginals of log-concave functions are log-concave** (Prékopa; Bombieri–Gubler, Lemma
C.3.4). If `f : E × F → ℝ≥0∞` is measurable and log-concave and `ν` has the Prékopa–Leindler
property at every weight, then `x ↦ ∫⁻ y, f (x, y) ∂ν` is log-concave. No measure on `E` and no
finiteness of the integrals is needed. -/
theorem LogConcave.lintegral_prod_right
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {f : E × F → ℝ≥0∞}
    (hf : Measurable f) (hlc : LogConcave f) :
    LogConcave fun x ↦ ∫⁻ y, f (x, y) ∂ν := by
  refine logConcave_def.2 fun x₁ x₂ a b ha hb hab ↦ ?_
  obtain rfl : a = 1 - b := by linarith
  have hPL := hν hb (by linarith) (hf.comp measurable_prodMk_left)
    (hf.comp measurable_prodMk_left) (hf.comp measurable_prodMk_left) fun y₁ y₂ ↦ by
      simpa [ENNReal.rpow_eq_pow] using
        hlc.rpow_mul_rpow_le (x := (x₁, y₁)) (y := (x₂, y₂)) ha hb hab
  simpa [ENNReal.rpow_eq_pow] using hPL

/-- **Marginals over a convex set of log-concave functions are log-concave** (Bombieri–Gubler,
Lemma C.3.4). If `f : E × F → ℝ≥0∞` is measurable and log-concave, `s ⊆ F` is measurable and
convex, and `ν` has the Prékopa–Leindler property at every weight, then
`x ↦ ∫⁻ y in s, f (x, y) ∂ν` is log-concave. -/
theorem LogConcave.setLIntegral_prod_right
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {f : E × F → ℝ≥0∞}
    (hf : Measurable f) (hlc : LogConcave f) {s : Set F} (hs : MeasurableSet s)
    (hsc : Convex ℝ s) :
    LogConcave fun x ↦ ∫⁻ y in s, f (x, y) ∂ν := by
  have h := (hlc.mul ((hsc.linear_preimage (LinearMap.snd ℝ E F)).logConcave_indicator 1)
    ).lintegral_prod_right hν (hf.mul (measurable_const.indicator (hs.preimage measurable_snd)))
  convert h using 2 with x
  rw [← lintegral_indicator hs]
  congr 1 with y
  by_cases hy : y ∈ s <;> simp [hy]

/-- **Brunn's principle, in log-concave form.** For a measurable convex set `s ⊆ E × F` and a
measure `ν` with the Prékopa–Leindler property at every weight, the measure of the slices,
`x ↦ ν (Prod.mk x ⁻¹' s)`, is log-concave. -/
theorem _root_.Convex.logConcave_measure_preimage_prodMk
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {s : Set (E × F)}
    (hs : MeasurableSet s) (hsc : Convex ℝ s) :
    LogConcave fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  convert (hsc.logConcave_indicator 1).lintegral_prod_right hν
    (measurable_const.indicator hs) using 2 with x
  rw [← lintegral_indicator_one (measurable_prodMk_left hs)]
  exact lintegral_congr fun y ↦ by by_cases hy : (x, y) ∈ s <;> simp [hy]

end AddCommMonoid

variable {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {ν : Measure F}

/-- **The central slice of a symmetric convex set is the largest.** For a measurable convex set
`s ⊆ E × F` with `-s = s` and a negation-invariant measure `ν` with the Prékopa–Leindler
property at every weight, every slice `Prod.mk x ⁻¹' s` has measure at most that of the central
slice `Prod.mk 0 ⁻¹' s`. -/
theorem _root_.Convex.measure_preimage_prodMk_le_measure_preimage_prodMk_zero
    [MeasurableNeg F] [ν.IsNegInvariant]
    (hν : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν.HasPrekopaLeindler θ) {s : Set (E × F)}
    (hs : MeasurableSet s) (hsc : Convex ℝ s) (hneg : ∀ p ∈ s, -p ∈ s) (x : E) :
    ν (Prod.mk x ⁻¹' s) ≤ ν (Prod.mk 0 ⁻¹' s) := by
  refine (hsc.logConcave_measure_preimage_prodMk hν hs).apply_le_apply_zero (fun x ↦ ?_) x
  have hslice : Prod.mk (-x) ⁻¹' s = -(Prod.mk x ⁻¹' s) := by
    ext y
    simp only [mem_preimage, Set.mem_neg]
    exact ⟨fun h ↦ by simpa using hneg _ h, fun h ↦ by simpa using hneg _ h⟩
  dsimp only
  rw [hslice, Measure.measure_neg]

end TauCeti
