/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Incidence.Basic
public import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith

/-!
# Parametric incidence transversality in finite dimensions

Let `F : E × P → V` be a parametrized family of maps and `j : W → V` a target map between
finite-dimensional real normed spaces. Specializing the Morse--Sard level-set theorems
`TauCeti.addHaar_setOf_not_isRegularParameterOn_eq_zero` and
`TauCeti.dense_setOf_isRegularParameterOn` from
`TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional` to `TauCeti.incidenceEquation F j` at level
`0` shows that if `F` and `j` are `C^n` above the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n` and the total derivative of
`incidenceEquation F j` is surjective along the incidence locus inside `U ⊆ (E × W) × P`, then the
parameters `p : P` failing incidence regularity on `U` form a set of additive Haar measure zero, and
the regular parameters are dense in `P`. Countable intersections of full-measure sets extend this
to simultaneous transversality (and low-dimensional avoidance) against countable families of target
maps.

## Main results

* `TauCeti.addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero`,
  `TauCeti.ae_isRegularIncidenceParameterOn`, and
  `TauCeti.dense_setOf_isRegularIncidenceParameterOn`: localized measure-zero, almost-everywhere,
  and density theorems for regular incidence parameters on `U`.
* `TauCeti.addHaar_setOf_not_isRegularIncidenceParameter_eq_zero`,
  `TauCeti.ae_isRegularIncidenceParameter`, and
  `TauCeti.dense_setOf_isRegularIncidenceParameter`: global `C^n` forms.
* `TauCeti.ae_forall_isRegularIncidenceParameterOn`,
  `TauCeti.dense_setOf_forall_isRegularIncidenceParameterOn`, and
  `TauCeti.ae_forall_disjoint_range_of_finrank_lt`: simultaneous generic transversality and
  dimension-counting avoidance for countable families of incidence problems.
* `TauCeti.isRegularIncidenceParameter_sq_add_zero_iff`: characterizes regular parameters of the
  quadratic family `(x, p) ↦ x ^ 2 + p` on `ℝ` against the origin (`p ≠ 0`), accompanied by
  concrete point-evaluation and identity-target examples.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2012, Chapter 6, Theorem 6.35 (Parametric Transversality Theorem).
* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 2 §3.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, Theorem 2.7.
-/

public section

open Filter Function MeasureTheory MeasureTheory.Measure Module Set
open scoped ContDiff Topology

namespace TauCeti

section FiniteDimensionalGeneric

variable {E W V P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Generic incidence parameters on a subset `U` (measure form).** Let `F : E × P → V` and
`j : W → V` be maps between finite-dimensional real normed spaces, and `U ⊆ (E × W) × P` any set.
If at every incidence point `z = ((x, y), p) ∈ U` with `F (x, p) = j y`, `F` is `C^n` at `(x, p)`,
`j` is `C^n` at `y`, and the total derivative of `incidenceEquation F j` at `z` is surjective, with
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, then the parameters not regular on `U` have
additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {n : ℕ∞ω}
    (hF : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n j z.1.2)
    (htotal : ∀ z ∈ U, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameterOn F j U p} = 0 := by
  have hn' : ((finrank ℝ (E × W) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rwa [Module.finrank_prod]
  simpa only [isRegularIncidenceParameterOn_iff] using
    addHaar_setOf_not_isRegularParameterOn_eq_zero (f := incidenceEquation F j) μ
      (fun z hzU hz0 ↦ (hF z hzU hz0).incidenceEquation (hj z hzU hz0))
      htotal hn'

/-- Almost every parameter for additive Haar measure is a regular incidence parameter on `U`. -/
theorem ae_isRegularIncidenceParameterOn
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {n : ℕ∞ω}
    (hF : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n j z.1.2)
    (htotal : ∀ z ∈ U, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameterOn F j U p :=
  ae_iff.2 (addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero μ hF hj htotal hn)

/-- The parameters that are regular on `U` are dense in `P` (needing no measurable space on `P`). -/
theorem dense_setOf_isRegularIncidenceParameterOn
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {n : ℕ∞ω}
    (hF : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n j z.1.2)
    (htotal : ∀ z ∈ U, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | IsRegularIncidenceParameterOn F j U p} := by
  have hn' : ((finrank ℝ (E × W) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rwa [Module.finrank_prod]
  simpa only [isRegularIncidenceParameterOn_iff] using
    dense_setOf_isRegularParameterOn (f := incidenceEquation F j)
      (fun z hzU hz0 ↦ (hF z hzU hz0).incidenceEquation (hj z hzU hz0))
      htotal hn'

/-- **Generic incidence parameters (global `C^n` measure form).** Under universal transversality for
`C^n` maps between finite-dimensional real normed spaces satisfying the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, the parameters whose slice is not transverse to
`j` have additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameter_eq_zero
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : W → V} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (hj : ContDiff ℝ n j)
    (htotal : ∀ z, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameter F j p} = 0 := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero (U := univ) μ
      (fun _ _ _ ↦ hF.contDiffAt) (fun _ _ _ ↦ hj.contDiffAt)
      (fun z _ ↦ htotal z) hn

/-- Almost every parameter for additive Haar measure has a slice transverse to `j`. -/
theorem ae_isRegularIncidenceParameter
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : W → V} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (hj : ContDiff ℝ n j)
    (htotal : ∀ z, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameter F j p :=
  ae_iff.2 (addHaar_setOf_not_isRegularIncidenceParameter_eq_zero μ hF hj htotal hn)

/-- The regular incidence parameters of a universally transverse `C^n` family above the Morse--Sard
threshold are dense in `P`. -/
theorem dense_setOf_isRegularIncidenceParameter
    {F : E × P → V} {j : W → V} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (hj : ContDiff ℝ n j)
    (htotal : ∀ z, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | IsRegularIncidenceParameter F j p} := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    dense_setOf_isRegularIncidenceParameterOn (U := univ)
      (fun _ _ _ ↦ hF.contDiffAt) (fun _ _ _ ↦ hj.contDiffAt)
      (fun z _ ↦ htotal z) hn

end FiniteDimensionalGeneric

section CountableFamily

variable {ι P : Type*} [Countable ι]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {E W V : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]
  [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, FiniteDimensional ℝ (V i)]

/-- **Simultaneous generic transversality for a countable family of incidence problems.** Almost
every parameter `p : P` (for additive Haar measure) is simultaneously regular on `U i` for
`F i : E i × P → V i` against `j i : W i → V i` for all `i : ι`. -/
theorem ae_forall_isRegularIncidenceParameterOn
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : ∀ i, E i × P → V i} {j : ∀ i, W i → V i}
    {U : ∀ i, Set ((E i × W i) × P)} {n : ι → ℕ∞ω}
    (hF : ∀ i, ∀ z ∈ U i, incidenceEquation (F i) (j i) z = 0 →
      ContDiffAt ℝ (n i) (F i) (z.1.1, z.2))
    (hj : ∀ i, ∀ z ∈ U i, incidenceEquation (F i) (j i) z = 0 →
      ContDiffAt ℝ (n i) (j i) z.1.2)
    (htotal : ∀ i, ∀ z ∈ U i, incidenceEquation (F i) (j i) z = 0 →
      Surjective (fderiv ℝ (incidenceEquation (F i) (j i)) z))
    (hn : ∀ i, ((finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ (V i) + 1 : ℕ) : ℕ∞ω) ≤ n i) :
    ∀ᵐ p ∂μ, ∀ i, IsRegularIncidenceParameterOn (F i) (j i) (U i) p :=
  ae_all_iff.2 fun i ↦
    ae_isRegularIncidenceParameterOn μ (hF i) (hj i) (htotal i) (hn i)

/-- Parameters simultaneously regular on `U i` for `F i : E i × P → V i` against a countable family
`j i : W i → V i` are dense in `P`. -/
theorem dense_setOf_forall_isRegularIncidenceParameterOn
    {F : ∀ i, E i × P → V i} {j : ∀ i, W i → V i}
    {U : ∀ i, Set ((E i × W i) × P)} {n : ι → ℕ∞ω}
    (hF : ∀ i, ∀ z ∈ U i, incidenceEquation (F i) (j i) z = 0 →
      ContDiffAt ℝ (n i) (F i) (z.1.1, z.2))
    (hj : ∀ i, ∀ z ∈ U i, incidenceEquation (F i) (j i) z = 0 →
      ContDiffAt ℝ (n i) (j i) z.1.2)
    (htotal : ∀ i, ∀ z ∈ U i, incidenceEquation (F i) (j i) z = 0 →
      Surjective (fderiv ℝ (incidenceEquation (F i) (j i)) z))
    (hn : ∀ i, ((finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ (V i) + 1 : ℕ) : ℕ∞ω) ≤ n i) :
    Dense {p | ∀ i, IsRegularIncidenceParameterOn (F i) (j i) (U i) p} := by
  borelize P
  exact Measure.dense_of_ae (μ := (addHaar : Measure P))
    (ae_forall_isRegularIncidenceParameterOn addHaar hF hj htotal hn)

/-- **Simultaneous generic avoidance of a countable family of low-dimensional targets.** When
`finrank ℝ (E i) + finrank ℝ (W i) < finrank ℝ (V i)` for every `i`, almost every parameter `p`
gives slices `x ↦ F i (x, p)` whose images miss `range (j i)` for all `i`. Notice that `1 ≤ n i`
already meets the Morse--Sard threshold
`finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ (V i) + 1 = 1`. -/
theorem ae_forall_disjoint_range_of_finrank_lt
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : ∀ i, E i × P → V i} {j : ∀ i, W i → V i} {n : ι → ℕ∞ω} (hn : ∀ i, 1 ≤ n i)
    (hF : ∀ i z, incidenceEquation (F i) (j i) z = 0 → ContDiffAt ℝ (n i) (F i) (z.1.1, z.2))
    (hj : ∀ i z, incidenceEquation (F i) (j i) z = 0 → ContDiffAt ℝ (n i) (j i) z.1.2)
    (htotal : ∀ i z, incidenceEquation (F i) (j i) z = 0 →
      Surjective (fderiv ℝ (incidenceEquation (F i) (j i)) z))
    (hdim : ∀ i, finrank ℝ (E i) + finrank ℝ (W i) < finrank ℝ (V i)) :
    ∀ᵐ p ∂μ, ∀ i, Disjoint (range fun x ↦ F i (x, p)) (range (j i)) := by
  have hae := ae_forall_isRegularIncidenceParameterOn (U := fun _ ↦ univ) (n := n) μ
    (fun i z _ ↦ hF i z) (fun i z _ ↦ hj i z) (fun i z _ ↦ htotal i z) fun i ↦ by
      have hsub : finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ (V i) = 0 :=
        Nat.sub_eq_zero_of_le (hdim i).le
      simpa [hsub] using hn i
  filter_upwards [hae] with p hp i
  exact (isRegularIncidenceParameterOn_univ.1 (hp i)).disjoint_range (hdim i)

end CountableFamily

section Examples

/-- For the quadratic family `F(x, p) = x ^ 2 + p` on `ℝ` against the point `0 : Unit → ℝ`, a
parameter `p : ℝ` is regular if and only if `p ≠ 0`: at `p = 0` the unique solution `x = 0` is
degenerate, for `p < 0` the two roots `±√(-p)` have nonzero derivative `2 x`, and for `p > 0` the
fibre is empty. -/
theorem isRegularIncidenceParameter_sq_add_zero_iff (p : ℝ) :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) (fun _ : Unit ↦ (0 : ℝ)) p ↔
      p ≠ 0 := by
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) :=
    (contDiff_fst.pow 2).add contDiff_snd
  have hj : ContDiff ℝ ∞ (fun _ : Unit ↦ (0 : ℝ)) := contDiff_const
  rw [isRegularIncidenceParameter_iff_surjective_coprod
    (fun _ _ _ ↦ hF.contDiffAt.differentiableAt (by simp))
    (fun _ _ _ ↦ hj.contDiffAt.differentiableAt (by simp))]
  have hslice (x u : ℝ) :
      fderiv ℝ (fun x' : ℝ ↦ (x', p).1 ^ 2 + (x', p).2) x u = 2 * x * u := by
    have hd : HasDerivAt (fun x' : ℝ ↦ x' ^ 2 + p) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const p
    have hfd := hd.hasFDerivAt.fderiv
    have hfun : (fun x' : ℝ ↦ (x', p).1 ^ 2 + (x', p).2) = fun x' : ℝ ↦ x' ^ 2 + p := rfl
    rw [hfun, hfd]
    simp [mul_comm]
  have hj0 (y : Unit) : fderiv ℝ (fun _ : Unit ↦ (0 : ℝ)) y = 0 := by
    simp
  constructor
  · intro h hp0
    subst hp0
    obtain ⟨⟨u, _⟩, huv⟩ := h 0 () (by norm_num) 1
    simp only [ContinuousLinearMap.coprod_apply, hslice 0 u, hj0, neg_zero, zero_apply] at huv
    norm_num at huv
  · intro hp x y hxy w
    have hx0 : x ≠ 0 := by
      intro rfl
      apply hp
      linarith
    refine ⟨(w / (2 * x), ()), ?_⟩
    have h2x : 2 * x ≠ 0 := mul_ne_zero two_ne_zero hx0
    simp only [ContinuousLinearMap.coprod_apply, hslice x (w / (2 * x)), hj0, neg_zero,
      zero_apply, add_zero]
    exact mul_div_cancel₀ w h2x

-- At `p = 0`, the quadratic family `(x, p) ↦ x ^ 2 + p` fails incidence regularity against `0`.
example :
    ¬ IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) (fun _ : Unit ↦ (0 : ℝ)) 0 := by
  rw [isRegularIncidenceParameter_sq_add_zero_iff]
  norm_num

-- At `p = -1`, the quadratic family `(x, p) ↦ x ^ 2 + p` has a nonempty regular fibre `{-1, 1}`
-- against `0`.
example :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2)
      (fun _ : Unit ↦ (0 : ℝ)) (-1) := by
  rw [isRegularIncidenceParameter_sq_add_zero_iff]
  norm_num

-- At `p = 1`, the quadratic family `(x, p) ↦ x ^ 2 + p` is regular against `0` (with empty fibre).
example :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2)
      (fun _ : Unit ↦ (0 : ℝ)) 1 := by
  rw [isRegularIncidenceParameter_sq_add_zero_iff]
  norm_num

-- Against `id : ℝ → ℝ`, every parameter `p : ℝ` of the quadratic family `(x, p) ↦ x ^ 2 + p` is
-- regular because `fderiv ℝ id y = id` already spans `ℝ`.
example (p : ℝ) :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) (id : ℝ → ℝ) p :=
  isRegularIncidenceParameter_id.2 fun _ ↦ by fun_prop

end Examples

end TauCeti
