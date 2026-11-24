/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Process.Kolmogorov
import TauCeti.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import TauCeti.MeasureTheory.Measure.ContinuousMap
import TauCeti.Probability.BrownianMotion.Basic
import TauCeti.Probability.BrownianMotion.Countable
import TauCeti.Probability.BrownianMotion.Regularity
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Continuity
import TauCeti.Probability.Process.Kolmogorov.Chentsov
import TauCeti.Topology.Instances.NNReal.Dyadic.Grid

/-!
# Wiener measure on continuous path space

We construct **Wiener measure** (`TauCeti.wienerMeasure`) on the space `C(ℝ≥0, ℝ)` of continuous
real-valued paths and prove that it is the unique Borel probability measure under which the
coordinate evaluation process `t ↦ (ω ↦ ω t)` is a standard real Brownian motion
(`ProbabilityTheory.IsBrownianReal`).

We also record path-space pushforward characterizations, singleton non-atomicity, symmetries
(reflection, increment-shift, and diffusive Brownian rescaling invariance), scalar-rescaling
rigidity, local `< 1 / 2`-Hölder regularity, and marginal moments of `wienerMeasure`. General
pre-Brownian singleton non-atomicity (`ProbabilityTheory.IsPreBrownianReal.nullSingletonClass`)
lives upstream in `TauCeti.Probability.BrownianMotion.Basic`, and general Brownian path-regularity
results (`isAEKolmogorovProcess_two_mul`, `exists_continuous_modification`,
`ae_exists_holderOnWith`) live upstream in `TauCeti.Probability.BrownianMotion.Regularity`.

## Main definitions and results

* `ProbabilityTheory.IsPreBrownianReal.isBrownianReal_eval_map` and
  `ProbabilityTheory.IsPreBrownianReal.map_eq_wienerMeasure`: pushing forward along any
  `F : Ω → C(ℝ≥0, ℝ)` with pre-Brownian coordinate evaluations produces `wienerMeasure`.
* `TauCeti.wienerMeasure`: Wiener measure on `C(ℝ≥0, ℝ)`, with `NullSingletonClass` instance giving
  `∀ f, wienerMeasure {f} = 0`.
* `TauCeti.exists_wienerMeasure`: existence of a Borel probability measure on `C(ℝ≥0, ℝ)` whose
  coordinate process satisfies `IsBrownianReal`.
* `TauCeti.eq_wienerMeasure_iff_isBrownianReal`, `TauCeti.eq_wienerMeasure_iff_isPreBrownianReal`,
  and `TauCeti.hasLaw_wienerMeasure_iff`: uniqueness and path-space law characterizations of Wiener
  measure.
* `TauCeti.map_scale_wienerMeasure`, `TauCeti.map_shift_wienerMeasure`,
  `TauCeti.map_neg_wienerMeasure`, and `TauCeti.map_smul_eq_wienerMeasure_iff`: diffusive scaling,
  increment-shift, and reflection invariance of Wiener measure, and characterization of scalar path
  rescalings preserving Wiener measure.
* `TauCeti.ae_exists_holderOnWith_wienerMeasure`: simultaneous local `< 1 / 2`-Hölder regularity
  of `wienerMeasure`-almost every path.

## References

* S. P. Lalley, *Brownian Motion*, University of Chicago lecture notes, Theorem 1.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, Theorem 14.2.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  §2.2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory ProbabilityTheory.BrownianReal Set WithLp
open scoped ENNReal Nat NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `F : Ω → C(ℝ≥0, ℝ)` has pre-Brownian coordinate evaluations, then pushing `P` forward along
`F` yields a probability measure under which coordinate evaluation on `C(ℝ≥0, ℝ)` is
`IsBrownianReal`. No separate measurability hypothesis on `F` is needed. -/
theorem IsPreBrownianReal.isBrownianReal_eval_map {F : Ω → C(ℝ≥0, ℝ)}
    (hF : IsPreBrownianReal (fun t ω ↦ F ω t) P) :
    IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) (P.map F) := by
  have hF_meas : AEMeasurable F P := ContinuousMap.aemeasurable_iff_eval.mpr hF.aemeasurable
  refine
    { hasLaw := fun I ↦ ?_
      cont := ae_of_all _ fun ω ↦ ω.continuous }
  have hres_meas : Measurable fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (ω : ℝ≥0 → ℝ) :=
    ContinuousMap.measurable_finsetRestrict I
  refine ⟨hres_meas.aemeasurable, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable hres_meas.aemeasurable hF_meas]
  exact (hF.hasLaw I).map_eq

end ProbabilityTheory

namespace TauCeti

section Construction

/-- The countable set of nonnegative rational times inside `ℝ≥0`. -/
private abbrev nnratTimeSet : Set ℝ≥0 := range ((↑) : ℚ≥0 → ℝ≥0)

private instance : Countable nnratTimeSet :=
  (countable_range ((↑) : ℚ≥0 → ℝ≥0)).to_subtype

/-- Embedding of a nonnegative rational time into `nnratTimeSet`. -/
private def nnratTime (r : ℚ≥0) : nnratTimeSet := ⟨r, ⟨r, rfl⟩⟩

private theorem exists_nnratBrownianSkeleton :
    ∃ P : Measure (nnratTimeSet → ℝ), IsProbabilityMeasure P ∧
      (∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ nnratTimeSet),
        MeasurePreserving (fun (x : nnratTimeSet → ℝ) (i : I) ↦ x ⟨i.val, hI i.property⟩) P
          (projectiveFamily I)) ∧
      ∀ ⦃n : ℕ⦄, n ≠ 0 →
        IsKolmogorovProcess (fun (t : nnratTimeSet) (x : nnratTimeSet → ℝ) ↦ x t) P
          (2 * n : ℕ) n (2 * n - 1)‼ :=
  exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable
    nnratTimeSet

/-- Canonical Brownian skeleton probability measure on `nnratTimeSet → ℝ`. -/
private def nnratBrownianMeasure : Measure (nnratTimeSet → ℝ) :=
  exists_nnratBrownianSkeleton.choose

private instance : IsProbabilityMeasure nnratBrownianMeasure :=
  exists_nnratBrownianSkeleton.choose_spec.1

private lemma hasLaw_finset_nnratBrownianMeasure (I : Finset ℝ≥0)
    (hI : (I : Set ℝ≥0) ⊆ nnratTimeSet) :
    HasLaw (fun (ω : nnratTimeSet → ℝ) (i : I) ↦ ω ⟨i.val, hI i.property⟩)
      (projectiveFamily I) nnratBrownianMeasure :=
  (exists_nnratBrownianSkeleton.choose_spec.2.1 I hI).hasLaw

private lemma isKolmogorovProcess_four_nnratBrownianMeasure :
    IsKolmogorovProcess (fun (t : nnratTimeSet) (ω : nnratTimeSet → ℝ) ↦ ω t)
      nnratBrownianMeasure 4 2 3 := by
  simpa [nnratBrownianMeasure, Nat.doubleFactorial] using
    exists_nnratBrownianSkeleton.choose_spec.2.2 (n := 2) two_ne_zero

/-- Any finite tuple of rational evaluations `(ω (nnratTime (v i)))_{i : ι}` has the centered
multivariate Gaussian law with covariance matrix `min (v i) (v j)`, even when `v` has repeated
entries. -/
private lemma hasLaw_toLp_nnratBrownianMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℚ≥0) :
    HasLaw (fun ω : nnratTimeSet → ℝ ↦ toLp 2 (fun i : ι ↦ ω (nnratTime (v i))))
      (multivariateGaussian 0
        (Matrix.of fun i j : ι ↦ min ((v i : ℝ≥0) : ℝ) ((v j : ℝ≥0) : ℝ)))
      nnratBrownianMeasure := by
  let I : Finset ℝ≥0 := Finset.univ.image fun i ↦ (v i : ℝ≥0)
  have hI : (I : Set ℝ≥0) ⊆ nnratTimeSet := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact ⟨v i, rfl⟩
  let f : ι → I := fun i ↦ ⟨(v i : ℝ≥0), Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hI_law :=
    (measurePreserving_toLp_projectiveFamily I).hasLaw.comp
      (hasLaw_finset_nnratBrownianMeasure I hI)
  have hcomp_law :
      HasLaw (fun x : EuclideanSpace ℝ I ↦ toLp 2 fun i : ι ↦ x (f i))
        (multivariateGaussian 0
          (Matrix.of fun i j : ι ↦ min ((v i : ℝ≥0) : ℝ) ((v j : ℝ≥0) : ℝ)))
        (multivariateGaussian 0 (BrownianReal.covMatrix I)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [TauCeti.Probability.map_comp_multivariateGaussian 0
      (BrownianReal.posSemidef_covMatrix I) f]
    congr 1
  exact hcomp_law.comp hI_law

private theorem exists_rawBrownian :
    ∃ B₀ : ℝ≥0 → (nnratTimeSet → ℝ) → ℝ,
      (∀ t : ℝ≥0, Measurable (B₀ t)) ∧
      (∀ ω : nnratTimeSet → ℝ, Continuous (B₀ · ω)) ∧
      (∀ r : ℚ≥0, B₀ r =ᵐ[nnratBrownianMeasure] fun ω ↦ ω (nnratTime r)) := by
  have hkol := isKolmogorovProcess_four_nnratBrownianMeasure
  obtain ⟨B₀, hmeas, hcont, hae, _⟩ :=
    exists_continuous_extension_of_nnrat (P := nnratBrownianMeasure)
      (X := fun (r : ℚ≥0) (ω : nnratTimeSet → ℝ) ↦ ω (nnratTime r)) (M := fun _ ↦ 3)
      (by norm_num : (0 : ℝ) < 4) one_lt_two
      (fun r s ↦ hkol.measurablePair (nnratTime r) (nnratTime s))
      (fun _ r s _ _ ↦ hkol.kolmogorovCondition (nnratTime r) (nnratTime s))
  exact ⟨B₀, hmeas, hcont, hae⟩

/-- Canonical all-paths continuous Brownian process on `nnratTimeSet → ℝ` constructed by dyadic
extension. -/
private def rawBrownian : ℝ≥0 → (nnratTimeSet → ℝ) → ℝ := exists_rawBrownian.choose

private lemma measurable_rawBrownian (t : ℝ≥0) : Measurable (rawBrownian t) :=
  exists_rawBrownian.choose_spec.1 t

private lemma continuous_rawBrownian (ω : nnratTimeSet → ℝ) : Continuous (rawBrownian · ω) :=
  exists_rawBrownian.choose_spec.2.1 ω

private lemma ae_eq_rawBrownian (r : ℚ≥0) :
    rawBrownian r =ᵐ[nnratBrownianMeasure] fun ω ↦ ω (nnratTime r) :=
  exists_rawBrownian.choose_spec.2.2 r

/-- The extended process `rawBrownian` has the finite-dimensional laws of Brownian motion. -/
private lemma isPreBrownianReal_rawBrownian :
    IsPreBrownianReal rawBrownian nnratBrownianMeasure where
  hasLaw I := by
    let v (n : ℕ) (i : I) : ℚ≥0 := approxDyadicNNRat n i.val
    let Z (n : ℕ) (ω : nnratTimeSet → ℝ) : EuclideanSpace ℝ I :=
      toLp 2 fun i : I ↦ rawBrownian (v n i) ω
    let Zlim (ω : nnratTimeSet → ℝ) : EuclideanSpace ℝ I :=
      toLp 2 (I.restrict (rawBrownian · ω))
    have hmeas_toLp (u : I → ℝ≥0) : Measurable fun ω ↦ toLp 2 fun i : I ↦ rawBrownian (u i) ω :=
      (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp
        (measurable_pi_iff.mpr fun i ↦ measurable_rawBrownian (u i))
    have hZ_meas (n : ℕ) : Measurable (Z n) := hmeas_toLp (fun i ↦ (v n i : ℝ≥0))
    have hZlim_meas : Measurable Zlim := hmeas_toLp (fun i ↦ i.val)
    -- Step 1: dyadic approximations `Z n` converge pointwise to `Zlim`, hence in distribution.
    have hZ_tendsto (ω : nnratTimeSet → ℝ) : Tendsto (fun n ↦ Z n ω) atTop (𝓝 (Zlim ω)) :=
      (PiLp.continuous_toLp 2 _).tendsto _ |>.comp
        (tendsto_pi_nhds.mpr fun i ↦
          ((continuous_rawBrownian ω).tendsto i.val).comp (tendsto_approxDyadicNNRat i.val))
    let S (u : I → ℝ≥0) : Matrix I I ℝ := Matrix.of fun i j : I ↦ min (u i : ℝ) (u j : ℝ)
    have hPSD (u : I → ℝ≥0) : (S u).PosSemidef := by
      let J : Finset ℝ≥0 := Finset.univ.image u
      let g : I → J := fun i ↦ ⟨u i, Finset.mem_image_of_mem u (Finset.mem_univ i)⟩
      have heq : S u = (BrownianReal.covMatrix J).submatrix g g := by
        ext i j; simp [S, BrownianReal.covMatrix_apply, g]
      exact heq ▸ (BrownianReal.posSemidef_covMatrix J).submatrix g
    have hZ_law (n : ℕ) :
        HasLaw (Z n) (multivariateGaussian 0 (S fun i ↦ (v n i : ℝ≥0))) nnratBrownianMeasure := by
      refine (hasLaw_toLp_nnratBrownianMeasure (v n)).congr ?_
      filter_upwards [ae_all_iff.mpr fun i ↦ ae_eq_rawBrownian (v n i)] with ω hω
      ext i; exact hω i
    have hlim := (tendstoInDistribution_of_ae_tendsto (μ' := nnratBrownianMeasure)
      (fun n ↦ (hZ_meas n).aemeasurable) hZlim_meas.aemeasurable
      (ae_of_all nnratBrownianMeasure hZ_tendsto)).tendsto
    have hlaw_pm (n : ℕ) :
        (⟨nnratBrownianMeasure.map (Z n), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ I)) =
        (multivariateGaussian 0 (S fun i ↦ (v n i : ℝ≥0))).toProbabilityMeasure :=
      Subtype.ext (hZ_law n).map_eq
    simp only [hlaw_pm] at hlim
    -- Step 2: weak continuity of `multivariateGaussian` identifies the limit law.
    have hc : Continuous (fun u : I → ℝ≥0 ↦
        (multivariateGaussian 0 (S u)).toProbabilityMeasure) :=
      Continuous.multivariateGaussian (m := fun _ ↦ 0) continuous_const (by fun_prop) hPSD
    have hu_tendsto : Tendsto (fun n ↦ fun i : I ↦ (v n i : ℝ≥0)) atTop (𝓝 fun i : I ↦ i.val) :=
      tendsto_pi_nhds.mpr fun i ↦ tendsto_approxDyadicNNRat i.val
    have hS_eq : S (fun i : I ↦ i.val) = BrownianReal.covMatrix I := by
      ext i j; simp [S, BrownianReal.covMatrix_apply]
    have hZlim_eq :
        nnratBrownianMeasure.map Zlim = multivariateGaussian 0 (BrownianReal.covMatrix I) := by
      simpa [hS_eq] using congrArg ProbabilityMeasure.toMeasure
        (tendsto_nhds_unique hlim ((hc.tendsto _).comp hu_tendsto))
    have hZlim_law :
        HasLaw Zlim (multivariateGaussian 0 (BrownianReal.covMatrix I)) nnratBrownianMeasure :=
      ⟨hZlim_meas.aemeasurable, hZlim_eq⟩
    simpa [Zlim, Function.comp_def] using
      (measurePreserving_ofLp_multivariateGaussian I).hasLaw.comp hZlim_law

end Construction

/-! ### Wiener measure and its universal properties -/

/-- **Wiener measure** on the continuous path space `C(ℝ≥0, ℝ)`: the unique Borel probability
measure under which the coordinate evaluation process `t ↦ (ω ↦ ω t)` is a standard real Brownian
motion (`ProbabilityTheory.IsBrownianReal`). -/
def wienerMeasure : Measure C(ℝ≥0, ℝ) :=
  nnratBrownianMeasure.map fun ω ↦ ⟨fun t ↦ rawBrownian t ω, continuous_rawBrownian ω⟩

instance : IsProbabilityMeasure wienerMeasure := by
  have hmeas : Measurable fun ω : nnratTimeSet → ℝ ↦
      (⟨fun t ↦ rawBrownian t ω, continuous_rawBrownian ω⟩ : C(ℝ≥0, ℝ)) :=
    ContinuousMap.measurable_iff_eval.mpr measurable_rawBrownian
  exact (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance

/-- Under `wienerMeasure`, coordinate evaluation `t ↦ (ω ↦ ω t)` is a standard real Brownian
motion. -/
theorem isBrownianReal_eval_wienerMeasure :
    IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) wienerMeasure :=
  isPreBrownianReal_rawBrownian.isBrownianReal_eval_map

/-- Under `wienerMeasure`, coordinate evaluation `t ↦ (ω ↦ ω t)` is pre-Brownian. -/
theorem isPreBrownianReal_eval_wienerMeasure :
    IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) wienerMeasure :=
  isBrownianReal_eval_wienerMeasure.toIsPreBrownianReal

/-- **Existence of Wiener measure** (Lalley, Theorem 1): there exists a Borel probability measure
on `C(ℝ≥0, ℝ)` whose coordinate process satisfies `IsBrownianReal`. -/
theorem exists_wienerMeasure :
    ∃ W : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure W ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W :=
  ⟨wienerMeasure, inferInstance, isBrownianReal_eval_wienerMeasure⟩

/-- **Uniqueness of Wiener measure:** any measure on `C(ℝ≥0, ℝ)` whose coordinate process satisfies
`IsPreBrownianReal` is equal to `wienerMeasure`. -/
theorem eq_wienerMeasure_of_isPreBrownianReal {μ : Measure C(ℝ≥0, ℝ)}
    (hμ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ) :
    μ = wienerMeasure :=
  continuousMap_measure_ext_of_forall_finset_map_restrict_eq fun I ↦
    (hμ.hasLaw I).map_eq.trans (isPreBrownianReal_eval_wienerMeasure.hasLaw I).map_eq.symm

/-- A measure on `C(ℝ≥0, ℝ)` equals `wienerMeasure` if and only if coordinate evaluation is
pre-Brownian under it. -/
theorem eq_wienerMeasure_iff_isPreBrownianReal {μ : Measure C(ℝ≥0, ℝ)} :
    μ = wienerMeasure ↔ IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ :=
  ⟨fun h ↦ h ▸ isPreBrownianReal_eval_wienerMeasure, eq_wienerMeasure_of_isPreBrownianReal⟩

/-- A measure on `C(ℝ≥0, ℝ)` equals `wienerMeasure` if and only if coordinate evaluation is a
standard real Brownian motion under it. -/
theorem eq_wienerMeasure_iff_isBrownianReal {μ : Measure C(ℝ≥0, ℝ)} :
    μ = wienerMeasure ↔ IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ :=
  ⟨fun h ↦ h ▸ isBrownianReal_eval_wienerMeasure,
    fun h ↦ eq_wienerMeasure_of_isPreBrownianReal h.toIsPreBrownianReal⟩

/-- The path-space law of any `C(ℝ≥0, ℝ)`-valued random variable whose coordinate evaluations form
a pre-Brownian motion is `wienerMeasure`. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.map_eq_wienerMeasure
    {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {F : Ω → C(ℝ≥0, ℝ)}
    (hF : IsPreBrownianReal (fun t ω ↦ F ω t) P) :
    P.map F = wienerMeasure :=
  eq_wienerMeasure_of_isPreBrownianReal hF.isBrownianReal_eval_map.toIsPreBrownianReal

/-- A `C(ℝ≥0, ℝ)`-valued random variable has law `wienerMeasure` if and only if its coordinate
evaluations form a pre-Brownian motion. -/
theorem hasLaw_wienerMeasure_iff {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Ω → C(ℝ≥0, ℝ)} :
    HasLaw F wienerMeasure P ↔ IsPreBrownianReal (fun t ω ↦ F ω t) P :=
  ⟨fun hF ↦ { hasLaw := fun I ↦ (isPreBrownianReal_eval_wienerMeasure.hasLaw I).comp hF },
    fun hF ↦ ⟨ContinuousMap.aemeasurable_iff_eval.mpr hF.aemeasurable, hF.map_eq_wienerMeasure⟩⟩

/-! ### Symmetry, scaling invariance, and path regularity of Wiener measure -/

/-- Wiener measure is invariant under path negation `ω ↦ -ω`. -/
@[simp]
theorem map_neg_wienerMeasure :
    wienerMeasure.map (-· : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) = wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.neg.map_eq_wienerMeasure

/-- **Brownian scaling invariance of Wiener measure:** for every `c ≠ 0`, pushing `wienerMeasure`
forward along `ω ↦ (t ↦ (√c)⁻¹ * ω (c * t))` recovers `wienerMeasure`. -/
theorem map_scale_wienerMeasure {c : ℝ≥0} (hc : c ≠ 0) :
    wienerMeasure.map
      (fun ω : C(ℝ≥0, ℝ) ↦ (⟨fun t ↦ (√(c : ℝ))⁻¹ * ω (c * t), by fun_prop⟩ : C(ℝ≥0, ℝ))) =
      wienerMeasure :=
  (isPreBrownianReal_eval_wienerMeasure.smul hc).map_eq_wienerMeasure

/-- **Increment-shift invariance of Wiener measure:** for every `t₀ : ℝ≥0`, pushing `wienerMeasure`
forward along `ω ↦ (t ↦ ω (t₀ + t) - ω t₀)` recovers `wienerMeasure`. -/
theorem map_shift_wienerMeasure (t₀ : ℝ≥0) :
    wienerMeasure.map
      (fun ω : C(ℝ≥0, ℝ) ↦ (⟨fun t ↦ ω (t₀ + t) - ω t₀, by fun_prop⟩ : C(ℝ≥0, ℝ))) =
      wienerMeasure :=
  (isPreBrownianReal_eval_wienerMeasure.shift t₀).map_eq_wienerMeasure

/-- Under `wienerMeasure`, almost every path is simultaneously `γ`-Hölder continuous on `Iic T`
for every `γ : ℝ≥0` with `(γ : ℝ) < 1 / 2` and every `T : ℝ≥0`. -/
theorem ae_exists_holderOnWith_wienerMeasure :
    ∀ᵐ (ω : C(ℝ≥0, ℝ)) ∂wienerMeasure,
      ∀ (γ : ℝ≥0), (γ : ℝ) < 1 / 2 → ∀ T : ℝ≥0, ∃ C : ℝ≥0, HolderOnWith C γ ω (Iic T) :=
  isBrownianReal_eval_wienerMeasure.ae_exists_holderOnWith

/-! ### Marginals, covariances, variances, and nondegeneracy -/

/-- Under `wienerMeasure`, evaluation at time `t` has law `gaussianReal 0 t`. -/
theorem hasLaw_eval_wienerMeasure (t : ℝ≥0) :
    HasLaw (fun ω : C(ℝ≥0, ℝ) ↦ ω t) (gaussianReal 0 t) wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.hasLaw_eval t

/-- Under `wienerMeasure`, the increment `ω s - ω t` has law `gaussianReal 0 (nndist s t)`. -/
theorem hasLaw_eval_sub_wienerMeasure (s t : ℝ≥0) :
    HasLaw (fun ω : C(ℝ≥0, ℝ) ↦ ω s - ω t) (gaussianReal 0 (nndist s t)) wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.hasLaw_sub s t

/-- Under `wienerMeasure`, almost every path starts at `0`. -/
theorem ae_eval_zero_wienerMeasure : ∀ᵐ ω ∂wienerMeasure, ω 0 = 0 :=
  isPreBrownianReal_eval_wienerMeasure.eval_zero_ae_eq_zero

/-- Expectation of coordinate evaluation at time `t` under `wienerMeasure`: `∫ ω, ω t = 0`. -/
@[simp]
theorem integral_eval_wienerMeasure (t : ℝ≥0) :
    ∫ ω : C(ℝ≥0, ℝ), ω t ∂wienerMeasure = 0 :=
  isPreBrownianReal_eval_wienerMeasure.integral_eval t

/-- Covariance of coordinate evaluations under `wienerMeasure`: `cov[ω s, ω t] = min s t`. -/
@[simp]
theorem covariance_eval_wienerMeasure (s t : ℝ≥0) :
    cov[fun ω : C(ℝ≥0, ℝ) ↦ ω s, fun ω : C(ℝ≥0, ℝ) ↦ ω t; wienerMeasure] = min (s : ℝ) (t : ℝ) :=
  isPreBrownianReal_eval_wienerMeasure.covariance_eval s t

/-- Variance of coordinate evaluation at time `t` under `wienerMeasure`: `Var[ω t] = t`. -/
@[simp]
theorem variance_eval_wienerMeasure (t : ℝ≥0) :
    Var[fun ω : C(ℝ≥0, ℝ) ↦ ω t; wienerMeasure] = t := by
  rw [(hasLaw_eval_wienerMeasure t).variance_eq, variance_id_gaussianReal]

/-- Variance of a coordinate increment under `wienerMeasure`: `Var[ω s - ω t] = dist s t`. -/
@[simp]
theorem variance_eval_sub_wienerMeasure (s t : ℝ≥0) :
    Var[fun ω : C(ℝ≥0, ℝ) ↦ ω s - ω t; wienerMeasure] = dist s t := by
  rw [(hasLaw_eval_sub_wienerMeasure s t).variance_eq, variance_id_gaussianReal, coe_nndist]

/-- Wiener measure has no singleton atoms: every single path has measure zero
(`∀ f, wienerMeasure {f} = 0`). -/
instance : NullSingletonClass wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.nullSingletonClass

/-- Wiener measure is never equal to a Dirac mass `Measure.dirac f`. -/
@[simp]
theorem wienerMeasure_ne_dirac (f : C(ℝ≥0, ℝ)) : wienerMeasure ≠ Measure.dirac f := by
  intro h
  simpa [h, Measure.dirac_apply_of_mem (mem_singleton f)] using
    measure_singleton (μ := wienerMeasure) f

/-- Scalar path rescaling `ω ↦ c • ω` (without time rescaling) preserves `wienerMeasure` if and only
if `c = 1` or `c = -1`. -/
@[simp]
theorem map_smul_eq_wienerMeasure_iff {c : ℝ} :
    wienerMeasure.map (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) = wienerMeasure ↔ c = 1 ∨ c = -1 := by
  constructor
  · intro h
    have hsmul_meas : Measurable (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) :=
      ContinuousMap.measurable_iff_eval.mpr fun t ↦
        measurable_const.mul (ContinuousMap.measurable_eval t)
    have hvar : Var[fun ω : C(ℝ≥0, ℝ) ↦ ω 1;
        wienerMeasure.map (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ))] = c ^ 2 := by
      rw [variance_map (ContinuousMap.measurable_eval 1).aemeasurable hsmul_meas.aemeasurable]
      have hcomp : ((fun ω : C(ℝ≥0, ℝ) ↦ ω 1) ∘ (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ))) =
          fun ω : C(ℝ≥0, ℝ) ↦ c * ω 1 := by ext ω; simp
      rw [hcomp, variance_const_mul, variance_eval_wienerMeasure, NNReal.coe_one, mul_one]
    rw [h, variance_eval_wienerMeasure, NNReal.coe_one] at hvar
    exact sq_eq_one_iff.mp hvar.symm
  · rintro (rfl | rfl) <;> simp

end TauCeti
