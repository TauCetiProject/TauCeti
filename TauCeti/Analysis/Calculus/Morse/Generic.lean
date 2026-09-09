/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Analysis.Calculus.Morse.Basic
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Almost every linear perturbation of a function is Morse

Morse homology starts from a function all of whose critical points are nondegenerate, so the
theory is empty until such functions are known to exist. This file proves that they are in fact
*generic*: on an open subset `U` of a finite-dimensional real normed space `E`, for a twice
continuously differentiable `f : E → ℝ` and **almost every** continuous linear functional
`a : E →L[ℝ] ℝ`, every critical point of `f - a` in `U` is nondegenerate.

The mechanism is the equal-dimensional case of Sard's theorem, applied not to `f` but to its
differential. Subtracting a linear functional changes the differential by a constant and leaves
the second derivative alone, so

* `x` is a critical point of `f - a` exactly when `fderiv ℝ f x = a`, and
* the second derivative of `f - a` at `x` is that of `f`.

Hence `f - a` has a *degenerate* critical point in `U` exactly when `a` is a **critical value of
the map `fderiv ℝ f : E → (E →L[ℝ] ℝ)`** taken on `U`; this is
`TauCeti.hasNondegenerateCriticalPointsOn_sub_iff`, and it is the whole content of the argument.
Domain and codomain of `fderiv ℝ f` have the same dimension, the continuous dual of a
finite-dimensional space having the dimension of the space
(`ContinuousLinearMap.finrank_dual_eq`), so
`TauCeti.addHaar_image_eq_zero_of_not_surjective_fderivWithin` applies and the bad set of `a` is
null. Note that only `C²` regularity of `f` is used: the map `fderiv ℝ f` is then merely
differentiable, which is all the equal-dimensional Sard lemma asks for, and no higher-stratum
Morse--Sard argument is needed.

The perturbation is written `f - a` rather than `f + a`; the two conventions differ by the sign of
`a`, and subtraction makes the criticality condition read `fderiv ℝ f x = a`, so that the
exceptional set is literally the set of critical values of `fderiv ℝ f`.

Nondegeneracy here is `TauCeti.HasNondegenerateCriticalPointsOn`, which asks nothing of `f` away
from its critical points; the regularity hypothesis `ContDiffOn ℝ 2 f U` is carried separately, as
`TauCeti/Analysis/Calculus/Morse/Basic.lean` explains.

## Main declarations

* `TauCeti.isNondegenerateCriticalPoint_sub_iff`: a point at which `f` is `C²` is a nondegenerate
  critical point of `f - a` exactly when `a` is the differential of `f` there and the second
  derivative of `f` is invertible.
* `TauCeti.hasNondegenerateCriticalPointsOn_sub_iff`: **`f - a` has nondegenerate critical points
  on `U` exactly when `a` is a regular value of `fderiv ℝ f` on `U`.**
* `TauCeti.ae_hasNondegenerateCriticalPointsOn_sub`: **almost every linear perturbation is Morse.**
* `TauCeti.dense_setOfPred_hasNondegenerateCriticalPointsOn_sub` and
  `TauCeti.exists_norm_lt_hasNondegenerateCriticalPointsOn_sub`: the good perturbations are dense,
  so they can be taken arbitrarily small in the operator norm.
* `TauCeti.ae_hasNondegenerateCriticalPointsOn_sub_inner`,
  `TauCeti.dense_setOfPred_hasNondegenerateCriticalPointsOn_sub_inner` and
  `TauCeti.exists_norm_lt_hasNondegenerateCriticalPointsOn_sub_inner`: the same three statements on
  an inner product space, with the perturbation written `⟪v, ·⟫` as in the gradient formulation.
* `TauCeti.finite_setOfPred_fderiv_sub_eq_zero`: a perturbation that is Morse on `U` has only
  finitely many critical points on a compact subset of `U`.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §7, where
  this genericity statement is proved in exactly this way.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {U : Set E} {x : E} {a : E →L[ℝ] ℝ}

/-! ### Morse perturbations are the regular values of the differential

The effect of the perturbation on the first two derivatives is general calculus, with no Morse
theory in it, so it lives in `TauCeti.Analysis.Calculus.SecondDerivative` as
`TauCeti.fderiv_sub_continuousLinearMap` and `TauCeti.fderiv_fderiv_sub_continuousLinearMap`.
-/

/-- A point at which `f` is `C²` is a nondegenerate critical point of `f - a` exactly when the
differential of `f` there is `a` and the second derivative of `f` there is invertible. Both
conditions are about `f` alone: the perturbation only moves the differential, so it selects which
points are critical without affecting whether they are degenerate. -/
theorem isNondegenerateCriticalPoint_sub_iff (hf : ContDiffAt ℝ 2 f x) (a : E →L[ℝ] ℝ) :
    IsNondegenerateCriticalPoint (fun y ↦ f y - a y) x ↔
      fderiv ℝ f x = a ∧ (fderiv ℝ (fderiv ℝ f) x).IsInvertible := by
  have hax : ContDiffAt ℝ 2 (fun y : E ↦ a y) x := a.contDiff.contDiffAt
  have h1 := fderiv_sub_continuousLinearMap (hf.differentiableAt (by norm_num)) a
  have h2 := fderiv_fderiv_sub_continuousLinearMap hf (by norm_num) a
  constructor
  · rintro ⟨-, h0, hinv⟩
    rw [h1, sub_eq_zero] at h0
    rw [h2] at hinv
    exact ⟨h0, hinv⟩
  · rintro ⟨h0, hinv⟩
    refine ⟨ContDiffAt.sub hf hax, ?_, ?_⟩
    · rw [h1, h0, sub_self]
    · rw [h2]; exact hinv

/-- **A perturbation that is Morse on `U` has only finitely many critical points on a compact
subset of `U`.** Continuity of `fderiv ℝ f` on the compact set closes the critical locus, and
nondegeneracy makes it discrete. Nothing beyond those two hypotheses on `K` is needed: the
perturbation shifts the differential of `f` by the constant `a`, so it neither disturbs the
continuity nor requires any regularity of its own. -/
theorem finite_setOfPred_fderiv_sub_eq_zero {K : Set E} (hK : IsCompact K)
    (hd : ∀ x ∈ K, DifferentiableAt ℝ f x) (hcont : ContinuousOn (fderiv ℝ f) K)
    (ha : HasNondegenerateCriticalPointsOn (fun y ↦ f y - a y) U) (hKU : K ⊆ U) :
    {x ∈ K | fderiv ℝ (fun y ↦ f y - a y) x = 0}.Finite :=
  (ha.mono hKU).finite_setOfPred_fderiv_eq_zero hK
    ((hcont.sub continuousOn_const).congr fun y hy ↦
      fderiv_sub_continuousLinearMap (hd y hy) a)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The perturbations that make `f` Morse are exactly the regular values of its differential.**
All critical points of `f - a` in `U` are nondegenerate if and only if `a` is not the value at a
point of `U` of the differential `fderiv ℝ f` at which the second derivative fails to be
surjective. -/
theorem hasNondegenerateCriticalPointsOn_sub_iff (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (a : E →L[ℝ] ℝ) :
    HasNondegenerateCriticalPointsOn (fun y ↦ f y - a y) U ↔
      a ∉ fderiv ℝ f '' {x ∈ U | ¬ Surjective (fderiv ℝ (fderiv ℝ f) x)} := by
  have hd : DifferentiableOn ℝ f U := hf.differentiableOn (by norm_num)
  constructor
  · rintro hM ⟨y, ⟨hyU, hyc⟩, rfl⟩
    have hcrit : fderiv ℝ (fun z ↦ f z - (fderiv ℝ f y) z) y = 0 := by
      rw [fderiv_sub_continuousLinearMap (hd.differentiableAt (hU.mem_nhds hyU)), sub_self]
    exact hyc (((isNondegenerateCriticalPoint_sub_iff (hf.contDiffAt (hU.mem_nhds hyU)) _).1
      (hasNondegenerateCriticalPointsOn_iff.1 hM hyU hcrit)).2.surjective)
  · refine fun ha ↦ hasNondegenerateCriticalPointsOn_iff.2 fun y hyU hy0 ↦ ?_
    rw [fderiv_sub_continuousLinearMap (hd.differentiableAt (hU.mem_nhds hyU)), sub_eq_zero] at hy0
    refine (isNondegenerateCriticalPoint_sub_iff (hf.contDiffAt (hU.mem_nhds hyU)) a).2
      ⟨hy0, ContinuousLinearMap.isInvertible_of_surjective ?_⟩
    by_contra hs
    exact ha ⟨y, ⟨hyU, hs⟩, hy0⟩

/-! ### Genericity -/

/-- **Almost every linear perturbation of a `C²` function is Morse.** For a Haar measure `ν` on
the continuous dual, for `ν`-almost every functional `a` the function `f - a` has only
nondegenerate critical points on the open set `U`.

The exceptional set is the set of critical values on `U` of the differential `fderiv ℝ f`, a map
between spaces of the same finite dimension, so it is null by the equal-dimensional case of
Sard's theorem.

Only the dual carries a measurable structure in the statement, since that is where `ν` lives; the
source `E` is measured only inside the proof, by Sard's lemma, and gets its Borel structure
there. -/
theorem ae_hasNondegenerateCriticalPointsOn_sub [MeasurableSpace (E →L[ℝ] ℝ)]
    [BorelSpace (E →L[ℝ] ℝ)] (ν : Measure (E →L[ℝ] ℝ)) [ν.IsAddHaarMeasure]
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ∀ᵐ a ∂ν, HasNondegenerateCriticalPointsOn (fun y ↦ f y - a y) U := by
  borelize E
  have hdf : DifferentiableOn ℝ (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen (m := 1) hU (by norm_num)).differentiableOn one_ne_zero
  have hnull : ν (fderiv ℝ f '' {x ∈ U | ¬ Surjective (fderiv ℝ (fderiv ℝ f) x)}) = 0 := by
    refine addHaar_image_eq_zero_of_not_surjective_fderivWithin ν
      ContinuousLinearMap.finrank_dual_eq.symm (fun y hy ↦ ?_) fun _ hy ↦ hy.2
    exact ((hdf y hy.1).differentiableAt (hU.mem_nhds hy.1)).hasFDerivAt.hasFDerivWithinAt
  rw [ae_iff]
  refine measure_mono_null (fun a ha ↦ ?_) hnull
  exact not_not.1 fun h ↦ ha ((hasNondegenerateCriticalPointsOn_sub_iff hU hf a).2 h)

/-- The linear perturbations that make a `C²` function Morse on an open set are dense in the
continuous dual. No measurable structure appears in the statement: the Haar measure that produces
the density is an auxiliary object of the proof, which installs the Borel structure it needs. -/
theorem dense_setOfPred_hasNondegenerateCriticalPointsOn_sub (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) :
    Dense {a : E →L[ℝ] ℝ | HasNondegenerateCriticalPointsOn (fun y ↦ f y - a y) U} := by
  borelize (E →L[ℝ] ℝ)
  refine Measure.dense_of_ae (μ := (addHaar : Measure (E →L[ℝ] ℝ))) ?_
  filter_upwards [ae_hasNondegenerateCriticalPointsOn_sub addHaar hU hf] with a ha using ha

/-- **A `C²` function is made Morse by an arbitrarily small linear perturbation**: for every
`ε > 0` there is a continuous linear functional of operator norm less than `ε` whose subtraction
leaves only nondegenerate critical points on `U`. -/
theorem exists_norm_lt_hasNondegenerateCriticalPointsOn_sub (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E →L[ℝ] ℝ, ‖a‖ < ε ∧ HasNondegenerateCriticalPointsOn (fun y ↦ f y - a y) U := by
  obtain ⟨a, hmem, hball⟩ :=
    (dense_setOfPred_hasNondegenerateCriticalPointsOn_sub hU hf).exists_mem_open
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩
  exact ⟨a, by simpa [Metric.mem_ball, dist_zero_right] using hball, hmem⟩

end FiniteDimensional

/-! ### The gradient formulation

On a real inner product space the perturbations are usually written `f - ⟪v, ·⟫`, so that the
gradient of the perturbed function is `∇f - v`; the Riesz isometry carries the statement above to
that form.
-/

section InnerProduct

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {U : Set E}

/-- **Almost every perturbation by a linear form `⟪v, ·⟫` of a `C²` function is Morse.** This is
`TauCeti.ae_hasNondegenerateCriticalPointsOn_sub` transported along the Riesz isometry, which is a
continuous linear equivalence and so carries null sets to null sets; the perturbed function has
gradient `∇f - v`, which is the shape the negative gradient flow is stated in.

No measurable structure on the dual appears in the statement: the Borel one is installed inside
the proof, where the Haar measure of the dual is the auxiliary object being transported. -/
theorem ae_hasNondegenerateCriticalPointsOn_sub_inner [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ∀ᵐ v ∂μ, HasNondegenerateCriticalPointsOn (fun y ↦ f y - ⟪v, y⟫_ℝ) U := by
  borelize (E →L[ℝ] ℝ)
  have hbad := ae_hasNondegenerateCriticalPointsOn_sub (addHaar : Measure (E →L[ℝ] ℝ)) hU hf
  rw [ae_iff] at hbad ⊢
  have hpre : {v : E | ¬ HasNondegenerateCriticalPointsOn (fun y ↦ f y - ⟪v, y⟫_ℝ) U} =
      (toDual ℝ E).toContinuousLinearEquiv ⁻¹'
        {a : E →L[ℝ] ℝ | ¬ HasNondegenerateCriticalPointsOn (fun y ↦ f y - a y) U} := by
    ext v
    simp [toDual_apply_apply]
  rw [hpre]
  exact (((toDual ℝ E).toContinuousLinearEquiv).quasiMeasurePreserving_addHaar μ
    addHaar).preimage_null hbad

/-- The vectors `v` for which subtracting `⟪v, ·⟫` makes a `C²` function Morse on an open set are
dense. As above, the Haar measure witnessing the density is internal to the proof, so the
statement mentions no measurable structure. -/
theorem dense_setOfPred_hasNondegenerateCriticalPointsOn_sub_inner (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) :
    Dense {v : E | HasNondegenerateCriticalPointsOn (fun y ↦ f y - ⟪v, y⟫_ℝ) U} := by
  borelize E
  refine Measure.dense_of_ae (μ := (addHaar : Measure E)) ?_
  filter_upwards [ae_hasNondegenerateCriticalPointsOn_sub_inner addHaar hU hf] with v hv using hv

/-- **A `C²` function is made Morse by subtracting `⟪v, ·⟫` for an arbitrarily small `v`**: for
every `ε > 0` there is a vector of norm less than `ε` whose associated linear form, subtracted,
leaves only nondegenerate critical points on `U`. Equivalently, the gradient of `f` may be shifted
by an arbitrarily small vector to make `f` Morse. -/
theorem exists_norm_lt_hasNondegenerateCriticalPointsOn_sub_inner (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, ‖v‖ < ε ∧ HasNondegenerateCriticalPointsOn (fun y ↦ f y - ⟪v, y⟫_ℝ) U := by
  obtain ⟨v, hmem, hball⟩ :=
    (dense_setOfPred_hasNondegenerateCriticalPointsOn_sub_inner hU hf).exists_mem_open
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩
  exact ⟨v, by simpa [Metric.mem_ball, dist_zero_right] using hball, hmem⟩

end InnerProduct

end TauCeti
