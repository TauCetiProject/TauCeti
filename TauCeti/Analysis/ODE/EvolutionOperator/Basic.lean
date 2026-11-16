/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv

/-!
# Stationary first-order evolution operators on unbounded domains

Given a continuous linear map `ι : D →L[ℝ] H` between real normed spaces (typically a compact
inclusion of a domain Banach space `D`, such as `H¹(S¹)`, into a Hilbert space `H`, such as
`H⁰(S¹)`), the evolution Sobolev space `Lᵖ(Ω; D) ∩ W^{1,p}(Ω; H)` is already realized by the
closed weak-derivative graph `WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))`, with
Euclidean graph norm `(‖u‖_{Lᵖ(Ω; D)}² + ‖(ι u)'‖_{Lᵖ(Ω; H)}²)¹⁄²`. No new Sobolev carrier is
introduced.

For a bounded operator `A : D →L[ℝ] H`, `TauCeti.WeakDerivStep.stationaryEvolutionOperator ι A`
realizes the stationary evolution operator `u ↦ (ι u)' + A u` as a bounded linear map into
`Lᵖ(Ω; H)`. It depends `1`-Lipschitz continuously on `A` in operator norm and satisfies the
derivative estimate `‖(ι u)'‖ ≤ ‖(ι u)' + A u‖ + ‖A‖ ‖u‖`.

This file also provides two structural tools on the evolution graph space:

* **Codomain projection (`TauCeti.WeakDerivStep.postcompBaseL`).** Postcomposing the `H`-valued
  field with a bounded linear map `T : H →L[ℝ] G` sends a weak-derivative graph element into
  `W^{1,p}(Ω; G)`. When `T` intertwines `A` with an operator `B : G →L[ℝ] G`
  (`T ∘L A = B ∘L T ∘L ι`), this intertwines `stationaryEvolutionOperator ι A` with the constant
  trajectory operator `u ↦ u' + B u` (`TauCeti.WeakDerivStep.trajectoryOperator_postcompBaseL`).
* **Time reflection (`TauCeti.WeakDerivStep.reflectEvolutionEquiv`).** On the full line `ℝ` with
  Lebesgue measure, reflection `s ↦ u(-s)` is an involutive linear isometry of the evolution
  Sobolev space that conjugates `∂s - A` to `-(∂s + A)`. Consequently `∂s + A` and `∂s - A` have
  the same operator norm, are simultaneously invertible, and have inverses of the same norm.

## Main declarations

* `TauCeti.WeakDerivStep.norm_compLpL_apply_one_weakFDeriv`: evaluating a 1D weak derivative at `1`
  preserves its `Lᵖ` norm.
* `TauCeti.WeakDerivStep.stationaryEvolutionOperator`: the stationary evolution operator
  `u ↦ (ι u)' + A u`, together with its operator norm bound `1 + ‖A‖`, `1`-Lipschitz dependence on
  `A`, and the derivative bound `‖(ι u)'‖ ≤ ‖(ι u)' + A u‖ + ‖A‖ ‖u‖`.
* `TauCeti.WeakDerivStep.postcompBaseL` and
  `TauCeti.WeakDerivStep.trajectoryOperator_postcompBaseL`: projection of a graph element along
  `T : H →L[ℝ] G` and intertwining with `trajectoryOperator`.
* `TauCeti.WeakDerivStep.reflectEvolutionEquiv`,
  `TauCeti.WeakDerivStep.isInvertible_stationaryEvolutionOperator_neg_iff`,
  `TauCeti.WeakDerivStep.norm_inverse_stationaryEvolutionOperator_neg`: time reflection on `ℝ` and
  invariance of norm, invertibility, and inverse norm under `A ↦ -A`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33 (the operator `d/ds + A` on `W^{1,2}(ℝ, H) ∩ L²(ℝ, D)`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

/-! ### Isometric evaluation of weak derivatives on the line -/

section EvalOne

variable {X H : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Evaluating the weak derivative of a one-dimensional `WeakDerivStep` element at `1 : ℝ`
preserves its `Lᵖ` norm, since evaluation at `1` is the inverse of the linear isometry
`toSpanSingletonLIE`. -/
theorem norm_compLpL_apply_one_weakFDeriv (base : X →L[ℝ] Lp H p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) :
    ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
      (weakFDeriv base u)‖ = ‖weakFDeriv base u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u)]
    with s hs
  rw [hs, ContinuousLinearMap.apply_apply]
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ H).symm.norm_map (weakFDeriv base u s))

end EvalOne

/-! ### Stationary evolution operators -/

section Stationary

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- The stationary first-order evolution operator `u ↦ (ι u)' + A u` on the evolution Sobolev space
`Lᵖ(Ω; D) ∩ W^{1,p}(Ω; H)`, realized as `WeakDerivStep mu Omega p (ι.compLpL p _)`. -/
def stationaryEvolutionOperator (ι A : D →L[ℝ] H) :
    WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)) →L[ℝ]
      Lp H p (mu.restrict Omega) :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
      (weakFDerivL (ι.compLpL p (mu.restrict Omega))) +
    (A.compLpL p (mu.restrict Omega)).comp
      (prevL (ι.compLpL p (mu.restrict Omega)))

/-- Applying `stationaryEvolutionOperator ι A` adds the weak derivative in direction `1` and the
pointwise action of `A`. -/
@[simp]
theorem stationaryEvolutionOperator_apply (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    stationaryEvolutionOperator ι A u =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
        (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u) +
      A.compLpL p (mu.restrict Omega) (prev (ι.compLpL p (mu.restrict Omega)) u) := by
  simp only [stationaryEvolutionOperator, add_apply, ContinuousLinearMap.comp_apply,
    weakFDerivL_apply, prevL_apply]

/-- Pointwise almost-everywhere formula for `stationaryEvolutionOperator`. -/
theorem stationaryEvolutionOperator_apply_ae (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    stationaryEvolutionOperator ι A u =ᵐ[mu.restrict Omega] fun s ↦
      weakFDeriv (ι.compLpL p (mu.restrict Omega)) u s 1 +
        A (prev (ι.compLpL p (mu.restrict Omega)) u s) := by
  rw [stationaryEvolutionOperator_apply]
  filter_upwards [Lp.coeFn_add
    ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u))
    (A.compLpL p (mu.restrict Omega) (prev (ι.compLpL p (mu.restrict Omega)) u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u),
    A.coeFn_compLpL (prev (ι.compLpL p (mu.restrict Omega)) u)] with s hs hd hA
  exact hs.trans (by simp only [Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply])

/-- Subtracting two stationary evolution operators cancels the derivative term. -/
theorem stationaryEvolutionOperator_sub (ι A B : D →L[ℝ] H) :
    stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      stationaryEvolutionOperator ι B =
      ((A - B).compLpL p (mu.restrict Omega)).comp
        (prevL (ι.compLpL p (mu.restrict Omega))) := by
  ext1 u
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (stationaryEvolutionOperator (p := p) ι A u)
      (stationaryEvolutionOperator (p := p) ι B u),
    stationaryEvolutionOperator_apply_ae ι A u,
    stationaryEvolutionOperator_apply_ae ι B u,
    (A - B).coeFn_compLpL (prev (ι.compLpL p (mu.restrict Omega)) u)] with s hsub hA hB hAB
  simp only [sub_apply, ContinuousLinearMap.comp_apply, prevL_apply]
  rw [hsub, Pi.sub_apply, hA, hB, hAB, sub_apply, add_sub_add_left_eq_sub]

/-- The operator norm of `stationaryEvolutionOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_stationaryEvolutionOperator_le (ι A : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [stationaryEvolutionOperator_apply]
  have hd : ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u)‖ ≤ ‖u‖ := by
    rw [norm_compLpL_apply_one_weakFDeriv]
    exact norm_weakFDeriv_le _ u
  have hA : ‖A.compLpL p (mu.restrict Omega)
      (prev (ι.compLpL p (mu.restrict Omega)) u)‖ ≤ ‖A‖ * ‖u‖ :=
    ((A.compLpL p (mu.restrict Omega)).le_opNorm _).trans <| by
      gcongr
      · exact A.norm_compLpL_le
      · exact norm_prev_le _ u
  calc
    _ ≤ ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
        (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u)‖ +
        ‖A.compLpL p (mu.restrict Omega) (prev (ι.compLpL p (mu.restrict Omega)) u)‖ :=
      norm_add_le _ _
    _ ≤ ‖u‖ + ‖A‖ * ‖u‖ := add_le_add hd hA
    _ = (1 + ‖A‖) * ‖u‖ := by ring

/-- Perturbing `A` changes `stationaryEvolutionOperator ι A` by at most `‖A - B‖` in operator
norm. -/
theorem norm_stationaryEvolutionOperator_sub_le (ι A B : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      stationaryEvolutionOperator ι B‖ ≤ ‖A - B‖ := by
  rw [stationaryEvolutionOperator_sub]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  simp only [ContinuousLinearMap.comp_apply, prevL_apply]
  exact (((A - B).compLpL p (mu.restrict Omega)).le_opNorm _).trans <| by
    gcongr
    · exact (A - B).norm_compLpL_le
    · exact norm_prev_le _ u

/-- `stationaryEvolutionOperator ι` is `1`-Lipschitz in operator norm. -/
theorem lipschitzWith_stationaryEvolutionOperator (ι : D →L[ℝ] H) :
    LipschitzWith 1 (stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_stationaryEvolutionOperator_sub_le (mu := mu) (Omega := Omega) (p := p) ι A B

/-- `stationaryEvolutionOperator ι` depends continuously in operator norm on `A`. -/
@[fun_prop]
theorem continuous_stationaryEvolutionOperator (ι : D →L[ℝ] H) :
    Continuous (stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  (lipschitzWith_stationaryEvolutionOperator ι).continuous

/-- The weak derivative of an evolution path is controlled by its image under
`stationaryEvolutionOperator ι A` and its `Lᵖ(Ω; D)` norm:
`‖(ι u)'‖ ≤ ‖(ι u)' + A u‖ + ‖A‖ ‖u‖`. -/
theorem norm_weakFDeriv_le_norm_stationaryEvolutionOperator_add (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    ‖weakFDeriv (ι.compLpL p (mu.restrict Omega)) u‖ ≤
      ‖stationaryEvolutionOperator ι A u‖ +
        ‖A‖ * ‖prev (ι.compLpL p (mu.restrict Omega)) u‖ := by
  have hT := stationaryEvolutionOperator_apply ι A u
  have hsub : (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u) =
      stationaryEvolutionOperator ι A u -
        A.compLpL p (mu.restrict Omega) (prev (ι.compLpL p (mu.restrict Omega)) u) :=
    eq_sub_of_add_eq hT.symm
  rw [← norm_compLpL_apply_one_weakFDeriv, hsub]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact ((A.compLpL p (mu.restrict Omega)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right A.norm_compLpL_le (norm_nonneg _))

end Stationary

/-! ### Codomain projection and intertwining with trajectory operators -/

section Postcomp

variable {X H G : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Postcomposing the field of a weak-derivative graph element with a continuous linear map
`T : H →L[ℝ] G` preserves weak differentiability on `Omega`. -/
theorem hasWeakFDerivOn_postcompBase [IsLocallyFiniteMeasure (mu.restrict Omega)]
    (base : X →L[ℝ] Lp H p (mu.restrict Omega)) (T : H →L[ℝ] G)
    (u : WeakDerivStep mu Omega p base) :
    HasWeakFDerivOn mu Omega
      (ContinuousLinearMap.id ℝ (Lp G p (mu.restrict Omega))
        (T.compLpL p (mu.restrict Omega) (base (prev base u))))
      ((ContinuousLinearMap.compL ℝ ℝ H G T).compLpL p (mu.restrict Omega)
        (weakFDeriv base u)) := by
  refine (((hasWeakFDerivOn_base_prev base u).clm_comp T).congr_ae
    (Filter.EventuallyEq.symm (T.coeFn_compLpL (base (prev base u))))).congr_ae_deriv ?_
  filter_upwards [(ContinuousLinearMap.compL ℝ ℝ H G T).coeFn_compLpL (weakFDeriv base u)] with s hs
  rw [hs, ContinuousLinearMap.compL_apply]

/-- Postcompose the `H`-valued field of a `WeakDerivStep` with `T : H →L[ℝ] G`, landing in
`W^{1,p}(Ω; G)`. -/
def postcompBaseL [IsLocallyFiniteMeasure (mu.restrict Omega)]
    (base : X →L[ℝ] Lp H p (mu.restrict Omega)) (T : H →L[ℝ] G) :
    WeakDerivStep mu Omega p base →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp G p (mu.restrict Omega))) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ mk _
        (T.compLpL p (mu.restrict Omega) (base (prev base u)))
        ((ContinuousLinearMap.compL ℝ ℝ H G T).compLpL p (mu.restrict Omega) (weakFDeriv base u))
        (hasWeakFDerivOn_postcompBase base T u)
      map_add' := fun u v ↦ ext (by simp only [prev_mk, prev_add, map_add])
      map_smul' := fun c u ↦ ext (by simp only [prev_mk, prev_smul, map_smul, RingHom.id_apply]) }
    (‖T‖ * (‖base‖ + 1))
    (fun u ↦ by
      refine (norm_le_norm_prev_add_norm_weakFDeriv _ _).trans ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, prev_mk, weakFDeriv_mk]
      have h1 : ‖T.compLpL p (mu.restrict Omega) (base (prev base u))‖ ≤ ‖T‖ * ‖base‖ * ‖u‖ :=
        ((T.compLpL p (mu.restrict Omega)).le_opNorm _).trans <| by
          calc
            _ ≤ ‖T‖ * (‖base‖ * ‖prev base u‖) := by
              gcongr
              · exact T.norm_compLpL_le
              · exact base.le_opNorm _
            _ ≤ ‖T‖ * (‖base‖ * ‖u‖) := by
              gcongr
              exact norm_prev_le base u
            _ = ‖T‖ * ‖base‖ * ‖u‖ := by ring
      have h2 : ‖(ContinuousLinearMap.compL ℝ ℝ H G T).compLpL p (mu.restrict Omega)
          (weakFDeriv base u)‖ ≤ ‖T‖ * ‖u‖ := by
        have hcomp : ‖ContinuousLinearMap.compL ℝ ℝ H G T‖ ≤ ‖T‖ :=
          ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun L ↦ T.opNorm_comp_le L
        refine (((ContinuousLinearMap.compL ℝ ℝ H G T).compLpL p (mu.restrict Omega)).le_opNorm
          _).trans ?_
        calc
          _ ≤ ‖T‖ * ‖weakFDeriv base u‖ := by
            gcongr
            exact (ContinuousLinearMap.compL ℝ ℝ H G T).norm_compLpL_le.trans hcomp
          _ ≤ ‖T‖ * ‖u‖ := mul_le_mul_of_nonneg_left (norm_weakFDeriv_le base u) (norm_nonneg T)
      linarith)

@[simp]
theorem prev_postcompBaseL [IsLocallyFiniteMeasure (mu.restrict Omega)]
    (base : X →L[ℝ] Lp H p (mu.restrict Omega)) (T : H →L[ℝ] G)
    (u : WeakDerivStep mu Omega p base) :
    prev (ContinuousLinearMap.id ℝ (Lp G p (mu.restrict Omega))) (postcompBaseL base T u) =
      T.compLpL p (mu.restrict Omega) (base (prev base u)) := by
  simp only [postcompBaseL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, prev_mk]

@[simp]
theorem weakFDeriv_postcompBaseL [IsLocallyFiniteMeasure (mu.restrict Omega)]
    (base : X →L[ℝ] Lp H p (mu.restrict Omega)) (T : H →L[ℝ] G)
    (u : WeakDerivStep mu Omega p base) :
    weakFDeriv (ContinuousLinearMap.id ℝ (Lp G p (mu.restrict Omega))) (postcompBaseL base T u) =
      (ContinuousLinearMap.compL ℝ ℝ H G T).compLpL p (mu.restrict Omega) (weakFDeriv base u) := by
  simp only [postcompBaseL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    weakFDeriv_mk]

/-- Evaluating the weak derivative of `postcompBaseL base T u` at `1` agrees with applying `T` to
the weak derivative of `u` evaluated at `1`. -/
theorem compLpL_apply_one_weakFDeriv_postcompBaseL [IsLocallyFiniteMeasure (mu.restrict Omega)]
    (base : X →L[ℝ] Lp H p (mu.restrict Omega)) (T : H →L[ℝ] G)
    (u : WeakDerivStep mu Omega p base) :
    (ContinuousLinearMap.apply ℝ G (1 : ℝ)).compLpL p (mu.restrict Omega)
        (weakFDeriv (ContinuousLinearMap.id ℝ (Lp G p (mu.restrict Omega)))
          (postcompBaseL base T u)) =
      T.compLpL p (mu.restrict Omega)
        ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
          (weakFDeriv base u)) := by
  apply Lp.ext
  rw [weakFDeriv_postcompBaseL]
  filter_upwards [(ContinuousLinearMap.apply ℝ G (1 : ℝ)).coeFn_compLpL
      ((ContinuousLinearMap.compL ℝ ℝ H G T).compLpL p (mu.restrict Omega) (weakFDeriv base u)),
    (ContinuousLinearMap.compL ℝ ℝ H G T).coeFn_compLpL (weakFDeriv base u),
    T.coeFn_compLpL
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega) (weakFDeriv base u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u)]
    with s h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  rfl

/-- **Intertwining stationary evolution operators with trajectory operators.** If `T : H →L[ℝ] G`
intertwines `A` with `B : G →L[ℝ] G`, meaning `T (A x) = B (T (ι x))` for all `x ∈ D`, and `BL` is
an `L∞` class of the constant operator `B`, then projecting along `T` intertwines
`stationaryEvolutionOperator ι A` with `trajectoryOperator BL`. -/
theorem trajectoryOperator_postcompBaseL [IsLocallyFiniteMeasure (mu.restrict Omega)]
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ι A : D →L[ℝ] H) (T : H →L[ℝ] G) (B : G →L[ℝ] G)
    (hinter : ∀ x : D, T (A x) = B (T (ι x)))
    (BL : Lp (G →L[ℝ] G) ∞ (mu.restrict Omega))
    (hBL : BL =ᵐ[mu.restrict Omega] fun _ ↦ B)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    trajectoryOperator BL (postcompBaseL (ι.compLpL p (mu.restrict Omega)) T u) =
      T.compLpL p (mu.restrict Omega) (stationaryEvolutionOperator ι A u) := by
  apply Lp.ext
  filter_upwards [trajectoryOperator_apply_ae BL (postcompBaseL _ T u),
    (ContinuousLinearMap.compL ℝ ℝ H G T).coeFn_compLpL (weakFDeriv _ u),
    T.coeFn_compLpL (ι.compLpL p (mu.restrict Omega) (prev _ u)),
    ι.coeFn_compLpL (prev _ u),
    hBL,
    T.coeFn_compLpL (stationaryEvolutionOperator ι A u),
    stationaryEvolutionOperator_apply_ae ι A u] with s hT hw hTι hι hBLs hTS hS
  rw [hT, weakFDeriv_postcompBaseL, prev_postcompBaseL, hw, hTι, hι, hBLs, hTS, hS, map_add,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hinter]

end Postcomp

/-! ### Time reflection on the full line -/

section Reflect

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {p : ENNReal} [Fact (1 ≤ p)]

private theorem measurePreserving_neg_top :
    MeasurePreserving (fun s : ℝ ↦ -s)
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    Measure.measurePreserving_neg (volume : Measure ℝ)

private def reflectLpEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ≃ₗᵢ[ℝ]
      Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ measurePreserving_neg_top measurePreserving_neg_top
    (Filter.Eventually.of_forall fun s ↦ neg_neg s)

private theorem coeFn_reflectLpEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ⇑(reflectLpEquiv (p := p) E f) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ f (-s) :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv ℝ _ _ _ f

private theorem hasWeakFDerivOn_reflect (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    HasWeakFDerivOn volume ⊤
      (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (reflectLpEquiv (p := p) D (prev _ u)))
      ((-reflectLpEquiv (p := p) (ℝ →L[ℝ] H) (weakFDeriv _ u) :
        Lp (ℝ →L[ℝ] H) p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) : ℝ → ℝ →L[ℝ] H) := by
  have h1 := (hasWeakFDerivOn_base_prev (ι.compLpL p _) u).comp_continuousLinearEquiv
    (U := ⊤) (ContinuousLinearEquiv.neg ℝ) (Measure.measurePreserving_neg volume)
    (Set.mapsTo_univ _ _)
  refine (h1.congr_ae ?_).congr_ae_deriv ?_
  · have hcomp := measurePreserving_neg_top.quasiMeasurePreserving.ae_eq_comp
      (ι.coeFn_compLpL (prev (ι.compLpL p _) u))
    filter_upwards [hcomp, ι.coeFn_compLpL (reflectLpEquiv (p := p) D (prev _ u)),
      coeFn_reflectLpEquiv (p := p) (prev _ u)] with s hιneg hιref href
    simp only [Function.comp_apply, ContinuousLinearEquiv.neg_apply] at hιneg ⊢
    rw [hιneg, hιref, href]
  · filter_upwards [Lp.coeFn_neg (reflectLpEquiv (p := p) (ℝ →L[ℝ] H) (weakFDeriv _ u)),
      coeFn_reflectLpEquiv (p := p) (weakFDeriv _ u)] with s hneg href
    ext
    simp only [hneg, Pi.neg_apply, neg_apply, href, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.neg_apply, map_neg]

private def reflectEvolutionFun (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :=
  mk (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (reflectLpEquiv (p := p) D (prev _ u))
    (-reflectLpEquiv (p := p) (ℝ →L[ℝ] H) (weakFDeriv _ u))
    (hasWeakFDerivOn_reflect ι u)

private theorem prev_reflectEvolutionFun (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    prev (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (reflectEvolutionFun ι u) =
      reflectLpEquiv (p := p) D (prev _ u) :=
  prev_mk _ _ _ _

private theorem weakFDeriv_reflectEvolutionFun (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    weakFDeriv (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (reflectEvolutionFun ι u) =
      -reflectLpEquiv (p := p) (ℝ →L[ℝ] H) (weakFDeriv _ u) :=
  weakFDeriv_mk _ _ _ _

private theorem reflectEvolutionFun_add (ι : D →L[ℝ] H)
    (u v : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    reflectEvolutionFun ι (u + v) = reflectEvolutionFun ι u + reflectEvolutionFun ι v :=
  ext (by
    rw [prev_reflectEvolutionFun, prev_add, map_add, prev_add,
      prev_reflectEvolutionFun, prev_reflectEvolutionFun])

private theorem reflectEvolutionFun_smul (ι : D →L[ℝ] H) (c : ℝ)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    reflectEvolutionFun ι (c • u) = c • reflectEvolutionFun ι u :=
  ext (by
    rw [prev_reflectEvolutionFun, prev_smul, map_smul, prev_smul, prev_reflectEvolutionFun])

private theorem norm_reflectEvolutionFun (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖reflectEvolutionFun ι u‖ = ‖u‖ := by
  have hsq : ‖reflectEvolutionFun ι u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ (reflectEvolutionFun ι u),
      norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ u,
      prev_reflectEvolutionFun, weakFDeriv_reflectEvolutionFun, norm_neg,
      (reflectLpEquiv (p := p) D).norm_map,
      (reflectLpEquiv (p := p) (ℝ →L[ℝ] H)).norm_map]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem reflectEvolutionFun_involutive (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    reflectEvolutionFun ι (reflectEvolutionFun ι u) = u := by
  apply ext
  rw [prev_reflectEvolutionFun, prev_reflectEvolutionFun]
  apply Lp.ext
  have h1 := coeFn_reflectLpEquiv (p := p) (reflectLpEquiv (p := p) D (prev _ u))
  have h2 := measurePreserving_neg_top.quasiMeasurePreserving.ae_eq_comp
    (coeFn_reflectLpEquiv (p := p) (prev _ u))
  filter_upwards [h1, h2] with s hs1 hs2
  simpa only [Function.comp_apply, neg_neg] using hs1.trans hs2

/-- Time reflection `s ↦ u(-s)` as an involutive linear isometry of the evolution Sobolev space
on `ℝ`. -/
def reflectEvolutionEquiv (ι : D →L[ℝ] H) :
    WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) ≃ₗᵢ[ℝ]
      WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) where
  toFun := reflectEvolutionFun ι
  invFun := reflectEvolutionFun ι
  left_inv := reflectEvolutionFun_involutive ι
  right_inv := reflectEvolutionFun_involutive ι
  map_add' := reflectEvolutionFun_add ι
  map_smul' := reflectEvolutionFun_smul ι
  norm_map' := norm_reflectEvolutionFun ι

/-- Time reflection is its own inverse. -/
@[simp]
theorem reflectEvolutionEquiv_symm (ι : D →L[ℝ] H) :
    (reflectEvolutionEquiv (p := p) ι).symm = reflectEvolutionEquiv (p := p) ι := by
  ext u
  rfl

private theorem prev_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    prev (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (reflectEvolutionEquiv ι u) =
      reflectLpEquiv (p := p) D (prev _ u) :=
  prev_reflectEvolutionFun ι u

private theorem weakFDeriv_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    weakFDeriv (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (reflectEvolutionEquiv ι u) = -reflectLpEquiv (p := p) (ℝ →L[ℝ] H) (weakFDeriv _ u) :=
  weakFDeriv_reflectEvolutionFun ι u

/-- Time reflection precomposes the `Lᵖ(ℝ; D)` path with negation almost everywhere. -/
theorem prev_reflectEvolutionEquiv_ae (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    prev (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (reflectEvolutionEquiv ι u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ prev (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u (-s) := by
  rw [prev_reflectEvolutionEquiv]
  exact coeFn_reflectLpEquiv (p := p) (prev _ u)

/-- Time reflection negates and reflects the weak derivative almost everywhere. -/
theorem weakFDeriv_reflectEvolutionEquiv_ae (ι : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    weakFDeriv (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (reflectEvolutionEquiv ι u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -weakFDeriv (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u (-s) := by
  rw [weakFDeriv_reflectEvolutionEquiv]
  filter_upwards [Lp.coeFn_neg (reflectLpEquiv (p := p) (ℝ →L[ℝ] H) (weakFDeriv _ u)),
    coeFn_reflectLpEquiv (p := p) (weakFDeriv _ u)] with s hneg href
  rw [hneg, Pi.neg_apply, href]

private def negReflectLpEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ≃ₗᵢ[ℝ]
      Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (reflectLpEquiv (p := p) E).trans (LinearIsometryEquiv.neg ℝ)

/-- Pointwise almost-everywhere conjugation of `∂s - A` and `∂s + A` under time reflection. -/
theorem stationaryEvolutionOperator_neg_reflectEvolutionEquiv_ae (ι A : D →L[ℝ] H)
    (u : WeakDerivStep volume ⊤ p (ι.compLpL p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    stationaryEvolutionOperator (p := p) ι (-A) (reflectEvolutionEquiv ι u)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -(stationaryEvolutionOperator (p := p) ι A u) (-s) := by
  have hSneg := measurePreserving_neg_top.quasiMeasurePreserving.ae_eq_comp
    (stationaryEvolutionOperator_apply_ae (p := p) ι A u)
  filter_upwards [stationaryEvolutionOperator_apply_ae (p := p) ι (-A)
      (reflectEvolutionEquiv (p := p) ι u),
    weakFDeriv_reflectEvolutionEquiv_ae (p := p) ι u,
    prev_reflectEvolutionEquiv_ae (p := p) ι u,
    hSneg] with s h1 h2 h3 h4
  simp only [Function.comp_apply] at h4
  rw [h1, h2, h3, neg_apply, neg_apply, h4]
  abel

/-- Time reflection conjugates `∂s - A` to `-(∂s + A)` on `ℝ`:
`∂s - A = (-reflect) ∘ (∂s + A) ∘ reflect⁻¹`. -/
private theorem stationaryEvolutionOperator_neg_eq (ι A : D →L[ℝ] H) :
    stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι (-A) =
      (negReflectLpEquiv (p := p) H).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι A).comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (reflectEvolutionEquiv (p := p) ι).symm.toContinuousLinearEquiv)) := by
  ext1 u
  set v := reflectEvolutionEquiv (p := p) ι u
  have hv : reflectEvolutionEquiv (p := p) ι v = u :=
    reflectEvolutionFun_involutive (p := p) ι u
  have hval : (negReflectLpEquiv (p := p) H).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι A).comp
        (ContinuousLinearEquiv.toContinuousLinearMap
          (reflectEvolutionEquiv (p := p) ι).symm.toContinuousLinearEquiv)) u =
      -reflectLpEquiv (p := p) H (stationaryEvolutionOperator (p := p) ι A v) := rfl
  rw [hval, ← hv]
  apply Lp.ext
  filter_upwards [stationaryEvolutionOperator_neg_reflectEvolutionEquiv_ae (p := p) ι A v,
    Lp.coeFn_neg (reflectLpEquiv (p := p) H (stationaryEvolutionOperator (p := p) ι A v)),
    coeFn_reflectLpEquiv (p := p) (stationaryEvolutionOperator (p := p) ι A v)] with s h1 h2 h3
  rw [h1, h2, Pi.neg_apply, h3]

/-- `∂s - A` and `∂s + A` have the same operator norm on `ℝ`. -/
theorem norm_stationaryEvolutionOperator_neg (ι A : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι (-A)‖ =
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι A‖ := by
  rw [stationaryEvolutionOperator_neg_eq]
  exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp
    (negReflectLpEquiv (p := p) H) _).trans
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ (reflectEvolutionEquiv (p := p) ι).symm)

/-- `∂s - A` is invertible on `ℝ` if and only if `∂s + A` is invertible on `ℝ`. -/
theorem isInvertible_stationaryEvolutionOperator_neg_iff (ι A : D →L[ℝ] H) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι (-A)).IsInvertible ↔
      (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι A).IsInvertible := by
  rw [stationaryEvolutionOperator_neg_eq, ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv]

/-- `(∂s - A)⁻¹` and `(∂s + A)⁻¹` have the same operator norm on `ℝ`. -/
theorem norm_inverse_stationaryEvolutionOperator_neg (ι A : D →L[ℝ] H) :
    ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι (-A)).inverse‖ =
      ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := p) ι A).inverse‖ := by
  rw [stationaryEvolutionOperator_neg_eq, ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearMap.comp_assoc]
  exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp
    (reflectEvolutionEquiv (p := p) ι) _).trans
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ (negReflectLpEquiv (p := p) H).symm)

end Reflect

end TauCeti.WeakDerivStep
