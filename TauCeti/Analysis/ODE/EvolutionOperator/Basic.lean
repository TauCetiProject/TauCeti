/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.MeasureTheory.Group.Inversion
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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
`Lᵖ(Ω; H)`. It depends `1`-Lipschitz continuously on `A` in operator norm, satisfies the derivative
estimate `‖(ι u)'‖ ≤ ‖(ι u)' + A u‖ + ‖A‖ ‖u‖`, characterizes weak solutions of `(ι u)' = f - A u`,
and agrees almost everywhere with the classical expression `(ι ∘ v)' + A ∘ v` on differentiable
representatives.

This file also provides two structural tools on the evolution graph space:

* **Intertwining with trajectory operators (`trajectoryOperator_postcompBaseL`).** Postcomposing
  the `H`-valued field with `T : H →L[ℝ] G` via `TauCeti.WeakDerivStep.postcompBaseL` intertwines
  `stationaryEvolutionOperator ι A` with the constant trajectory operator `u ↦ u' + B u` whenever
  `T ∘L A = B ∘L T ∘L ι`.
* **Time reflection (`TauCeti.WeakDerivStep.reflectEvolutionEquiv`).** On the full line `ℝ` with
  any additive Haar measure, reflection `s ↦ u(-s)` is an involutive linear isometry of the
  evolution Sobolev space that conjugates `∂s - A` to `-(∂s + A)`
  (`stationaryEvolutionOperator_neg_eq`) and conjugates their inverses
  (`inverse_stationaryEvolutionOperator_neg`). Consequently `∂s + A` and `∂s - A` have the same
  operator norm, are simultaneously invertible, and have inverses of the same norm.

## Main declarations

* `TauCeti.WeakDerivStep.stationaryEvolutionOperator`: the stationary evolution operator
  `u ↦ (ι u)' + A u`, together with its operator norm bound `1 + ‖A‖`, `1`-Lipschitz dependence on
  `A`, derivative bound `‖(ι u)'‖ ≤ ‖(ι u)' + A u‖ + ‖A‖ ‖u‖`, weak-ODE characterization
  (`stationaryEvolutionOperator_eq_iff_hasWeakLineDerivOn`,
  `exists_prev_eq_and_stationaryEvolutionOperator_eq_of_hasWeakLineDerivOn`), and classical
  derivative agreement (`stationaryEvolutionOperator_apply_ae_eq_deriv_add`).
* `TauCeti.WeakDerivStep.trajectoryOperator_postcompBaseL`: intertwining of
  `stationaryEvolutionOperator` with `trajectoryOperator` under `postcompBaseL`.
* `TauCeti.WeakDerivStep.reflectEvolutionEquiv`,
  `TauCeti.WeakDerivStep.stationaryEvolutionOperator_neg_eq`,
  `TauCeti.WeakDerivStep.inverse_stationaryEvolutionOperator_neg`,
  `TauCeti.WeakDerivStep.isInvertible_stationaryEvolutionOperator_neg_iff`,
  `TauCeti.WeakDerivStep.norm_inverse_stationaryEvolutionOperator_neg`: time reflection on `ℝ` and
  conjugation / invariance of norm, invertibility, and inverse under `A ↦ -A`.

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
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
        (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u) +
      A.compLp (prev (ι.compLpL p (mu.restrict Omega)) u) := by
  simp only [stationaryEvolutionOperator, add_apply, ContinuousLinearMap.comp_apply,
    weakFDerivL_apply, prevL_apply, ContinuousLinearMap.compLpL_apply]

/-- Pointwise almost-everywhere formula for `stationaryEvolutionOperator`. -/
theorem stationaryEvolutionOperator_apply_ae (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    stationaryEvolutionOperator ι A u =ᵐ[mu.restrict Omega] fun s ↦
      weakFDeriv (ι.compLpL p (mu.restrict Omega)) u s 1 +
        A (prev (ι.compLpL p (mu.restrict Omega)) u s) := by
  rw [stationaryEvolutionOperator_apply]
  filter_upwards [Lp.coeFn_add
    ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u))
    (A.compLp (prev (ι.compLpL p (mu.restrict Omega)) u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLp
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u),
    A.coeFn_compLp (prev (ι.compLpL p (mu.restrict Omega)) u)] with s hs hd hA
  exact hs.trans (by simp only [Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply])

/-- Subtracting two stationary evolution operators cancels the derivative term. -/
theorem stationaryEvolutionOperator_sub (ι A B : D →L[ℝ] H) :
    stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      stationaryEvolutionOperator ι B =
      ((A - B).compLpL p (mu.restrict Omega)).comp
        (prevL (ι.compLpL p (mu.restrict Omega))) := by
  simp only [stationaryEvolutionOperator, ContinuousLinearMap.sub_compLpL,
    ContinuousLinearMap.sub_comp]
  abel

/-- The operator norm of `stationaryEvolutionOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_stationaryEvolutionOperator_le (ι A : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [stationaryEvolutionOperator_apply]
  have hd : ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u)‖ ≤ ‖u‖ := by
    rw [ContinuousLinearMap.norm_compLp_apply_one]
    exact norm_weakFDeriv_le _ u
  have hA : ‖A.compLp (prev (ι.compLpL p (mu.restrict Omega)) u)‖ ≤ ‖A‖ * ‖u‖ := by
    rw [← ContinuousLinearMap.compLpL_apply]
    exact ((A.compLpL p (mu.restrict Omega)).le_opNorm _).trans <| by
      gcongr
      · exact A.norm_compLpL_le
      · exact norm_prev_le _ u
  calc
    _ ≤ ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
        (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u)‖ +
        ‖A.compLp (prev (ι.compLpL p (mu.restrict Omega)) u)‖ :=
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
  have hsub : (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u) =
      stationaryEvolutionOperator ι A u -
        A.compLp (prev (ι.compLpL p (mu.restrict Omega)) u) :=
    eq_sub_of_add_eq hT.symm
  rw [← ContinuousLinearMap.norm_compLp_apply_one, hsub]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  rw [← ContinuousLinearMap.compLpL_apply]
  exact ((A.compLpL p (mu.restrict Omega)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right A.norm_compLpL_le (norm_nonneg _))

/-- Solving `stationaryEvolutionOperator ι A u = f` is equivalent to the weak ordinary
differential equation `(ι u)' = f - A u`. -/
theorem stationaryEvolutionOperator_eq_iff_hasWeakLineDerivOn (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)))
    (f : Lp H p (mu.restrict Omega)) :
    stationaryEvolutionOperator ι A u = f ↔ HasWeakLineDerivOn mu Omega
      (fun s ↦ ι (prev (ι.compLpL p (mu.restrict Omega)) u s))
      (fun s ↦ f s - A (prev (ι.compLpL p (mu.restrict Omega)) u s)) 1 := by
  have hd : HasWeakLineDerivOn mu Omega
      (fun s ↦ ι (prev (ι.compLpL p (mu.restrict Omega)) u s))
      (fun s ↦ weakFDeriv (ι.compLpL p (mu.restrict Omega)) u s 1) 1 :=
    ((hasWeakFDerivOn_base_prev _ u).hasWeakLineDerivOn 1).congr_ae (ι.coeFn_compLpL (prev _ u))
  constructor
  · intro h
    apply hd.congr_ae_deriv
    have hformula := stationaryEvolutionOperator_apply_ae ι A u
    rw [h] at hformula
    filter_upwards [hformula] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · intro h
    apply Lp.ext
    filter_upwards [stationaryEvolutionOperator_apply_ae ι A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd']
    exact sub_add_cancel _ _

/-- **Weak solutions are values of evolution-graph elements.** If `x : Lᵖ(Ω; D)` solves the weak
ODE `(ι ∘ x)' = f - A x`, then `x` is the `D`-valued component of an element `u` of the evolution
Sobolev space with `stationaryEvolutionOperator ι A u = f`. -/
theorem exists_prev_eq_and_stationaryEvolutionOperator_eq_of_hasWeakLineDerivOn (ι A : D →L[ℝ] H)
    {x : Lp D p (mu.restrict Omega)} {f : Lp H p (mu.restrict Omega)}
    (h : HasWeakLineDerivOn mu Omega (fun s ↦ ι (x s)) (fun s ↦ f s - A (x s)) 1) :
    ∃ u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)),
      prev (ι.compLpL p (mu.restrict Omega)) u = x ∧
        stationaryEvolutionOperator ι A u = f := by
  let g := f - A.compLp x
  let lift := (ContinuousLinearMap.toSpanSingletonLIE ℝ H).toLinearIsometry.toContinuousLinearMap
  have hg : (fun s ↦ f s - A (x s)) =ᵐ[mu.restrict Omega] g := by
    filter_upwards [Lp.coeFn_sub f (A.compLp x), A.coeFn_compLp x] with s hs hAs
    simp only [g, hs, Pi.sub_apply, hAs]
  have hD : HasWeakFDerivOn mu Omega (ι.compLpL p (mu.restrict Omega) x) (lift.compLp g) := by
    rw [hasWeakFDerivOn_iff]
    intro r
    refine (by simpa using ((h.congr_ae (ι.coeFn_compLpL x).symm).congr_ae_deriv
      hg).smul_direction r : HasWeakLineDerivOn _ _ _ _ r).congr_ae_deriv ?_
    filter_upwards [lift.coeFn_compLp g] with s hs
    simp [lift, hs]
  refine ⟨mk _ x _ hD, prev_mk _ _ _ _, ?_⟩
  rw [stationaryEvolutionOperator_eq_iff_hasWeakLineDerivOn, prev_mk]
  exact h

/-- **Intertwining stationary evolution operators with trajectory operators.** If `T : H →L[ℝ] G`
intertwines `A` with `B : G →L[ℝ] G`, meaning `T (A x) = B (T (ι x))` for all `x ∈ D`, and `BL` is
an `L∞` class of the constant operator `B`, then projecting along `T` intertwines
`stationaryEvolutionOperator ι A` with `trajectoryOperator BL`. -/
theorem trajectoryOperator_postcompBaseL
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (ι A : D →L[ℝ] H) (T : H →L[ℝ] G) (B : G →L[ℝ] G)
    (hinter : ∀ x : D, T (A x) = B (T (ι x)))
    (BL : Lp (G →L[ℝ] G) ∞ (mu.restrict Omega))
    (hBL : BL =ᵐ[mu.restrict Omega] fun _ ↦ B)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    trajectoryOperator BL (postcompBaseL (ι.compLpL p (mu.restrict Omega)) T u) =
      T.compLp (stationaryEvolutionOperator ι A u) := by
  apply Lp.ext
  filter_upwards [trajectoryOperator_apply_ae BL (postcompBaseL _ T u),
    (ContinuousLinearMap.compL ℝ ℝ H G T).coeFn_compLp (weakFDeriv _ u),
    T.coeFn_compLp (ι.compLpL p (mu.restrict Omega) (prev _ u)),
    ι.coeFn_compLpL (prev _ u),
    hBL,
    T.coeFn_compLp (stationaryEvolutionOperator ι A u),
    stationaryEvolutionOperator_apply_ae ι A u] with s hT hw hTι hι hBLs hTS hS
  rw [hT, weakFDeriv_postcompBaseL, prev_postcompBaseL, hw, hTι, hι, hBLs, hTS, hS, map_add,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hinter]

end Stationary

/-! ### Classical derivative agreement and time reflection under additive Haar measure -/

section AddHaar

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure] {Omega : Opens ℝ}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- For a representative `v : ℝ → D` whose image `ι ∘ v` is differentiable on `Omega` with locally
integrable derivative, `stationaryEvolutionOperator ι A u` agrees almost everywhere with the
classical expression `(ι ∘ v)' + A ∘ v`. -/
theorem stationaryEvolutionOperator_apply_ae_eq_deriv_add (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)))
    {v : ℝ → D}
    (hv : prev (ι.compLpL p (mu.restrict Omega)) u =ᵐ[mu.restrict Omega] v)
    (hdv : LocallyIntegrableOn (fderiv ℝ (ι ∘ v)) Omega mu)
    (hvd : ∀ s ∈ (Omega : Set ℝ), DifferentiableAt ℝ (ι ∘ v) s) :
    stationaryEvolutionOperator ι A u =ᵐ[mu.restrict Omega] fun s ↦ deriv (ι ∘ v) s + A (v s) := by
  have hweak : HasWeakFDerivOn mu Omega (ι ∘ v)
      (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u) := by
    refine (hasWeakFDerivOn_base_prev _ u).congr_ae ?_
    filter_upwards [ι.coeFn_compLpL (prev _ u), hv] with s hs hvs
    rw [hs, Function.comp_apply, hvs]
  filter_upwards [stationaryEvolutionOperator_apply_ae ι A u,
    hweak.ae_eq_fderiv hdv hvd, hv] with s hs hd hvs
  rw [hs, hd, hvs, fderiv_apply_one_eq_deriv]

end AddHaar

/-! ### Time reflection on the full line -/

section Reflect

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

private theorem hasWeakFDerivOn_reflect (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    HasWeakFDerivOn mu ⊤
      (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (negLpₗᵢ ℝ (prev _ u)))
      ((-negLpₗᵢ ℝ (weakFDeriv _ u) :
        Lp (ℝ →L[ℝ] H) p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) : ℝ → ℝ →L[ℝ] H) := by
  have h1 := (hasWeakFDerivOn_base_prev (ι.compLpL p _) u).comp_continuousLinearEquiv
    (U := ⊤) (ContinuousLinearEquiv.neg ℝ) (Measure.measurePreserving_neg mu)
    (Set.mapsTo_univ _ _)
  refine (h1.congr_ae ?_).congr_ae_deriv ?_
  · have hcomp := (Measure.measurePreserving_neg
        (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))).quasiMeasurePreserving.ae_eq_comp
      (ι.coeFn_compLpL (prev (ι.compLpL p _) u))
    filter_upwards [hcomp, ι.coeFn_compLpL (negLpₗᵢ ℝ (prev _ u)),
      coeFn_negLpₗᵢ (𝕜 := ℝ) (prev _ u)] with s hιneg hιref href
    simp only [Function.comp_apply, ContinuousLinearEquiv.neg_apply] at hιneg ⊢
    rw [hιneg, hιref, href]
  · filter_upwards [Lp.coeFn_neg (negLpₗᵢ ℝ (weakFDeriv _ u)),
      coeFn_negLpₗᵢ (𝕜 := ℝ) (weakFDeriv _ u)] with s hneg href
    ext
    simp only [hneg, Pi.neg_apply, neg_apply, href, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.neg_apply, map_neg]

/-- Time reflection `s ↦ u(-s)` as an involutive linear isometry of the evolution Sobolev space
on `ℝ`. -/
def reflectEvolutionEquiv (ι : D →L[ℝ] H) :
    WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict Set.univ)) ≃ₗᵢ[ℝ]
      WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict Set.univ)) where
  toFun u := mk _ (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u))
    (hasWeakFDerivOn_reflect ι u)
  invFun u := mk _ (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u))
    (hasWeakFDerivOn_reflect ι u)
  left_inv u := ext (by simp only [prev_mk, negLpₗᵢ_negLpₗᵢ])
  right_inv u := ext (by simp only [prev_mk, negLpₗᵢ_negLpₗᵢ])
  map_add' u v := ext (by simp only [prev_mk, prev_add, map_add])
  map_smul' c u := ext (by simp only [prev_mk, prev_smul, map_smul, RingHom.id_apply])
  norm_map' u := by
    have hsq : ‖mk (ι.compLpL p (mu.restrict Set.univ))
        (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u))
        (hasWeakFDerivOn_reflect ι u)‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq,
        norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ u,
        prev_mk, weakFDeriv_mk, norm_neg, (negLpₗᵢ ℝ).norm_map, (negLpₗᵢ ℝ).norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Time reflection acts on the `Lᵖ(ℝ; D)` path by `TauCeti.negLpₗᵢ`. -/
@[simp]
theorem prev_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict Set.univ))) :
    prev (Omega := ⊤) (ι.compLpL p (mu.restrict Set.univ)) (reflectEvolutionEquiv ι u) =
      negLpₗᵢ ℝ (prev (Omega := ⊤) (ι.compLpL p (mu.restrict Set.univ)) u) :=
  prev_mk _ _ _ _

/-- Time reflection negates and reflects the weak derivative via `TauCeti.negLpₗᵢ`. -/
@[simp]
theorem weakFDeriv_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict Set.univ))) :
    weakFDeriv (Omega := ⊤) (ι.compLpL p (mu.restrict Set.univ)) (reflectEvolutionEquiv ι u) =
      -negLpₗᵢ ℝ (weakFDeriv (Omega := ⊤) (ι.compLpL p (mu.restrict Set.univ)) u) :=
  weakFDeriv_mk _ _ _ _

/-- Time reflection is involutive. -/
@[simp]
theorem reflectEvolutionEquiv_apply_self (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict Set.univ))) :
    reflectEvolutionEquiv ι (reflectEvolutionEquiv ι u) = u :=
  ext (by simp only [prev_reflectEvolutionEquiv, negLpₗᵢ_negLpₗᵢ])

/-- Time reflection is its own inverse. -/
@[simp]
theorem reflectEvolutionEquiv_symm (ι : D →L[ℝ] H) :
    (reflectEvolutionEquiv (mu := mu) (p := p) ι).symm =
      reflectEvolutionEquiv (mu := mu) (p := p) ι :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

/-- Composing time reflection with itself is the identity equivalence. -/
@[simp]
theorem reflectEvolutionEquiv_trans_self (ι : D →L[ℝ] H) :
    (reflectEvolutionEquiv (mu := mu) (p := p) ι).trans
      (reflectEvolutionEquiv (mu := mu) (p := p) ι) = LinearIsometryEquiv.refl ℝ _ :=
  LinearIsometryEquiv.ext fun u ↦ reflectEvolutionEquiv_apply_self ι u

/-- Time reflection precomposes the `Lᵖ(ℝ; D)` path with negation almost everywhere. -/
theorem prev_reflectEvolutionEquiv_ae (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    prev (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (reflectEvolutionEquiv ι u) =ᵐ[mu.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ prev (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u (-s) := by
  have h : prev (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) (reflectEvolutionEquiv ι u) =
      negLpₗᵢ ℝ (prev (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) :=
    prev_reflectEvolutionEquiv ι u
  rw [h]
  exact coeFn_negLpₗᵢ (𝕜 := ℝ) (prev _ u)

/-- Time reflection negates and reflects the weak derivative almost everywhere. -/
theorem weakFDeriv_reflectEvolutionEquiv_ae (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (reflectEvolutionEquiv ι u) =ᵐ[mu.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u (-s) := by
  have h : weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (reflectEvolutionEquiv ι u) =
      -negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) :=
    weakFDeriv_reflectEvolutionEquiv ι u
  rw [h]
  filter_upwards [Lp.coeFn_neg (negLpₗᵢ ℝ (weakFDeriv _ u)),
    coeFn_negLpₗᵢ (𝕜 := ℝ) (weakFDeriv _ u)] with s hneg href
  rw [hneg, Pi.neg_apply, href]

/-- Pointwise almost-everywhere conjugation of `∂s - A` and `∂s + A` under time reflection. -/
theorem stationaryEvolutionOperator_neg_reflectEvolutionEquiv_ae (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    stationaryEvolutionOperator (mu := mu) (p := p) ι (-A) (reflectEvolutionEquiv ι u)
      =ᵐ[mu.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -(stationaryEvolutionOperator (mu := mu) (p := p) ι A u) (-s) := by
  have hSneg := (Measure.measurePreserving_neg
      (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))).quasiMeasurePreserving.ae_eq_comp
    (stationaryEvolutionOperator_apply_ae (mu := mu) (p := p) ι A u)
  filter_upwards [stationaryEvolutionOperator_apply_ae (mu := mu) (p := p) ι (-A)
      (reflectEvolutionEquiv (mu := mu) (p := p) ι u),
    weakFDeriv_reflectEvolutionEquiv_ae (mu := mu) (p := p) ι u,
    prev_reflectEvolutionEquiv_ae (mu := mu) (p := p) ι u,
    hSneg] with s h1 h2 h3 h4
  simp only [Function.comp_apply] at h4
  rw [h1, h2, h3, neg_apply, neg_apply, h4]
  abel

/-- Time reflection conjugates `∂s - A` to `-(∂s + A)` on `ℝ`:
`∂s - A = -(negLpₗᵢ ∘ (∂s + A) ∘ reflectEvolutionEquiv)`. -/
theorem stationaryEvolutionOperator_neg_eq (ι A : D →L[ℝ] H) :
    stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A) =
      -((negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) :
          Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] _).comp
        ((stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).comp
          (reflectEvolutionEquiv (mu := mu) (p := p) ι :
            WeakDerivStep mu ⊤ p
              (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _))) := by
  ext1 u
  set v := reflectEvolutionEquiv (mu := mu) (p := p) ι u
  have hv : reflectEvolutionEquiv (mu := mu) (p := p) ι v = u :=
    reflectEvolutionEquiv_apply_self (mu := mu) (p := p) ι u
  have hval : (-((negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) :
        Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] _).comp
      ((stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).comp
        (reflectEvolutionEquiv (mu := mu) (p := p) ι :
          WeakDerivStep mu ⊤ p
            (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _)))) u =
      -negLpₗᵢ ℝ (stationaryEvolutionOperator (mu := mu) (p := p) ι A v) := rfl
  rw [hval]
  conv_lhs => rw [← hv]
  apply Lp.ext
  filter_upwards [stationaryEvolutionOperator_neg_reflectEvolutionEquiv_ae
      (mu := mu) (p := p) ι A v,
    Lp.coeFn_neg (negLpₗᵢ ℝ (stationaryEvolutionOperator (mu := mu) (p := p) ι A v)),
    coeFn_negLpₗᵢ (𝕜 := ℝ)
      (stationaryEvolutionOperator (mu := mu) (p := p) ι A v)] with s h1 h2 h3
  rw [h1, h2, Pi.neg_apply, h3]

/-- `∂s - A` and `∂s + A` have the same operator norm on `ℝ`. -/
@[simp]
theorem norm_stationaryEvolutionOperator_neg (ι A : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)‖ =
      ‖stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A‖ := by
  rw [stationaryEvolutionOperator_neg_eq, ContinuousLinearMap.opNorm_neg,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- `∂s - A` is invertible on `ℝ` if and only if `∂s + A` is invertible on `ℝ`. -/
@[simp]
theorem isInvertible_stationaryEvolutionOperator_neg_iff (ι A : D →L[ℝ] H) :
    (stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)).IsInvertible ↔
      (stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).IsInvertible := by
  let eL := negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ))
  let eR := reflectEvolutionEquiv (mu := mu) (p := p) ι
  have hL : (eL : Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] _) =
      eL.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext1 f; rfl
  have hR : (eR : WeakDerivStep mu ⊤ p
        (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _) =
      eR.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext1 u; rfl
  rw [stationaryEvolutionOperator_neg_eq, ← neg_one_smul ℝ,
    ContinuousLinearMap.isInvertible_smul_iff (by norm_num : (-1 : ℝ) ≠ 0), hL, hR,
    ContinuousLinearMap.isInvertible_equiv_comp, ContinuousLinearMap.isInvertible_comp_equiv]

/-- Time reflection conjugates `(∂s - A)⁻¹` to `-(∂s + A)⁻¹` on `ℝ`. -/
theorem inverse_stationaryEvolutionOperator_neg (ι A : D →L[ℝ] H) :
    (stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)).inverse =
      -((reflectEvolutionEquiv (mu := mu) (p := p) ι :
          WeakDerivStep mu ⊤ p
            (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _).comp
        ((stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).inverse.comp
          (negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) :
            Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] _))) := by
  let eL := negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ))
  let eR := reflectEvolutionEquiv (mu := mu) (p := p) ι
  let eL' : Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) ≃L[ℝ]
      Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) := eL.toContinuousLinearEquiv
  let eR' : WeakDerivStep mu ⊤ p
        (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) ≃L[ℝ]
      WeakDerivStep mu ⊤ p
        (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) := eR.toContinuousLinearEquiv
  let T := stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A
  have h1 : (stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)).inverse =
      (-(eL'.toContinuousLinearMap.comp (T.comp eR'.toContinuousLinearMap))).inverse :=
    congrArg ContinuousLinearMap.inverse <|
      (stationaryEvolutionOperator_neg_eq ι A).trans <|
        congrArg Neg.neg (ContinuousLinearMap.ext fun _ ↦ rfl)
  have h2 : (-(eL'.toContinuousLinearMap.comp (T.comp eR'.toContinuousLinearMap))).inverse =
      -(eR'.toContinuousLinearMap.comp (T.inverse.comp eL'.toContinuousLinearMap)) := by
    have hconj : ∀ {M : Type _} {M₂ : Type _}
        [TopologicalSpace M] [AddCommGroup M] [Module ℝ M] [IsTopologicalAddGroup M]
        [TopologicalSpace M₂] [AddCommGroup M₂] [Module ℝ M₂] [IsTopologicalAddGroup M₂]
        [ContinuousConstSMul ℝ M₂]
        (eL : M₂ ≃L[ℝ] M₂) (_ : eL.symm = eL) (eR : M ≃L[ℝ] M) (_ : eR.symm = eR)
        (T : M →L[ℝ] M₂),
        (-(eL.toContinuousLinearMap.comp (T.comp eR.toContinuousLinearMap))).inverse =
          -(eR.toContinuousLinearMap.comp (T.inverse.comp eL.toContinuousLinearMap)) := by
      intro M M₂ _ _ _ _ _ _ _ _ _ eL heL eR heR T
      ext1 f
      rw [← neg_one_smul ℝ, ContinuousLinearMap.inverse_smul_apply (by norm_num : (-1 : ℝ) ≠ 0),
        ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv]
      simp [heL, heR]
    exact hconj eL'
      (eL.toContinuousLinearEquiv_symm.symm.trans
        (congrArg LinearIsometryEquiv.toContinuousLinearEquiv negLpₗᵢ_symm))
      eR'
      (eR.toContinuousLinearEquiv_symm.symm.trans
        (congrArg LinearIsometryEquiv.toContinuousLinearEquiv (reflectEvolutionEquiv_symm ι)))
      T
  exact h1.trans <| h2.trans <| congrArg Neg.neg (ContinuousLinearMap.ext fun _ ↦ rfl)

/-- `(∂s - A)⁻¹` and `(∂s + A)⁻¹` have the same operator norm on `ℝ`. -/
@[simp]
theorem norm_inverse_stationaryEvolutionOperator_neg (ι A : D →L[ℝ] H) :
    ‖(stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)).inverse‖ =
      ‖(stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).inverse‖ := by
  rw [inverse_stationaryEvolutionOperator_neg, ContinuousLinearMap.opNorm_neg,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end Reflect

end TauCeti.WeakDerivStep
