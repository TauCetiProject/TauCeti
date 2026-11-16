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

Given `ι, A : D →L[ℝ] H` between real normed spaces, the evolution Sobolev space
`Lᵖ(Ω; D) ∩ W^{1,p}(Ω; H)` is realized by the weak-derivative graph
`WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))`, and
`TauCeti.WeakDerivStep.stationaryEvolutionOperator ι A` realizes `u ↦ (ι u)' + A u` as a bounded
linear map into `Lᵖ(Ω; H)`.

## Main declarations

* `TauCeti.WeakDerivStep.stationaryEvolutionOperator`: `u ↦ (ι u)' + A u`, with operator norm
  bound `1 + ‖A‖`, `1`-Lipschitz continuity in `A`, derivative bound
  `‖(ι u)'‖ ≤ ‖(ι u)' + A u‖ + ‖A‖ ‖u‖`, weak-ODE equivalence
  (`stationaryEvolutionOperator_eq_iff_hasWeakLineDerivOn`,
  `exists_prev_eq_and_stationaryEvolutionOperator_eq_of_hasWeakLineDerivOn`), and classical
  derivative agreement (`stationaryEvolutionOperator_apply_ae_eq_deriv_add`).
* `TauCeti.WeakDerivStep.trajectoryOperator_postcompBaseL`: intertwining of
  `stationaryEvolutionOperator` with `trajectoryOperator` under `postcompBaseL`.
* `TauCeti.WeakDerivStep.reflectEvolutionEquiv`,
  `TauCeti.WeakDerivStep.stationaryEvolutionOperator_neg_eq`,
  `TauCeti.WeakDerivStep.inverse_stationaryEvolutionOperator_neg`,
  `TauCeti.WeakDerivStep.isInvertible_stationaryEvolutionOperator_neg_iff`,
  `TauCeti.WeakDerivStep.norm_inverse_stationaryEvolutionOperator_neg`: time reflection `s ↦ u(-s)`
  on `ℝ` under any additive Haar measure, conjugating `∂s - A` to `-(∂s + A)` and preserving norm,
  invertibility, and inverse norm.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 2.
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
    (A.compLpL p (mu.restrict Omega)).comp (prevL (ι.compLpL p (mu.restrict Omega)))

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
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ u)) (A.compLp (prev _ u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLp (weakFDeriv _ u),
    A.coeFn_compLp (prev _ u)] with s hs hd hA
  exact hs.trans (by simp only [Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply])

/-- Subtracting two stationary evolution operators cancels the derivative term. -/
theorem stationaryEvolutionOperator_sub (ι A B : D →L[ℝ] H) :
    stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      stationaryEvolutionOperator ι B =
      ((A - B).compLpL p (mu.restrict Omega)).comp (prevL (ι.compLpL p (mu.restrict Omega))) := by
  simp only [stationaryEvolutionOperator, ContinuousLinearMap.sub_compLpL,
    ContinuousLinearMap.sub_comp]
  abel

/-- The operator norm of `stationaryEvolutionOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_stationaryEvolutionOperator_le (ι A : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  rw [stationaryEvolutionOperator_apply]
  have hd : ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ u)‖ ≤ ‖u‖ := by
    rw [ContinuousLinearMap.norm_compLp_apply_one]; exact norm_weakFDeriv_le _ u
  have hA : ‖A.compLp (prev _ u)‖ ≤ ‖A‖ * ‖u‖ :=
    (A.norm_compLp_le _).trans (by gcongr; exact norm_prev_le _ u)
  linarith [norm_add_le ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ u))
    (A.compLp (prev _ u))]

/-- Perturbing `A` changes `stationaryEvolutionOperator ι A` by at most `‖A - B‖` in operator
norm. -/
theorem norm_stationaryEvolutionOperator_sub_le (ι A B : D →L[ℝ] H) :
    ‖stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      stationaryEvolutionOperator ι B‖ ≤ ‖A - B‖ := by
  rw [stationaryEvolutionOperator_sub]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
  simpa only [ContinuousLinearMap.comp_apply, prevL_apply, ContinuousLinearMap.compLpL_apply] using
    ((A - B).norm_compLp_le _).trans (by gcongr; exact norm_prev_le _ u)

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
  rw [← ContinuousLinearMap.norm_compLp_apply_one,
    eq_sub_of_add_eq (stationaryEvolutionOperator_apply ι A u).symm]
  exact (norm_sub_le _ _).trans (by gcongr; exact A.norm_compLp_le _)

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
  refine ⟨fun h ↦ hd.congr_ae_deriv ?_, fun h ↦ Lp.ext ?_⟩
  · filter_upwards [h ▸ stationaryEvolutionOperator_apply_ae ι A u] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · filter_upwards [stationaryEvolutionOperator_apply_ae ι A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd', sub_add_cancel]

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
    filter_upwards [lift.coeFn_compLp g] with s hs using by simp [lift, hs]
  refine ⟨mk _ x _ hD, prev_mk _ _ _ _, ?_⟩
  rw [stationaryEvolutionOperator_eq_iff_hasWeakLineDerivOn, prev_mk]; exact h

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
    ι.coeFn_compLpL (prev _ u), hBL, T.coeFn_compLp (stationaryEvolutionOperator ι A u),
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
  have hweak : HasWeakFDerivOn mu Omega (ι ∘ v) (weakFDeriv _ u) :=
    (hasWeakFDerivOn_base_prev _ u).congr_ae <| by
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
      (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) (negLpₗᵢ ℝ (prev _ u)))
      ((-negLpₗᵢ ℝ (weakFDeriv _ u) :
        Lp (ℝ →L[ℝ] H) p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) : ℝ → ℝ →L[ℝ] H) := by
  have h1 := (hasWeakFDerivOn_base_prev (ι.compLpL p _) u).comp_continuousLinearEquiv
    (U := ⊤) (ContinuousLinearEquiv.neg ℝ) (Measure.measurePreserving_neg mu) (Set.mapsTo_univ _ _)
  refine (h1.congr_ae ?_).congr_ae_deriv ?_
  · have hcomp :=
      (Measure.measurePreserving_neg (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))).quasiMeasurePreserving
        |>.ae_eq_comp (ι.coeFn_compLpL (prev (ι.compLpL p _) u))
    filter_upwards [hcomp, ι.coeFn_compLpL (negLpₗᵢ ℝ (prev _ u)),
      coeFn_negLpₗᵢ (𝕜 := ℝ) (prev _ u)] with s hιneg hιref href
    simpa only [Function.comp_apply, ContinuousLinearEquiv.neg_apply, hιref, href] using hιneg
  · filter_upwards [Lp.coeFn_neg (negLpₗᵢ ℝ (weakFDeriv _ u)),
      coeFn_negLpₗᵢ (𝕜 := ℝ) (weakFDeriv _ u)] with s hneg href
    rw [hneg, Pi.neg_apply, href]
    ext
    simp

/-- Time reflection `s ↦ u(-s)` as an involutive linear isometry of the evolution Sobolev space
on `ℝ`. -/
def reflectEvolutionEquiv (ι : D →L[ℝ] H) :
    WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) ≃ₗᵢ[ℝ]
      WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) where
  toFun u := mk _ (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u)) (hasWeakFDerivOn_reflect ι u)
  invFun u :=
    mk _ (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u)) (hasWeakFDerivOn_reflect ι u)
  left_inv u := ext (by simp only [prev_mk, negLpₗᵢ_negLpₗᵢ])
  right_inv u := ext (by simp only [prev_mk, negLpₗᵢ_negLpₗᵢ])
  map_add' u v := ext (by simp only [prev_mk, prev_add, map_add])
  map_smul' c u := ext (by simp only [prev_mk, prev_smul, map_smul, RingHom.id_apply])
  norm_map' u := by
    have hsq : ‖mk (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))
        (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u))
        (hasWeakFDerivOn_reflect ι u)‖ ^ 2 = ‖u‖ ^ 2 := by
      calc ‖mk (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))
              (negLpₗᵢ ℝ (prev _ u)) (-negLpₗᵢ ℝ (weakFDeriv _ u))
              (hasWeakFDerivOn_reflect ι u)‖ ^ 2
          = ‖negLpₗᵢ ℝ (prev _ u)‖ ^ 2 + ‖-negLpₗᵢ ℝ (weakFDeriv _ u)‖ ^ 2 := by
            rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, prev_mk, weakFDeriv_mk]
        _ = ‖prev _ u‖ ^ 2 + ‖weakFDeriv _ u‖ ^ 2 := by
            rw [norm_neg, (negLpₗᵢ ℝ).norm_map, (negLpₗᵢ ℝ).norm_map]
        _ = ‖u‖ ^ 2 := (norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ u).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Time reflection acts on the `Lᵖ(ℝ; D)` path by `TauCeti.negLpₗᵢ`. -/
theorem prev_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    prev (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) (reflectEvolutionEquiv ι u) =
      negLpₗᵢ ℝ (prev (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) :=
  prev_mk _ _ _ _

/-- Time reflection negates and reflects the weak derivative via `TauCeti.negLpₗᵢ`. -/
theorem weakFDeriv_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) (reflectEvolutionEquiv ι u) =
      -negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) :=
  weakFDeriv_mk _ _ _ _

/-- Time reflection is involutive. -/
theorem reflectEvolutionEquiv_apply_self (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
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
  LinearIsometryEquiv.ext (reflectEvolutionEquiv_apply_self ι)

/-- Time reflection conjugates `∂s - A` to `-(∂s + A)` on `ℝ`:
`∂s - A = -(negLpₗᵢ ∘ (∂s + A) ∘ reflectEvolutionEquiv)`. -/
theorem stationaryEvolutionOperator_neg_eq (ι A : D →L[ℝ] H) :
    stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A) =
      -((negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) :
          Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] _).comp
        ((stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).comp
          (reflectEvolutionEquiv (mu := mu) (p := p) ι :
            WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _))) :=
  by
  ext1 u
  change _ = -(negLpₗᵢ ℝ (stationaryEvolutionOperator ι A (reflectEvolutionEquiv ι u)))
  have hneg : (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
      (-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)) =
      -(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
        (negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)) :=
    map_neg ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p _) _
  rw [stationaryEvolutionOperator_apply, stationaryEvolutionOperator_apply,
    weakFDeriv_reflectEvolutionEquiv, prev_reflectEvolutionEquiv,
    ContinuousLinearMap.neg_compLp, map_add, hneg,
    compLp_negLpₗᵢ, compLp_negLpₗᵢ, map_neg, negLpₗᵢ_negLpₗᵢ, negLpₗᵢ_negLpₗᵢ]
  abel

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
      eL.toContinuousLinearEquiv.toContinuousLinearMap := ContinuousLinearMap.ext fun _ ↦ rfl
  have hR :
      (eR : WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _) =
      eR.toContinuousLinearEquiv.toContinuousLinearMap := ContinuousLinearMap.ext fun _ ↦ rfl
  rw [stationaryEvolutionOperator_neg_eq, ← neg_one_smul ℝ,
    ContinuousLinearMap.isInvertible_smul_iff (by norm_num : (-1 : ℝ) ≠ 0), hL, hR,
    ContinuousLinearMap.isInvertible_equiv_comp, ContinuousLinearMap.isInvertible_comp_equiv]

private theorem inverse_neg_comp_equiv {X Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [IsTopologicalAddGroup X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
    [ContinuousConstSMul ℝ Y]
    (eL : Y ≃L[ℝ] Y) (L : X →L[ℝ] Y) (eR : X ≃L[ℝ] X) (heL : eL.symm = eL) (heR : eR.symm = eR) :
    (-(eL.toContinuousLinearMap.comp (L.comp eR.toContinuousLinearMap))).inverse =
      -(eR.toContinuousLinearMap.comp (L.inverse.comp eL.toContinuousLinearMap)) := by
  ext1 f
  rw [← neg_one_smul ℝ, ContinuousLinearMap.inverse_smul_apply (by norm_num : (-1 : ℝ) ≠ 0),
    ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv]
  simp [heL, heR]

/-- Time reflection conjugates `(∂s - A)⁻¹` to `-(∂s + A)⁻¹` on `ℝ`. -/
theorem inverse_stationaryEvolutionOperator_neg (ι A : D →L[ℝ] H) :
    (stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)).inverse =
      -((reflectEvolutionEquiv (mu := mu) (p := p) ι :
          WeakDerivStep mu ⊤ p (ι.compLpL p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ] _).comp
        ((stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).inverse.comp
          (negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) :
            Lp H p (mu.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] _))) := by
  let eL :=
    (negLpₗᵢ ℝ (E := H) (p := p) (μ := mu.restrict ((⊤ : Opens ℝ) : Set ℝ))).toContinuousLinearEquiv
  let eR := (reflectEvolutionEquiv (mu := mu) (p := p) ι).toContinuousLinearEquiv
  have heL : eL.symm = eL :=
    ContinuousLinearEquiv.ext (funext fun f ↦ eL.symm_apply_eq.2 (negLpₗᵢ_negLpₗᵢ f).symm)
  have heR : eR.symm = eR :=
    ContinuousLinearEquiv.ext (funext fun u ↦ eR.symm_apply_eq.2
      (reflectEvolutionEquiv_apply_self ι u).symm)
  have h1 : (stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι (-A)).inverse =
      (-(eL.toContinuousLinearMap.comp
        ((stationaryEvolutionOperator (mu := mu) (Omega := ⊤) (p := p) ι A).comp
          eR.toContinuousLinearMap))).inverse :=
    congrArg ContinuousLinearMap.inverse <| (stationaryEvolutionOperator_neg_eq ι A).trans <|
      congrArg Neg.neg (ContinuousLinearMap.ext fun _ ↦ rfl)
  exact h1.trans <| (inverse_neg_comp_equiv eL _ eR heL heR).trans <|
    congrArg Neg.neg (ContinuousLinearMap.ext fun _ ↦ rfl)

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
