/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.PolynomialVector
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.MvPolynomial.L1Norm
import TauCeti.Analysis.Normed.Group.Pi

/-!
# Moments on the Fock space and approximation by polynomial vectors

For a Fock vector `v ∈ 𝓕(ε)` and `N ∈ ℕ` the *moment* `M_N(v) = ∫ (1 + ‖y‖)^N |v(y)| dμ(y)`, with
`‖y‖` the sup norm on `ι → ℂ`, is a weighted `L¹` norm with values in `[0, ∞]`; `v` has *finite
moments* if all of them are finite. They play the role of Schwartz seminorms, and the vectors with
finite moments form a subspace stable under the Heisenberg operators and the Weil representation.

The moments grow at most polynomially under the Heisenberg operators and the Weil representation,
satisfy Minkowski's inequality for Bochner integrals, and are finite on polynomial vectors. A
vector with finite moments is approximated by polynomial vectors in all moments at once: the
superposition `v = ∫ v(y) ϱ(y) e dy` is truncated in the exponential series of the reproducing
kernel `e(x) e(y) exp (∑ i, conj (ζ(y) i) ζ(x) i)`, and dominated convergence applies. Finally a
continuous linear form that is bounded by its differences under Heisenberg translations of size at
most `t` is at most `C ‖ℓ‖ t^N` times the `N`-th moment, by Taylor expansion along the Heisenberg
derivatives of polynomial vectors and induction on `N`.

## Main definitions

* `TauCeti.Fock.moment`, `TauCeti.Fock.HasFiniteMoments`: `M_N` and finiteness of all moments.

## Main results

* `TauCeti.Fock.moment_zero`, `TauCeti.Fock.moment_add_le`, `TauCeti.Fock.moment_heisenbergRep_le`,
  `TauCeti.Fock.moment_weilRep_le`, `TauCeti.Fock.moment_integral_le`: `M_0` is the norm, the
  moments are subadditive, grow at most polynomially under the Heisenberg operators and the Weil
  representation, and satisfy Minkowski's inequality.
* `TauCeti.Fock.hasFiniteMoments_polyVector`, `TauCeti.Fock.HasFiniteMoments.add`,
  `TauCeti.Fock.HasFiniteMoments.smul`, `TauCeti.Fock.HasFiniteMoments.heisenbergRep`,
  `TauCeti.Fock.HasFiniteMoments.weilRep`, `TauCeti.Fock.hasFiniteMoments_integral`: polynomial
  vectors have finite moments, and so do sums, multiples, translates, Weil transforms and
  integrals of vectors with finite moments.
* `TauCeti.Fock.exists_tendsto_moment`: approximation by polynomial vectors in all moments.
* `TauCeti.Fock.enorm_le_mul_moment`, `TauCeti.Fock.exists_enorm_le_mul_moment_of_norm_sub_le`:
  bounds for linear forms by moments, the second for forms controlled by short Heisenberg
  differences.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Weil/Fock/WeightedNorms.lean` (`New.Fock.fockMoment`,
`New.Exchange.IsSchwartzVector`, `New.Fock.fockMoment_zero`,
`New.Fock.fockMoment_realHeisenbergOp_le`, `New.Fock.enorm_le_mul_fockMoment`,
`New.Fock.fockMoment_polyVector_ne_top`, `New.Fock.isSchwartzVector_vacVector`,
`New.Fock.fockMoment_integral_le`, `New.Fock.isSchwartzVector_integral`,
`New.Fock.exists_tendsto_fockMoment`, `New.Fock.fockMoment_realWeil_le`,
`New.Fock.hasDerivAt_realHeisenbergOp_realHeisenbergOp`,
`New.Fock.exists_norm_realHeisenbergOp_polyVector_le`,
`New.Fock.exists_enorm_le_mul_fockMoment_of_norm_sub_le`).

## References

* G. B. Folland, *Harmonic analysis in phase space*, Ann. of Math. Stud. 122 (1989), Chapter 1.
* H. Reiter, *Metaplectic groups and Segal algebras*, Lecture Notes in Math. 1382 (1989).
-/

public noncomputable section

open MeasureTheory Complex Finset Filter Matrix
open scoped ComplexConjugate ENNReal

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### Moments -/

/-- The *moment* `M_N(v) = ∫ (1 + ‖y‖) ^ N |v(y)| dμ(y) ∈ [0, ∞]` of a Fock vector, for the sup
norm `‖y‖` on `ι → ℂ` and `μ = π^{-|ι|} dy`. -/
def moment (N : ℕ) (v : FockSpace ε) : ℝ≥0∞ := ∫⁻ y, (1 + ‖y‖ₑ) ^ N * ‖v y‖ₑ ∂measure ι

/-- A Fock vector *has finite moments* if `M_N(v) < ∞` for every `N`. -/
def HasFiniteMoments (v : FockSpace ε) : Prop := ∀ N, moment N v ≠ ⊤

/-- The moment of order `0` is the norm: `M_0(v) = ‖v‖`. -/
theorem moment_zero (v : FockSpace ε) : moment 0 v = ‖v‖ₑ := by
  rw [moment, ← ofReal_norm, ReproducingModel.norm_eq_integral_norm,
    ofReal_integral_norm_eq_lintegral_eNorm v.integrable]
  simp

theorem moment_smul (N : ℕ) (c : ℂ) (v : FockSpace ε) : moment N (c • v) = ‖c‖ₑ * moment N v := by
  simp [moment, ← lintegral_const_mul', mul_left_comm]

/-- The moments are subadditive. -/
theorem moment_add_le (N : ℕ) (v w : FockSpace ε) : moment N (v + w) ≤ moment N v + moment N w := by
  have h_meas : Measurable fun y : ι → ℂ ↦ (1 + ‖y‖ₑ) ^ N * ‖v y‖ₑ :=
    ((measurable_id.eNorm.const_add 1).pow_const N).mul
      (ReproducingModel.continuous v).measurable.eNorm
  rw [moment, moment, moment, ← lintegral_add_left h_meas]
  refine lintegral_mono fun y ↦ ?_
  rw [ReproducingModel.add_apply, ← mul_add]
  gcongr
  exact eNorm_add_le _ _

theorem moment_eq_lintegral_ofReal (N : ℕ) (v : FockSpace ε) :
    moment N v = ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ N * ‖v y‖) ∂measure ι := by
  simp (disch := positivity) [moment, ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_add]

/-- A Heisenberg translation by `y` multiplies a moment by at most `(1 + ‖y‖) ^ N`. -/
theorem moment_heisenbergRep_le (N : ℕ) (y : ι → ℂ) (v : FockSpace ε) :
    moment N (ReproducingModel.heisenbergRep y v) ≤ (1 + ‖y‖ₑ) ^ N * moment N v := by
  have h_weight (x : ι → ℂ) : 1 + ‖x + y‖ₑ ≤ (1 + ‖y‖ₑ) * (1 + ‖x‖ₑ) :=
    calc 1 + ‖x + y‖ₑ ≤ 1 + (‖x‖ₑ + ‖y‖ₑ) := by gcongr; exact eNorm_add_le _ _
      _ ≤ (1 + ‖y‖ₑ) * (1 + ‖x‖ₑ) := by
        rw [add_mul, one_mul, mul_add, mul_one]
        calc 1 + (‖x‖ₑ + ‖y‖ₑ) = 1 + ‖y‖ₑ + ‖x‖ₑ := by ring
          _ ≤ 1 + ‖y‖ₑ + (‖x‖ₑ + ‖y‖ₑ * ‖x‖ₑ) := by gcongr; exact le_self_add
          _ = _ := by ring
  calc moment N (ReproducingModel.heisenbergRep y v)
      = ∫⁻ x, (1 + ‖x + y‖ₑ) ^ N * ‖v x‖ₑ ∂measure ι := by
        rw [moment, ← lintegral_add_right_eq_self _ y]
        simp [ReproducingModel.heisenbergRep_apply, HeisenbergDatum.enorm_apply]
    _ ≤ ∫⁻ x, ((1 + ‖y‖ₑ) * (1 + ‖x‖ₑ)) ^ N * ‖v x‖ₑ ∂measure ι := by
        gcongr with x
        exact h_weight x
    _ = (1 + ‖y‖ₑ) ^ N * moment N v := by
        simp [moment, mul_pow, mul_assoc, lintegral_const_mul']

/-- *Superposition bound*: a bounded linear form `ℓ` with `|ℓ(ϱ(z) e)| ≤ S (1 + ‖z‖) ^ N` for all
`z` satisfies `|ℓ(v)| ≤ S M_N(v)` for every Fock vector `v`. -/
theorem enorm_le_mul_moment {N : ℕ} {S : ℝ} {ℓ : FockSpace ε →L[ℂ] ℂ}
    (h_bound : ∀ z : ι → ℂ,
      ‖ℓ (ReproducingModel.heisenbergRep z ReproducingModel.vacuum)‖ ≤ S * (1 + ‖z‖) ^ N)
    (v : FockSpace ε) : ‖ℓ v‖ₑ ≤ ENNReal.ofReal S * moment N v := by
  calc ‖ℓ v‖ₑ ≤ ∫⁻ z, ENNReal.ofReal ‖v z‖ * ENNReal.ofReal (S * (1 + ‖z‖) ^ N) ∂measure ι := by
        rw [ReproducingModel.map_eq_integral v ℓ]
        refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun z ↦ ?_)
        rw [eNorm_smul, ← ofReal_norm, ← ofReal_norm]
        gcongr
        exact h_bound z
    _ = ENNReal.ofReal S * moment N v := by
        rw [moment_eq_lintegral_ofReal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hS : 0 ≤ S := (norm_nonneg _).trans (by simpa using h_bound 0)
        refine lintegral_congr fun z ↦ ?_
        rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hS]
        ring_nf

/-- Polynomial vectors have finite moments. -/
theorem hasFiniteMoments_polyVector (P : MvPolynomial ι ℂ) : HasFiniteMoments (polyVector ε P) := by
  intro N
  have h_int := (integrable_exp_mul_norm_gaussian (ι := ι) (N + P.totalDegree)).const_mul
    P.l1Norm
  rw [moment_eq_lintegral_ofReal, ← lt_top_iff_ne_top]
  refine lt_of_le_of_lt (lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal ?_) h_int.lintegral_lt_top
  have h_one : 1 + ‖y‖ ≤ Real.exp ‖y‖ := by linarith [Real.add_one_le_exp ‖y‖]
  have h_eval : ‖MvPolynomial.eval (holomorphicCoord ε y) P‖ ≤
      P.l1Norm * Real.exp ‖y‖ ^ P.totalDegree := by
    refine (P.norm_eval_le_l1Norm_mul_max_one_pow _).trans ?_
    rw [norm_holomorphicCoord]
    gcongr
    · exact P.l1Norm_nonneg
    · exact max_le (Real.one_le_exp (norm_nonneg _)) (by linarith)
  calc (1 + ‖y‖) ^ N * ‖polyVector ε P y‖
      = (1 + ‖y‖) ^ N * ‖MvPolynomial.eval (holomorphicCoord ε y) P‖ * ‖gaussian ι y‖ := by
        rw [polyVector_apply, norm_mul, mul_assoc]
    _ ≤ Real.exp ‖y‖ ^ N * (P.l1Norm * Real.exp ‖y‖ ^ P.totalDegree) * ‖gaussian ι y‖ := by
        gcongr
    _ = P.l1Norm * (Real.exp ((N + P.totalDegree) * ‖y‖) * ‖gaussian ι y‖) := by
        rw [add_mul, Real.exp_add, Real.exp_natCast_mul, Real.exp_natCast_mul]
        ring

/-- The vacuum has finite moments. -/
theorem hasFiniteMoments_vacuum : HasFiniteMoments (ReproducingModel.vacuum : FockSpace ε) := by
  simpa using hasFiniteMoments_polyVector (ε := ε) 1

theorem HasFiniteMoments.add {v w : FockSpace ε} (hv : HasFiniteMoments v)
    (hw : HasFiniteMoments w) : HasFiniteMoments (v + w) :=
  fun N ↦ ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hv N, hw N⟩) (moment_add_le N v w)

theorem HasFiniteMoments.smul {v : FockSpace ε} (hv : HasFiniteMoments v) (c : ℂ) :
    HasFiniteMoments (c • v) :=
  fun N ↦ by rw [moment_smul]; exact ENNReal.mul_ne_top eNorm_ne_top (hv N)

theorem HasFiniteMoments.neg {v : FockSpace ε} (hv : HasFiniteMoments v) :
    HasFiniteMoments (-v) := by
  simpa using hv.smul (-1)

theorem HasFiniteMoments.sub {v w : FockSpace ε} (hv : HasFiniteMoments v)
    (hw : HasFiniteMoments w) : HasFiniteMoments (v - w) := by
  simpa [sub_eq_add_neg] using hv.add hw.neg

/-- The Heisenberg operators preserve finite moments. -/
theorem HasFiniteMoments.heisenbergRep {v : FockSpace ε} (hv : HasFiniteMoments v) (y : ι → ℂ) :
    HasFiniteMoments (ReproducingModel.heisenbergRep y v) :=
  fun N ↦ ne_top_of_le_ne_top (ENNReal.mul_ne_top (by finiteness) (hv N))
    (moment_heisenbergRep_le N y v)

/-! ### Integrals of Fock vectors -/

section Integral

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite ν] {F : Y → FockSpace ε}

/-- The value of a Fock vector at `y` is jointly continuous in the vector and `y`. -/
private theorem continuous_apply_uncurry :
    Continuous fun p : (ι → ℂ) × FockSpace ε ↦ p.2 p.1 := by
  have h : Continuous fun p : (ι → ℂ) × FockSpace ε ↦
      ReproducingModel.evalCLM 0 (ReproducingModel.heisenbergRep (-p.1) p.2) :=
    (ReproducingModel.evalCLM 0).continuous.comp
      (HeisenbergDatum.Representation.continuous_apply_apply _ continuous_fst.neg continuous_snd)
  refine h.congr fun p ↦ ?_
  simp [HeisenbergDatum.apply_zero]

/-- *Minkowski's inequality* for moments: `M_N(∫ F) ≤ ∫ M_N(F)`. -/
theorem moment_integral_le (N : ℕ) :
    moment N (∫ t, F t ∂ν) ≤ ∫⁻ t, moment N (F t) ∂ν := by
  by_cases hF : Integrable F ν
  · have h_meas : AEStronglyMeasurable (fun p : Y × (ι → ℂ) ↦ F p.1 p.2)
        (ν.prod (measure ι)) :=
      continuous_apply_uncurry.comp_aestronglyMeasurable
        (measurable_snd.aestronglyMeasurable.prodMk
          (AEStronglyMeasurable.comp_fst hF.aestronglyMeasurable))
    have h_apply (y : ι → ℂ) : (∫ t, F t ∂ν) y = ∫ t, F t y ∂ν := by
      simpa using (ContinuousLinearMap.integral_comp_comm (ReproducingModel.evalCLM y) hF).symm
    calc moment N (∫ t, F t ∂ν)
        ≤ ∫⁻ y, (1 + ‖y‖ₑ) ^ N * ∫⁻ t, ‖F t y‖ₑ ∂ν ∂measure ι := by
          simp only [moment, h_apply]
          gcongr
          exact eNorm_integral_le_lintegral_eNorm _
      _ = ∫⁻ y, ∫⁻ t, (1 + ‖y‖ₑ) ^ N * ‖F t y‖ₑ ∂ν ∂measure ι :=
          lintegral_congr fun y ↦ (lintegral_const_mul' _ _ (by finiteness)).symm
      _ = ∫⁻ t, moment N (F t) ∂ν :=
          (lintegral_lintegral_swap (((measurable_snd.eNorm.const_add 1).pow_const
            N).aemeasurable.mul h_meas.aemeasurable.eNorm)).symm
  · simp [moment, integral_undef hF]

/-- A strongly measurable family of Fock vectors with `∫ M_N(F) < ∞` for every `N` is Bochner
integrable, and its integral has finite moments. -/
theorem hasFiniteMoments_integral (hF_meas : AEStronglyMeasurable F ν)
    (h_fin : ∀ N, ∫⁻ t, moment N (F t) ∂ν ≠ ⊤) :
    Integrable F ν ∧ HasFiniteMoments (∫ t, F t ∂ν) :=
  ⟨⟨hF_meas, hasFiniteIntegral_iff_eNorm.2 (by simpa [moment_zero] using (h_fin 0).lt_top)⟩,
    fun N ↦ ne_top_of_le_ne_top (h_fin N) (moment_integral_le N)⟩

end Integral

/-- If `M_{N'}(F y) ≤ C (1 + ‖y‖) ^ N`, then `∫ M_{N'}(v(y) F(y)) dμ(y) ≤ C M_N(v)`. -/
private theorem lintegral_moment_smul_le {N N' : ℕ} {C : ℝ≥0∞} {F : (ι → ℂ) → FockSpace ε}
    (h_growth : ∀ y, moment N' (F y) ≤ C * (1 + ‖y‖ₑ) ^ N) (v : FockSpace ε) :
    ∫⁻ y, moment N' (v y • F y) ∂measure ι ≤ C * moment N v := by
  calc ∫⁻ y, moment N' (v y • F y) ∂measure ι
      ≤ ∫⁻ y, ‖v y‖ₑ * (C * (1 + ‖y‖ₑ) ^ N) ∂measure ι := by
        simp only [moment_smul]
        gcongr with y
        exact h_growth y
    _ = C * moment N v := by
        have h_meas : Measurable fun y : ι → ℂ ↦ (1 + ‖y‖ₑ) ^ N * ‖v y‖ₑ :=
          ((measurable_id.eNorm.const_add 1).pow_const N).mul
            (ReproducingModel.continuous v).measurable.eNorm
        rw [moment, ← lintegral_const_mul C h_meas]
        exact lintegral_congr fun y ↦ by ring

/-! ### The Weil representation -/

/-- The Weil operator as an integral: `ω(g) v = Δ_∞(g) ∫ v(y) ϱ(g y) e dμ(y)`. -/
private theorem weilRep_eq_integral (g : unitaryGroup ε) (v : FockSpace ε) :
    weilRep ε g v = multiplier ε g • ∫ y, v y •
      ReproducingModel.heisenbergRep (g • y) ReproducingModel.vacuum ∂measure ι := by
  rw [ReproducingModel.weilRep_apply_eq, ReproducingModel.weilOp_apply_eq,
    HeisenbergDatum.Representation.integrated_apply]
  simp only [HeisenbergDatum.Representation.twist_apply]

open scoped Matrix.Norms.Operator in
/-- The Weil representation and moments:
`M_N(ω_ε(u) v) ≤ |Δ_∞(u)| (1 + ‖u‖) ^ N M_N(e) M_N(v)`, for the operator norm of `u` for the
sup norm. -/
theorem moment_weilRep_le (N : ℕ) (g : unitaryGroup ε) (v : FockSpace ε) :
    moment N (weilRep ε g v) ≤ ‖multiplier ε g‖ₑ *
      ((1 + ‖((g : GL ι ℂ) : Matrix ι ι ℂ)‖ₑ) ^ N *
        moment N (ReproducingModel.vacuum : FockSpace ε) * moment N v) := by
  have h_point (y : ι → ℂ) :
      moment N (ReproducingModel.heisenbergRep (g • y) (ReproducingModel.vacuum : FockSpace ε)) ≤
        (1 + ‖((g : GL ι ℂ) : Matrix ι ι ℂ)‖ₑ) ^ N *
          moment N (ReproducingModel.vacuum : FockSpace ε) * (1 + ‖y‖ₑ) ^ N := by
    set A := ((g : GL ι ℂ) : Matrix ι ι ℂ)
    have h_mulVec : ‖A *ᵥ y‖ₑ ≤ ‖A‖ₑ * ‖y‖ₑ := by
      rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, eNorm_eq_nnNorm, ← ENNReal.coe_mul]
      exact_mod_cast Matrix.linfty_opNNNorm_mulVec A y
    refine (moment_heisenbergRep_le N _ _).trans ?_
    rw [smul_def, mul_right_comm, ← mul_pow]
    gcongr
    calc 1 + ‖A *ᵥ y‖ₑ ≤ 1 + ‖A‖ₑ * ‖y‖ₑ := by gcongr
      _ ≤ (1 + ‖A‖ₑ) * (1 + ‖y‖ₑ) := by
          rw [add_mul, one_mul, mul_add, mul_one, add_assoc]
          gcongr
          exact le_add_self.trans le_add_self
  rw [weilRep_eq_integral, moment_smul]
  gcongr
  exact (moment_integral_le N).trans (lintegral_moment_smul_le h_point v)

open scoped Matrix.Norms.Operator in
/-- The Weil representation preserves finite moments. -/
theorem HasFiniteMoments.weilRep {v : FockSpace ε} (hv : HasFiniteMoments v)
    (g : unitaryGroup ε) : HasFiniteMoments (weilRep ε g v) :=
  fun N ↦ ne_top_of_le_ne_top (ENNReal.mul_ne_top eNorm_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      eNorm_ne_top⟩)) (hasFiniteMoments_vacuum N)) (hv N)))
    (moment_weilRep_le N g v)

/-! ### Approximation by polynomial vectors -/

omit [DecidableEq ι] in
/-- The Gaussian absorbs polynomial weights: if `s ≤ (‖u‖ + 1) t`, then
`s ^ N |e(u)| ≤ exp (N²) t ^ N`. -/
private theorem pow_mul_norm_gaussian_le (N : ℕ) {s t : ℝ} {u : ι → ℂ}
    (h_le : s ≤ (‖u‖ + 1) * t) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s ^ N * ‖gaussian ι u‖ ≤ Real.exp (N ^ 2) * t ^ N := by
  have h_gauss : ‖gaussian ι u‖ ≤ Real.exp (-‖u‖ ^ 2 / 2) := by
    rw [norm_gaussian]
    gcongr
    exact Pi.norm_pow_le_sum_norm_pow u two_ne_zero
  have h_one : ‖u‖ + 1 ≤ Real.exp ‖u‖ := by linarith [Real.add_one_le_exp ‖u‖]
  calc s ^ N * ‖gaussian ι u‖ ≤ (Real.exp ‖u‖ * t) ^ N * Real.exp (-‖u‖ ^ 2 / 2) := by
        gcongr
        exact h_le.trans (mul_le_mul_of_nonneg_right h_one ht)
    _ = Real.exp (N * ‖u‖ - ‖u‖ ^ 2 / 2) * t ^ N := by
        rw [mul_pow, ← Real.exp_natCast_mul, sub_eq_add_neg, Real.exp_add, neg_div]
        ring
    _ ≤ Real.exp (N ^ 2) * t ^ N := by
        gcongr
        nlinarith [sq_nonneg (‖u‖ - N)]

/-- The phase `S(y, w) = ∑ i, conj (ζ(y) i) ζ(w) i` of the reproducing kernel. -/
private abbrev kernelPhase (ε : ι → ℤˣ) (y w : ι → ℂ) : ℂ :=
  ∑ i, conj (holomorphicCoord ε y i) * holomorphicCoord ε w i

omit [DecidableEq ι] in
/-- Gaussian domination of the reproducing kernel:
`(1 + ‖w‖) ^ N |e(w)| |e(y)| exp |S(y, w)| ≤ exp (N²) (1 + ‖y‖) ^ N`. -/
private theorem pow_mul_kernel_le (N : ℕ) (y w : ι → ℂ) :
    (1 + ‖w‖) ^ N * (‖gaussian ι w‖ * ‖gaussian ι y‖ * Real.exp ‖kernelPhase ε y w‖) ≤
      Real.exp (N ^ 2) * (1 + ‖y‖) ^ N := by
  let u : ι → ℂ := fun i ↦ ((‖y i‖ - ‖w i‖ : ℝ) : ℂ)
  have h_u (i : ι) : ‖u i‖ = |‖y i‖ - ‖w i‖| := by
    simp only [u, Complex.norm_real, Real.norm_eq_abs]
  have h_S : ‖kernelPhase ε y w‖ ≤ ∑ i, ‖y i‖ * ‖w i‖ :=
    (norm_sum_le _ _).trans_eq (sum_congr rfl fun i _ ↦ by simp [norm_holomorphicCoord_apply])
  have h_sq : ‖gaussian ι w‖ * ‖gaussian ι y‖ * Real.exp ‖kernelPhase ε y w‖ ≤
      ‖gaussian ι u‖ := by
    simp only [norm_gaussian, ← Real.exp_add, Real.exp_le_exp, h_u, sq_abs]
    have h_expand : ∑ i, (‖y i‖ - ‖w i‖) ^ 2 =
        ∑ i, ‖w i‖ ^ 2 + ∑ i, ‖y i‖ ^ 2 - 2 * ∑ i, ‖y i‖ * ‖w i‖ := by
      simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ by ring
    linarith
  have h_w : ‖w‖ ≤ ‖y‖ + ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    have := norm_le_pi_norm y i
    have := norm_le_pi_norm u i
    rw [h_u] at this
    linarith [le_abs_self (‖w i‖ - ‖y i‖), abs_sub_comm (‖y i‖) (‖w i‖)]
  have h_tri : 1 + ‖w‖ ≤ (‖u‖ + 1) * (1 + ‖y‖) := by nlinarith [norm_nonneg y, norm_nonneg u]
  calc _ ≤ (1 + ‖w‖) ^ N * ‖gaussian ι u‖ := by gcongr
    _ ≤ _ := pow_mul_norm_gaussian_le N h_tri (by positivity) (by positivity)

/-- The monomial `∏ j, X (p j)` of a word `p : Fin k → ι`. -/
private def prodX {k : ℕ} (p : Fin k → ι) : MvPolynomial ι ℂ := ∏ j, MvPolynomial.X (p j)

/-- The `n`-th partial sum of the exponential series of the reproducing kernel, as an operator:
`∑_{k < n} (1 / k!) ∑_{p : Fin k → ι} ⟨w_p, ·⟩ w_p` with `w_p` the vector of `prodX p`. -/
private def partialKernelOp (ε : ι → ℤˣ) (n : ℕ) : FockSpace ε →L[ℂ] FockSpace ε :=
  ∑ k ∈ range n, ∑ p : Fin k → ι, ((k.factorial : ℂ)⁻¹) •
    (ReproducingModel.innerSL (polyVector ε (prodX p))).smulRight (polyVector ε (prodX p))

private theorem innerSL_heisenbergRep_vacuum_right (w : FockSpace ε) (y : ι → ℂ) :
    ReproducingModel.innerSL w (ReproducingModel.heisenbergRep y ReproducingModel.vacuum) =
      conj (w y) := by
  rw [← ReproducingModel.conj_innerSL, ReproducingModel.innerSL_heisenbergRep_vacuum]

/-- The kernel of `1 - partialKernelOp ε n`: at `w`, the translate of the vacuum by `y` gives
`e(w) e(y)` times the tail of the exponential series at `S(y, w)`. -/
private theorem one_sub_partialKernelOp_apply (n : ℕ) (y w : ι → ℂ) :
    (1 - partialKernelOp ε n) (ReproducingModel.heisenbergRep y ReproducingModel.vacuum) w =
      gaussian ι w * gaussian ι y * (cexp (kernelPhase ε y w) -
        ∑ k ∈ range n, kernelPhase ε y w ^ k / k.factorial) := by
  have h_translate : ReproducingModel.heisenbergRep y (ReproducingModel.vacuum : FockSpace ε) w =
      gaussian ι w * gaussian ι y * cexp (kernelPhase ε y w) := by
    rw [ReproducingModel.heisenbergRep_apply, ReproducingModel.vacuum_apply,
      heisenbergDatum_mul_gaussian]
  have h_word {k : ℕ} (p : Fin k → ι) :
      conj (polyVector ε (prodX p) y) * polyVector ε (prodX p) w = gaussian ι w * gaussian ι y *
        ∏ j, conj (holomorphicCoord ε y (p j)) * holomorphicCoord ε w (p j) := by
    simp only [polyVector_apply, prodX, MvPolynomial.eval_X, map_mul,
      map_prod, prod_mul_distrib, (isVacuum_gaussian (ε := ε)).conj_apply]
    ring
  have h_pow (k : ℕ) : ∑ p : Fin k → ι,
      ∏ j, conj (holomorphicCoord ε y (p j)) * holomorphicCoord ε w (p j) =
        kernelPhase ε y w ^ k :=
    (Fintype.sum_pow (fun i ↦ conj (holomorphicCoord ε y i) * holomorphicCoord ε w i) k).symm
  rw [← ReproducingModel.evalCLM_apply]
  simp only [partialKernelOp, sub_apply, one_apply_eq_self, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_heisenbergRep_vacuum_right, map_sub, map_sum,
    map_smul, ReproducingModel.evalCLM_apply, smul_eq_mul, h_translate, h_word, mul_sub, mul_sum]
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← h_pow, sum_div, mul_sum]
  exact sum_congr rfl fun p _ ↦ by ring

/-- The moment of `v - K_n v` is at most the weighted `L¹` norm on `(ι → ℂ)²` of `v(y)` times the
kernel of `1 - K_n`. -/
private theorem moment_sub_partialKernelOp_le (N n : ℕ) (v : FockSpace ε) :
    moment N (v - partialKernelOp ε n v) ≤ ∫⁻ p : (ι → ℂ) × (ι → ℂ), ENNReal.ofReal
      ((1 + ‖p.2‖) ^ N * ‖v p.1 * (gaussian ι p.2 * gaussian ι p.1 *
        (cexp (kernelPhase ε p.1 p.2) - ∑ k ∈ range n, kernelPhase ε p.1 p.2 ^ k / k.factorial))‖)
          ∂(measure ι).prod (measure ι) := by
  have hv := ReproducingModel.continuous v
  have h_eq : v - partialKernelOp ε n v = ∫ y, v y • (1 - partialKernelOp ε n)
      (ReproducingModel.heisenbergRep y ReproducingModel.vacuum) ∂measure ι := by
    rw [← ReproducingModel.map_eq_integral, sub_apply, one_apply_eq_self]
  rw [h_eq, lintegral_prod _ (by fun_prop)]
  refine (moment_integral_le N).trans (le_of_eq (lintegral_congr fun y ↦ ?_))
  simp only [moment_eq_lintegral_ofReal, ReproducingModel.smul_apply, one_sub_partialKernelOp_apply]

/-- The weighted partial sums of the reproducing kernel are dominated, uniformly in `n`. -/
private theorem norm_smul_partialSum_le (N m n : ℕ) (v : FockSpace ε) (y w : ι → ℂ) :
    ‖(1 + ‖w‖) ^ N • (v y * (gaussian ι w * gaussian ι y *
      ∑ k ∈ range n, kernelPhase ε y w ^ k / k.factorial))‖ ≤
      Real.exp ((m + N : ℕ) ^ 2) * ((1 + ‖y‖) ^ (m + N) * ‖v y‖) * (1 + ‖w‖) ^ (-(m : ℝ)) := by
  have h_series : ‖∑ k ∈ range n, kernelPhase ε y w ^ k / k.factorial‖ ≤
      Real.exp ‖kernelPhase ε y w‖ :=
    (norm_sum_le _ _).trans ((sum_le_sum fun k _ ↦ by simp).trans
      (Real.sum_le_exp_of_nonneg (norm_nonneg _) n))
  have h_pos : 0 < 1 + ‖w‖ := by positivity
  have h_kernel := pow_mul_kernel_le (ε := ε) (m + N) y w
  rw [Real.rpow_neg h_pos.le, Real.rpow_natCast, norm_smul, Real.norm_of_nonneg (by positivity),
    norm_mul, norm_mul, norm_mul]
  calc (1 + ‖w‖) ^ N * (‖v y‖ * (‖gaussian ι w‖ * ‖gaussian ι y‖ *
        ‖∑ k ∈ range n, kernelPhase ε y w ^ k / k.factorial‖))
      ≤ (1 + ‖w‖) ^ N * (‖v y‖ * (‖gaussian ι w‖ * ‖gaussian ι y‖ *
          Real.exp ‖kernelPhase ε y w‖)) := by gcongr
    _ = (1 + ‖w‖) ^ (m + N) * (‖gaussian ι w‖ * ‖gaussian ι y‖ *
          Real.exp ‖kernelPhase ε y w‖) * ‖v y‖ * ((1 + ‖w‖) ^ m)⁻¹ := by
        rw [pow_add]
        field_simp
    _ ≤ _ := by
        rw [show Real.exp ((m + N : ℕ) ^ 2) * ((1 + ‖y‖) ^ (m + N) * ‖v y‖) * ((1 + ‖w‖) ^ m)⁻¹ =
          Real.exp ((m + N : ℕ) ^ 2) * (1 + ‖y‖) ^ (m + N) * ‖v y‖ * ((1 + ‖w‖) ^ m)⁻¹ by ring]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_kernel (norm_nonneg _))
          (by positivity)

/-- **Approximation by polynomial vectors**: a Fock vector with finite moments is the
limit of polynomial vectors `v_{P_n}` in every moment at once. -/
theorem exists_tendsto_moment {v : FockSpace ε} (hv : HasFiniteMoments v) :
    ∃ P : ℕ → MvPolynomial ι ℂ, ∀ N,
      Tendsto (fun n ↦ moment N (v - polyVector ε (P n))) atTop (nhds 0) := by
  have hv_cont := ReproducingModel.continuous v
  let P (n : ℕ) : MvPolynomial ι ℂ := ∑ k ∈ range n, ∑ p : Fin k → ι,
    ((k.factorial : ℂ)⁻¹ * ReproducingModel.innerSL (polyVector ε (prodX p)) v) • prodX p
  have hP (n : ℕ) : polyVector ε (P n) = partialKernelOp ε n v := by
    simp [P, partialKernelOp, sum_apply, smul_smul]
  refine ⟨P, fun N ↦ ?_⟩
  set m := (measure ι).integrablePower
  let G (n : ℕ) (p : (ι → ℂ) × (ι → ℂ)) : ℂ := (1 + ‖p.2‖) ^ N • (v p.1 *
    (gaussian ι p.2 * gaussian ι p.1 * ∑ k ∈ range n, kernelPhase ε p.1 p.2 ^ k / k.factorial))
  let g (p : (ι → ℂ) × (ι → ℂ)) : ℂ := (1 + ‖p.2‖) ^ N • (v p.1 *
    (gaussian ι p.2 * gaussian ι p.1 * cexp (kernelPhase ε p.1 p.2)))
  have h_le (n : ℕ) : moment N (v - polyVector ε (P n)) ≤
      ∫⁻ p, ENNReal.ofReal ‖G n p - g p‖ ∂(measure ι).prod (measure ι) := by
    refine (hP n ▸ moment_sub_partialKernelOp_le N n v).trans
      (le_of_eq (lintegral_congr fun p ↦ ?_))
    rw [norm_sub_rev, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), ← mul_sub,
      ← mul_sub]
  have h_int : Integrable (fun y : ι → ℂ ↦ (1 + ‖y‖) ^ (m + N) * ‖v y‖) (measure ι) := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (.of_forall fun y ↦ by positivity)).2 ?_⟩
    rw [← moment_eq_lintegral_ofReal]
    exact (hv (m + N)).lt_top
  have h_bound := ((h_int.const_mul (Real.exp ((m + N : ℕ) ^ 2))).mul_prod
    (Measure.integrable_pow_neg_integrablePower (measure ι)))
  have h_tendsto := tendsto_lintegral_norm_of_dominated_convergence (F := G) (f := g)
    (fun n ↦ by fun_prop) h_bound.hasFiniteIntegral
    (fun n ↦ .of_forall fun p ↦ norm_smul_partialSum_le N m n v p.1 p.2)
    (.of_forall fun p ↦ by
      have h := (NormedSpace.expSeries_div_hasSum_exp (kernelPhase ε p.1 p.2)).tendsto_sum_nat
      rw [← Complex.exp_eq_exp_ℂ] at h
      exact ((h.const_mul _).const_mul _).const_smul _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto
    (fun _ ↦ zero_le) h_le

/-! ### Linear forms controlled by short differences -/

/-- Heisenberg translations along a line through a translate of a polynomial vector: the curve
`r ↦ ϱ(r y) ϱ(z) v_P` has derivative `ϱ(s y) ϱ(z) v_Q` at `s`, with
`Q = κ P + D_y P` and `κ = z* ε y - y* ε z`. -/
theorem hasDerivAt_heisenbergRep_heisenbergRep (y z : ι → ℂ) (P : MvPolynomial ι ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ ReproducingModel.heisenbergRep (r • y)
        (ReproducingModel.heisenbergRep z (polyVector ε P)))
      (ReproducingModel.heisenbergRep (s • y) (ReproducingModel.heisenbergRep z (polyVector ε
        ((star z ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ z) • P +
          heisenbergDeriv ε y P)))) s := by
  set ϱ := ReproducingModel.heisenbergRep (β := heisenbergDatum ε) (μ := measure ι)
    (e := gaussian ι)
  set κ : ℂ := star z ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ z
  have h_comm (r : ℝ) (v : FockSpace ε) :
      ϱ (r • y) (ϱ z v) = cexp (r * κ) • ϱ z (ϱ (r • y) v) := by
    rw [HeisenbergDatum.Representation.apply_apply, HeisenbergDatum.Representation.apply_apply,
      smul_smul, add_comm]
    congr 1
    simp only [heisenbergDatum_apply, ← Complex.exp_add, κ]
    congr 1
    simp only [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.real_smul]
    ring
  have h_line (r : ℝ) (v : FockSpace ε) : ϱ (r • y) v = ϱ (s • y) (ϱ ((r - s) • y) v) := by
    rw [HeisenbergDatum.Representation.apply_apply, ← add_smul, add_sub_cancel]
    convert (one_smul ℂ _).symm
    simp only [heisenbergDatum_apply, star_smul, star_trivial, Matrix.mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_comm s, sub_self, zero_div, Complex.exp_zero]
  have h_exp : HasDerivAt (fun r : ℝ ↦ cexp (r * κ)) κ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const κ).cexp
  have h_zero : HasDerivAt (fun r : ℝ ↦ ϱ (r • y) (ϱ z (polyVector ε P)))
      (ϱ z (polyVector ε (κ • P + heisenbergDeriv ε y P))) 0 := by
    simp only [h_comm]
    have h := h_exp.smul (((ϱ z).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_heisenbergRep_polyVector y P))
    convert h using 1
    · rfl
    · simp [HeisenbergDatum.Representation.zero_apply, add_comm]
  rw [funext fun r : ℝ ↦ h_line r (ϱ z (polyVector ε P))]
  exact ((ϱ (s • y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
    (HasDerivAt.comp_sub_const s s (by rwa [sub_self]))

/-- `κ P + D_y P` coordinate by coordinate, with `κ = z* ε y - y* ε z`. -/
private theorem smul_add_heisenbergDeriv_eq_sum (y z : ι → ℂ) (P : MvPolynomial ι ℂ) :
    (star z ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ z) • P + heisenbergDeriv ε y P =
      ∑ i, ((((ε i : ℤ) : ℂ) * (conj (z i) * y i) - ((ε i : ℤ) : ℂ) * (conj (y i) * z i)) • P +
        y i • raiseOp ε i P - conj (y i * ((ε i : ℤ) : ℂ)) • lowerOp ε i P) := by
  rw [star_dotProduct_signMatrix_mulVec, star_dotProduct_signMatrix_mulVec, heisenbergDeriv_apply,
    ← sum_sub_distrib, sum_smul, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by abel

/-- One step of the induction of `exists_norm_heisenbergRep_polyVector_le`: if every polynomial
vector satisfies the bound of order `N`, then a short difference of a translate of `v_P` gains a
factor `t (1 + ‖z‖)`. -/
private theorem norm_sub_heisenbergRep_le {N : ℕ} {C : MvPolynomial ι ℂ → ℝ}
    (hC : ∀ Q, 0 ≤ C Q) {t : ℝ} {ℓ : FockSpace ε →L[ℂ] ℂ} (ht : 0 ≤ t) (ht_le : t ≤ 1)
    (h_bound : ∀ Q z, ‖ℓ (ReproducingModel.heisenbergRep z (polyVector ε Q))‖ ≤
      C Q * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N)
    (P : MvPolynomial ι ℂ) (z y : ι → ℂ) (hy : ‖y‖ ≤ t) :
    ‖ℓ (ReproducingModel.heisenbergRep z (polyVector ε P)) - ℓ (ReproducingModel.heisenbergRep y
      (ReproducingModel.heisenbergRep z (polyVector ε P)))‖ ≤
      (∑ i, (2 * C P + C (raiseOp ε i P) + C (lowerOp ε i P))) * 2 ^ N * ‖ℓ‖ * t ^ (N + 1) *
        (1 + ‖z‖) ^ (N + 1) := by
  set ϱ := ReproducingModel.heisenbergRep (β := heisenbergDatum ε) (μ := measure ι)
    (e := gaussian ι)
  set m : ℝ := ‖ℓ‖ * t ^ N * (2 * (1 + ‖z‖)) ^ N
  have h_shift (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) (Q : MvPolynomial ι ℂ) :
      ‖ℓ (ϱ (s • y) (ϱ z (polyVector ε Q)))‖ ≤ C Q * m := by
    have h_norm : 1 + ‖s • y + z‖ ≤ 2 * (1 + ‖z‖) := by
      have : ‖s • y‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg hs.1]
        nlinarith [hs.2, norm_nonneg y]
      linarith [norm_add_le (s • y) z, norm_nonneg z]
    rw [HeisenbergDatum.Representation.apply_apply, map_smul, norm_smul,
      HeisenbergDatum.norm_apply, one_mul]
    refine (h_bound Q _).trans ?_
    simp only [m, ← mul_assoc]
    gcongr
    exact mul_nonneg (mul_nonneg (hC Q) (norm_nonneg _)) (pow_nonneg ht _)
  have h_i (i : ι) : ‖y i‖ ≤ t * (1 + ‖z‖) :=
    ((norm_le_pi_norm y i).trans hy).trans (le_mul_of_one_le_right ht (by simp))
  have h_c (i : ι) : ‖((ε i : ℤ) : ℂ) * (conj (z i) * y i) - ((ε i : ℤ) : ℂ) * (conj (y i) * z i)‖ ≤
      2 * (t * (1 + ‖z‖)) := by
    have h_z := norm_le_pi_norm z i
    have h_y := (norm_le_pi_norm y i).trans hy
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, norm_sign, RCLike.norm_conj, one_mul]
    nlinarith [norm_nonneg (y i), norm_nonneg (z i)]
  have h_deriv (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
      ‖ℓ (ϱ (s • y) (ϱ z (polyVector ε ((star z ⬝ᵥ signMatrix ε *ᵥ y -
        star y ⬝ᵥ signMatrix ε *ᵥ z) • P + heisenbergDeriv ε y P))))‖ ≤
        (∑ i, (2 * C P + C (raiseOp ε i P) + C (lowerOp ε i P))) * m * (t * (1 + ‖z‖)) := by
    rw [smul_add_heisenbergDeriv_eq_sum, sum_mul, sum_mul]
    simp only [map_sum, map_sub, map_add, map_smul]
    refine norm_sum_le_of_le _ fun i _ ↦ ?_
    refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have h_star : ‖conj (y i * ((ε i : ℤ) : ℂ))‖ = ‖y i‖ := by
      rw [RCLike.norm_conj, norm_mul, norm_sign, mul_one]
    simp only [norm_smul, h_star]
    have := hC P
    grw [h_c, h_i, h_shift s hs, h_shift s hs, h_shift s hs]
    exact le_of_eq (by ring)
  have h_mv := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun r _ ↦
    (((ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_heisenbergRep_heisenbergRep y z P r))).hasDerivWithinAt) h_deriv
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', one_smul, zero_smul,
    HeisenbergDatum.Representation.zero_apply] at h_mv
  rw [norm_sub_rev]
  exact h_mv.trans_eq (by simp only [m, mul_pow]; ring)

/-- The induction behind `exists_norm_heisenbergRep_polyVector_le`, for `0 ≤ t ≤ 1`: each
Heisenberg derivative gains a factor `t` and costs a factor `1 + ‖z‖`. -/
private theorem exists_norm_heisenbergRep_polyVector_le_aux (N : ℕ) (P : MvPolynomial ι ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ℓ : FockSpace ε →L[ℂ] ℂ), 0 ≤ t → t ≤ 1 →
      (∀ (f : FockSpace ε) (B : ℝ), (∀ y : ι → ℂ, ‖y‖ ≤ t →
        ‖ℓ f - ℓ (ReproducingModel.heisenbergRep y f)‖ ≤ B) → ‖ℓ f‖ ≤ B) →
      ∀ z : ι → ℂ, ‖ℓ (ReproducingModel.heisenbergRep z (polyVector ε P))‖ ≤
        C * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
  induction N generalizing P with
  | zero =>
    refine ⟨‖polyVector ε P‖, norm_nonneg _, fun t ℓ _ _ _ z ↦ ?_⟩
    simpa [mul_comm, HeisenbergDatum.Representation.norm_apply] using
      ℓ.le_opNorm (ReproducingModel.heisenbergRep z (polyVector ε P))
  | succ N ih =>
    choose C hC h_bound using ih
    refine ⟨(∑ i, (2 * C P + C (raiseOp ε i P) + C (lowerOp ε i P))) * 2 ^ N,
      mul_nonneg (sum_nonneg fun i _ ↦ by linarith [hC P, hC (raiseOp ε i P), hC (lowerOp ε i P)])
        (by positivity), fun t ℓ ht ht_le hℓ z ↦ hℓ _ _ fun y hy ↦ ?_⟩
    exact norm_sub_heisenbergRep_le hC ht ht_le (fun Q ↦ h_bound Q t ℓ ht ht_le hℓ) P z y hy

/-- Each Heisenberg derivative gains a factor `t` and costs a factor `1 + ‖z‖`. For each `N` and
`P` there is `C ≥ 0` such that for every `t` and every bounded linear form `ℓ` whose values are
bounded, when `t < 1`, by any bound on its differences under translations of size at most `t`,
`|ℓ(ϱ(z) v_P)| ≤ C ‖ℓ‖ t ^ N (1 + ‖z‖) ^ N`. For `t < 0` the hypothesis on `ℓ` cannot hold. -/
theorem exists_norm_heisenbergRep_polyVector_le (N : ℕ) (P : MvPolynomial ι ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ℓ : FockSpace ε →L[ℂ] ℂ),
      (t < 1 → ∀ (f : FockSpace ε) (B : ℝ), (∀ y : ι → ℂ, ‖y‖ ≤ t →
        ‖ℓ f - ℓ (ReproducingModel.heisenbergRep y f)‖ ≤ B) → ‖ℓ f‖ ≤ B) →
      ∀ z : ι → ℂ, ‖ℓ (ReproducingModel.heisenbergRep z (polyVector ε P))‖ ≤
        C * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
  obtain ⟨C, hC, h_bound⟩ := exists_norm_heisenbergRep_polyVector_le_aux (ε := ε) N P
  set c := ‖polyVector ε P‖
  refine ⟨C + c, by positivity, fun t ℓ h_diff z ↦ ?_⟩
  rcases lt_or_ge t 1 with ht_lt | ht_ge
  · rcases lt_or_ge t 0 with ht_neg | ht_nonneg
    · -- No translation has negative size, so every `ℓ f` would be bounded by `-1`.
      have h := h_diff ht_lt 0 (-1) fun y hy ↦ absurd ((norm_nonneg y).trans hy) ht_neg.not_ge
      linarith [norm_nonneg (ℓ 0)]
    calc ‖ℓ (ReproducingModel.heisenbergRep z (polyVector ε P))‖
        ≤ C * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := h_bound t ℓ ht_nonneg ht_lt.le (h_diff ht_lt) z
      _ ≤ (C + c) * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
          gcongr
          exact le_add_of_nonneg_right (norm_nonneg _)
  · calc ‖ℓ (ReproducingModel.heisenbergRep z (polyVector ε P))‖ ≤ c * ‖ℓ‖ * 1 * 1 := by
          simpa [mul_comm, c, HeisenbergDatum.Representation.norm_apply] using
            ℓ.le_opNorm (ReproducingModel.heisenbergRep z (polyVector ε P))
      _ ≤ (C + c) * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
          gcongr
          · exact le_add_of_nonneg_left hC
          · exact one_le_pow₀ ht_ge
          · exact one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))

/-- **Linear forms controlled by short differences.** For each `N` there is `C` such that for
every `t`, every bounded linear form `ℓ` and every Fock vector `v`, `|ℓ(v)| ≤ C ‖ℓ‖ t ^ N M_N(v)`,
provided (when `t < 1`) that `|ℓ(f)| ≤ B` whenever `|ℓ(f) - ℓ(ϱ(y) f)| ≤ B` for all `‖y‖ ≤ t`. -/
theorem exists_enorm_le_mul_moment_of_norm_sub_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ℓ : FockSpace ε →L[ℂ] ℂ) (v : FockSpace ε),
      (t < 1 → ∀ (f : FockSpace ε) (B : ℝ), (∀ y : ι → ℂ, ‖y‖ ≤ t →
        ‖ℓ f - ℓ (ReproducingModel.heisenbergRep y f)‖ ≤ B) → ‖ℓ f‖ ≤ B) →
      ‖ℓ v‖ₑ ≤ ENNReal.ofReal (C * ‖ℓ‖ * t ^ N) * moment N v := by
  obtain ⟨C, hC, h_bound⟩ := exists_norm_heisenbergRep_polyVector_le (ε := ε) N 1
  exact ⟨C, hC, fun t ℓ v h_diff ↦
    enorm_le_mul_moment (fun z ↦ by simpa using h_bound t ℓ h_diff z) v⟩

end TauCeti.Fock
