/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Unbounded spectral integration against a projection-valued measure

Let `P` be a projection-valued measure on a measurable space `X` acting on a complex Hilbert
space `H`, with finite diagonal scalar measures `P.diag ξ` and polarized complex measures
`μ_(ψ,ξ) = P.polarizedComplexMeasure ψ ξ`. For any measurable symbol `f : X → ℂ` — not assumed
bounded — this file constructs the unbounded **spectral integral**
`P.spectralIntegral f hf : H →ₗ.[ℂ] H`, classically written `∫ f dP`.

Its domain is the maximal second-moment subspace

`{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`,

equivalently `{x : H | MemLp f 2 (P.diag x)}`. On this subspace the bounded truncations
`f_n = {t | ‖f t‖ ≤ n}.indicator f` form a Cauchy sequence in `H` under the bounded functional
calculus `P.integral`, because `‖P.integral (f_m - f_n) x‖ ^ 2 = ∫ ‖f_m - f_n‖ ^ 2 d(P.diag x)`
vanishes as `m, n → ∞` by dominated convergence. Passing to the limit defines a linear map on the
second-moment domain.

By the Cauchy–Schwarz bound for polarized spectral measures
(`ProjValMeasure.lintegral_polarizedComplexMeasure_variation_sq_le`), every `x` in the domain and
every `y : H` make `f` integrable with respect to the variation `|μ_(y,x)|`, with
`∫ t, ‖f t‖ ∂|μ_(y,x)| ≤ ‖y‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag x))`, and the matrix elements of the
spectral integral are given by scalar integration against the polarized measures:

`⟪y, P.spectralIntegral f hf x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; μ_(y,x)]`.

Together with the second-moment domain, these matrix elements determine the partial operator
uniquely (`eq_spectralIntegral_of_domain_of_inner`).

Key structural properties proved here:
* **Norm identity**: `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`.
* **Bounded compatibility and cutoffs**: for a `BoundedBorelFunction`, `P.spectralIntegral` is
  `(P.integral g).toLinearMap.toPMap ⊤`; on any measurable set `B` where `‖f‖ ≤ M`, `P.proj B hB`
  maps `H` into the domain and `P.spectralIntegral` acts on `P.proj B hB ξ` as the bounded integral
  of `B.indicator f`.
* **Density and truncation core**: the sublevel projections `P.proj {t | ‖f t‖ ≤ n}` converge
  strongly to the identity, so the domain is dense and `⨆ n, (P.proj {t | ‖f t‖ ≤ n} _).range` is
  a graph core (`LinearPMap.HasCore`).
* **Adjoint, closedness, normality, self-adjointness, and positivity**:
  `(P.spectralIntegral f hf).adjoint = P.spectralIntegral (star ∘ f) _` with equal domains
  and equal norms; consequently `P.spectralIntegral f hf` is closed and normal, it is
  self-adjoint if and only if `star (f t) = f t` holds `P.ae`-almost everywhere, and its quadratic
  form has nonnegative real part if and only if `0 ≤ (f t).re` holds `P.ae`-almost everywhere.
* **Almost-everywhere invariance, pushforward, and algebraic laws**: two measurable symbols define
  the same spectral integral iff they agree `P.ae`-almost everywhere; pushing `P` forward along a
  measurable map `κ` pulls the symbol back along `κ`; constants, negation, scalar multiples (with
  equality of domains for nonzero scalars), bounded symbol perturbations, and extension of operator
  sums and differences on intersected domains all follow from the matrix-element characterization.
* **Existence and uniqueness** (`existsUnique_spectralIntegral`): packages the domain, matrix
  elements, density, closedness, second-moment norm identity, and adjoint characterization into a
  single `∃!` statement.

No topological or separability hypothesis is imposed on `X` or `H`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS Graduate Studies in Mathematics 99,
  2009, Section 3.1, Theorem 3.2 and Lemma 3.5.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.3.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press, 1980, Section VIII.3.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal LinearPMap

namespace TauCeti
namespace ProjValMeasure

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Construction via bounded sublevel truncations -/

/-- The maximal second-moment submodule `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` of a
measurable symbol `f`. -/
private def spectralDomain (P : ProjValMeasure X H) (f : X → ℂ) : Submodule ℂ H where
  carrier := {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}
  zero_mem' := by
    simp
  add_mem' {x y} hx hy := by
    change ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag (x + y)) < ∞
    have hle : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag (x + y)) ≤
        (2 : ℝ≥0∞) * (∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) + ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag y)) := by
      calc
        ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag (x + y))
            ≤ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂((2 : ℝ≥0∞) • (P.diag x + P.diag y)) :=
          lintegral_mono' (P.diag_add_le x y) le_rfl
        _ = (2 : ℝ≥0∞) * (∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) + ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag y)) := by
          rw [lintegral_smul_measure, lintegral_add_measure, smul_eq_mul]
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.add_lt_top.mpr ⟨hx, hy⟩))
  smul_mem' c {x} hx := by
    change ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag (c • x)) < ∞
    rw [P.diag_smul c x, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) hx

/-- The `n`-th sublevel truncation `{t | ‖f t‖ ≤ n}.indicator f` as a bounded Borel symbol. -/
private def cutoffSymbol (f : X → ℂ) (hf : Measurable f) (n : ℕ) : BoundedBorelFunction X :=
  BoundedBorelFunction.ofFunction ({t : X | ‖f t‖ ≤ n}.indicator f)
    (hf.indicator (measurableSet_le hf.norm measurable_const))
    ⟨n, Nat.cast_nonneg n, fun t => by
      by_cases ht : t ∈ {s : X | ‖f s‖ ≤ n}
      · rw [Set.indicator_of_mem ht]
        exact ht
      · rw [Set.indicator_of_notMem ht, norm_zero]
        exact Nat.cast_nonneg n⟩

private theorem cutoffSymbol_apply (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    cutoffSymbol f hf n t = ({s : X | ‖f s‖ ≤ n}.indicator f) t :=
  BoundedBorelFunction.ofFunction_apply _ _ _ t

private theorem norm_cutoffSymbol_le (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    ‖cutoffSymbol f hf n t‖ ≤ ‖f t‖ := by
  rw [cutoffSymbol_apply]
  exact norm_indicator_le_norm_self f t

private theorem tendsto_cutoffSymbol (f : X → ℂ) (hf : Measurable f) (t : X) :
    Tendsto (fun n : ℕ => cutoffSymbol f hf n t) atTop (𝓝 (f t)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
  have ht : t ∈ {s : X | ‖f s‖ ≤ n} := hN.trans (Nat.cast_le.mpr hn)
  dsimp only
  rw [cutoffSymbol_apply, Set.indicator_of_mem ht]

private theorem integrable_norm_sq_of_lintegral_lt_top (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) :
    Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) := by
  refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine (lintegral_congr fun t => ?_).trans_lt hx
  rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]

/-- On the second-moment subspace, the bounded cutoff integrals of `f` form a Cauchy sequence in
`H`. -/
private theorem cauchySeq_integral_cutoffSymbol (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) :
    CauchySeq fun n : ℕ => P.integral (cutoffSymbol f hf n) x := by
  have hx_int : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    P.integrable_norm_sq_of_lintegral_lt_top hf hx
  let δ : ℕ → ℝ := fun n => ∫ t, ‖cutoffSymbol f hf n t - f t‖ ^ 2 ∂(P.diag x)
  have hδ_int (n : ℕ) :
      Integrable (fun t => ‖cutoffSymbol f hf n t - f t‖ ^ 2) (P.diag x) := by
    refine (hx_int.const_mul 4).mono'
      (((cutoffSymbol f hf n).measurable.sub hf).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖cutoffSymbol f hf n t - f t‖ ^ 2
          ≤ (‖cutoffSymbol f hf n t‖ + ‖f t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ (‖f t‖ + ‖f t‖) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (add_le_add_left (norm_cutoffSymbol_le f hf n t) _) 2
      _ = 4 * ‖f t‖ ^ 2 := by ring
  have hδ_tendsto : Tendsto δ atTop (𝓝 0) := by
    rw [← MeasureTheory.integral_zero X ℝ (μ := P.diag x)]
    exact tendsto_integral_of_dominated_convergence (fun t => 4 * ‖f t‖ ^ 2)
      (fun n => (((cutoffSymbol f hf n).measurable.sub hf).norm.pow_const 2).aestronglyMeasurable)
      (hx_int.const_mul 4)
      (fun n => Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        calc
          ‖cutoffSymbol f hf n t - f t‖ ^ 2 ≤ (‖f t‖ + ‖f t‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _)
              ((norm_sub_le _ _).trans (add_le_add_left (norm_cutoffSymbol_le f hf n t) _)) 2
          _ = 4 * ‖f t‖ ^ 2 := by ring)
      (Eventually.of_forall fun t => by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_cutoffSymbol f hf t)).pow 2)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε4 : 0 < ε ^ 2 / 4 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hδ_tendsto (ε ^ 2 / 4) hε4
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm' : δ m < ε ^ 2 / 4 := by
    have h := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
    exact h
  have hn' : δ n < ε ^ 2 / 4 := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
    exact h
  have hmn_le :
      dist (P.integral (cutoffSymbol f hf m) x) (P.integral (cutoffSymbol f hf n) x) ^ 2 ≤
        2 * δ m + 2 * δ n := by
    rw [dist_eq_norm, ← sub_apply, ← map_sub, P.norm_sq_integral_apply]
    have hsub_int :
        Integrable (fun t => ‖(cutoffSymbol f hf m - cutoffSymbol f hf n) t‖ ^ 2) (P.diag x) := by
      refine ((hδ_int m).const_mul 2 |>.add ((hδ_int n).const_mul 2)).mono'
        (((cutoffSymbol f hf m - cutoffSymbol f hf n).measurable.norm.pow_const
          2).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _), BoundedBorelFunction.sub_apply, Pi.add_apply]
      have htri : ‖cutoffSymbol f hf m t - cutoffSymbol f hf n t‖ ≤
          ‖cutoffSymbol f hf m t - f t‖ + ‖cutoffSymbol f hf n t - f t‖ := by
        simpa [sub_sub_sub_cancel_right] using
          norm_sub_le (cutoffSymbol f hf m t - f t) (cutoffSymbol f hf n t - f t)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖cutoffSymbol f hf m t - f t‖ - ‖cutoffSymbol f hf n t - f t‖)]
    calc
      ∫ t, ‖(cutoffSymbol f hf m - cutoffSymbol f hf n) t‖ ^ 2 ∂(P.diag x)
          ≤ ∫ t, (2 * ‖cutoffSymbol f hf m t - f t‖ ^ 2 +
              2 * ‖cutoffSymbol f hf n t - f t‖ ^ 2) ∂(P.diag x) := by
        refine integral_mono hsub_int (((hδ_int m).const_mul 2).add ((hδ_int n).const_mul 2))
          fun t => ?_
        rw [BoundedBorelFunction.sub_apply]
        have htri : ‖cutoffSymbol f hf m t - cutoffSymbol f hf n t‖ ≤
            ‖cutoffSymbol f hf m t - f t‖ + ‖cutoffSymbol f hf n t - f t‖ := by
          simpa [sub_sub_sub_cancel_right] using
            norm_sub_le (cutoffSymbol f hf m t - f t) (cutoffSymbol f hf n t - f t)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖cutoffSymbol f hf m t - f t‖ - ‖cutoffSymbol f hf n t - f t‖)]
      _ = 2 * δ m + 2 * δ n := by
        rw [integral_add ((hδ_int m).const_mul 2) ((hδ_int n).const_mul 2),
          integral_const_mul, integral_const_mul]
  have hlt : dist (P.integral (cutoffSymbol f hf m) x)
      (P.integral (cutoffSymbol f hf n) x) ^ 2 < ε ^ 2 := by
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- The **unbounded spectral integral** `∫ f dP` of a measurable symbol `f : X → ℂ` against a
projection-valued measure `P`, as a partial linear operator `H →ₗ.[ℂ] H` on the maximal
second-moment domain `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`. -/
def spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) : H →ₗ.[ℂ] H where
  domain := P.spectralDomain f
  toFun :=
    { toFun x := limUnder atTop fun n : ℕ => P.integral (cutoffSymbol f hf n) (x : H)
      map_add' x y := by
        have hx := tendsto_nhds_limUnder
          (cauchySeq_tendsto_of_complete (P.cauchySeq_integral_cutoffSymbol hf x.2))
        have hy := tendsto_nhds_limUnder
          (cauchySeq_tendsto_of_complete (P.cauchySeq_integral_cutoffSymbol hf y.2))
        have hxy := tendsto_nhds_limUnder
          (cauchySeq_tendsto_of_complete (P.cauchySeq_integral_cutoffSymbol hf (x + y).2))
        refine tendsto_nhds_unique hxy ?_
        simpa only [Submodule.coe_add, map_add] using hx.add hy
      map_smul' c x := by
        have hx := tendsto_nhds_limUnder
          (cauchySeq_tendsto_of_complete (P.cauchySeq_integral_cutoffSymbol hf x.2))
        have hcx := tendsto_nhds_limUnder
          (cauchySeq_tendsto_of_complete (P.cauchySeq_integral_cutoffSymbol hf (c • x).2))
        refine tendsto_nhds_unique hcx ?_
        simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using hx.const_smul c }

private theorem tendsto_integral_cutoffSymbol (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n : ℕ => P.integral (cutoffSymbol f hf n) (x : H)) atTop
      (𝓝 (P.spectralIntegral f hf x)) :=
  tendsto_nhds_limUnder
    (cauchySeq_tendsto_of_complete (P.cauchySeq_integral_cutoffSymbol hf x.2))

/-! ## Domain characterizations -/

/-- Membership in the domain of `P.spectralIntegral f hf` is finiteness of the second spectral
moment `∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x)`. -/
@[simp]
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {x : H} :
    x ∈ (P.spectralIntegral f hf).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  (Iff.rfl)

/-- Membership in the domain of `P.spectralIntegral f hf` is equivalent to Bochner integrability
of `t ↦ ‖f t‖ ^ 2` against `P.diag x`. -/
theorem mem_spectralIntegral_domain_iff_integrable_norm_sq (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} :
    x ∈ (P.spectralIntegral f hf).domain ↔ Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) := by
  rw [P.mem_spectralIntegral_domain_iff hf]
  refine ⟨P.integrable_norm_sq_of_lintegral_lt_top hf, fun h => ?_⟩
  refine (lintegral_congr fun t => ?_).trans_lt h.2
  calc
    ‖f t‖ₑ ^ 2 = ENNReal.ofReal (‖f t‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ‖‖f t‖ ^ 2‖ₑ := by
      rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _)]

/-- Membership in the domain of `P.spectralIntegral f hf` is equivalent to
`MemLp f 2 (P.diag x)`. -/
theorem mem_spectralIntegral_domain_iff_memLp (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} :
    x ∈ (P.spectralIntegral f hf).domain ↔ MemLp f 2 (P.diag x) := by
  rw [P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf,
    memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable]

/-! ## Polarized-measure integrability, matrix elements, norm identity, and uniqueness -/

/-- For every `x` in the domain of `P.spectralIntegral f hf` and every `y : H`, `f` is integrable
with respect to the polarized complex measure `P.polarizedComplexMeasure y x` (that is, with
respect to its total-variation measure). -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    (P.polarizedComplexMeasure y x).Integrable f := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hsq :
      (∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure y x).variation) ^ 2 < ∞ :=
    (P.lintegral_polarizedComplexMeasure_variation_sq_le y x hf.eNorm).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top)
        ((P.mem_spectralIntegral_domain_iff hf).mp hx))
  by_contra htop
  rw [not_lt_top_iff] at htop
  rw [htop] at hsq
  exact lt_irrefl ∞ hsq

/-- For every `x` in the domain of `P.spectralIntegral f hf`, `f` is Bochner integrable against the
diagonal scalar measure `P.diag x`. -/
theorem integrable_diag_of_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    Integrable f (P.diag x) := by
  simpa [VectorMeasure.Integrable, P.variation_polarizedComplexMeasure_self] using
    P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hx x

/-- **Cauchy–Schwarz variation bound** for a vector `x` in the spectral-integral domain:
`∫ t, ‖f t‖ ∂|μ_(y,x)| ≤ ‖y‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag x))`. -/
theorem integral_norm_polarizedComplexMeasure_variation_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure y x).variation ≤
      ‖y‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) := by
  have hint_var : Integrable (fun t => ‖f t‖) (P.polarizedComplexMeasure y x).variation :=
    (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hx y).norm
  have hint_diag : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf).mp hx
  have hlhs_nonneg : 0 ≤ ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure y x).variation :=
    integral_nonneg fun _ => norm_nonneg _
  have hrhs_nonneg : 0 ≤ ‖y‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) := by positivity
  rw [← sq_le_sq₀ hlhs_nonneg hrhs_nonneg, mul_pow,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have hcs := P.lintegral_polarizedComplexMeasure_variation_sq_le y x hf.eNorm
  have hlhs_eq :
      ENNReal.ofReal ((∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure y x).variation) ^ 2) =
        (∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure y x).variation) ^ 2 := by
    rw [ENNReal.ofReal_pow hlhs_nonneg,
      ofReal_integral_eq_lintegral_ofReal hint_var (Eventually.of_forall fun _ => norm_nonneg _)]
    congr 1
    exact lintegral_congr fun t => ofReal_norm (f t)
  have hrhs_eq :
      ENNReal.ofReal (‖y‖ ^ 2 * ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) =
        ‖y‖ₑ ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ofReal_integral_eq_lintegral_ofReal hint_diag (Eventually.of_forall fun _ => sq_nonneg _)]
    congr 1
    refine lintegral_congr fun _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← hlhs_eq, ← hrhs_eq] at hcs
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcs

/-- **Matrix elements of the unbounded spectral integral**: for `x` in the domain and any `y : H`,
`⟪y, P.spectralIntegral f hf x⟫_ℂ = ∫ᵛ t, f t ∂[mul ℝ ℂ; P.polarizedComplexMeasure y x]`. -/
theorem inner_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    ⟪y, P.spectralIntegral f hf x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hint := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x.2 y
  have hlim_vec :
      Tendsto (fun n : ℕ => ⟪y, P.integral (cutoffSymbol f hf n) (x : H)⟫_ℂ)
        atTop (𝓝 ⟪y, P.spectralIntegral f hf x⟫_ℂ) :=
    tendsto_const_nhds.inner (P.tendsto_integral_cutoffSymbol hf x)
  have hlim_int :
      Tendsto (fun n : ℕ => ∫ᵛ t, cutoffSymbol f hf n t
          ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
        atTop (𝓝 (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
      (fun n => (cutoffSymbol f hf n).measurable.aestronglyMeasurable)
      hint.norm
      (fun n => Eventually.of_forall (norm_cutoffSymbol_le f hf n))
      (Eventually.of_forall (tendsto_cutoffSymbol f hf))
  refine tendsto_nhds_unique ?_ hlim_int
  refine hlim_vec.congr fun n => ?_
  exact (P.integral_polarizedComplexMeasure_eq_inner_integral (cutoffSymbol f hf n) y x).symm

/-- Diagonal matrix elements of the unbounded spectral integral are Bochner integrals against the
diagonal scalar measure `P.diag x`. -/
theorem inner_self_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ⟪(x : H), P.spectralIntegral f hf x⟫_ℂ = ∫ t, f t ∂(P.diag x) := by
  rw [P.inner_spectralIntegral hf x x, P.integral_polarizedComplexMeasure_self]

/-- **Second-moment norm identity** for the unbounded spectral integral:
`‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. -/
theorem norm_sq_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  have hx_int : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf).mp x.2
  have hlim_lhs :
      Tendsto (fun n : ℕ => ‖P.integral (cutoffSymbol f hf n) (x : H)‖ ^ 2) atTop
        (𝓝 (‖P.spectralIntegral f hf x‖ ^ 2)) :=
    (P.tendsto_integral_cutoffSymbol hf x).norm.pow 2
  have hlim_rhs :
      Tendsto (fun n : ℕ => ∫ t, ‖cutoffSymbol f hf n t‖ ^ 2 ∂(P.diag x)) atTop
        (𝓝 (∫ t, ‖f t‖ ^ 2 ∂(P.diag x))) :=
    tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
      (fun n => ((cutoffSymbol f hf n).measurable.norm.pow_const 2).aestronglyMeasurable)
      hx_int
      (fun n => Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffSymbol_le f hf n t) 2)
      (Eventually.of_forall fun t => (tendsto_cutoffSymbol f hf t).norm.pow 2)
  exact tendsto_nhds_unique hlim_lhs
    (hlim_rhs.congr fun n => (P.norm_sq_integral_apply (cutoffSymbol f hf n) x).symm)

/-- Extended-norm form of `norm_sq_spectralIntegral`. -/
theorem enorm_sq_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
  have hx_int : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf).mp x.2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), P.norm_sq_spectralIntegral hf x,
    ofReal_integral_eq_lintegral_ofReal hx_int (Eventually.of_forall fun _ => sq_nonneg _)]
  refine lintegral_congr fun _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Uniqueness of the unbounded spectral integral**: any partial linear operator `T` with the
second-moment domain and the polarized-measure matrix elements of `f` equals
`P.spectralIntegral f hf`. -/
theorem eq_spectralIntegral_of_domain_of_inner (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (T : H →ₗ.[ℂ] H)
    (hdom : ∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞)
    (hinner : ∀ (x : T.domain) (y : H),
      ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :
    T = P.spectralIntegral f hf := by
  refine LinearPMap.ext (Submodule.ext hdom) fun x hxT hxS => ?_
  refine ext_inner_left ℂ fun y => ?_
  rw [hinner ⟨x, hxT⟩ y, P.inner_spectralIntegral hf ⟨x, hxS⟩ y]

/-! ## Bounded compatibility, spectral cutoffs, density, and graph core -/

/-- For a bounded Borel symbol `g`, the unbounded spectral integral agrees with the everywhere
defined bounded functional calculus `(P.integral g).toLinearMap.toPMap ⊤`. -/
theorem spectralIntegral_boundedBorelFunction (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) :
    P.spectralIntegral g g.measurable = (P.integral g).toLinearMap.toPMap ⊤ := by
  symm
  refine P.eq_spectralIntegral_of_domain_of_inner g.measurable _ (fun x => ?_) (fun x y => ?_)
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff]
    have hle : ∫⁻ t, ‖g t‖ₑ ^ 2 ∂(P.diag x) ≤ ‖g‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
      calc
        ∫⁻ t, ‖g t‖ₑ ^ 2 ∂(P.diag x) ≤ ∫⁻ _, ‖g‖ₑ ^ 2 ∂(P.diag x) :=
          lintegral_mono fun t => pow_le_pow_left' (by
            rw [← ofReal_norm, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (g.norm_coe_le_norm t)) 2
        _ = ‖g‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by rw [lintegral_const, P.diag_univ x]
    exact hle.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top)
      (ENNReal.pow_lt_top eNorm_lt_top))
  · exact (P.integral_polarizedComplexMeasure_eq_inner_integral g y x).symm

/-- Spectral projections preserve the domain of `P.spectralIntegral f hf`. -/
theorem proj_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_proj hB x]
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt
    ((P.mem_spectralIntegral_domain_iff hf).mp hx)

/-- Spectral projections commute with `P.spectralIntegral f hf` on its domain. -/
theorem spectralIntegral_proj (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf hB x.2⟩ =
      P.proj B hB (P.spectralIntegral f hf x) := by
  refine ext_inner_left ℂ fun y => ?_
  rw [P.inner_spectralIntegral hf, P.polarizedComplexMeasure_proj_right y x hB]
  calc
    ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; (P.polarizedComplexMeasure y x).restrict B]
        = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ;
            P.polarizedComplexMeasure (P.proj B hB y) x] := by
      rw [P.polarizedComplexMeasure_proj_left y x hB]
    _ = ⟪P.proj B hB y, P.spectralIntegral f hf x⟫_ℂ :=
      (P.inner_spectralIntegral hf x (P.proj B hB y)).symm
    _ = ⟪y, P.proj B hB (P.spectralIntegral f hf x)⟫_ℂ :=
      (P.isSelfAdjoint_proj B hB).isSymmetric y _

/-- On any measurable set `B` where `‖f‖` is bounded by `M`, `P.proj B hB` maps every vector of `H`
into the domain of `P.spectralIntegral f hf`. -/
theorem proj_mem_spectralIntegral_domain_of_norm_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {M : ℝ}
    (hM : ∀ t ∈ B, ‖f t‖ ≤ M) (ξ : H) :
    P.proj B hB ξ ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_proj hB ξ]
  have hle : ∫⁻ t in B, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) ≤ ENNReal.ofReal (max M 0) ^ 2 * ‖ξ‖ₑ ^ 2 := by
    calc
      ∫⁻ t in B, ‖f t‖ₑ ^ 2 ∂(P.diag ξ)
          ≤ ∫⁻ _ in B, ENNReal.ofReal (max M 0) ^ 2 ∂(P.diag ξ) := by
        refine setLIntegral_mono' hB fun t ht => pow_le_pow_left' ?_ 2
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((hM t ht).trans (le_max_left M 0))
      _ = ENNReal.ofReal (max M 0) ^ 2 * (P.diag ξ) B := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (max M 0) ^ 2 * ‖ξ‖ₑ ^ 2 := by
        rw [← P.diag_univ ξ]
        exact mul_le_mul_right (measure_mono (Set.subset_univ B)) _
  exact hle.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    (ENNReal.pow_lt_top eNorm_lt_top))

/-- **Action on spectral cutoffs**: on any measurable set `B` where `‖f‖ ≤ M` (`0 ≤ M`),
`P.spectralIntegral f hf` acts on `P.proj B hB ξ` as the bounded integral of `B.indicator f`. -/
theorem spectralIntegral_proj_of_norm_le (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t ∈ B, ‖f t‖ ≤ M) (ξ : H) :
    P.spectralIntegral f hf
        ⟨P.proj B hB ξ, P.proj_mem_spectralIntegral_domain_of_norm_le hf hB hM ξ⟩ =
      P.integral (BoundedBorelFunction.ofFunction (B.indicator f) (hf.indicator hB)
        ⟨M, hM0, fun t => by
          by_cases ht : t ∈ B
          · rw [Set.indicator_of_mem ht]
            exact hM t ht
          · rw [Set.indicator_of_notMem ht, norm_zero]
            exact hM0⟩) ξ := by
  refine ext_inner_left ℂ fun y => ?_
  rw [P.inner_spectralIntegral hf, P.polarizedComplexMeasure_proj_right y ξ hB,
    ← P.integral_polarizedComplexMeasure_eq_inner_integral, ← VectorMeasure.integral_indicator hB]
  simp only [BoundedBorelFunction.ofFunction_apply]

/-- Sublevel projections `P.proj {t | ‖f t‖ ≤ n}` converge strongly to the identity on `H`. -/
theorem tendsto_proj_sublevel (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) (ξ : H) :
    Tendsto (fun n : ℕ => P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) ξ)
      atTop (𝓝 ξ) := by
  let hBn : ∀ n : ℕ, MeasurableSet {t : X | ‖f t‖ ≤ n} :=
    fun n => measurableSet_le hf.norm measurable_const
  have hlim :
      Tendsto (fun n : ℕ => P.integral (BoundedBorelFunction.indicator {t | ‖f t‖ ≤ n} (hBn n) 1) ξ)
        atTop (𝓝 (P.integral 1 ξ)) := by
    refine P.tendsto_integral_apply_filter_of_dominated_convergence (M := 1)
      (Eventually.of_forall fun n => Eventually.of_forall fun t => ?_)
      (Eventually.of_forall fun t => ?_) ξ
    · by_cases ht : ‖f t‖ ≤ n <;> simp [ht]
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
      refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
      have ht : t ∈ {s : X | ‖f s‖ ≤ n} := hN.trans (Nat.cast_le.mpr hn)
      simp [ht]
  simpa [P.integral_indicator] using hlim

/-- The domain of `P.spectralIntegral f hf` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    Dense ((P.spectralIntegral f hf).domain : Set H) := fun ξ =>
  mem_closure_of_tendsto (P.tendsto_proj_sublevel hf ξ)
    (Eventually.of_forall fun n =>
      P.proj_mem_spectralIntegral_domain_of_norm_le hf (B := {t | ‖f t‖ ≤ n})
        (measurableSet_le hf.norm measurable_const) (fun _ ht => ht) ξ)

/-- The supremum of the ranges of the sublevel projections `P.proj {t | ‖f t‖ ≤ n}` lies inside the
domain of `P.spectralIntegral f hf`. -/
theorem iSup_range_proj_sublevel_le_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).range) ≤
      (P.spectralIntegral f hf).domain := by
  refine iSup_le fun n => ?_
  rintro _ ⟨ξ, rfl⟩
  exact P.proj_mem_spectralIntegral_domain_of_norm_le hf
    (measurableSet_le hf.norm measurable_const) (fun _ ht => ht) ξ

/-! ## Adjoint, closedness, normality, self-adjointness, and positivity -/

/-- `P.spectralIntegral (star ∘ f) _` is a formal adjoint of `P.spectralIntegral f hf`. -/
theorem isFormalAdjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).IsFormalAdjoint
      (P.spectralIntegral (star ∘ f) (continuous_star.measurable.comp hf)) := by
  have hf_star : Measurable (star ∘ f) := continuous_star.measurable.comp hf
  intro x y
  have hstar_cutoff (n : ℕ) :
      cutoffSymbol (star ∘ f) hf_star n = star (cutoffSymbol f hf n) := by
    ext t
    by_cases ht : t ∈ {s : X | ‖f s‖ ≤ n}
    · have ht' : t ∈ {s : X | ‖(star ∘ f) s‖ ≤ n} := by simpa using ht
      rw [cutoffSymbol_apply, BoundedBorelFunction.star_apply, cutoffSymbol_apply,
        Set.indicator_of_mem ht', Set.indicator_of_mem ht, Function.comp_apply]
    · have ht' : t ∉ {s : X | ‖(star ∘ f) s‖ ≤ n} := by simpa using ht
      rw [cutoffSymbol_apply, BoundedBorelFunction.star_apply, cutoffSymbol_apply,
        Set.indicator_of_notMem ht', Set.indicator_of_notMem ht, star_zero]
  have hx := P.tendsto_integral_cutoffSymbol hf x
  have hy := P.tendsto_integral_cutoffSymbol hf_star y
  have hlhs : Tendsto (fun n : ℕ => ⟪P.integral (cutoffSymbol f hf n) (x : H), (y : H)⟫_ℂ)
      atTop (𝓝 ⟪P.spectralIntegral f hf x, (y : H)⟫_ℂ) :=
    hx.inner tendsto_const_nhds
  have hrhs :
      Tendsto (fun n : ℕ => ⟪(x : H), P.integral (cutoffSymbol (star ∘ f) hf_star n) (y : H)⟫_ℂ)
        atTop (𝓝 ⟪(x : H), P.spectralIntegral (star ∘ f) hf_star y⟫_ℂ) :=
    tendsto_const_nhds.inner hy
  refine tendsto_nhds_unique hlhs (hrhs.congr fun n => ?_)
  rw [hstar_cutoff n, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **Adjoint of the unbounded spectral integral**: the Hilbert-space adjoint of
`P.spectralIntegral f hf` is `P.spectralIntegral (star ∘ f) (continuous_star.measurable.comp hf)`,
with equality of domains and actions. -/
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint =
      P.spectralIntegral (star ∘ f) (continuous_star.measurable.comp hf) := by
  have hf_star : Measurable (star ∘ f) := continuous_star.measurable.comp hf
  have hdense := P.dense_spectralIntegral_domain hf
  have hle : P.spectralIntegral (star ∘ f) hf_star ≤ (P.spectralIntegral f hf).adjoint :=
    (P.isFormalAdjoint_spectralIntegral hf).le_adjoint hdense
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 ?_)).symm
  intro y hy
  let z : H := (P.spectralIntegral f hf).adjoint ⟨y, hy⟩
  let hBn : ∀ n : ℕ, MeasurableSet {t : X | ‖f t‖ ≤ n} :=
    fun n => measurableSet_le hf.norm measurable_const
  have hident (n : ℕ) :
      P.integral (star (cutoffSymbol f hf n)) y = P.proj {t | ‖f t‖ ≤ n} (hBn n) z := by
    refine ext_inner_right ℂ fun u => ?_
    have hu_mem : P.proj {t | ‖f t‖ ≤ n} (hBn n) u ∈ (P.spectralIntegral f hf).domain :=
      P.proj_mem_spectralIntegral_domain_of_norm_le hf (hBn n) (fun _ ht => ht) u
    have hu_act :
        P.spectralIntegral f hf ⟨P.proj {t | ‖f t‖ ≤ n} (hBn n) u, hu_mem⟩ =
          P.integral (cutoffSymbol f hf n) u := by
      exact P.spectralIntegral_proj_of_norm_le hf (hBn n) (Nat.cast_nonneg n)
        (fun _ ht => ht) u
    calc
      ⟪P.integral (star (cutoffSymbol f hf n)) y, u⟫_ℂ
          = ⟪y, P.integral (cutoffSymbol f hf n) u⟫_ℂ := by
        rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪y, P.spectralIntegral f hf ⟨P.proj {t | ‖f t‖ ≤ n} (hBn n) u, hu_mem⟩⟫_ℂ := by
        rw [hu_act]
      _ = ⟪z, P.proj {t | ‖f t‖ ≤ n} (hBn n) u⟫_ℂ :=
        (LinearPMap.adjoint_isFormalAdjoint hdense ⟨y, hy⟩ ⟨_, hu_mem⟩).symm
      _ = ⟪P.proj {t | ‖f t‖ ≤ n} (hBn n) z, u⟫_ℂ :=
        ((P.isSelfAdjoint_proj _ (hBn n)).isSymmetric z u).symm
  have hstep (n : ℕ) :
      ∫⁻ t, ‖cutoffSymbol f hf n t‖ₑ ^ 2 ∂(P.diag y) ≤ ‖z‖ₑ ^ 2 := by
    have hnorm : ‖P.integral (star (cutoffSymbol f hf n)) y‖ ≤ ‖z‖ := by
      rw [hident n]
      exact P.norm_proj_apply_le _ (hBn n) z
    have hsq :
        ∫ t, ‖cutoffSymbol f hf n t‖ ^ 2 ∂(P.diag y) ≤ ‖z‖ ^ 2 := by
      have heq :
          ∫ t, ‖cutoffSymbol f hf n t‖ ^ 2 ∂(P.diag y) =
            ‖P.integral (star (cutoffSymbol f hf n)) y‖ ^ 2 := by
        rw [P.norm_sq_integral_apply]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
        dsimp only
        rw [BoundedBorelFunction.star_apply, norm_star]
      rw [heq]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hint : Integrable (fun t => ‖cutoffSymbol f hf n t‖ ^ 2) (P.diag y) :=
      .of_bound ((cutoffSymbol f hf n).measurable.norm.pow_const 2).aestronglyMeasurable
        (‖cutoffSymbol f hf n‖ ^ 2)
        (Eventually.of_forall fun t => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) ((cutoffSymbol f hf n).norm_coe_le_norm t) 2)
    calc
      ∫⁻ t, ‖cutoffSymbol f hf n t‖ₑ ^ 2 ∂(P.diag y)
          = ENNReal.ofReal (∫ t, ‖cutoffSymbol f hf n t‖ ^ 2 ∂(P.diag y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun _ => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (‖z‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
      _ = ‖z‖ₑ ^ 2 := by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hmono : Monotone fun (n : ℕ) t => ‖cutoffSymbol f hf n t‖ₑ ^ 2 := by
    intro m n hmn t
    refine pow_le_pow_left' ?_ 2
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hmt : t ∈ {s : X | ‖f s‖ ≤ m}
    · have hnt : t ∈ {s : X | ‖f s‖ ≤ n} :=
        le_trans (show ‖f t‖ ≤ m from hmt) (Nat.cast_le.mpr hmn)
      rw [cutoffSymbol_apply, cutoffSymbol_apply, Set.indicator_of_mem hmt,
        Set.indicator_of_mem hnt]
    · rw [cutoffSymbol_apply, Set.indicator_of_notMem hmt, norm_zero]
      exact norm_nonneg _
  have hsup (t : X) : (⨆ n : ℕ, ‖cutoffSymbol f hf n t‖ₑ ^ 2) = ‖(star ∘ f) t‖ₑ ^ 2 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
    refine tendsto_nhds_unique (tendsto_atTop_iSup fun m n hmn => hmono hmn t) ?_
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
    have ht : t ∈ {s : X | ‖f s‖ ≤ n} := hN.trans (Nat.cast_le.mpr hn)
    dsimp only
    rw [cutoffSymbol_apply, Set.indicator_of_mem ht, Function.comp_apply,
      ← ofReal_norm, ← ofReal_norm, norm_star]
  change y ∈ (P.spectralIntegral (star ∘ f) hf_star).domain
  rw [P.mem_spectralIntegral_domain_iff hf_star]
  have hiSup :
      ∫⁻ t, ‖(star ∘ f) t‖ₑ ^ 2 ∂(P.diag y) =
        ⨆ n : ℕ, ∫⁻ t, ‖cutoffSymbol f hf n t‖ₑ ^ 2 ∂(P.diag y) := by
    rw [← lintegral_iSup (fun n => (cutoffSymbol f hf n).measurable.eNorm.pow_const 2) hmono]
    exact lintegral_congr fun t => (hsup t).symm
  rw [hiSup]
  exact (iSup_le hstep).trans_lt (ENNReal.pow_lt_top eNorm_lt_top)

/-- `P.spectralIntegral f hf` is a closed operator. -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).IsClosed := by
  have hf_star : Measurable (star ∘ f) := continuous_star.measurable.comp hf
  have heq : P.spectralIntegral f hf = (P.spectralIntegral (star ∘ f) hf_star).adjoint := by
    rw [P.adjoint_spectralIntegral hf_star]
    congr!
    ext t
    simp
  rw [heq]
  exact LinearPMap.adjoint_isClosed (P.dense_spectralIntegral_domain hf_star)

/-- **Normality (domain equality)**: the adjoint of `P.spectralIntegral f hf` has the exact same
domain as `P.spectralIntegral f hf`. -/
@[simp]
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain = (P.spectralIntegral f hf).domain := by
  rw [P.adjoint_spectralIntegral hf]
  ext x
  simp only [P.mem_spectralIntegral_domain_iff, Function.comp_apply, ← ofReal_norm, norm_star]

/-- Matrix elements of `(P.spectralIntegral f hf).adjoint` are the polarized-measure integrals of
`star ∘ f`. -/
theorem inner_adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).adjoint.domain) (y : H) :
    ⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ =
      ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hf_star : Measurable (star ∘ f) := continuous_star.measurable.comp hf
  have hx' : (x : H) ∈ (P.spectralIntegral (star ∘ f) hf_star).domain :=
    congrArg LinearPMap.domain (P.adjoint_spectralIntegral hf) ▸ x.2
  rw [LinearPMap.congr_fun (P.adjoint_spectralIntegral hf) x.2 hx']
  exact P.inner_spectralIntegral hf_star ⟨x, hx'⟩ y

/-- **Normality (norm equality)**: `P.spectralIntegral f hf` and its adjoint have equal norms at
every vector of their common domain. -/
theorem norm_adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖(P.spectralIntegral f hf).adjoint
        ⟨(x : H), (P.adjoint_spectralIntegral_domain hf).symm ▸ x.2⟩‖ =
      ‖P.spectralIntegral f hf x‖ := by
  have hf_star : Measurable (star ∘ f) := continuous_star.measurable.comp hf
  have hx' : (x : H) ∈ (P.spectralIntegral (star ∘ f) hf_star).domain := by
    rw [P.mem_spectralIntegral_domain_iff hf_star]
    simpa only [Function.comp_apply, ← ofReal_norm, norm_star] using
      (P.mem_spectralIntegral_domain_iff hf).mp x.2
  rw [LinearPMap.congr_fun (P.adjoint_spectralIntegral hf)
    ((P.adjoint_spectralIntegral_domain hf).symm ▸ x.2) hx']
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [P.norm_sq_spectralIntegral hf_star, P.norm_sq_spectralIntegral hf]
  exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun _ => by simp)

/-- **Truncation graph core**: the supremum of the ranges of the sublevel projections
`P.proj {t | ‖f t‖ ≤ n}` is a graph core (`LinearPMap.HasCore`) for `P.spectralIntegral f hf`. -/
theorem hasCore_iSup_range_proj_sublevel (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).range) := by
  let S : Submodule ℂ H :=
    ⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).range
  rw [(P.isClosed_spectralIntegral hf).hasCore_iff_graph_subset_closure
    (P.iSup_range_proj_sublevel_le_domain hf)]
  rintro ⟨x, y⟩ hxy
  have hx_dom : x ∈ (P.spectralIntegral f hf).domain := LinearPMap.mem_domain_of_mem_graph hxy
  have hy_eq : P.spectralIntegral f hf ⟨x, hx_dom⟩ = y :=
    ((LinearPMap.image_iff hx_dom).2 hxy).symm
  let hBn : ∀ n : ℕ, MeasurableSet {t : X | ‖f t‖ ≤ n} :=
    fun n => measurableSet_le hf.norm measurable_const
  let u : ℕ → H := fun n => P.proj {t | ‖f t‖ ≤ n} (hBn n) x
  have huS (n : ℕ) : u n ∈ S :=
    Submodule.mem_iSup_of_mem n ⟨x, rfl⟩
  have hu_dom (n : ℕ) : u n ∈ ((P.spectralIntegral f hf).domRestrict S).domain :=
    ⟨huS n, P.iSup_range_proj_sublevel_le_domain hf (huS n)⟩
  have htend :
      Tendsto (fun n : ℕ => (u n, (P.spectralIntegral f hf).domRestrict S ⟨u n, hu_dom n⟩))
        atTop (𝓝 (x, y)) := by
    refine (P.tendsto_proj_sublevel hf x).prodMk_nhds ?_
    rw [← hy_eq]
    refine (P.tendsto_proj_sublevel hf (P.spectralIntegral f hf ⟨x, hx_dom⟩)).congr fun n =>
      (P.spectralIntegral_proj hf (hBn n) ⟨x, hx_dom⟩).symm
  exact mem_closure_of_tendsto htend
    (Eventually.of_forall fun n => LinearPMap.mem_graph _ ⟨u n, hu_dom n⟩)

/-! ## Almost-everywhere invariance, self-adjointness, and positivity -/

/-- Two measurable symbols have the same unbounded spectral integral against `P` if and only if
they agree `P.ae`-almost everywhere. -/
theorem spectralIntegral_eq_spectralIntegral_iff (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg ↔ f =ᶠ[P.ae] g := by
  constructor
  · intro hfg
    let Bn : ℕ → Set X := fun n => {t | ‖f t‖ ≤ n ∧ ‖g t‖ ≤ n}
    have hBn (n : ℕ) : MeasurableSet (Bn n) :=
      (measurableSet_le hf.norm measurable_const).inter
        (measurableSet_le hg.norm measurable_const)
    have hae_n (n : ℕ) : (Bn n).indicator f =ᶠ[P.ae] (Bn n).indicator g := by
      let fn : BoundedBorelFunction X :=
        BoundedBorelFunction.ofFunction ((Bn n).indicator f) (hf.indicator (hBn n))
          ⟨n, Nat.cast_nonneg n, fun t => by
            by_cases ht : t ∈ Bn n
            · rw [Set.indicator_of_mem ht]
              exact ht.1
            · rw [Set.indicator_of_notMem ht, norm_zero]
              exact Nat.cast_nonneg n⟩
      let gn : BoundedBorelFunction X :=
        BoundedBorelFunction.ofFunction ((Bn n).indicator g) (hg.indicator (hBn n))
          ⟨n, Nat.cast_nonneg n, fun t => by
            by_cases ht : t ∈ Bn n
            · rw [Set.indicator_of_mem ht]
              exact ht.2
            · rw [Set.indicator_of_notMem ht, norm_zero]
              exact Nat.cast_nonneg n⟩
      have hfn_coe : ⇑fn = (Bn n).indicator f := by
        ext t
        exact BoundedBorelFunction.ofFunction_apply _ _ _ t
      have hgn_coe : ⇑gn = (Bn n).indicator g := by
        ext t
        exact BoundedBorelFunction.ofFunction_apply _ _ _ t
      rw [← hfn_coe, ← hgn_coe, ← P.integral_eq_integral_iff fn gn]
      ext ξ
      have hfn := P.spectralIntegral_proj_of_norm_le hf (hBn n) (Nat.cast_nonneg n)
        (fun _ ht => ht.1) ξ
      have hgn := P.spectralIntegral_proj_of_norm_le hg (hBn n) (Nat.cast_nonneg n)
        (fun _ ht => ht.2) ξ
      exact hfn.symm.trans ((LinearPMap.congr_fun hfg _ _).trans hgn)
    rw [EventuallyEq, P.eventually_ae_iff]
    intro ξ
    have hξ : ∀ᵐ t ∂(P.diag ξ), ∀ n : ℕ, (Bn n).indicator f t = (Bn n).indicator g t :=
      ae_all_iff.mpr fun n => P.ae_diag_of_ae ξ (hae_n n)
    refine hξ.mono fun t ht => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (max ‖f t‖ ‖g t‖)
    have htN : t ∈ Bn N :=
      ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
    simpa only [Set.indicator_of_mem htN] using ht N
  · intro hfg
    refine P.eq_spectralIntegral_of_domain_of_inner hg (P.spectralIntegral f hf)
      (fun x => ?_) (fun x y => ?_)
    · rw [P.mem_spectralIntegral_domain_iff hf,
        lintegral_congr_ae ((P.ae_diag_of_ae x hfg).mono fun _ ht => by rw [ht])]
    · rw [P.inner_spectralIntegral hf x y]
      exact VectorMeasure.integral_congr_ae
        ((P.polarizedComplexMeasure_variation_absolutelyContinuous_right y x).ae_eq
          (P.ae_diag_of_ae x hfg))

/-- Measurable symbols that agree `P.ae`-almost everywhere define the same unbounded spectral
integral. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᶠ[P.ae] g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg :=
  (P.spectralIntegral_eq_spectralIntegral_iff hf hg).mpr h

/-- **Self-adjointness criterion**: `P.spectralIntegral f hf` is self-adjoint if and only if
`star (f t) = f t` holds `P.ae`-almost everywhere. -/
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔ ∀ᶠ t in P.ae, star (f t) = f t := by
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral hf,
    P.spectralIntegral_eq_spectralIntegral_iff (continuous_star.measurable.comp hf) hf]
  rfl

/-- **Quadratic-form positivity criterion**: the real part of `⟪x, P.spectralIntegral f hf x⟫_ℂ`
is nonnegative on the domain if and only if `0 ≤ (f t).re` holds `P.ae`-almost everywhere. -/
theorem forall_re_inner_spectralIntegral_nonneg_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (∀ x : (P.spectralIntegral f hf).domain, 0 ≤ (⟪(x : H), P.spectralIntegral f hf x⟫_ℂ).re) ↔
      ∀ᶠ t in P.ae, 0 ≤ (f t).re := by
  constructor
  · intro hpos
    rw [P.eventually_ae_iff]
    intro ξ
    let Bn : ℕ → Set X := fun n => {t | (f t).re < 0 ∧ ‖f t‖ ≤ n}
    have hBn (n : ℕ) : MeasurableSet (Bn n) :=
      (measurableSet_lt (Complex.continuous_re.measurable.comp hf) measurable_const).inter
        (measurableSet_le hf.norm measurable_const)
    have hnull (n : ℕ) : (P.diag ξ) (Bn n) = 0 := by
      let x : H := P.proj (Bn n) (hBn n) ξ
      have hx : x ∈ (P.spectralIntegral f hf).domain :=
        P.proj_mem_spectralIntegral_domain_of_norm_le hf (hBn n) (fun _ ht => ht.2) ξ
      have hint_x : Integrable f (P.diag x) :=
        P.integrable_diag_of_mem_spectralIntegral_domain hf hx
      have hre_nonneg : 0 ≤ ∫ t, (f t).re ∂(P.diag x) := by
        have h := hpos ⟨x, hx⟩
        rw [P.inner_self_spectralIntegral hf, ← RCLike.re_eq_complex_re,
          ← integral_re hint_x] at h
        simpa only [RCLike.re_eq_complex_re] using h
      have hre_nonpos : ∫ t, (f t).re ∂(P.diag x) ≤ 0 := by
        rw [P.diag_proj (hBn n) ξ, ← neg_nonneg, ← integral_neg]
        refine setIntegral_nonneg (hBn n) fun t ht => ?_
        exact neg_nonneg.mpr ht.1.le
      have hzero : ∫ t, -(f t).re ∂(P.diag x) = 0 := by
        rw [integral_neg, neg_eq_zero]
        exact le_antisymm hre_nonpos hre_nonneg
      have hint_neg : Integrable (fun t => -(f t).re) (P.diag x) :=
        (Complex.reCLM.integrable_comp hint_x).neg
      have hae_zero : (fun t => -(f t).re) =ᵐ[P.diag x] 0 := by
        rw [P.diag_proj (hBn n) ξ] at hint_neg hzero ⊢
        exact (integral_eq_zero_iff_of_nonneg_ae
          ((ae_restrict_mem (hBn n)).mono fun t ht => neg_nonneg.mpr ht.1.le)
          hint_neg).mp hzero
      rw [P.diag_proj (hBn n) ξ, Filter.EventuallyEq, ae_restrict_iff' (hBn n)] at hae_zero
      rw [measure_eq_zero_iff_ae_notMem]
      refine hae_zero.mono fun t ht hmem => ?_
      have h0 : -(f t).re = 0 := ht hmem
      linarith [hmem.1]
    have hsub : {t : X | ¬ 0 ≤ (f t).re} ⊆ ⋃ n : ℕ, Bn n := by
      intro t ht
      obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
      exact Set.mem_iUnion.mpr ⟨N, lt_of_not_ge ht, hN⟩
    exact measure_mono_null hsub (measure_iUnion_null hnull)
  · intro hre x
    have hint : Integrable f (P.diag x) :=
      P.integrable_diag_of_mem_spectralIntegral_domain hf x.2
    rw [P.inner_self_spectralIntegral hf x, ← RCLike.re_eq_complex_re, ← integral_re hint]
    simpa only [RCLike.re_eq_complex_re] using integral_nonneg_of_ae (P.ae_diag_of_ae x hre)

/-! ## Measurable reindexing (change of variables) -/

/-- Pushing `P` forward along a measurable map `κ` pushes its polarized complex measures forward
along `κ`. -/
@[simp]
theorem polarizedComplexMeasure_map (P : ProjValMeasure X H) (κ : X → Y) (hκ : Measurable κ)
    (ψ ξ : H) :
    (P.map κ hκ).polarizedComplexMeasure ψ ξ = (P.polarizedComplexMeasure ψ ξ).map κ := by
  ext B hB
  rw [VectorMeasure.map_apply _ hκ hB, (P.map κ hκ).polarizedComplexMeasure_apply ψ ξ B hB,
    map_proj, P.polarizedComplexMeasure_apply ψ ξ (κ ⁻¹' B) (hκ hB)]

/-- **Change of variables** for the unbounded spectral integral: integrating a measurable symbol
`f : Y → ℂ` against `P.map κ hκ` equals integrating `f ∘ κ` against `P`, with equality of domains
and actions. -/
theorem spectralIntegral_map (P : ProjValMeasure X H) (κ : X → Y) (hκ : Measurable κ)
    {f : Y → ℂ} (hf : Measurable f) :
    (P.map κ hκ).spectralIntegral f hf = P.spectralIntegral (f ∘ κ) (hf.comp hκ) := by
  symm
  refine (P.map κ hκ).eq_spectralIntegral_of_domain_of_inner hf _ (fun x => ?_) (fun x y => ?_)
  · rw [P.mem_spectralIntegral_domain_iff (hf.comp hκ), map_diag,
      lintegral_map (hf.eNorm.pow_const 2) hκ]
    rfl
  · rw [P.inner_spectralIntegral (hf.comp hκ) x y, P.polarizedComplexMeasure_map κ hκ y x,
      VectorMeasure.integral_map hκ hf.aestronglyMeasurable
        (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain (hf.comp hκ) x.2 y)]
    rfl

/-! ## Algebraic laws -/

/-- The spectral integral of a constant symbol `fun _ ↦ c` is the everywhere-defined scalar
operator `c • id`. -/
theorem spectralIntegral_const (P : ProjValMeasure X H) (c : ℂ) :
    P.spectralIntegral (fun _ => c) measurable_const =
      c • (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  symm
  refine P.eq_spectralIntegral_of_domain_of_inner measurable_const _ (fun x => ?_) (fun x y => ?_)
  · simp [P.diag_univ x, ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top)
      (ENNReal.pow_lt_top eNorm_lt_top)]
  · have hx_apply : ((LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤) x = (x : H) := rfl
    rw [LinearPMap.smul_apply, hx_apply, inner_smul_right,
      VectorMeasure.integral_const, P.polarizedComplexMeasure_apply y x Set.univ MeasurableSet.univ,
      P.proj_univ, ContinuousLinearMap.id_apply, ContinuousLinearMap.mul_apply']

/-- The spectral integral of the zero symbol is `0 : H →ₗ.[ℂ] H` (with domain `⊤`). -/
@[simp]
theorem spectralIntegral_zero (P : ProjValMeasure X H) :
    P.spectralIntegral 0 measurable_const = 0 := by
  refine (P.spectralIntegral_const 0).trans ?_
  refine LinearPMap.ext rfl fun x _ _ => ?_
  rw [LinearPMap.smul_apply, zero_smul]
  rfl

/-- The spectral integral of the constant unit symbol `1` is the everywhere-defined identity
operator. -/
@[simp]
theorem spectralIntegral_one (P : ProjValMeasure X H) :
    P.spectralIntegral 1 measurable_const = (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ :=
  (P.spectralIntegral_const 1).trans (one_smul ℂ _)

/-- Negating a measurable symbol negates its unbounded spectral integral (with identical domain). -/
@[simp]
theorem spectralIntegral_neg (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (-f) hf.neg = -P.spectralIntegral f hf := by
  symm
  refine P.eq_spectralIntegral_of_domain_of_inner hf.neg _ (fun x => ?_) (fun x y => ?_)
  · simp only [LinearPMap.neg_domain, P.mem_spectralIntegral_domain_iff hf, Pi.neg_apply,
      ← ofReal_norm, norm_neg]
  · rw [LinearPMap.neg_apply, inner_neg_right, P.inner_spectralIntegral hf x y,
      VectorMeasure.integral_neg]

/-- For every scalar `c : ℂ`, `P.spectralIntegral (c • f)` extends `c • P.spectralIntegral f hf`
(for `c = 0`, the right-hand side has domain `⊤` while `0 • T` retains `T.domain`). -/
theorem smul_spectralIntegral_le (P : ProjValMeasure X H) (c : ℂ) {f : X → ℂ} (hf : Measurable f) :
    c • P.spectralIntegral f hf ≤ P.spectralIntegral (c • f) (hf.const_smul c) := by
  refine ⟨fun x hx => ?_, fun x x' hxx' => ?_⟩
  · rw [P.mem_spectralIntegral_domain_iff (hf.const_smul c)]
    have hle : ∫⁻ t, ‖(c • f) t‖ₑ ^ 2 ∂(P.diag x) =
        ‖c‖ₑ ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
      rw [← lintegral_const_mul' _ _ (ENNReal.pow_lt_top eNorm_lt_top).ne]
      refine lintegral_congr fun t => ?_
      rw [Pi.smul_apply, eNorm_smul, mul_pow]
    rw [hle]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top)
      ((P.mem_spectralIntegral_domain_iff hf).mp hx)
  · refine ext_inner_left ℂ fun y => ?_
    rw [LinearPMap.smul_apply, inner_smul_right, P.inner_spectralIntegral hf x y,
      P.inner_spectralIntegral (hf.const_smul c) x' y, hxx']
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (VectorMeasure.integral_const_mul (P.polarizedComplexMeasure y x') c f).symm

/-- For a nonzero scalar `c ≠ 0`, `P.spectralIntegral (c • f)` equals `c • P.spectralIntegral f hf`
with equality of domains and actions. -/
theorem spectralIntegral_smul_of_ne_zero (P : ProjValMeasure X H) {c : ℂ} (hc : c ≠ 0) {f : X → ℂ}
    (hf : Measurable f) :
    P.spectralIntegral (c • f) (hf.const_smul c) = c • P.spectralIntegral f hf := by
  refine (LinearPMap.eq_of_le_of_domain_eq (P.smul_spectralIntegral_le c hf)
    (le_antisymm (P.smul_spectralIntegral_le c hf).1 ?_)).symm
  intro x hx
  have hinv := (P.smul_spectralIntegral_le c⁻¹ (hf.const_smul c)).1 hx
  change x ∈ (P.spectralIntegral f hf).domain
  rw [P.mem_spectralIntegral_domain_iff hf]
  have heq : c⁻¹ • (c • f) = f := inv_smul_smul₀ hc f
  simpa only [P.mem_spectralIntegral_domain_iff, heq] using hinv

/-- **Sum extension law**: for measurable symbols `f, g : X → ℂ`, `P.spectralIntegral (f + g)`
extends the operator sum `P.spectralIntegral f hf + P.spectralIntegral g hg` on the intersection
of their domains. -/
theorem add_spectralIntegral_le (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) :
    P.spectralIntegral f hf + P.spectralIntegral g hg ≤
      P.spectralIntegral (f + g) (hf.add hg) := by
  refine ⟨fun x hx => ?_, fun x x' hxx' => ?_⟩
  · rw [P.mem_spectralIntegral_domain_iff_memLp (hf.add hg)]
    exact ((P.mem_spectralIntegral_domain_iff_memLp hf).mp hx.1).add
      ((P.mem_spectralIntegral_domain_iff_memLp hg).mp hx.2)
  · refine ext_inner_left ℂ fun y => ?_
    have hxf : (x' : H) ∈ (P.spectralIntegral f hf).domain := hxx' ▸ x.2.1
    have hxg : (x' : H) ∈ (P.spectralIntegral g hg).domain := hxx' ▸ x.2.2
    have hxeq :
        (P.spectralIntegral f hf + P.spectralIntegral g hg) x =
          P.spectralIntegral f hf ⟨x', hxf⟩ + P.spectralIntegral g hg ⟨x', hxg⟩ := by
      rcases x with ⟨x_val, hx_mem⟩
      cases hxx'
      rfl
    rw [hxeq, inner_add_right, P.inner_spectralIntegral hf ⟨x', hxf⟩ y,
      P.inner_spectralIntegral hg ⟨x', hxg⟩ y, P.inner_spectralIntegral (hf.add hg) x' y,
      ← VectorMeasure.integral_add
        (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hxf y)
        (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hg hxg y)]

/-- **Difference extension law**: for measurable symbols `f, g : X → ℂ`,
`P.spectralIntegral (f - g)` extends `P.spectralIntegral f hf - P.spectralIntegral g hg` on the
intersection of their domains. -/
theorem sub_spectralIntegral_le (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) :
    P.spectralIntegral f hf - P.spectralIntegral g hg ≤
      P.spectralIntegral (f - g) (hf.sub hg) := by
  simpa only [sub_eq_add_neg, P.spectralIntegral_neg hg] using
    P.add_spectralIntegral_le hf hg.neg

/-- Perturbing an unbounded measurable symbol `f` by a bounded Borel symbol `g` preserves the
domain and gives the exact operator sum. -/
theorem spectralIntegral_add_boundedBorelFunction (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (g : BoundedBorelFunction X) :
    P.spectralIntegral (f + ⇑g) (hf.add g.measurable) =
      P.spectralIntegral f hf + P.spectralIntegral g g.measurable := by
  refine (LinearPMap.eq_of_le_of_domain_eq (P.add_spectralIntegral_le hf g.measurable)
    (le_antisymm (P.add_spectralIntegral_le hf g.measurable).1 ?_)).symm
  intro x hx
  have hxg : x ∈ (P.spectralIntegral g g.measurable).domain := by
    rw [P.spectralIntegral_boundedBorelFunction g]
    trivial
  refine ⟨?_, hxg⟩
  change x ∈ (P.spectralIntegral f hf).domain
  rw [P.mem_spectralIntegral_domain_iff_memLp hf]
  have hsub := ((P.mem_spectralIntegral_domain_iff_memLp (hf.add g.measurable)).mp hx).sub
    ((P.mem_spectralIntegral_domain_iff_memLp g.measurable).mp hxg)
  simpa only [add_sub_cancel_right] using hsub

/-! ## Headline existence and uniqueness -/

/-- **Existence and uniqueness of the unbounded spectral integral**: for a projection-valued
measure `P` on `X` acting on a complex Hilbert space `H` and any measurable symbol `f : X → ℂ`,
there is a unique partial linear operator `T : H →ₗ.[ℂ] H` with the second-moment domain and
polarized-measure matrix elements of `f`; moreover `T` is densely defined and closed, satisfies the
second-moment norm identity, and its Hilbert-space adjoint has the same domain and the matrix
elements of `star ∘ f`. -/
theorem existsUnique_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    ∃! T : H →ₗ.[ℂ] H,
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (∀ x : T.domain, ‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) ∧
      T.adjoint.domain = T.domain ∧
      (∀ (x : T.adjoint.domain) (y : H),
        ⟪y, T.adjoint x⟫_ℂ =
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  refine ⟨P.spectralIntegral f hf,
    ⟨fun _ => P.mem_spectralIntegral_domain_iff hf,
      P.inner_spectralIntegral hf,
      P.dense_spectralIntegral_domain hf,
      P.isClosed_spectralIntegral hf,
      P.norm_sq_spectralIntegral hf,
      P.adjoint_spectralIntegral_domain hf,
      P.inner_adjoint_spectralIntegral hf⟩, ?_⟩
  rintro T ⟨hdom, hinner, -, -, -, -, -⟩
  exact P.eq_spectralIntegral_of_domain_of_inner hf T hdom hinner

end ProjValMeasure
end TauCeti
