/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.DominatedConvergence
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# The unbounded Borel spectral integral of a projection-valued measure

Let `P` be a projection-valued measure on a measurable space `X` acting on a complex Hilbert space
`H`, and let `f : X → ℂ` be a measurable symbol. When `f` is unbounded, the spectral integral
`∫ f dP` cannot be defined everywhere on `H`; its natural domain is the second-moment subspace

`P.spectralIntegralDomain f = {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`,

equivalently `{x : H | MemLp f 2 (P.diag x)}`.

Truncating `f` to the measurable sublevel sets `{t | ‖f t‖ ≤ n}` produces bounded Borel symbols
whose spectral integrals form a Cauchy sequence at every `x` in the second-moment domain; their
strong limit defines the partial linear operator `P.spectralIntegral f hf : H →ₗ.[ℂ] H`.

Passing to the limit in the bounded Borel calculus yields the fundamental properties of the
unbounded spectral integral without separability or topological assumptions on `X`:

* **Matrix elements and uniqueness** (`inner_spectralIntegral`, `eq_spectralIntegral_iff`):
  for `x` in the domain and `y : H`,
  `⟪y, P.spectralIntegral f hf x⟫_ℂ = ∫ᵛ t, f t ∂[mul ℝ ℂ; P.polarizedComplexMeasure y x]`,
  and these matrix elements together with the second-moment domain determine the operator uniquely.
* **Isometry on each spectral measure** (`norm_sq_spectralIntegral`, `enorm_sq_spectralIntegral`):
  `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`.
* **Compatibility with the bounded calculus** (`spectralIntegral_boundedBorelFunction`): for a
  bounded Borel symbol `f`, `P.spectralIntegral f f.measurable = (P.integral f).toPMap ⊤`.
* **Almost-everywhere exactness** (`spectralIntegral_eq_spectralIntegral_iff`):
  `P.spectralIntegral f hf = P.spectralIntegral g hg ↔ f =ᶠ[P.ae] g`.
* **Dense domain, Hilbert adjoint, closedness, and core** (`dense_spectralIntegral_domain`,
  `adjoint_spectralIntegral`, `isClosed_spectralIntegral`, `hasCore_spectralIntegral`): the domain
  is dense, `(P.spectralIntegral f hf)† = P.spectralIntegral (star f) _`, the operator is closed
  and normal (`adjoint_spectralIntegral_domain`, `norm_adjoint_spectralIntegral`), and the supremum
  of the bounded spectral subspaces `range (P.proj {t | ‖f t‖ ≤ n} _)` is a graph core.
* **Self-adjointness and positivity** (`isSelfAdjoint_spectralIntegral_iff`,
  `re_inner_self_spectralIntegral_nonneg`): `P.spectralIntegral f hf` is self-adjoint if and only
  if `f` is `P`-almost everywhere real-valued, and `P`-almost everywhere nonnegative real part
  gives a nonnegative quadratic form.

## Main declarations

* `TauCeti.ProjValMeasure.spectralIntegralDomain`: the second-moment domain submodule.
* `TauCeti.ProjValMeasure.spectralIntegral`: the unbounded Borel spectral integral `H →ₗ.[ℂ] H`.
* `TauCeti.ProjValMeasure.adjoint_spectralIntegral`: `(P.spectralIntegral f hf)†` is the spectral
  integral of `star f`.
* `TauCeti.ProjValMeasure.hasCore_spectralIntegral`: the supremum of
  `range (P.proj {t | ‖f t‖ ≤ n} _)` is a core for `P.spectralIntegral f hf`.
* `TauCeti.ProjValMeasure.isSelfAdjoint_spectralIntegral_iff`: characterization of self-adjoint
  spectral integrals by `P.ae` real-valuedness.
* `TauCeti.ProjValMeasure.existsUnique_spectralIntegral`: combined existence, uniqueness,
  closedness, density, norm, and adjoint theorem for the unbounded spectral integral.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS Graduate Studies in Mathematics 99,
  2009, §3.1, Theorem 3.2 and Lemma 3.5.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.3.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Second-moment domain -/

/-- The second-moment domain `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` of the unbounded spectral
integral of `f` against `P`, bundled as a submodule of `H`. -/
def spectralIntegralDomain (P : ProjValMeasure X H) (f : X → ℂ) : Submodule ℂ H where
  carrier := {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    refine (lintegral_mono' (P.diag_add_le x y) le_rfl).trans_lt ?_
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hx, ENNReal.mul_lt_top ENNReal.coe_lt_top hy⟩
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [P.diag_smul c x, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hx

/-- Membership in `P.spectralIntegralDomain f` is finiteness of the second spectral moment. -/
@[simp]
theorem mem_spectralIntegralDomain_iff (P : ProjValMeasure X H) (f : X → ℂ) (x : H) :
    x ∈ P.spectralIntegralDomain f ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  (Iff.rfl)

/-- Conjugating the symbol preserves the second-moment domain. -/
@[simp]
theorem spectralIntegralDomain_star (P : ProjValMeasure X H) (f : X → ℂ) :
    P.spectralIntegralDomain (star f) = P.spectralIntegralDomain f := by
  ext x
  simp [mem_spectralIntegralDomain_iff]

/-- Negating the symbol preserves the second-moment domain. -/
@[simp]
theorem spectralIntegralDomain_neg (P : ProjValMeasure X H) (f : X → ℂ) :
    P.spectralIntegralDomain (-f) = P.spectralIntegralDomain f := by
  ext x
  simp [mem_spectralIntegralDomain_iff]

private theorem integrable_norm_sq_diag_iff_mem_spectralIntegralDomain (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) (x : H) :
    Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) ↔ x ∈ P.spectralIntegralDomain f := by
  rw [Integrable, and_iff_right (hf.norm.pow_const 2).aestronglyMeasurable, hasFiniteIntegral_def]
  simp_rw [Real.eNorm_of_nonneg (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-! ## Construction of the unbounded spectral integral -/

/-- The `n`-th bounded Borel truncation of a measurable symbol `f`, equal to `f` where `‖f t‖ ≤ n`
and `0` elsewhere. -/
private def spectralCutoff (f : X → ℂ) (hf : Measurable f) (n : ℕ) : BoundedBorelFunction X :=
  BoundedBorelFunction.ofFunction ({t : X | ‖f t‖ ≤ n}.indicator f)
    (hf.indicator (measurableSet_le hf.norm measurable_const))
    ⟨n, Nat.cast_nonneg n, fun t => by by_cases ht : ‖f t‖ ≤ n <;> simp [ht]⟩

private theorem spectralCutoff_apply (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    spectralCutoff f hf n t = ({t : X | ‖f t‖ ≤ n}).indicator f t := by
  simp [spectralCutoff]

private theorem norm_spectralCutoff_le_self (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    ‖spectralCutoff f hf n t‖ ≤ ‖f t‖ := by
  rw [spectralCutoff_apply]
  exact norm_indicator_le_norm_self f t

private theorem eNorm_spectralCutoff_le_self (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    ‖spectralCutoff f hf n t‖ₑ ≤ ‖f t‖ₑ := by
  by_cases ht : ‖f t‖ ≤ n <;> simp [spectralCutoff_apply, ht]

private theorem star_spectralCutoff (f : X → ℂ) (hf : Measurable f) (n : ℕ) :
    star (spectralCutoff f hf n) =
      spectralCutoff (star f) (continuous_star.measurable.comp hf) n := by
  ext t
  by_cases ht : ‖f t‖ ≤ n <;> simp [spectralCutoff_apply, ht]

private theorem tendsto_spectralCutoff (f : X → ℂ) (hf : Measurable f) (t : X) :
    Tendsto (fun n => spectralCutoff f hf n t) atTop (𝓝 (f t)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖f t‖⌉₊] with n hn
  have ht : ‖f t‖ ≤ n := (Nat.le_ceil ‖f t‖).trans (Nat.cast_le.2 hn)
  simp [spectralCutoff_apply, ht]

/-- Tail-integral upper bound on the difference of two bounded cutoff integrals. -/
private theorem norm_sq_integral_spectralCutoff_sub_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x))
    {N k : ℕ} (hk : N ≤ k) :
    ‖P.integral (spectralCutoff f hf k) x - P.integral (spectralCutoff f hf N) x‖ ^ 2 ≤
      ∫ t, ({t : X | (N : ℝ) < ‖f t‖}).indicator (fun t => ‖f t‖ ^ 2) t ∂(P.diag x) := by
  have hpt (t : X) :
      ‖(spectralCutoff f hf k - spectralCutoff f hf N) t‖ ^ 2 ≤
        ({t : X | (N : ℝ) < ‖f t‖}).indicator (fun t => ‖f t‖ ^ 2) t := by
    rw [BoundedBorelFunction.sub_apply]
    by_cases hNt : ‖f t‖ ≤ N
    · have hkt : ‖f t‖ ≤ k := hNt.trans (Nat.cast_le.2 hk)
      have hnot : ¬(N : ℝ) < ‖f t‖ := not_lt.2 hNt
      simp [spectralCutoff_apply, hNt, hkt, hnot]
    · have hlt : (N : ℝ) < ‖f t‖ := lt_of_not_ge hNt
      by_cases hkt : ‖f t‖ ≤ k <;> simp [spectralCutoff_apply, hNt, hkt, hlt]
  have hsub_int : Integrable
      (fun t => ‖(spectralCutoff f hf k - spectralCutoff f hf N) t‖ ^ 2) (P.diag x) :=
    .of_bound (((spectralCutoff f hf k - spectralCutoff f hf N).measurable.norm.pow_const
        2).aestronglyMeasurable)
      (‖spectralCutoff f hf k - spectralCutoff f hf N‖ ^ 2)
      (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((spectralCutoff f hf k - spectralCutoff f hf N).norm_coe_le_norm t) 2)
  rw [← _root_.sub_apply, ← map_sub, P.norm_sq_integral_apply]
  exact integral_mono hsub_int (hint.indicator (measurableSet_lt measurable_const hf.norm)) hpt

/-- For `x ∈ P.spectralIntegralDomain f`, the bounded cutoff integrals
`P.integral (spectralCutoff f hf n) x` form a Cauchy sequence in `H`. -/
private theorem cauchySeq_integral_spectralCutoff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ P.spectralIntegralDomain f) :
    CauchySeq (fun n => P.integral (spectralCutoff f hf n) x) := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.integrable_norm_sq_diag_iff_mem_spectralIntegralDomain hf x).2 hx
  let tail : ℕ → X → ℝ := fun N => ({t : X | (N : ℝ) < ‖f t‖}).indicator (fun t => ‖f t‖ ^ 2)
  have htail_tendsto : Tendsto (fun N => ∫ t, tail N t ∂(P.diag x)) atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (fun t => ‖f t‖ ^ 2)
      (fun N => ((hf.norm.pow_const 2).indicator
        (measurableSet_lt measurable_const hf.norm)).aestronglyMeasurable) hint
      (fun N => Eventually.of_forall fun t => by
        by_cases ht : (N : ℝ) < ‖f t‖ <;> simp [ht])
      (Eventually.of_forall fun t => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈‖f t‖⌉₊] with N hN
        have hnot : ¬(N : ℝ) < ‖f t‖ := not_lt.2 ((Nat.le_ceil ‖f t‖).trans (Nat.cast_le.2 hN))
        simp [hnot])
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (tendsto_order.1 htail_tendsto).2 ((ε / 2) ^ 2) (by positivity)
    |>.exists_forall_of_atTop
  refine ⟨N, fun m hm n hn => ?_⟩
  have hstep (k : ℕ) (hk : N ≤ k) :
      dist (P.integral (spectralCutoff f hf k) x) (P.integral (spectralCutoff f hf N) x) <
        ε / 2 := by
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity)
      ((P.norm_sq_integral_spectralCutoff_sub_le hf hint hk).trans_lt (hN N le_rfl))
  calc
    dist (P.integral (spectralCutoff f hf m) x) (P.integral (spectralCutoff f hf n) x)
        ≤ dist (P.integral (spectralCutoff f hf m) x) (P.integral (spectralCutoff f hf N) x) +
          dist (P.integral (spectralCutoff f hf N) x) (P.integral (spectralCutoff f hf n) x) :=
      dist_triangle _ _ _
    _ = dist (P.integral (spectralCutoff f hf m) x) (P.integral (spectralCutoff f hf N) x) +
          dist (P.integral (spectralCutoff f hf n) x) (P.integral (spectralCutoff f hf N) x) := by
      rw [dist_comm (P.integral (spectralCutoff f hf N) x)]
    _ < ε / 2 + ε / 2 := add_lt_add (hstep m hm) (hstep n hn)
    _ = ε := add_halves ε

private theorem exists_tendsto_integral_spectralCutoff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : P.spectralIntegralDomain f) :
    ∃ w : H, Tendsto (fun n => P.integral (spectralCutoff f hf n) (x : H)) atTop (𝓝 w) :=
  cauchySeq_tendsto_of_complete (P.cauchySeq_integral_spectralCutoff hf x.2)

/-- The linear map on `P.spectralIntegralDomain f` sending `x` to the strong limit of the bounded
cutoff integrals `P.integral (spectralCutoff f hf n) x`. -/
private def spectralIntegralLinearMap (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    P.spectralIntegralDomain f →ₗ[ℂ] H where
  toFun x := (P.exists_tendsto_integral_spectralCutoff hf x).choose
  map_add' x y := by
    refine tendsto_nhds_unique (P.exists_tendsto_integral_spectralCutoff hf (x + y)).choose_spec ?_
    simpa only [Submodule.coe_add, map_add] using
      (P.exists_tendsto_integral_spectralCutoff hf x).choose_spec.add
        (P.exists_tendsto_integral_spectralCutoff hf y).choose_spec
  map_smul' c x := by
    refine tendsto_nhds_unique (P.exists_tendsto_integral_spectralCutoff hf (c • x)).choose_spec ?_
    simpa only [Submodule.coe_smul_of_tower, map_smul, RingHom.id_apply] using
      (P.exists_tendsto_integral_spectralCutoff hf x).choose_spec.const_smul c

/-- The **unbounded Borel spectral integral** `∫ f dP` of a measurable symbol `f : X → ℂ` against a
projection-valued measure `P`, defined as a partial linear operator on the second-moment domain
`P.spectralIntegralDomain f`. -/
def spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) : H →ₗ.[ℂ] H where
  domain := P.spectralIntegralDomain f
  toFun := P.spectralIntegralLinearMap f hf

/-- The domain of `P.spectralIntegral f hf` is `P.spectralIntegralDomain f`. -/
@[simp]
theorem spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).domain = P.spectralIntegralDomain f :=
  (rfl)

/-- Membership in the domain of `P.spectralIntegral f hf` is finiteness of the second spectral
moment. -/
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ := by
  rw [spectralIntegral_domain, mem_spectralIntegralDomain_iff]

/-- For a measurable symbol `f`, `x` lies in `(P.spectralIntegral f hf).domain` iff
`f ∈ L²(P.diag x)`. -/
theorem mem_spectralIntegral_domain_iff_memLp (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ MemLp f 2 (P.diag x) := by
  rw [P.mem_spectralIntegral_domain_iff hf, memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  simp

/-- `t ↦ ‖f t‖ ^ 2` is Bochner-integrable against `P.diag x` iff
`x ∈ (P.spectralIntegral f hf).domain`. -/
theorem integrable_norm_sq_diag_iff_mem_spectralIntegral_domain (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) (x : H) :
    Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) ↔ x ∈ (P.spectralIntegral f hf).domain := by
  rw [spectralIntegral_domain, P.integrable_norm_sq_diag_iff_mem_spectralIntegralDomain hf]

/-- Every vector `x ∈ (P.spectralIntegral f hf).domain` makes `f` integrable against `P.diag x`. -/
theorem integrable_diag_of_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    Integrable f (P.diag x) := by
  have hint := P.integrable_polarizedComplexMeasure_of_lintegral_sq_lt_top x x hf
    ((P.mem_spectralIntegral_domain_iff hf x).1 hx)
  rwa [VectorMeasure.Integrable, P.variation_polarizedComplexMeasure_self] at hint

/-- Every spectral projection preserves `(P.spectralIntegral f hf).domain`. -/
theorem proj_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_proj B hB x]
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt
    ((P.mem_spectralIntegral_domain_iff hf x).1 hx)

/-- If `f` is bounded on a measurable set `B`, then `P.proj B hB ξ` lies in
`(P.spectralIntegral f hf).domain` for every `ξ : H`. -/
theorem proj_mem_spectralIntegral_domain_of_norm_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {R : ℝ} (hfB : ∀ t ∈ B, ‖f t‖ ≤ R)
    (ξ : H) :
    P.proj B hB ξ ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_proj B hB ξ]
  have hle : ∫⁻ t in B, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) ≤
      ∫⁻ _ in B, ENNReal.ofReal (max R 0) ^ 2 ∂(P.diag ξ) := by
    refine setLIntegral_mono' hB fun t ht => ?_
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hfB t ht).trans (le_max_left R 0))
  refine hle.trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

/-- Projections onto `{t | ‖f t‖ ≤ n}` map every vector into `(P.spectralIntegral f hf).domain`. -/
theorem proj_mem_spectralIntegral_domain_le_norm (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (n : ℕ) (ξ : H) :
    P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) ξ ∈
      (P.spectralIntegral f hf).domain :=
  P.proj_mem_spectralIntegral_domain_of_norm_le hf (measurableSet_le hf.norm measurable_const)
    (fun _ ht => ht) ξ

/-- The spectral projections `P({t | ‖f t‖ ≤ n})` converge strongly to the identity as `n → ∞`. -/
theorem tendsto_proj_le_norm (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) (ξ : H) :
    Tendsto (fun n : ℕ =>
      P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) ξ) atTop (𝓝 ξ) := by
  have h := P.tendsto_integral_apply_filter_of_dominated_convergence (l := atTop)
    (F := fun n : ℕ => BoundedBorelFunction.indicator {t | ‖f t‖ ≤ n}
      (measurableSet_le hf.norm measurable_const) 1)
    (f := 1) (M := 1)
    (Eventually.of_forall fun n => Eventually.of_forall fun t => by
      by_cases ht : ‖f t‖ ≤ n <;> simp [ht])
    (Eventually.of_forall fun t => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖f t‖⌉₊] with n hn
      have ht : ‖f t‖ ≤ n := (Nat.le_ceil ‖f t‖).trans (Nat.cast_le.2 hn)
      simp [ht])
    ξ
  simpa [P.integral_indicator, map_one] using h

private theorem tendsto_integral_spectralCutoff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n => P.integral (spectralCutoff f hf n) (x : H)) atTop
      (𝓝 (P.spectralIntegral f hf x)) :=
  (P.exists_tendsto_integral_spectralCutoff hf x).choose_spec

/-! ## Matrix elements, uniqueness, and norm -/

/-- **Matrix elements of the unbounded spectral integral.** For `x` in the second-moment domain and
any `y : H`, `⟪y, P.spectralIntegral f hf x⟫_ℂ` is the integral of `f` against the polarized
complex measure `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    ⟪y, P.spectralIntegral f hf x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hint := P.integrable_polarizedComplexMeasure_of_lintegral_sq_lt_top y x hf x.2
  have hinner : Tendsto (fun n => ⟪y, P.integral (spectralCutoff f hf n) (x : H)⟫_ℂ) atTop
      (𝓝 ⟪y, P.spectralIntegral f hf x⟫_ℂ) :=
    ((innerSL ℂ y).continuous.tendsto _).comp (P.tendsto_integral_spectralCutoff hf x)
  refine tendsto_nhds_unique hinner ?_
  simp_rw [← P.integral_polarizedComplexMeasure_eq_inner_integral]
  exact VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
    (fun n => (spectralCutoff f hf n).measurable.aestronglyMeasurable)
    hint.norm
    (fun n => Eventually.of_forall (norm_spectralCutoff_le_self f hf n))
    (Eventually.of_forall (tendsto_spectralCutoff f hf))

/-- Diagonal matrix elements of `P.spectralIntegral f hf` are Bochner integrals against `P.diag x`.
-/
theorem inner_self_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ⟪(x : H), P.spectralIntegral f hf x⟫_ℂ = ∫ t, f t ∂(P.diag x) := by
  rw [P.inner_spectralIntegral hf x x, P.integral_polarizedComplexMeasure_self]

/-- **Uniqueness characterization of the unbounded spectral integral**: a partial linear map `T`
equals `P.spectralIntegral f hf` if and only if its domain is the second-moment subspace and its
matrix elements are given by scalar integration against the polarized complex measures. -/
theorem eq_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {T : H →ₗ.[ℂ] H} :
    T = P.spectralIntegral f hf ↔
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ =
          ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  constructor
  · rintro rfl
    exact ⟨P.mem_spectralIntegral_domain_iff hf, P.inner_spectralIntegral hf⟩
  · rintro ⟨hdom, hinner⟩
    refine LinearPMap.ext (Submodule.ext hdom) fun x hxT hxS => ?_
    refine ext_inner_left ℂ fun y => ?_
    rw [hinner ⟨x, hxT⟩ y, (P.inner_spectralIntegral hf ⟨x, hxS⟩ y).symm]

/-- **Isometry identity** for the unbounded spectral integral:
`‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. -/
theorem norm_sq_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.integrable_norm_sq_diag_iff_mem_spectralIntegral_domain hf x).2 x.2
  have hnorm : Tendsto (fun n => ‖P.integral (spectralCutoff f hf n) (x : H)‖ ^ 2) atTop
      (𝓝 (‖P.spectralIntegral f hf x‖ ^ 2)) :=
    ((P.tendsto_integral_spectralCutoff hf x).norm).pow 2
  refine tendsto_nhds_unique hnorm ?_
  simp_rw [P.norm_sq_integral_apply]
  exact tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
    (fun n => ((spectralCutoff f hf n).measurable.norm.pow_const 2).aestronglyMeasurable)
    hint
    (fun n => Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_spectralCutoff_le_self f hf n t) 2)
    (Eventually.of_forall fun t => ((tendsto_spectralCutoff f hf t).norm).pow 2)

/-- Extended-norm form of `norm_sq_spectralIntegral`. -/
theorem enorm_sq_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
  have hsq : ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(P.diag x) = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), P.norm_sq_spectralIntegral hf x,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      (hf.norm.pow_const 2).aestronglyMeasurable,
    hsq, ENNReal.ofReal_toReal x.2.ne]

/-! ## Compatibility with projections and bounded symbols -/

/-- Spectral projections commute with the unbounded spectral integral on its domain. -/
theorem spectralIntegral_proj (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf hB x.2⟩ =
      P.proj B hB (P.spectralIntegral f hf x) := by
  have hcomm (n : ℕ) :
      P.integral (spectralCutoff f hf n) (P.proj B hB x) =
        P.proj B hB (P.integral (spectralCutoff f hf n) x) := by
    rw [← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul,
      mul_comm (spectralCutoff f hf n), map_mul, mul_apply_eq_comp]
  refine tendsto_nhds_unique
    (P.tendsto_integral_spectralCutoff hf ⟨P.proj B hB x, _⟩) ?_
  simpa only [Function.comp_def, hcomm] using
    ((P.proj B hB).continuous.tendsto _).comp (P.tendsto_integral_spectralCutoff hf x)

/-- On a measurable set `B` where `‖f‖ ≤ R`, applying `P.spectralIntegral f hf` to `P.proj B hB ξ`
coincides with the bounded spectral integral of `B.indicator f` applied to `ξ`. -/
theorem spectralIntegral_proj_of_norm_le (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) {R : ℝ} (hR : 0 ≤ R) (hfB : ∀ t ∈ B, ‖f t‖ ≤ R) (ξ : H) :
    P.spectralIntegral f hf
        ⟨P.proj B hB ξ, P.proj_mem_spectralIntegral_domain_of_norm_le hf hB hfB ξ⟩ =
      P.integral (BoundedBorelFunction.ofFunction (B.indicator f) (hf.indicator hB)
        ⟨R, hR, fun t => by
          by_cases ht : t ∈ B
          · simpa [Set.indicator_of_mem ht] using hfB t ht
          · simp [Set.indicator_of_notMem ht, hR]⟩) ξ := by
  let g : BoundedBorelFunction X :=
    BoundedBorelFunction.ofFunction (B.indicator f) (hf.indicator hB)
      ⟨R, hR, fun t => by
        by_cases ht : t ∈ B
        · simpa [Set.indicator_of_mem ht] using hfB t ht
        · simp [Set.indicator_of_notMem ht, hR]⟩
  refine tendsto_nhds_unique
    (P.tendsto_integral_spectralCutoff hf ⟨P.proj B hB ξ, _⟩) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈R⌉₊] with n hn
  have hmul : spectralCutoff f hf n * BoundedBorelFunction.indicator B hB 1 = g := by
    ext t
    by_cases ht : t ∈ B
    · have hfn : ‖f t‖ ≤ n :=
        (hfB t ht).trans ((Nat.le_ceil R).trans (Nat.cast_le.2 hn))
      simp [g, spectralCutoff_apply, ht, hfn]
    · simp [g, spectralCutoff_apply, ht]
  rw [← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul, hmul]

private theorem spectralIntegral_proj_le_norm (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (n : ℕ) (ξ : H) :
    P.spectralIntegral f hf
        ⟨P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) ξ,
          P.proj_mem_spectralIntegral_domain_le_norm hf n ξ⟩ =
      P.integral (spectralCutoff f hf n) ξ :=
  P.spectralIntegral_proj_of_norm_le hf (measurableSet_le hf.norm measurable_const)
    (Nat.cast_nonneg n) (fun _ ht => ht) ξ

/-- On `x ∈ (P.spectralIntegral f hf).domain`, applying `P.spectralIntegral f hf` to the
truncated vectors `P({t | ‖f t‖ ≤ n}) x` converges in norm to `P.spectralIntegral f hf x`. -/
theorem tendsto_spectralIntegral_proj_le_norm (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n : ℕ => P.spectralIntegral f hf
      ⟨P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) x,
        P.proj_mem_spectralIntegral_domain_le_norm hf n x⟩)
      atTop (𝓝 (P.spectralIntegral f hf x)) := by
  simpa only [P.spectralIntegral_proj_le_norm hf] using
    P.tendsto_integral_spectralCutoff hf x

/-- **Compatibility with the bounded Borel calculus**: for a bounded Borel symbol `f`, the
unbounded spectral integral has domain `⊤` and agrees with `P.integral f`. -/
theorem spectralIntegral_boundedBorelFunction (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) :
    P.spectralIntegral f f.measurable = (P.integral f : H →ₗ[ℂ] H).toPMap ⊤ := by
  symm
  refine (P.eq_spectralIntegral_iff f.measurable).2 ⟨fun x => ?_, fun x y => ?_⟩
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff]
    have hle : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) ≤ ∫⁻ _, ENNReal.ofReal ‖f‖ ^ 2 ∂(P.diag x) := by
      refine lintegral_mono fun t => ?_
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (f.norm_coe_le_norm t)
    refine hle.trans_lt ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)
  · have heq : ((P.integral f : H →ₗ[ℂ] H).toPMap ⊤) x = P.integral f x :=
      LinearMap.toPMap_apply (P.integral f : H →ₗ[ℂ] H) ⊤ ⟨x, Submodule.mem_top⟩
    rw [heq]
    exact (P.integral_polarizedComplexMeasure_eq_inner_integral f y x).symm

private theorem enorm_sq_integral_apply (P : ProjValMeasure X H) (f : BoundedBorelFunction X)
    (ξ : H) :
    ‖P.integral f ξ‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) := by
  have hmem : ξ ∈ (P.spectralIntegral f f.measurable).domain := by
    rw [P.spectralIntegral_boundedBorelFunction f, LinearMap.toPMap_domain]
    exact Submodule.mem_top
  have heq : P.spectralIntegral f f.measurable ⟨ξ, hmem⟩ = P.integral f ξ :=
    (LinearPMap.congr_fun (P.spectralIntegral_boundedBorelFunction f) hmem Submodule.mem_top).trans
      (LinearMap.toPMap_apply (P.integral f : H →ₗ[ℂ] H) ⊤ ⟨ξ, Submodule.mem_top⟩)
  rw [← heq, P.enorm_sq_spectralIntegral f.measurable]

/-! ## Almost-everywhere exactness and algebraic laws -/

/-- Symbols agreeing `P`-almost everywhere have equal unbounded spectral integrals. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) (hfg : f =ᶠ[P.ae] g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg := by
  refine (P.eq_spectralIntegral_iff hg).2 ⟨fun x => ?_, fun x y => ?_⟩
  · rw [P.mem_spectralIntegral_domain_iff hf,
      lintegral_congr_ae ((P.ae_diag_of_ae x hfg).mono fun t ht => by rw [ht])]
  · rw [P.inner_spectralIntegral hf x y]
    exact VectorMeasure.integral_congr_ae
      (P.ae_variation_polarizedComplexMeasure_of_ae y x hfg)

/-- **Exactness of the unbounded spectral integral**: two measurable symbols have the same spectral
integral against `P` if and only if they agree `P`-almost everywhere. -/
theorem spectralIntegral_eq_spectralIntegral_iff (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg ↔ f =ᶠ[P.ae] g := by
  refine ⟨fun h => ?_, P.spectralIntegral_congr_ae hf hg⟩
  let B : ℕ → Set X := fun n => {t | ‖f t‖ ≤ n} ∩ {t | ‖g t‖ ≤ n}
  have hB (n : ℕ) : MeasurableSet (B n) :=
    (measurableSet_le hf.norm measurable_const).inter (measurableSet_le hg.norm measurable_const)
  have hn (n : ℕ) : ∀ᶠ t in P.ae, (B n).indicator f t = (B n).indicator g t := by
    let fb : BoundedBorelFunction X :=
      BoundedBorelFunction.ofFunction ((B n).indicator f) (hf.indicator (hB n))
        ⟨n, Nat.cast_nonneg n, fun t => by
          by_cases ht : t ∈ B n
          · simpa [Set.indicator_of_mem ht] using ht.1
          · simp [Set.indicator_of_notMem ht]⟩
    let gb : BoundedBorelFunction X :=
      BoundedBorelFunction.ofFunction ((B n).indicator g) (hg.indicator (hB n))
        ⟨n, Nat.cast_nonneg n, fun t => by
          by_cases ht : t ∈ B n
          · simpa [Set.indicator_of_mem ht] using ht.2
          · simp [Set.indicator_of_notMem ht]⟩
    have hint : P.integral fb = P.integral gb := by
      ext ξ
      have hfξ := P.spectralIntegral_proj_of_norm_le hf (hB n) (Nat.cast_nonneg n)
        (fun _ ht => ht.1) ξ
      have hgξ := P.spectralIntegral_proj_of_norm_le hg (hB n) (Nat.cast_nonneg n)
        (fun _ ht => ht.2) ξ
      exact hfξ.symm.trans ((LinearPMap.congr_fun h _ _).trans hgξ)
    exact ((P.integral_eq_integral_iff fb gb).1 hint).mono fun t ht => by simpa [fb, gb] using ht
  rw [EventuallyEq, P.eventually_ae_iff]
  intro ξ
  filter_upwards [ae_all_iff.2 fun n => P.ae_diag_of_ae ξ (hn n)] with t ht
  let N : ℕ := max ⌈‖f t‖⌉₊ ⌈‖g t‖⌉₊
  have htN : t ∈ B N :=
    ⟨(Nat.le_ceil ‖f t‖).trans (Nat.cast_le.2 (le_max_left _ _)),
      (Nat.le_ceil ‖g t‖).trans (Nat.cast_le.2 (le_max_right _ _))⟩
  simpa [Set.indicator_of_mem htN] using ht N

/-- The spectral integral of `0` is `0` (with domain `⊤`). -/
@[simp]
theorem spectralIntegral_zero (P : ProjValMeasure X H)
    (h0 : Measurable (0 : X → ℂ) := measurable_const) :
    P.spectralIntegral 0 h0 = 0 := by
  symm
  refine (P.eq_spectralIntegral_iff h0).2 ⟨fun x => ?_, fun x y => ?_⟩
  · simp [LinearPMap.zero_domain]
  · simp

/-- The spectral integral of `1` is the identity `(1 : H →ₗ[ℂ] H)` on `⊤`. -/
theorem spectralIntegral_one (P : ProjValMeasure X H)
    (h1 : Measurable (1 : X → ℂ) := measurable_const) :
    P.spectralIntegral 1 h1 = (1 : H →ₗ[ℂ] H).toPMap ⊤ := by
  simpa [map_one] using P.spectralIntegral_boundedBorelFunction 1

/-- The spectral integral of a constant `c` is `c • 1` on `⊤`. -/
theorem spectralIntegral_const (P : ProjValMeasure X H) (c : ℂ)
    (hc : Measurable (fun _ : X => c) := measurable_const) :
    P.spectralIntegral (fun _ => c) hc =
      (c • (1 : H →ₗ[ℂ] H)).toPMap ⊤ := by
  have hrhs : (P.integral (algebraMap ℂ (BoundedBorelFunction X) c) : H →ₗ[ℂ] H) = c • 1 := by
    rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]
  simpa only [hrhs, BoundedBorelFunction.coe_algebraMap] using
    P.spectralIntegral_boundedBorelFunction (algebraMap ℂ (BoundedBorelFunction X) c)

/-- Negating the symbol negates the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_neg (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (-f) hf.neg = -P.spectralIntegral f hf := by
  symm
  refine (P.eq_spectralIntegral_iff hf.neg).2 ⟨fun x => ?_, fun x y => ?_⟩
  · rw [LinearPMap.neg_domain, P.mem_spectralIntegral_domain_iff hf]
    simp
  · rw [LinearPMap.neg_apply, inner_neg_right, P.inner_spectralIntegral hf x y,
      ← VectorMeasure.integral_neg]

/-- Scalar multiplication satisfies `c • f[P] ≤ (c • f)[P]` for all `c : ℂ` (at `c = 0`, the right
side has domain `⊤` while the left side retains the domain of `f[P]`). -/
theorem smul_spectralIntegral_le (P : ProjValMeasure X H) (c : ℂ) {f : X → ℂ}
    (hf : Measurable f) :
    c • P.spectralIntegral f hf ≤ P.spectralIntegral (c • f) (hf.const_smul c) := by
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · rw [LinearPMap.smul_domain, P.mem_spectralIntegral_domain_iff hf] at hx
    rw [P.mem_spectralIntegral_domain_iff (hf.const_smul c)]
    have hle : ∫⁻ t, ‖(c • f) t‖ₑ ^ 2 ∂(P.diag x) = ‖c‖ₑ ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
      rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)]
      refine lintegral_congr fun t => ?_
      rw [Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow]
    rw [hle]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) hx
  · refine ext_inner_left ℂ fun z => ?_
    rw [LinearPMap.smul_apply, inner_smul_right, P.inner_spectralIntegral hf x z,
      P.inner_spectralIntegral (hf.const_smul c) y z, hxy]
    exact (VectorMeasure.integral_fun_smul_of_smul_left
      (fun a u v => by simp [mul_assoc]) c f).symm

/-- For `c ≠ 0`, `(c • f)[P] = c • f[P]` with equality of domains. -/
theorem spectralIntegral_smul (P : ProjValMeasure X H) {c : ℂ} (hc : c ≠ 0) {f : X → ℂ}
    (hf : Measurable f) :
    P.spectralIntegral (c • f) (hf.const_smul c) = c • P.spectralIntegral f hf := by
  refine (LinearPMap.eq_of_le_of_domain_eq (P.smul_spectralIntegral_le c hf) ?_).symm
  refine le_antisymm (P.smul_spectralIntegral_le c hf).1 fun x hx => ?_
  have hx' := (P.smul_spectralIntegral_le c⁻¹ (hf.const_smul c)).1 hx
  simpa [inv_smul_smul₀ hc] using hx'

/-- Addition of spectral integrals extends from the intersection of their domains:
`f[P] + g[P] ≤ (f + g)[P]`. -/
theorem add_spectralIntegral_le (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) :
    P.spectralIntegral f hf + P.spectralIntegral g hg ≤
      P.spectralIntegral (f + g) (hf.add hg) := by
  have hdom : (P.spectralIntegral f hf + P.spectralIntegral g hg).domain ≤
      (P.spectralIntegral (f + g) (hf.add hg)).domain := by
    intro x hx
    have hfx := (P.mem_spectralIntegral_domain_iff hf x).1 hx.1
    have hgx := (P.mem_spectralIntegral_domain_iff hg x).1 hx.2
    rw [P.mem_spectralIntegral_domain_iff (hf.add hg)]
    have hpt (t : X) : ‖(f + g) t‖ₑ ^ 2 ≤ 2 * ‖f t‖ₑ ^ 2 + 2 * ‖g t‖ₑ ^ 2 := by
      rw [Pi.add_apply, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      have hreal : ‖f t + g t‖ ^ 2 ≤ 2 * ‖f t‖ ^ 2 + 2 * ‖g t‖ ^ 2 := by
        have htri := norm_add_le (f t) (g t)
        nlinarith [sq_nonneg (‖f t‖ - ‖g t‖), norm_nonneg (f t + g t)]
      refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two,
        ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm, ofReal_norm, ENNReal.ofReal_ofNat]
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_add_left' ((hf.eNorm.pow_const 2).const_mul 2).aemeasurable,
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hfx, ENNReal.mul_lt_top ENNReal.ofNat_lt_top hgx⟩
  refine ⟨hdom, fun x y hxy => ?_⟩
  refine ext_inner_left ℂ fun z => ?_
  have hfx := (P.mem_spectralIntegral_domain_iff hf x).1 x.2.1
  have hgx := (P.mem_spectralIntegral_domain_iff hg x).1 x.2.2
  have hintf := P.integrable_polarizedComplexMeasure_of_lintegral_sq_lt_top z x hf hfx
  have hintg := P.integrable_polarizedComplexMeasure_of_lintegral_sq_lt_top z x hg hgx
  rw [LinearPMap.add_apply, inner_add_right, P.inner_spectralIntegral hf ⟨x, x.2.1⟩ z,
    P.inner_spectralIntegral hg ⟨x, x.2.2⟩ z, P.inner_spectralIntegral (hf.add hg) y z, ← hxy,
    ← VectorMeasure.integral_add hintf hintg]

/-- Subtraction of spectral integrals extends from the intersection of their domains:
`f[P] - g[P] ≤ (f - g)[P]`. -/
theorem sub_spectralIntegral_le (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) :
    P.spectralIntegral f hf - P.spectralIntegral g hg ≤
      P.spectralIntegral (f - g) (hf.sub hg) := by
  simpa only [sub_eq_add_neg, P.spectralIntegral_neg hg] using
    P.add_spectralIntegral_le hf hg.neg

/-- Adding a bounded Borel symbol `g` to `f` leaves the second-moment domain unchanged and acts as
the bounded perturbation `(P.integral g).toLinearMap +ᵥ P.spectralIntegral f hf`. -/
theorem spectralIntegral_vadd_boundedBorelFunction (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (⇑g + f) (g.measurable.add hf) =
      (P.integral g).toLinearMap +ᵥ P.spectralIntegral f hf := by
  have hgdom : (P.spectralIntegral g g.measurable).domain = ⊤ := by
    rw [P.spectralIntegral_boundedBorelFunction g, LinearMap.toPMap_domain]
  have hle : (P.integral g).toLinearMap +ᵥ P.spectralIntegral f hf ≤
      P.spectralIntegral (⇑g + f) (g.measurable.add hf) := by
    refine ⟨fun x hx => (P.add_spectralIntegral_le g.measurable hf).1
      ⟨hgdom.symm ▸ Submodule.mem_top, hx⟩, fun x y hxy => ?_⟩
    have hgx : (x : H) ∈ (P.spectralIntegral g g.measurable).domain :=
      hgdom.symm ▸ Submodule.mem_top
    have hadd := (P.add_spectralIntegral_le g.measurable hf).2
      (x := ⟨x, hgx, x.2⟩) (y := y) hxy
    rw [LinearPMap.add_apply] at hadd
    rw [LinearPMap.vadd_apply, ← hadd]
    congr 1
    exact (LinearPMap.congr_fun (P.spectralIntegral_boundedBorelFunction g) hgx
      Submodule.mem_top).symm
  refine (LinearPMap.eq_of_le_of_domain_eq hle ?_).symm
  refine le_antisymm hle.1 fun x hx => ?_
  have hgx : x ∈ (P.spectralIntegral ⇑(-g) (-g).measurable).domain := by
    rw [P.spectralIntegral_boundedBorelFunction (-g), LinearMap.toPMap_domain]
    exact Submodule.mem_top
  have hx' := (P.add_spectralIntegral_le (-g).measurable (g.measurable.add hf)).1 ⟨hgx, hx⟩
  rw [P.mem_spectralIntegral_domain_iff] at hx'
  rw [LinearPMap.vadd_domain, P.mem_spectralIntegral_domain_iff]
  simpa using hx'

/-! ## Dense domain, Hilbert adjoint, closedness, and truncation core -/

/-- The second-moment domain of `P.spectralIntegral f hf` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    Dense ((P.spectralIntegral f hf).domain : Set H) := fun ξ =>
  mem_closure_of_tendsto (P.tendsto_proj_le_norm hf ξ)
    (Eventually.of_forall fun n => P.proj_mem_spectralIntegral_domain_le_norm hf n ξ)

/-- `P.spectralIntegral (star f) _` is a formal adjoint of `P.spectralIntegral f hf`. -/
theorem isFormalAdjoint_spectralIntegral_star (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)).IsFormalAdjoint
      (P.spectralIntegral f hf) := by
  set hfs : Measurable (star f) := continuous_star.measurable.comp hf
  intro y x
  have hlhs : Tendsto (fun n => ⟪P.integral (spectralCutoff (star f) hfs n) (y : H), (x : H)⟫_ℂ)
      atTop (𝓝 ⟪P.spectralIntegral (star f) hfs y, (x : H)⟫_ℂ) :=
    ((P.tendsto_integral_spectralCutoff hfs y).inner tendsto_const_nhds)
  have hrhs : Tendsto (fun n => ⟪(y : H), P.integral (spectralCutoff f hf n) (x : H)⟫_ℂ)
      atTop (𝓝 ⟪(y : H), P.spectralIntegral f hf x⟫_ℂ) :=
    (tendsto_const_nhds.inner (P.tendsto_integral_spectralCutoff hf x))
  refine tendsto_nhds_unique hlhs (hrhs.congr fun n => ?_)
  rw [← star_spectralCutoff f hf n, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

private theorem integral_spectralCutoff_star_eq_proj_adjoint (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : (P.spectralIntegral f hf).adjoint.domain) (n : ℕ) :
    P.integral (spectralCutoff (star f) (continuous_star.measurable.comp hf) n) (y : H) =
      P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)
        ((P.spectralIntegral f hf).adjoint y) := by
  set hfs : Measurable (star f) := continuous_star.measurable.comp hf
  set W : Set X := {t | ‖f t‖ ≤ n}
  have hW : MeasurableSet W := measurableSet_le hf.norm measurable_const
  have hdense : Dense ((P.spectralIntegral f hf).domain : Set H) :=
    P.dense_spectralIntegral_domain hf
  refine ext_inner_right ℂ fun z => ?_
  have hz_mem : P.proj W hW z ∈ (P.spectralIntegral f hf).domain :=
    P.proj_mem_spectralIntegral_domain_le_norm hf n z
  calc
    ⟪P.integral (spectralCutoff (star f) hfs n) (y : H), z⟫_ℂ
        = ⟪(y : H), P.integral (spectralCutoff f hf n) z⟫_ℂ := by
          rw [← star_spectralCutoff f hf n, map_star, ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪(y : H), P.spectralIntegral f hf ⟨P.proj W hW z, hz_mem⟩⟫_ℂ := by
          rw [P.spectralIntegral_proj_le_norm hf n z]
    _ = ⟪(P.spectralIntegral f hf).adjoint y, P.proj W hW z⟫_ℂ :=
          (LinearPMap.adjoint_isFormalAdjoint hdense y ⟨P.proj W hW z, hz_mem⟩).symm
    _ = ⟪P.proj W hW ((P.spectralIntegral f hf).adjoint y), z⟫_ℂ :=
          ((P.isSelfAdjoint_proj W hW).isSymmetric _ z).symm

/-- **Hilbert adjoint of the unbounded spectral integral**: `(P.spectralIntegral f hf)†` equals
`P.spectralIntegral (star f) _`. -/
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf) := by
  set hfs : Measurable (star f) := continuous_star.measurable.comp hf
  set T := P.spectralIntegral f hf
  have hdense : Dense (T.domain : Set H) := P.dense_spectralIntegral_domain hf
  have hle : P.spectralIntegral (star f) hfs ≤ T.adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense (P.isFormalAdjoint_spectralIntegral_star hf).symm
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  set w : H := T.adjoint ⟨y, hy⟩
  have hbound (n : ℕ) :
      ∫⁻ t, ‖spectralCutoff (star f) hfs n t‖ₑ ^ 2 ∂(P.diag y) ≤ ‖w‖ₑ ^ 2 := by
    rw [← P.enorm_sq_integral_apply, P.integral_spectralCutoff_star_eq_proj_adjoint hf ⟨y, hy⟩ n]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (P.norm_proj_apply_le _ _ w)
  have hmono : Monotone (fun n t => ‖spectralCutoff (star f) hfs n t‖ₑ ^ 2) := by
    intro m n hmn t
    by_cases hmt : ‖f t‖ ≤ m
    · have hnt : ‖f t‖ ≤ n := hmt.trans (Nat.cast_le.2 hmn)
      simp [spectralCutoff_apply, hmt, hnt]
    · simp [spectralCutoff_apply, hmt]
  have hsup (t : X) : (⨆ n : ℕ, ‖spectralCutoff (star f) hfs n t‖ₑ ^ 2) = ‖star f t‖ₑ ^ 2 := by
    refine le_antisymm (iSup_le fun n => pow_le_pow_left'
      (eNorm_spectralCutoff_le_self (star f) hfs n t) 2) ?_
    have ht : ‖f t‖ ≤ ⌈‖f t‖⌉₊ := Nat.le_ceil _
    refine le_iSup_of_le ⌈‖f t‖⌉₊ ?_
    simp [spectralCutoff_apply, ht]
  rw [P.mem_spectralIntegral_domain_iff hfs]
  calc
    ∫⁻ t, ‖star f t‖ₑ ^ 2 ∂(P.diag y)
        = ∫⁻ t, (⨆ n : ℕ, ‖spectralCutoff (star f) hfs n t‖ₑ ^ 2) ∂(P.diag y) :=
          lintegral_congr fun t => (hsup t).symm
    _ = ⨆ n : ℕ, ∫⁻ t, ‖spectralCutoff (star f) hfs n t‖ₑ ^ 2 ∂(P.diag y) :=
          lintegral_iSup (fun n => (spectralCutoff (star f) hfs n).measurable.eNorm.pow_const 2)
            hmono
    _ ≤ ‖w‖ₑ ^ 2 := iSup_le hbound
    _ < ∞ := ENNReal.pow_lt_top eNorm_lt_top

/-- The unbounded spectral integral is a closed operator. -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).IsClosed := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have heq : P.spectralIntegral f hf = (P.spectralIntegral (star f) hfs).adjoint := by
    rw [P.adjoint_spectralIntegral hfs]
    congr! 1
    exact (star_star f).symm
  rw [heq]
  exact LinearPMap.adjoint_isClosed (P.dense_spectralIntegral_domain hfs)

/-- **Spectral truncation core**: the supremum of the ranges of the spectral projections
`P({t | ‖f t‖ ≤ n})` is a graph core for `P.spectralIntegral f hf`. -/
theorem hasCore_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, LinearMap.range
        (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) : H →ₗ[ℂ] H)) := by
  let S : Submodule ℂ H :=
    ⨆ n : ℕ, LinearMap.range
      (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) : H →ₗ[ℂ] H)
  have hS : S ≤ (P.spectralIntegral f hf).domain := by
    refine iSup_le fun n => ?_
    rintro _ ⟨ξ, rfl⟩
    exact P.proj_mem_spectralIntegral_domain_le_norm hf n ξ
  rw [(P.isClosed_spectralIntegral hf).hasCore_iff_graph_subset_closure hS]
  intro p hp
  obtain ⟨x, hx1, hx2⟩ := (P.spectralIntegral f hf).mem_graph_iff.1 hp
  have hp_eq : p = ((x : H), P.spectralIntegral f hf x) := Prod.ext hx1.symm hx2.symm
  rw [hp_eq]
  let u : ℕ → H := fun n =>
    P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) x
  have huS (n : ℕ) : u n ∈ S :=
    Submodule.mem_iSup_of_mem n (LinearMap.mem_range_self _ (x : H))
  have hu_lim : Tendsto u atTop (𝓝 (x : H)) :=
    P.tendsto_proj_le_norm hf x
  have hTu_lim :
      Tendsto (fun n => P.spectralIntegral f hf ⟨u n, hS (huS n)⟩) atTop
        (𝓝 (P.spectralIntegral f hf x)) :=
    P.tendsto_spectralIntegral_proj_le_norm hf x
  refine mem_closure_of_tendsto (hu_lim.prodMk_nhds hTu_lim) (Eventually.of_forall fun n => ?_)
  have hmem : u n ∈ S ⊓ (P.spectralIntegral f hf).domain := ⟨huS n, hS (huS n)⟩
  have heq : ((P.spectralIntegral f hf).domRestrict S) ⟨u n, hmem⟩ =
      P.spectralIntegral f hf ⟨u n, hS (huS n)⟩ :=
    LinearPMap.domRestrict_apply rfl
  rw [← heq]
  exact ((P.spectralIntegral f hf).domRestrict S).mem_graph ⟨u n, hmem⟩

/-! ## Normality, self-adjointness, positivity, and combined characterization -/

/-- The Hilbert adjoint of `P.spectralIntegral f hf` has the same domain as
`P.spectralIntegral f hf`. -/
@[simp]
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain = (P.spectralIntegral f hf).domain := by
  rw [P.adjoint_spectralIntegral hf, spectralIntegral_domain, spectralIntegral_domain,
    spectralIntegralDomain_star]

/-- **Normality of the unbounded spectral integral**: `‖(P.spectralIntegral f hf)† x‖` equals
`‖P.spectralIntegral f hf x‖` on their common domain. -/
theorem norm_adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖(P.spectralIntegral f hf).adjoint ⟨x, (P.adjoint_spectralIntegral_domain hf).symm ▸ x.2⟩‖ =
      ‖P.spectralIntegral f hf x‖ := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) hfs).domain := by
    rw [P.mem_spectralIntegral_domain_iff hfs]
    simpa using (P.mem_spectralIntegral_domain_iff hf x).1 x.2
  have heq := LinearPMap.congr_fun (P.adjoint_spectralIntegral hf)
    ((P.adjoint_spectralIntegral_domain hf).symm ▸ x.2) hx'
  rw [heq]
  have hsq : ‖P.spectralIntegral (star f) hfs ⟨x, hx'⟩‖ ^ 2 =
      ‖P.spectralIntegral f hf x‖ ^ 2 := by
    rw [P.norm_sq_spectralIntegral hfs ⟨x, hx'⟩, P.norm_sq_spectralIntegral hf x]
    simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- `P.spectralIntegral f hf` is self-adjoint if and only if `f` is `P`-almost everywhere equal to
its complex conjugate. -/
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔ ∀ᶠ t in P.ae, star (f t) = f t := by
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral hf,
    P.spectralIntegral_eq_spectralIntegral_iff]
  rfl

/-- The spectral integral of a real-valued measurable symbol `g : X → ℝ` is self-adjoint. -/
theorem isSelfAdjoint_spectralIntegral_ofReal (P : ProjValMeasure X H) {g : X → ℝ}
    (hg : Measurable g) :
    IsSelfAdjoint (P.spectralIntegral (fun t => (g t : ℂ)) (Complex.measurable_ofReal.comp hg)) :=
  (P.isSelfAdjoint_spectralIntegral_iff _).2 (Eventually.of_forall fun t => by simp)

/-- The real part of the quadratic form of `P.spectralIntegral f hf` is the integral of `(f t).re`
against `P.diag x`. -/
theorem re_inner_self_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    (⟪(x : H), P.spectralIntegral f hf x⟫_ℂ).re = ∫ t, (f t).re ∂(P.diag x) := by
  rw [P.inner_self_spectralIntegral hf x, ← RCLike.re_eq_complex_re,
    integral_re (P.integrable_diag_of_mem_spectralIntegral_domain hf x.2)]

/-- **Positivity**: if `(f t).re ≥ 0` holds `P`-almost everywhere, then the real part of the
quadratic form `⟪x, P.spectralIntegral f hf x⟫_ℂ` is nonnegative on the second-moment domain. -/
theorem re_inner_self_spectralIntegral_nonneg (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (hpos : ∀ᶠ t in P.ae, 0 ≤ (f t).re)
    (x : (P.spectralIntegral f hf).domain) :
    0 ≤ (⟪(x : H), P.spectralIntegral f hf x⟫_ℂ).re := by
  rw [P.re_inner_self_spectralIntegral hf x]
  exact integral_nonneg_of_ae (P.ae_diag_of_ae x hpos)

/-- **The unbounded Borel spectral integral**: for every projection-valued measure `P` on an
arbitrary measurable space `X` and every measurable symbol `f : X → ℂ`, there exists a unique
partial linear operator `T : H →ₗ.[ℂ] H` whose domain is the second-moment subspace and whose
matrix elements are the integrals of `f` against the polarized complex measures of `P`; moreover,
`T` is densely defined and closed, its squared norm is the second spectral moment, and its Hilbert
adjoint has the same domain and the matrix elements of `star ∘ f`. -/
theorem existsUnique_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    ∃! T : H →ₗ.[ℂ] H,
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ =
          ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (∀ x : T.domain, ‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) ∧
      T.adjoint.domain = T.domain ∧
      (∀ (x : T.adjoint.domain) (y : H),
        ⟪y, T.adjoint x⟫_ℂ =
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  refine ⟨P.spectralIntegral f hf,
    ⟨P.mem_spectralIntegral_domain_iff hf, P.inner_spectralIntegral hf,
      P.dense_spectralIntegral_domain hf, P.isClosed_spectralIntegral hf,
      P.norm_sq_spectralIntegral hf, P.adjoint_spectralIntegral_domain hf, ?_⟩,
    fun T hT => (P.eq_spectralIntegral_iff hf).2 ⟨hT.1, hT.2.1⟩⟩
  intro x y
  have hx_dom : (x : H) ∈ (P.spectralIntegral f hf).domain :=
    P.adjoint_spectralIntegral_domain hf ▸ x.2
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) hfs).domain := by
    rw [P.mem_spectralIntegral_domain_iff hfs]
    simpa using (P.mem_spectralIntegral_domain_iff hf x).1 hx_dom
  rw [LinearPMap.congr_fun (P.adjoint_spectralIntegral hf) x.2 hx']
  exact P.inner_spectralIntegral hfs ⟨x, hx'⟩ y

end TauCeti.ProjValMeasure
