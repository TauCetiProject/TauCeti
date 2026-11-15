/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Diag
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement

/-!
# The unbounded spectral integral of a projection-valued measure

Let `P` be a normalized projection-valued measure on a measurable space `X` acting on a complex
Hilbert space `H`, with diagonal scalar measures `P.diag x`. To every measurable symbol
`f : X → ℂ`, this file attaches the partial linear operator `P.spectralIntegral f hf : H →ₗ.[ℂ] H`
whose domain is the maximal second-moment subspace

`P.spectralIntegralDomain f = {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`

and whose value on `x` in that domain is the norm limit of the bounded spectral cutoff integrals
`P.integral (1_{‖f‖ ≤ n} · f) x` as `n → ∞`. The construction requires neither separability of `H`
nor any topological structure on `X`.

## Main definitions and results

* `TauCeti.ProjValMeasure.spectralIntegralDomain`: the maximal second-moment submodule
  `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`.
* `TauCeti.ProjValMeasure.spectralIntegral`: the unbounded spectral integral
  `P.spectralIntegral f hf : H →ₗ.[ℂ] H`.
* `TauCeti.ProjValMeasure.dense_spectralIntegral_domain`: the domain of `P.spectralIntegral f hf`
  is dense in `H`.
* `TauCeti.ProjValMeasure.norm_sq_spectralIntegral_apply`: the second-moment norm identity
  `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`.
* `TauCeti.ProjValMeasure.inner_spectralIntegral_apply`: for `x` in the domain and `y : H`,
  `⟪y, P.spectralIntegral f hf x⟫_ℂ` is the vector-measure integral of `f` against
  `P.polarizedComplexMeasure y x`.
* `TauCeti.ProjValMeasure.eq_spectralIntegral_iff`: the second-moment domain and polarized matrix
  elements uniquely characterize `P.spectralIntegral f hf`.
* `TauCeti.ProjValMeasure.spectralIntegral_eq_spectralIntegral_iff`: two measurable symbols define
  the same unbounded spectral integral if and only if they agree `P`-almost everywhere.
* `TauCeti.ProjValMeasure.spectralIntegral_boundedBorelFunction`: bounded Borel symbols have
  domain `⊤` and agree with the bounded functional calculus `P.integral`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1,
  equations (3.25)–(3.28) and Theorem 3.2.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.3.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The maximal second-moment domain -/

/-- The maximal second-moment subspace `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` of a symbol
`f : X → ℂ` with respect to a projection-valued measure `P`. -/
noncomputable def spectralIntegralDomain (P : ProjValMeasure X H) (f : X → ℂ) : Submodule ℂ H where
  carrier := {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}
  zero_mem' := by simp [P.diag_zero]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    refine (lintegral_mono' (P.diag_add_le x y) le_rfl).trans_lt ?_
    rw [two_nsmul, two_nsmul, lintegral_add_measure, lintegral_add_measure, lintegral_add_measure]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hx, hx⟩, ENNReal.add_lt_top.2 ⟨hy, hy⟩⟩
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [P.diag_smul, lintegral_smul_measure]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hx

/-- Membership in `P.spectralIntegralDomain f` is finiteness of the second spectral moment. -/
@[simp]
theorem mem_spectralIntegralDomain_iff (P : ProjValMeasure X H) (f : X → ℂ) (x : H) :
    x ∈ P.spectralIntegralDomain f ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  (Iff.rfl)

/-- When `t ↦ ‖f t‖ ^ 2` is `P.diag x`-almost everywhere strongly measurable, membership in
`P.spectralIntegralDomain f` is equivalent to Bochner integrability of `t ↦ ‖f t‖ ^ 2` against
`P.diag x`. -/
theorem mem_spectralIntegralDomain_iff_integrable_norm_sq (P : ProjValMeasure X H)
    {f : X → ℂ} {x : H} (hmeas : AEStronglyMeasurable (fun t => ‖f t‖ ^ 2) (P.diag x)) :
    x ∈ P.spectralIntegralDomain f ↔ Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) := by
  have heq : (∫⁻ t, ‖‖f t‖ ^ 2‖ₑ ∂(P.diag x)) = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
    refine lintegral_congr fun t => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [mem_spectralIntegralDomain_iff, Integrable, HasFiniteIntegral, heq,
    and_iff_right hmeas]

/-- For a measurable symbol `f`, every vector in `P.spectralIntegralDomain f` makes
`t ↦ ‖f t‖ ^ 2` integrable against `P.diag x`. -/
theorem integrable_norm_sq_of_mem_spectralIntegralDomain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ P.spectralIntegralDomain f) :
    Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
  (P.mem_spectralIntegralDomain_iff_integrable_norm_sq
    (hf.norm.pow_const 2).aestronglyMeasurable).1 hx

/-- Symbols that agree `P`-almost everywhere have the same second-moment domain. -/
theorem spectralIntegralDomain_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ}
    (h : f =ᶠ[P.ae] g) :
    P.spectralIntegralDomain f = P.spectralIntegralDomain g := by
  ext x
  simp only [mem_spectralIntegralDomain_iff]
  rw [lintegral_congr_ae ((P.ae_diag_of_ae x h).mono fun t ht => by rw [ht])]

/-- Complex conjugation of the symbol preserves the second-moment domain. -/
@[simp]
theorem spectralIntegralDomain_star (P : ProjValMeasure X H) (f : X → ℂ) :
    P.spectralIntegralDomain (star f) = P.spectralIntegralDomain f := by
  ext x
  simp [mem_spectralIntegralDomain_iff]

/-- Negation of the symbol preserves the second-moment domain. -/
@[simp]
theorem spectralIntegralDomain_neg (P : ProjValMeasure X H) (f : X → ℂ) :
    P.spectralIntegralDomain (-f) = P.spectralIntegralDomain f := by
  ext x
  simp [mem_spectralIntegralDomain_iff]

/-- Scaling a symbol can only enlarge its second-moment domain (equality holds when the scalar is
nonzero; at `0` the scaled domain is `⊤`). -/
theorem le_spectralIntegralDomain_smul (P : ProjValMeasure X H) (c : ℂ) (f : X → ℂ) :
    P.spectralIntegralDomain f ≤ P.spectralIntegralDomain (c • f) := by
  intro x hx
  rw [mem_spectralIntegralDomain_iff] at hx ⊢
  have hle : (∫⁻ t, ‖(c • f) t‖ₑ ^ 2 ∂(P.diag x)) =
      ‖c‖ₑ ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)]
    refine lintegral_congr fun t => ?_
    rw [Pi.smul_apply, eNorm_smul, mul_pow]
  rw [hle]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) hx

/-- Scaling a symbol by a nonzero complex scalar preserves its second-moment domain. -/
theorem spectralIntegralDomain_smul_of_ne_zero (P : ProjValMeasure X H) {c : ℂ} (hc : c ≠ 0)
    (f : X → ℂ) :
    P.spectralIntegralDomain (c • f) = P.spectralIntegralDomain f := by
  refine le_antisymm ?_ (P.le_spectralIntegralDomain_smul c f)
  simpa [inv_smul_smul₀ hc] using P.le_spectralIntegralDomain_smul c⁻¹ (c • f)

/-- For a measurable symbol `f`, the intersection of the second-moment domains of `f` and `g` lies
in the second-moment domain of `f + g`. -/
theorem le_spectralIntegralDomain_add (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (g : X → ℂ) :
    P.spectralIntegralDomain f ⊓ P.spectralIntegralDomain g ≤
      P.spectralIntegralDomain (f + g) := by
  intro x hx
  rcases Submodule.mem_inf.1 hx with ⟨hxf, hxg⟩
  rw [mem_spectralIntegralDomain_iff] at hxf hxg ⊢
  have hpoint (t : X) : ‖(f + g) t‖ₑ ^ 2 ≤ 2 * ‖f t‖ₑ ^ 2 + 2 * ‖g t‖ₑ ^ 2 := by
    have hreal : ‖f t + g t‖ ^ 2 ≤ 2 * ‖f t‖ ^ 2 + 2 * ‖g t‖ ^ 2 := by
      nlinarith [norm_add_le (f t) (g t), norm_nonneg (f t + g t), sq_nonneg (‖f t‖ - ‖g t‖)]
    have h := ENNReal.ofReal_le_ofReal hreal
    rwa [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ofReal_norm, ofReal_norm] at h
  refine (lintegral_mono hpoint).trans_lt ?_
  rw [lintegral_add_left ((hf.eNorm.pow_const 2).const_mul 2),
    lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (by simp) hxf, ENNReal.mul_lt_top (by simp) hxg⟩

/-- Projecting onto a measurable set `B` where `f` is `P`-almost everywhere bounded sends every
vector into `P.spectralIntegralDomain f`. -/
theorem proj_apply_mem_spectralIntegralDomain (P : ProjValMeasure X H) {f : X → ℂ} {B : Set X}
    (hB : MeasurableSet B) {M : ℝ} (hBM : ∀ᶠ t in P.ae, t ∈ B → ‖f t‖ ≤ M) (x : H) :
    P.proj B hB x ∈ P.spectralIntegralDomain f := by
  rw [mem_spectralIntegralDomain_iff, P.diag_proj B hB x]
  have hae : ∀ᵐ t ∂(P.diag x).restrict B, ‖f t‖ₑ ^ 2 ≤ ENNReal.ofReal M ^ 2 := by
    filter_upwards [ae_restrict_of_ae (P.ae_diag_of_ae x hBM), ae_restrict_mem hB] with t ht htB
    rw [← ofReal_norm]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (ht htB)) 2
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

/-- A symbol that is `P`-almost everywhere bounded has full second-moment domain `⊤`. -/
theorem spectralIntegralDomain_eq_top_of_ae_norm_le (P : ProjValMeasure X H) {f : X → ℂ} {M : ℝ}
    (hf : ∀ᶠ t in P.ae, ‖f t‖ ≤ M) :
    P.spectralIntegralDomain f = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx := P.proj_apply_mem_spectralIntegralDomain (f := f) MeasurableSet.univ
    (hf.mono fun _ ht _ => ht) x
  rwa [P.proj_univ, ContinuousLinearMap.id_apply] at hx

/-- The zero symbol has full second-moment domain `⊤`. -/
@[simp]
theorem spectralIntegralDomain_zero (P : ProjValMeasure X H) :
    P.spectralIntegralDomain 0 = ⊤ :=
  P.spectralIntegralDomain_eq_top_of_ae_norm_le (M := 0) (Eventually.of_forall fun _ => by simp)

/-- The unit symbol has full second-moment domain `⊤`. -/
@[simp]
theorem spectralIntegralDomain_one (P : ProjValMeasure X H) :
    P.spectralIntegralDomain 1 = ⊤ :=
  P.spectralIntegralDomain_eq_top_of_ae_norm_le (M := 1) (Eventually.of_forall fun _ => by simp)

/-- Every constant symbol has full second-moment domain `⊤`. -/
@[simp]
theorem spectralIntegralDomain_const (P : ProjValMeasure X H) (c : ℂ) :
    P.spectralIntegralDomain (fun _ => c) = ⊤ :=
  P.spectralIntegralDomain_eq_top_of_ae_norm_le (M := ‖c‖) (Eventually.of_forall fun _ => le_rfl)

/-- Every bounded Borel symbol has full second-moment domain `⊤`. -/
@[simp]
theorem spectralIntegralDomain_boundedBorelFunction (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) :
    P.spectralIntegralDomain f = ⊤ :=
  P.spectralIntegralDomain_eq_top_of_ae_norm_le (Eventually.of_forall f.norm_coe_le_norm)

/-! ### Cutoff approximation and construction of the unbounded spectral integral -/

/-- The bounded Borel truncation `1_{‖f‖ ≤ n} · f` of a measurable symbol `f`. -/
private noncomputable def cutoffSymbol (f : X → ℂ) (hf : Measurable f) (n : ℕ) :
    BoundedBorelFunction X :=
  BoundedBorelFunction.ofFunction ({t | ‖f t‖ ≤ n}.indicator f)
    (hf.indicator (measurableSet_le hf.norm measurable_const))
    ⟨n, Nat.cast_nonneg n, fun t => by
      by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)}
      · simpa [Set.indicator_of_mem ht] using ht
      · simp [Set.indicator_of_notMem ht]⟩

private theorem cutoffSymbol_apply (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    cutoffSymbol f hf n t = {t | ‖f t‖ ≤ n}.indicator f t := by
  simp [cutoffSymbol]

private theorem cutoffSymbol_star (f : X → ℂ) (hf : Measurable f) (n : ℕ) :
    cutoffSymbol (star f) (continuous_star.measurable.comp hf) n = star (cutoffSymbol f hf n) := by
  ext t
  by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)}
  · simp [cutoffSymbol_apply, Set.indicator_of_mem ht]
  · simp [cutoffSymbol_apply, Set.indicator_of_notMem ht]

private theorem tendsto_cutoffSymbol_apply (f : X → ℂ) (hf : Measurable f) (t : X) :
    Tendsto (fun n => cutoffSymbol f hf n t) atTop (𝓝 (f t)) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} := hN.trans (Nat.cast_le.2 hn)
  rw [cutoffSymbol_apply, Set.indicator_of_mem ht]

private theorem norm_cutoffSymbol_apply_le (f : X → ℂ) (hf : Measurable f) (n : ℕ) (t : X) :
    ‖cutoffSymbol f hf n t‖ ≤ ‖f t‖ := by
  rw [cutoffSymbol_apply]
  exact norm_indicator_le_norm_self f t

private theorem norm_sq_integral_cutoffSymbol_sub_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ P.spectralIntegralDomain f) {N m n : ℕ}
    (hm : N ≤ m) (hn : N ≤ n) :
    ‖P.integral (cutoffSymbol f hf m) x - P.integral (cutoffSymbol f hf n) x‖ ^ 2 ≤
      4 * ∫ t, {s | (N : ℝ) < ‖f s‖}.indicator (fun s => ‖f s‖ ^ 2) t ∂(P.diag x) := by
  have hint := P.integrable_norm_sq_of_mem_spectralIntegralDomain hf hx
  have hmeasN : MeasurableSet {s | (N : ℝ) < ‖f s‖} := measurableSet_lt measurable_const hf.norm
  rw [← sub_apply, ← map_sub, P.norm_sq_integral_apply, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    ((hint.indicator hmeasN).const_mul 4) (Eventually.of_forall fun t => ?_)
  simp only [BoundedBorelFunction.sub_apply]
  by_cases ht : (N : ℝ) < ‖f t‖
  · rw [Set.indicator_of_mem ht]
    have hsum : ‖cutoffSymbol f hf m t - cutoffSymbol f hf n t‖ ≤ 2 * ‖f t‖ := by
      linarith [norm_sub_le (cutoffSymbol f hf m t) (cutoffSymbol f hf n t),
        norm_cutoffSymbol_apply_le f hf m t, norm_cutoffSymbol_apply_le f hf n t]
    nlinarith [norm_nonneg (cutoffSymbol f hf m t - cutoffSymbol f hf n t)]
  · have hle : ‖f t‖ ≤ N := not_lt.1 ht
    have hmt : t ∈ {s | ‖f s‖ ≤ (m : ℝ)} := hle.trans (Nat.cast_le.2 hm)
    have hnt : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} := hle.trans (Nat.cast_le.2 hn)
    simp [cutoffSymbol_apply, ht, Set.indicator_of_mem hmt, Set.indicator_of_mem hnt]

private theorem tendsto_integral_tail_norm_sq (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ P.spectralIntegralDomain f) :
    Tendsto (fun N : ℕ => ∫ t, {s | (N : ℝ) < ‖f s‖}.indicator (fun s => ‖f s‖ ^ 2) t ∂(P.diag x))
      atTop (𝓝 0) := by
  have hint := P.integrable_norm_sq_of_mem_spectralIntegralDomain hf hx
  simpa using tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun t => ‖f t‖ ^ 2)
    (fun N =>
      ((hf.norm.pow_const 2).indicator
        (measurableSet_lt measurable_const hf.norm)).aestronglyMeasurable)
    hint
    (fun N => Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) t)]
      by_cases ht : (N : ℝ) < ‖f t‖ <;> simp [ht])
    (Eventually.of_forall fun t => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnot : ¬ ((n : ℝ) < ‖f t‖) := not_lt.2 (hN.trans (Nat.cast_le.2 hn))
      simp [hnot])

private theorem cauchySeq_integral_cutoffSymbol (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ P.spectralIntegralDomain f) :
    CauchySeq fun n => P.integral (cutoffSymbol f hf n) x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hlim :
      Tendsto (fun N : ℕ =>
        4 * ∫ t, {s | (N : ℝ) < ‖f s‖}.indicator (fun s => ‖f s‖ ^ 2) t ∂(P.diag x))
        atTop (𝓝 0) := by
    simpa using (tendsto_integral_tail_norm_sq P hf hx).const_mul 4
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))).exists_forall_of_atTop
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have hsq : ‖P.integral (cutoffSymbol f hf m) x - P.integral (cutoffSymbol f hf n) x‖ ^ 2 <
      ε ^ 2 :=
    (norm_sq_integral_cutoffSymbol_sub_le P hf hx hm hn).trans_lt (hN N le_rfl)
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsq

/-- The **unbounded spectral integral** `P.spectralIntegral f hf : H →ₗ.[ℂ] H` of a measurable
symbol `f : X → ℂ` against a projection-valued measure `P`. Its domain is the maximal second-moment
subspace `P.spectralIntegralDomain f`, and its action is the strong limit of the bounded cutoff
integrals `P.integral (1_{‖f‖ ≤ n} · f)`. -/
noncomputable def spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    H →ₗ.[ℂ] H where
  domain := P.spectralIntegralDomain f
  toFun :=
    { toFun x := limUnder atTop fun n => P.integral (cutoffSymbol f hf n) (x : H)
      map_add' x y := by
        have hx := (cauchySeq_integral_cutoffSymbol P hf x.2).tendsto_limUnder
        have hy := (cauchySeq_integral_cutoffSymbol P hf y.2).tendsto_limUnder
        have hxy := (cauchySeq_integral_cutoffSymbol P hf (x + y).2).tendsto_limUnder
        refine tendsto_nhds_unique hxy ?_
        simpa only [Submodule.coe_add, map_add] using hx.add hy
      map_smul' c x := by
        have hx := (cauchySeq_integral_cutoffSymbol P hf x.2).tendsto_limUnder
        have hcx := (cauchySeq_integral_cutoffSymbol P hf (c • x).2).tendsto_limUnder
        refine tendsto_nhds_unique hcx ?_
        simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using hx.const_smul c }

private theorem tendsto_integral_cutoffSymbol (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n => P.integral (cutoffSymbol f hf n) (x : H)) atTop
      (𝓝 (P.spectralIntegral f hf x)) :=
  (cauchySeq_integral_cutoffSymbol P hf x.2).tendsto_limUnder

/-! ### Domain, density, norm identity, and polarized matrix elements -/

/-- The domain of `P.spectralIntegral f hf` is `P.spectralIntegralDomain f`. -/
@[simp]
theorem spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).domain = P.spectralIntegralDomain f :=
  (rfl)

/-- Membership in the domain of `P.spectralIntegral f hf` is finiteness of the second spectral
moment. -/
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  (Iff.rfl)

/-- Projecting onto a measurable set `B` where `f` is `P`-almost everywhere bounded sends every
vector into the domain of `P.spectralIntegral f hf`. -/
theorem proj_apply_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {M : ℝ}
    (hBM : ∀ᶠ t in P.ae, t ∈ B → ‖f t‖ ≤ M) (x : H) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [spectralIntegral_domain]
  exact P.proj_apply_mem_spectralIntegralDomain hB hBM x

/-- For every vector `x : H`, the spectral cutoff projections `P({t | ‖f t‖ ≤ n}) x` converge to
`x` in norm as `n → ∞`. -/
theorem tendsto_proj_norm_le (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) (x : H) :
    Tendsto (fun n : ℕ => P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) x)
      atTop (𝓝 x) := by
  have hlim :
      Tendsto
        (fun n : ℕ =>
          P.integral
            (BoundedBorelFunction.indicator {t | ‖f t‖ ≤ n}
              (measurableSet_le hf.norm measurable_const) 1) x)
        atTop (𝓝 (P.integral 1 x)) := by
    refine P.tendsto_integral_apply_filter_of_dominated_convergence (M := 1)
      (Eventually.of_forall fun n => Eventually.of_forall fun t => by
        by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)}
        · simp [Set.indicator_of_mem ht]
        · simp [Set.indicator_of_notMem ht])
      (Eventually.of_forall fun t => ?_) x
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} := hN.trans (Nat.cast_le.2 hn)
    simp [Set.indicator_of_mem ht]
  rw [map_one, one_apply_eq_self] at hlim
  exact hlim.congr fun n => by rw [P.integral_indicator]

/-- The domain of `P.spectralIntegral f hf` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    Dense ((P.spectralIntegral f hf).domain : Set H) := by
  intro x
  refine mem_closure_of_tendsto (P.tendsto_proj_norm_le hf x) (Eventually.of_forall fun n => ?_)
  exact P.proj_apply_mem_spectralIntegral_domain hf (measurableSet_le hf.norm measurable_const)
    (M := n) (Eventually.of_forall fun _ ht => ht) x

/-- **Norm-square identity** for the unbounded spectral integral:
`‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. -/
theorem norm_sq_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  have hlim_vec := ((continuous_norm.pow 2).tendsto _).comp
    (tendsto_integral_cutoffSymbol P hf x)
  have hlim_int :
      Tendsto (fun n => ∫ t, ‖cutoffSymbol f hf n t‖ ^ 2 ∂(P.diag x)) atTop
        (𝓝 (∫ t, ‖f t‖ ^ 2 ∂(P.diag x))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
      (fun n => ((cutoffSymbol f hf n).measurable.norm.pow_const 2).aestronglyMeasurable)
      (P.integrable_norm_sq_of_mem_spectralIntegralDomain hf x.2)
      (fun n => Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffSymbol_apply_le f hf n t) 2)
      (Eventually.of_forall fun t =>
        ((continuous_norm.pow 2).tendsto _).comp (tendsto_cutoffSymbol_apply f hf t))
  refine tendsto_nhds_unique hlim_vec (hlim_int.congr fun n => ?_)
  exact (P.norm_sq_integral_apply (cutoffSymbol f hf n) x).symm

/-- Norm identity for the unbounded spectral integral:
`‖P.spectralIntegral f hf x‖ = √(∫ t, ‖f t‖ ^ 2 ∂(P.diag x))`. -/
theorem norm_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ = Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) := by
  rw [← Real.sqrt_sq (norm_nonneg (P.spectralIntegral f hf x)),
    P.norm_sq_spectralIntegral_apply f hf x]

/-- Extended-norm-square identity for the unbounded spectral integral:
`‖P.spectralIntegral f hf x‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x)`. -/
theorem enorm_sq_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
  have hint := P.integrable_norm_sq_of_mem_spectralIntegralDomain hf x.2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), P.norm_sq_spectralIntegral_apply,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
  refine lintegral_congr fun t => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Every measurable symbol `f` is integrable against `P.polarizedComplexMeasure y x` whenever `x`
lies in the domain of `P.spectralIntegral f hf` and `y : H` is arbitrary. -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain
    (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    (P.polarizedComplexMeasure y x).Integrable f :=
  P.integrable_variation_polarizedComplexMeasure_of_lintegral_pow_two_lt_top y x
    hf.aestronglyMeasurable x.2

/-- **Matrix-element identity** for the unbounded spectral integral: for `x` in the domain and
every `y : H`, `⟪y, P.spectralIntegral f hf x⟫_ℂ` is the integral of `f` against the polarized
complex measure `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    ⟪y, P.spectralIntegral f hf x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hlim_inner :
      Tendsto (fun n => ⟪y, P.integral (cutoffSymbol f hf n) x⟫_ℂ) atTop
        (𝓝 ⟪y, P.spectralIntegral f hf x⟫_ℂ) :=
    (continuous_const.inner continuous_id).tendsto _ |>.comp
      (tendsto_integral_cutoffSymbol P hf x)
  have hint := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x y
  have hlim_int :
      Tendsto
        (fun n =>
          ∫ᵛ t, cutoffSymbol f hf n t
            ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
        atTop
        (𝓝 (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
      (fun n => (cutoffSymbol f hf n).measurable.aestronglyMeasurable)
      hint.norm
      (fun n => Eventually.of_forall (norm_cutoffSymbol_apply_le f hf n))
      (Eventually.of_forall (tendsto_cutoffSymbol_apply f hf))
  refine tendsto_nhds_unique hlim_inner (hlim_int.congr fun n => ?_)
  exact P.integral_polarizedComplexMeasure_eq_inner_integral (cutoffSymbol f hf n) y x

/-- Formal-adjoint symmetry of the unbounded spectral integral: for `x` in the domain of `f` and `y`
in the domain of `star f`, the inner product of `P.spectralIntegral f hf x` with `y` equals the
inner product of `x` with `P.spectralIntegral (star f) _ y`. -/
theorem inner_spectralIntegral_star (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain)
    (y : (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)).domain) :
    ⟪P.spectralIntegral f hf x, (y : H)⟫_ℂ =
      ⟪(x : H), P.spectralIntegral (star f) (continuous_star.measurable.comp hf) y⟫_ℂ := by
  have hlhs :
      Tendsto (fun n => ⟪P.integral (cutoffSymbol f hf n) x, (y : H)⟫_ℂ) atTop
        (𝓝 ⟪P.spectralIntegral f hf x, (y : H)⟫_ℂ) :=
    (continuous_id.inner continuous_const).tendsto _ |>.comp
      (tendsto_integral_cutoffSymbol P hf x)
  have hrhs :
      Tendsto
        (fun n =>
          ⟪(x : H),
            P.integral (cutoffSymbol (star f) (continuous_star.measurable.comp hf) n) y⟫_ℂ)
        atTop
        (𝓝 ⟪(x : H), P.spectralIntegral (star f) (continuous_star.measurable.comp hf) y⟫_ℂ) :=
    (continuous_const.inner continuous_id).tendsto _ |>.comp
      (tendsto_integral_cutoffSymbol P (continuous_star.measurable.comp hf) y)
  refine tendsto_nhds_unique hlhs (hrhs.congr fun n => ?_)
  rw [cutoffSymbol_star, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **Uniqueness characterization** of the unbounded spectral integral: a partial linear operator
`T : H →ₗ.[ℂ] H` equals `P.spectralIntegral f hf` if and only if its domain is the second-moment
subspace and its matrix elements are the polarized integrals of `f`. -/
theorem eq_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (T : H →ₗ.[ℂ] H) :
    T = P.spectralIntegral f hf ↔
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
        ∀ (x : T.domain) (y : H),
          ⟪y, T x⟫_ℂ =
            ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  refine ⟨fun h => ?_, fun ⟨hdom, hinner⟩ => ?_⟩
  · subst h
    exact ⟨fun _ => Iff.rfl, P.inner_spectralIntegral_apply f hf⟩
  · refine LinearPMap.ext (Submodule.ext hdom) fun x hx₁ hx₂ => ?_
    refine ext_inner_left ℂ fun y => ?_
    rw [hinner ⟨x, hx₁⟩ y, P.inner_spectralIntegral_apply f hf ⟨x, hx₂⟩ y]

/-! ### Almost-everywhere invariance, bounded compatibility, and spectral cutoffs -/

/-- Measurable symbols that agree `P`-almost everywhere define the same unbounded spectral
integral, with equal domains and actions. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : f =ᶠ[P.ae] g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg := by
  rw [P.eq_spectralIntegral_iff hg]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [P.mem_spectralIntegral_domain_iff f hf, ← P.mem_spectralIntegralDomain_iff g,
      ← P.spectralIntegralDomain_congr_ae h, P.mem_spectralIntegralDomain_iff]
  · rw [P.inner_spectralIntegral_apply f hf x y]
    refine VectorMeasure.integral_congr_ae ?_
    exact P.variation_polarizedComplexMeasure_absolutelyContinuous_right y x
      (P.ae_diag_of_ae x h)

/-- On a bounded Borel symbol `g`, the unbounded spectral integral has full domain `⊤` and agrees
with the bounded functional calculus `P.integral g`. -/
@[simp]
theorem spectralIntegral_boundedBorelFunction (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) :
    P.spectralIntegral g g.measurable = (P.integral g).toLinearMap.toPMap ⊤ := by
  symm
  rw [P.eq_spectralIntegral_iff g.measurable]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [LinearMap.toPMap_domain, ← P.mem_spectralIntegralDomain_iff g x,
      P.spectralIntegralDomain_boundedBorelFunction]
  · exact (P.integral_polarizedComplexMeasure_eq_inner_integral g y x).symm

/-- Evaluating `P.spectralIntegral` of a bounded Borel symbol `g` gives `P.integral g`. -/
@[simp]
theorem spectralIntegral_boundedBorelFunction_apply (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (x : (P.spectralIntegral g g.measurable).domain) :
    P.spectralIntegral g g.measurable x = P.integral g x :=
  @(LinearPMap.ext_iff.1 (P.spectralIntegral_boundedBorelFunction g)).2 x x.2 trivial

/-- The unbounded spectral integral of `0` is the zero operator on `⊤`. -/
@[simp]
theorem spectralIntegral_zero (P : ProjValMeasure X H) :
    P.spectralIntegral 0 measurable_const = 0 := by
  symm
  rw [P.eq_spectralIntegral_iff (f := 0) measurable_const]
  refine ⟨fun x => ?_, fun x y => by simp⟩
  rw [LinearPMap.zero_domain, ← P.mem_spectralIntegralDomain_iff _ x, P.spectralIntegralDomain_zero]

/-- The unbounded spectral integral of `1` is the identity operator on `⊤`. -/
@[simp]
theorem spectralIntegral_one (P : ProjValMeasure X H) :
    P.spectralIntegral 1 measurable_const = LinearMap.id.toPMap ⊤ := by
  simpa [ContinuousLinearMap.one_def] using P.spectralIntegral_boundedBorelFunction 1

/-- The unbounded spectral integral of a constant symbol `fun _ => c` is `c • id` on `⊤`. -/
theorem spectralIntegral_const (P : ProjValMeasure X H) (c : ℂ) :
    P.spectralIntegral (fun _ => c) measurable_const = (c • LinearMap.id).toPMap ⊤ := by
  symm
  rw [P.eq_spectralIntegral_iff measurable_const]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [LinearMap.toPMap_domain, ← P.mem_spectralIntegralDomain_iff _ x,
      P.spectralIntegralDomain_const]
  · rw [LinearMap.toPMap_apply (c • LinearMap.id) ⊤ x, LinearMap.smul_apply, LinearMap.id_apply]
    have h := P.integral_polarizedComplexMeasure_eq_inner_integral
      (algebraMap ℂ (BoundedBorelFunction X) c) y x
    simpa [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, one_apply_eq_self] using h.symm

/-- Negating the symbol negates the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_neg (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (-f) hf.neg = -P.spectralIntegral f hf := by
  symm
  rw [P.eq_spectralIntegral_iff hf.neg]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [LinearPMap.neg_domain, spectralIntegral_domain, ← P.spectralIntegralDomain_neg f,
      P.mem_spectralIntegralDomain_iff]
  · rw [LinearPMap.neg_apply, inner_neg_right, P.inner_spectralIntegral_apply f hf x y,
      ← VectorMeasure.integral_neg]

/-- Scaling a symbol by `c : ℂ` extends `c • P.spectralIntegral f hf` (with domain equality when
`c ≠ 0`; at `c = 0` the scaled symbol has domain `⊤`). -/
theorem le_spectralIntegral_smul (P : ProjValMeasure X H) (c : ℂ) {f : X → ℂ}
    (hf : Measurable f) :
    c • P.spectralIntegral f hf ≤ P.spectralIntegral (c • f) (hf.const_smul c) := by
  refine ⟨P.le_spectralIntegralDomain_smul c f, fun x₁ x₂ hx => ?_⟩
  refine ext_inner_left ℂ fun y => ?_
  rw [LinearPMap.smul_apply, inner_smul_right, P.inner_spectralIntegral_apply f hf x₁ y,
    P.inner_spectralIntegral_apply (c • f) (hf.const_smul c) x₂ y, hx]
  exact (VectorMeasure.integral_fun_smul_of_smul_left
    (fun a z w => mul_assoc a z w) c f).symm

/-- Scaling a symbol by a nonzero complex scalar scales its unbounded spectral integral with
equality of domains. -/
theorem spectralIntegral_smul_of_ne_zero (P : ProjValMeasure X H) {c : ℂ} (hc : c ≠ 0)
    {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (c • f) (hf.const_smul c) = c • P.spectralIntegral f hf :=
  (LinearPMap.eq_of_le_of_domain_eq (P.le_spectralIntegral_smul c hf)
    (P.spectralIntegralDomain_smul_of_ne_zero hc f).symm).symm

/-- Projecting the output of `P.spectralIntegral f hf` onto a measurable set `B` where `f` agrees
`P`-almost everywhere with a bounded Borel symbol `g` gives the bounded integral of `1_B · g`. -/
theorem proj_spectralIntegral_apply_eq_integral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) (g : BoundedBorelFunction X)
    (hfg : ∀ᶠ t in P.ae, t ∈ B → f t = g t) (x : (P.spectralIntegral f hf).domain) :
    P.proj B hB (P.spectralIntegral f hf x) =
      P.integral (BoundedBorelFunction.indicator B hB g) x := by
  have hlim := ((P.proj B hB).continuous.tendsto _).comp (tendsto_integral_cutoffSymbol P hf x)
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g‖
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Function.comp_apply, ← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul]
  congr 1
  refine P.integral_congr_ae ?_
  filter_upwards [hfg] with t ht
  rw [BoundedBorelFunction.mul_apply, BoundedBorelFunction.indicator_apply,
    BoundedBorelFunction.indicator_apply]
  by_cases htB : t ∈ B
  · have hft : f t = g t := ht htB
    have hnorm : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} := by
      simp only [Set.mem_ofPred_eq, hft]
      exact (g.norm_coe_le_norm t).trans (hN.trans (Nat.cast_le.2 hn))
    simp only [Set.indicator_of_mem htB, BoundedBorelFunction.one_apply, one_mul,
      cutoffSymbol_apply, Set.indicator_of_mem hnorm, hft]
  · simp [Set.indicator_of_notMem htB]

/-- On a vector projected onto a measurable set `B` where `f` agrees `P`-almost everywhere with a
bounded Borel symbol `g`, `P.spectralIntegral f hf` acts as the bounded integral of `1_B · g`. -/
theorem spectralIntegral_apply_proj_eq_integral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) (g : BoundedBorelFunction X)
    (hfg : ∀ᶠ t in P.ae, t ∈ B → f t = g t) (x : H) :
    P.spectralIntegral f hf
        ⟨P.proj B hB x,
          P.proj_apply_mem_spectralIntegral_domain hf hB (M := ‖g‖)
            (hfg.mono fun t ht htB => (ht htB).symm ▸ g.norm_coe_le_norm t) x⟩ =
      P.integral (BoundedBorelFunction.indicator B hB g) x := by
  let px : (P.spectralIntegral f hf).domain :=
    ⟨P.proj B hB x,
      P.proj_apply_mem_spectralIntegral_domain hf hB (M := ‖g‖)
        (hfg.mono fun t ht htB => (ht htB).symm ▸ g.norm_coe_le_norm t) x⟩
  have hfixed : P.proj B hB (P.spectralIntegral f hf px) = P.spectralIntegral f hf px := by
    have hlim := ((P.proj B hB).continuous.tendsto _).comp (tendsto_integral_cutoffSymbol P hf px)
    refine tendsto_nhds_unique hlim ((tendsto_integral_cutoffSymbol P hf px).congr fun n => ?_)
    have hcomm := (P.forall_commute_integral_iff (P.proj B hB)).2
      (fun C hC => P.proj_mul_comm B C hB hC) (cutoffSymbol f hf n)
    symm
    calc P.proj B hB (P.integral (cutoffSymbol f hf n) (P.proj B hB x))
        = (P.proj B hB * P.integral (cutoffSymbol f hf n)) (P.proj B hB x) := by
            rw [mul_apply_eq_comp]
      _ = P.integral (cutoffSymbol f hf n) (P.proj B hB (P.proj B hB x)) := by
            rw [hcomm.eq, mul_apply_eq_comp]
      _ = P.integral (cutoffSymbol f hf n) px := by rw [P.proj_apply_proj]
  calc P.spectralIntegral f hf px
      = P.proj B hB (P.spectralIntegral f hf px) := hfixed.symm
    _ = P.integral (BoundedBorelFunction.indicator B hB g) (P.proj B hB x) :=
          P.proj_spectralIntegral_apply_eq_integral hf hB g hfg px
    _ = P.integral (BoundedBorelFunction.indicator B hB g *
          BoundedBorelFunction.indicator B hB 1) x := by
          rw [← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul]
    _ = P.integral (BoundedBorelFunction.indicator B hB g) x := by
          congr 2
          ext t
          by_cases ht : t ∈ B <;> simp [ht]

/-- Every spectral projection onto a measurable set `B` where `f` is `P`-almost everywhere bounded
commutes with `P.spectralIntegral f hf` on its domain. -/
theorem proj_spectralIntegral_apply_eq (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) {M : ℝ} (hBM : ∀ᶠ t in P.ae, t ∈ B → ‖f t‖ ≤ M)
    (x : (P.spectralIntegral f hf).domain) :
    P.proj B hB (P.spectralIntegral f hf x) =
      P.spectralIntegral f hf
        ⟨P.proj B hB x, P.proj_apply_mem_spectralIntegral_domain hf hB hBM x⟩ := by
  let S : Set X := B ∩ {t | ‖f t‖ ≤ max M 0}
  have hS : MeasurableSet S := hB.inter (measurableSet_le hf.norm measurable_const)
  let g : BoundedBorelFunction X :=
    BoundedBorelFunction.ofFunction (S.indicator f) (hf.indicator hS)
      ⟨max M 0, le_max_right M 0, fun t => by
        by_cases ht : t ∈ S
        · simpa [Set.indicator_of_mem ht] using ht.2
        · simp [Set.indicator_of_notMem ht]⟩
  have hfg : ∀ᶠ t in P.ae, t ∈ B → f t = g t := by
    filter_upwards [hBM] with t ht htB
    have htS : t ∈ S := ⟨htB, (ht htB).trans (le_max_left M 0)⟩
    simp [g, Set.indicator_of_mem htS]
  rw [P.proj_spectralIntegral_apply_eq_integral hf hB g hfg x,
    ← P.spectralIntegral_apply_proj_eq_integral hf hB g hfg x]

/-- For every `x` in the domain of `P.spectralIntegral f hf`, the images of the spectral cutoff
projections `P({t | ‖f t‖ ≤ n}) x` under `P.spectralIntegral f hf` converge to
`P.spectralIntegral f hf x` as `n → ∞`. -/
theorem tendsto_spectralIntegral_proj_norm_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto
      (fun n : ℕ =>
        P.spectralIntegral f hf
          ⟨P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) x,
            P.proj_apply_mem_spectralIntegral_domain hf
              (measurableSet_le hf.norm measurable_const) (M := n)
              (Eventually.of_forall fun _ ht => ht) x⟩)
      atTop (𝓝 (P.spectralIntegral f hf x)) := by
  refine (tendsto_integral_cutoffSymbol P hf x).congr fun n => ?_
  have hproj := P.spectralIntegral_apply_proj_eq_integral hf
    (B := {t | ‖f t‖ ≤ (n : ℝ)})
    (measurableSet_le hf.norm measurable_const) (cutoffSymbol f hf n)
    (Eventually.of_forall fun t ht => by simp [cutoffSymbol_apply, Set.indicator_of_mem ht]) x
  have hind :
      BoundedBorelFunction.indicator {t | ‖f t‖ ≤ n}
          (measurableSet_le hf.norm measurable_const) (cutoffSymbol f hf n) =
        cutoffSymbol f hf n := by
    ext t
    by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} <;> simp [cutoffSymbol_apply, ht]
  rw [hind] at hproj
  exact hproj.symm

/-- Two measurable symbols define the same unbounded spectral integral if and only if they agree
`P`-almost everywhere. -/
theorem spectralIntegral_eq_spectralIntegral_iff (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg ↔ f =ᶠ[P.ae] g := by
  refine ⟨fun h => ?_, P.spectralIntegral_congr_ae hf hg⟩
  rw [Filter.EventuallyEq, P.eventually_ae_iff]
  intro ξ
  have hall :
      ∀ n : ℕ,
        ∀ᵐ t ∂(P.diag ξ),
          t ∈ {s | ‖f s‖ ≤ (n : ℝ)} ∩ {s | ‖g s‖ ≤ (n : ℝ)} → f t = g t := by
    intro n
    let B : Set X := {s | ‖f s‖ ≤ (n : ℝ)} ∩ {s | ‖g s‖ ≤ (n : ℝ)}
    have hB : MeasurableSet B :=
      (measurableSet_le hf.norm measurable_const).inter
        (measurableSet_le hg.norm measurable_const)
    have hmemf := P.proj_apply_mem_spectralIntegral_domain hf hB (M := n)
      (Eventually.of_forall fun _ ht => ht.1) ξ
    have hmemg := P.proj_apply_mem_spectralIntegral_domain hg hB (M := n)
      (Eventually.of_forall fun _ ht => ht.2) ξ
    have heq := @(LinearPMap.ext_iff.1 h).2 (P.proj B hB ξ) hmemf hmemg
    rw [P.spectralIntegral_apply_proj_eq_integral hf hB (cutoffSymbol f hf n)
          (Eventually.of_forall fun t ht => by simp [cutoffSymbol_apply, Set.indicator_of_mem ht.1])
          ξ,
        P.spectralIntegral_apply_proj_eq_integral hg hB (cutoffSymbol g hg n)
          (Eventually.of_forall fun t ht => by simp [cutoffSymbol_apply, Set.indicator_of_mem ht.2])
          ξ,
        ← sub_eq_zero, ← sub_apply, ← map_sub, P.integral_apply_eq_zero_iff] at heq
    filter_upwards [heq] with t ht htB
    have htB' : t ∈ B := htB
    have hsub :
        (BoundedBorelFunction.indicator B hB (cutoffSymbol f hf n) -
            BoundedBorelFunction.indicator B hB (cutoffSymbol g hg n)) t = 0 := ht
    rw [BoundedBorelFunction.sub_apply, BoundedBorelFunction.indicator_apply,
      BoundedBorelFunction.indicator_apply, Set.indicator_of_mem htB', Set.indicator_of_mem htB',
      cutoffSymbol_apply, cutoffSymbol_apply, Set.indicator_of_mem htB.1,
      Set.indicator_of_mem htB.2, sub_eq_zero] at hsub
    exact hsub
  filter_upwards [ae_all_iff.2 hall] with t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖f t‖ ‖g t‖)
  exact ht n ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩

end TauCeti.ProjValMeasure
