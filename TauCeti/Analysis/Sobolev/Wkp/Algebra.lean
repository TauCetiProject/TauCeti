/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.SupercriticalMultiplication
import TauCeti.Analysis.Sobolev.BesselPotential.Holder
import TauCeti.Analysis.Sobolev.GagliardoNirenberg
import TauCeti.Analysis.Sobolev.Wkp.BilinOfAeMul
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# `W^{k,p}(ℝⁿ)`, `k p > n`, is an algebra

Let `E` be a finite-dimensional real inner product space of dimension `n`, let `2 ≤ p < ∞` and let
`k p > n`. The weak-derivative Sobolev space `W^{k,p}(E)` on the whole space is closed under
pointwise multiplication, with the estimate

`‖u v‖_{W^{k,p}} ≤ C ‖u‖_{W^{k,p}} ‖v‖_{W^{k,p}}`

for a constant `C` depending only on `E`, `k` and `p` (`TauCeti.Wkp.exists_norm_mul_le`).
Multiplication is then a bounded bilinear map `W^{k,p}(E) × W^{k,p}(E) → W^{k,p}(E)`
(`TauCeti.Wkp.mulOfFinrankLtL`). For
`p > n` this holds at every order `k ≥ 1` (`TauCeti.Wkp.mulL`), since then every factor of positive
order is bounded, and the two multiplications agree where both are defined
(`TauCeti.Wkp.mulOfFinrankLtL_eq_mulL`). The content here is the range `2 ≤ p ≤ n` with
`k p > n`, in which the intermediate derivatives of the factors need not be bounded. The range
`n / k < p < 2` is not covered.

For classical functions this gives the estimate that makes the `Lᵖ` norms of the derivatives
through order `k` behave like a Banach algebra norm. If `f` and `g` are `Cᵏ` on `E` and their
derivatives through order `k` lie in `Lᵖ`, then so do the derivatives of `f g` through order `k`,
and `∑_{i ≤ k} ‖Dⁱ (f g)‖_p ≤ C (∑_{i ≤ k} ‖Dⁱ f‖_p) (∑_{i ≤ k} ‖Dⁱ g‖_p)`
(`TauCeti.exists_sum_lpNorm_iteratedFDeriv_mul_le`).

These are the estimates behind nonlinear analysis on the scale of `Lᵖ` derivatives of order
`k > n / p`: polynomial expressions of such functions stay in the scale, with norms controlled by
those of their factors. No explicit value of the constants is claimed.

## The argument

Two estimates combine. The Moser product estimate
(`TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le`) bounds, for `Cᵏ` functions with compact
support,

`‖Dⁱ (f g)‖_p ≤ C (‖f‖_∞ ‖Dⁱ g‖_p + ‖Dⁱ f‖_p ‖g‖_∞)`,

and the Sobolev embedding `W^{k,p}(E) ⊆ C_b^{0,α}(E)` for `k p > n` (`TauCeti.Wkp.toCkHolderSpace`)
bounds `‖f‖_∞` by the `W^{k,p}` norm. Together they give the algebra estimate for test functions.
Test functions are dense in `W^{k,p}(E)` (`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`), and by the
estimate the products of approximating test functions form a Cauchy sequence; its limit has as
value the product of the values, since multiplication `L^∞ × Lᵖ → Lᵖ` is continuous and the values
converge in `L^∞` by the embedding. The Moser estimate rests on the Gagliardo–Nirenberg inequality
for intermediate derivatives (`TauCeti.exists_eLpNorm_iteratedFDeriv_le`), whose proof needs
`p ≥ 2`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Theorem 4.39.
* M. E. Taylor, *Partial Differential Equations III*, 2nd ed., Springer, 2011, Chapter 13, §3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory TopologicalSpace Module
open scoped ENNReal NNReal Topology Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace Wkp

/-- An exponent `q` with `d < k q.toReal` for a natural number `d` is finite, since
`∞.toReal = 0`. -/
private theorem ne_top_of_natCast_lt_mul_toReal {d : ℕ} {q : ℝ≥0∞} (h : (d : ℝ) < k * q.toReal) :
    q ≠ ∞ := by
  rintro rfl
  rw [ENNReal.toReal_top, mul_zero] at h
  exact h.not_ge (Nat.cast_nonneg _)

/-- For `k p > n`, the values of the elements of `W^{k,p}(E)` are represented by a continuous linear
map into `L^∞`: the Sobolev embedding into bounded Hölder functions, followed by the inclusion of
bounded continuous functions into `L^∞`. -/
private theorem exists_toLpTop (hp : 1 < p) (hp' : p ≠ ∞)
    (hk : (finrank ℝ E : ℝ) < k * p.toReal) :
    ∃ J : Wkp (volume : Measure E) ⊤ p k →L[ℝ]
        Lp ℝ ∞ ((volume : Measure E).restrict ((⊤ : Opens E) : Set E)),
      ∀ u, (J u : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)] value k u := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp).ne' hp'
  have hd : 0 < (k : ℝ) - finrank ℝ E / p.toReal := by
    rw [sub_pos, div_lt_iff₀ hp0]
    exact hk
  set α : ℝ≥0 := (min (1 / 2) ((k : ℝ) - finrank ℝ E / p.toReal)).toNNReal
  have hα : (α : ℝ) = min (1 / 2) ((k : ℝ) - finrank ℝ E / p.toReal) :=
    Real.coe_toNNReal _ (le_min (by norm_num) hd.le)
  have hα0 : 0 < α := by
    rw [← NNReal.coe_pos, hα]
    exact lt_min (by norm_num) hd
  have hα1 : α < 1 := by
    rw [← NNReal.coe_lt_coe, hα, NNReal.coe_one]
    exact (min_le_left _ _).trans_lt (by norm_num)
  have h : ((0 : ℕ) : ℝ) + α ≤ k - finrank ℝ E / p.toReal := by
    rw [hα, Nat.cast_zero, zero_add]
    exact min_le_right _ _
  set S := toCkHolderSpace hp hp' k 0 hα0 hα1 h
  refine ⟨(BoundedContinuousFunction.toLpTop _ ℝ).comp
    (CkHolderSpace.toBoundedContinuousFunctionCLM.comp S), fun u ↦ ?_⟩
  filter_upwards [BoundedContinuousFunction.coeFn_toLpTop _ (𝕜 := ℝ)
    (S u).toBoundedContinuousFunction,
    ae_restrict_of_ae (value_ae_eq_toCkHolderSpace hp hp' (hα0 := hα0) (hα1 := hα1) (h := h) u)]
    with x hx hu
  simp only [ContinuousLinearMap.comp_apply, CkHolderSpace.toBoundedContinuousFunctionCLM_apply]
  rw [hx, hu, CkHolderSpace.coe_toBoundedContinuousFunction]

/-- The `Lᵖ` norm of each derivative through order `k` of a `Cᵏ` representative of
`z ∈ W^{k,p}(E)` is at most `‖z‖`. -/
private theorem eLpNorm_iteratedFDeriv_le_enorm (z : Wkp (volume : Measure E) ⊤ p k)
    {h : E → ℝ} (hh : ContDiff ℝ k h) (hz : (value k z : E → ℝ) =ᵐ[volume] h) {i : ℕ}
    (hi : i ≤ k) : eLpNorm (iteratedFDeriv ℝ i h) p volume ≤ ‖z‖ₑ := by
  have hres : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume :=
    Measure.restrict_coe_opens_top volume
  have hmem := memLp_iteratedFDeriv_of_contDiffOn k z hh.contDiffOn (ae_restrict_of_ae hz) i hi
  have hle := lpNorm_iteratedFDeriv_le_of_contDiffOn k z hh.contDiffOn (ae_restrict_of_ae hz) i hi
  rw [hres] at hmem hle
  rw [← ofReal_norm]
  exact (ENNReal.le_ofReal_iff_toReal_le hmem.eLpNorm_ne_top (norm_nonneg z)).2 hle

/-- **The algebra estimate for compactly supported representatives.** If the values of
`W^{k,p}(E)` are represented in `L^∞` by a bounded operator `J`, then for `2 ≤ p < ∞` there is a
constant `C` such that whenever `u` and `v` are represented by `Cᵏ` functions `f` and `g` with
compact support, `f g` is the value of some `w` with `‖w‖ ≤ C ‖u‖ ‖v‖`. This is the Moser product
estimate, with `‖f‖_∞ ≤ ‖J‖ ‖u‖` and `‖Dⁱ g‖_p ≤ ‖v‖`. -/
private theorem exists_value_ae_eq_mul_and_norm_le_of_hasCompactSupport (hp : 2 ≤ p)
    (hp' : p ≠ ∞) {J : Wkp (volume : Measure E) ⊤ p k →L[ℝ]
      Lp ℝ ∞ ((volume : Measure E).restrict ((⊤ : Opens E) : Set E))}
    (hJ : ∀ u, (J u : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)]
      value k u) :
    ∃ C, ∀ (u v : Wkp (volume : Measure E) ⊤ p k) {f g : E → ℝ}, ContDiff ℝ k f →
      HasCompactSupport f → ContDiff ℝ k g → HasCompactSupport g →
      (value k u : E → ℝ) =ᵐ[volume] f → (value k v : E → ℝ) =ᵐ[volume] g →
      ∃ w : Wkp (volume : Measure E) ⊤ p k, (value k w : E → ℝ) =ᵐ[volume] f * g ∧
        ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  choose c hc using fun i : ℕ ↦ exists_eLpNorm_iteratedFDeriv_bilinear_le
    (μ := (volume : Measure E)) (F := ℝ) (G := ℝ) (H := ℝ) hp hp' i
  refine ⟨∑ i ∈ Finset.range (k + 1), 2 * c i * ‖J‖, fun u v f g hf hfc hg hgc hu hv ↦ ?_⟩
  have hfg : ContDiff ℝ k (f * g) := hf.mul hg
  obtain ⟨w, hw, hwn⟩ := exists_value_ae_eq_and_norm_le (p := p) hfg fun i hi ↦
    (hfg.continuous_iteratedFDeriv (by exact_mod_cast hi)).memLp_of_hasCompactSupport (μ := volume)
      (hfc.mul_right.iteratedFDeriv i)
  refine ⟨w, hw, hwn.trans ?_⟩
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  -- The sup norm of a representative is bounded through `J`.
  have hsup (z : Wkp (volume : Measure E) ⊤ p k) {h : E → ℝ}
      (hz : (value k z : E → ℝ) =ᵐ[volume] h) : eLpNorm h ∞ volume ≤ ‖J‖ₑ * ‖z‖ₑ := by
    calc eLpNorm h ∞ volume
        = eLpNorm h ∞ ((volume : Measure E).restrict ((⊤ : Opens E) : Set E)) := by
          rw [Measure.restrict_coe_opens_top]
      _ = ‖J z‖ₑ := by rw [Lp.eNorm_def, eLpNorm_congr_ae ((hJ z).trans (ae_restrict_of_ae hz))]
      _ ≤ ‖J‖ₑ * ‖z‖ₑ := J.le_opENorm z
  have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
  calc eLpNorm (iteratedFDeriv ℝ i (f * g)) p volume
      ≤ c i * ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * (eLpNorm f ∞ volume *
          eLpNorm (iteratedFDeriv ℝ i g) p volume +
            eLpNorm (iteratedFDeriv ℝ i f) p volume * eLpNorm g ∞ volume) := by
        -- `f * g` is the bilinear expression `x ↦ mul (f x) (g x)` of the Moser estimate.
        rw [show f * g = fun x ↦ ContinuousLinearMap.mul ℝ ℝ (f x) (g x) by ext; simp]
        exact hc i _ f g (hf.of_le (by exact_mod_cast hik)) hfc (hg.of_le (by exact_mod_cast hik))
          hgc
    _ ≤ c i * 1 * (‖J‖ₑ * ‖u‖ₑ * ‖v‖ₑ + ‖u‖ₑ * (‖J‖ₑ * ‖v‖ₑ)) := by
        gcongr
        exacts [hsup u hu, eLpNorm_iteratedFDeriv_le_enorm v hg hv hik,
          eLpNorm_iteratedFDeriv_le_enorm u hf hu hik, hsup v hv]
    _ = ENNReal.ofReal (2 * c i * ‖J‖ * ‖u‖ * ‖v‖) := by
        simp (disch := positivity) only [ENNReal.ofReal_mul, ofReal_norm, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_ofNat]
        ring

/-- **The algebra estimate for test functions.** If the values of `W^{k,p}(E)` are represented in
`L^∞` by a bounded operator `J` and `2 ≤ p < ∞`, the product `a b` of two test functions on `E` is
the value of an element `P a b` of `W^{k,p}(E)`, and `P` satisfies the bilinear estimates
`‖P a b‖ ≤ C ‖a‖ ‖b‖` and `‖P a b - P a' b'‖ ≤ C ‖a - a'‖ ‖b‖ + C ‖a'‖ ‖b - b'‖` in the
`W^{k,p}` norm. -/
private theorem exists_value_ae_eq_mul_testFunction (hp : 2 ≤ p) (hp' : p ≠ ∞)
    {J : Wkp (volume : Measure E) ⊤ p k →L[ℝ]
      Lp ℝ ∞ ((volume : Measure E).restrict ((⊤ : Opens E) : Set E))}
    (hJ : ∀ u, (J u : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)]
      value k u) :
    ∃ (C : ℝ) (P : 𝓓((⊤ : Opens E), ℝ) → 𝓓((⊤ : Opens E), ℝ) → Wkp (volume : Measure E) ⊤ p k),
      (∀ a b, (value k (P a b) : E → ℝ) =ᵐ[volume] ⇑a * ⇑b) ∧
      (∀ a b, ‖P a b‖ ≤ C * ‖ofTestFunctionₗ (mu := volume) (p := p) k a‖ *
        ‖ofTestFunctionₗ (mu := volume) (p := p) k b‖) ∧
      ∀ a b a' b', ‖P a b - P a' b'‖ ≤
        C * ‖ofTestFunctionₗ (mu := volume) (p := p) k a -
          ofTestFunctionₗ (mu := volume) (p := p) k a'‖ *
            ‖ofTestFunctionₗ (mu := volume) (p := p) k b‖ +
        C * ‖ofTestFunctionₗ (mu := volume) (p := p) k a'‖ *
          ‖ofTestFunctionₗ (mu := volume) (p := p) k b -
            ofTestFunctionₗ (mu := volume) (p := p) k b'‖ := by
  obtain ⟨C, hC⟩ := exists_value_ae_eq_mul_and_norm_le_of_hasCompactSupport hp hp' hJ
  choose P hP hPn using fun a b : 𝓓((⊤ : Opens E), ℝ) ↦ hC (ofTestFunctionₗ k a)
    (ofTestFunctionₗ k b) (a.contDiff.of_le (by exact_mod_cast le_top)) a.hasCompactSupport
    (b.contDiff.of_le (by exact_mod_cast le_top)) b.hasCompactSupport
    (value_ofTestFunctionₗ_top_ae k a) (value_ofTestFunctionₗ_top_ae k b)
  refine ⟨C, P, hP, hPn, fun a b a' b' ↦ ?_⟩
  have hadd (z z' : Wkp (volume : Measure E) ⊤ p k) :
      (value k (z + z') : E → ℝ) =ᵐ[volume] value k z + value k z' := by
    simpa only [EventuallyEq, Measure.ae_restrict_coe_opens_top] using value_add_ae k z z'
  -- `a b - a' b' = (a - a') b + a' (b - b')`.
  have hsplit : P a b - P a' b' = P (a - a') b + P a' (b - b') := by
    rw [sub_eq_iff_eq_add]
    refine ext_ae ?_
    filter_upwards [hadd (P (a - a') b + P a' (b - b')) (P a' b'),
      hadd (P (a - a') b) (P a' (b - b')), hP a b, hP a' b', hP (a - a') b,
      hP a' (b - b')] with x h₁ h₂ h₃ h₄ h₅ h₆
    simp only [Pi.add_apply, Pi.mul_apply, FunLike.coe_sub, Pi.sub_apply] at h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₃, h₁, h₂, h₄, h₅, h₆]
    ring
  rw [hsplit, ← map_sub, ← map_sub]
  exact (norm_add_le _ _).trans (add_le_add (hPn _ _) (hPn _ _))

/-- **Products pass to limits.** If the values of `W^{k,p}(E)` are represented in `L^∞` by a
bounded operator `J`, and `z n → w`, `a n → u` and `b n → v` in `W^{k,p}(E)`, where the value of
each `z n` is the product of the values of `a n` and `b n`, then the value of `w` is the product of
the values of `u` and `v`: multiplication `L^∞ × Lᵖ → Lᵖ` is continuous. -/
private theorem value_ae_eq_mul_of_tendsto {J : Wkp (volume : Measure E) ⊤ p k →L[ℝ]
      Lp ℝ ∞ ((volume : Measure E).restrict ((⊤ : Opens E) : Set E))}
    (hJ : ∀ u, (J u : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)]
      value k u) {z a b : ℕ → Wkp (volume : Measure E) ⊤ p k}
    {w u v : Wkp (volume : Measure E) ⊤ p k}
    (hz : Tendsto z atTop (𝓝 w)) (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v))
    (hzab : ∀ n, (value k (z n) : E → ℝ) =ᵐ[volume] fun x ↦ value k (a n) x * value k (b n) x) :
    (value k w : E → ℝ) =ᵐ[volume] fun x ↦ value k u x * value k v x := by
  -- `M` is multiplication `L^∞ × Lᵖ → Lᵖ`; it is kept opaque so that unification does not unfold
  -- the `Lp` structure.
  obtain ⟨M, hM⟩ : ∃ M : Lp ℝ ∞ ((volume : Measure E).restrict ((⊤ : Opens E) : Set E)) →L[ℝ]
      Lp ℝ p ((volume : Measure E).restrict ((⊤ : Opens E) : Set E)) →L[ℝ]
        Lp ℝ p ((volume : Measure E).restrict ((⊤ : Opens E) : Set E)),
      ∀ f g, (M f g : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)]
        fun x ↦ f x * g x :=
    ⟨(ContinuousLinearMap.mul ℝ ℝ).holderL _ ∞ p p,
      fun f g ↦ (ContinuousLinearMap.coeFn_holder _ f g).trans
        (.of_forall fun _ ↦ ContinuousLinearMap.mul_apply' ℝ ℝ (f _) (g _))⟩
  have heq (n : ℕ) : value k (z n) = M (J (a n)) (value k (b n)) := by
    refine Lp.ext ?_
    filter_upwards [ae_restrict_of_ae (hzab n), hM (J (a n)) (value k (b n)), hJ (a n)]
      with x h₁ h₂ h₃
    rw [h₁, h₂, h₃]
  have hlim : Tendsto (fun n ↦ M (J (a n)) (value k (b n))) atTop (𝓝 (M (J u) (value k v))) :=
    (M.continuous₂.tendsto (J u, value k v)).comp
      (((J.continuous.tendsto u).comp ha).prodMk_nhds (tendsto_value hb))
  have hval : value k w = M (J u) (value k v) :=
    tendsto_nhds_unique (tendsto_value hz) (hlim.congr fun n ↦ (heq n).symm)
  rw [EventuallyEq, ← Measure.ae_restrict_coe_opens_top]
  filter_upwards [hM (J u) (value k v), hJ u] with x h₁ h₂
  rw [hval, h₁, h₂]

/-- **`W^{k,p}(E)`, `k p > dim E`, is an algebra.** For `2 ≤ p < ∞` and `k p > dim E` there is a
constant `C` such that for all `u, v ∈ W^{k,p}(E)` on the whole space, the pointwise product of
their values is the value of some `w ∈ W^{k,p}(E)` with `‖w‖ ≤ C ‖u‖ ‖v‖`. Finiteness of `p` is
implied by `k p > dim E`, since `∞.toReal = 0`. -/
theorem exists_norm_mul_le (hp : 2 ≤ p) (hk : (finrank ℝ E : ℝ) < k * p.toReal) :
    ∃ C, ∀ u v : Wkp (volume : Measure E) ⊤ p k, ∃ w : Wkp (volume : Measure E) ⊤ p k,
      (value k w : E → ℝ) =ᵐ[volume] (fun x ↦ value k u x * value k v x) ∧
        ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hp' : p ≠ ∞ := ne_top_of_natCast_lt_mul_toReal hk
  set T := ofTestFunctionₗ (mu := (volume : Measure E)) (Omega := ⊤) (p := p) k
  obtain ⟨J, hJ⟩ := exists_toLpTop (ENNReal.one_lt_two.trans_le hp) hp' hk
  obtain ⟨C, P, hP, hPn, hPsub⟩ := exists_value_ae_eq_mul_testFunction hp hp' hJ
  -- Approximate `u` and `v` by test functions.
  have hseq (z : Wkp (volume : Measure E) ⊤ p k) :
      ∃ φ : ℕ → 𝓓((⊤ : Opens E), ℝ), Tendsto (fun n ↦ T (φ n)) atTop (𝓝 z) := by
    obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 (denseRange_ofTestFunctionₗ_top hp' k z)
    choose φ hφ using hx
    exact ⟨φ, by rwa [show (fun n ↦ T (φ n)) = x from funext hφ]⟩
  refine ⟨C, fun u v ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hseq u
  obtain ⟨ψ, hψ⟩ := hseq v
  -- The products `P (φ n) (ψ n)` form a Cauchy sequence, by the estimate for differences.
  have hcauchy : CauchySeq fun n ↦ P (φ n) (ψ n) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_fst
    have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_snd
    have hu0 := cauchySeq_iff_tendsto_dist_atTop_0.1 hφ.cauchySeq
    have hv0 := cauchySeq_iff_tendsto_dist_atTop_0.1 hψ.cauchySeq
    simp only [dist_eq_norm] at hu0 hv0
    have h0 : Tendsto (fun n : ℕ × ℕ ↦ C * ‖T (φ n.1) - T (φ n.2)‖ * ‖T (ψ n.1)‖ +
        C * ‖T (φ n.2)‖ * ‖T (ψ n.1) - T (ψ n.2)‖) atTop (𝓝 0) := by
      simpa using ((hu0.const_mul C).mul (hψ.comp hfst).norm).add
        (((hφ.comp hsnd).norm.const_mul C).mul hv0)
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (dist_eq_norm _ _).trans_le (hPsub _ _ _ _)) h0
  -- Its limit has the product of the values of `u` and `v` as value.
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨w, value_ae_eq_mul_of_tendsto hJ hw hφ hψ fun n ↦ ?_,
    le_of_tendsto_of_tendsto' hw.norm ((hφ.norm.const_mul C).mul hψ.norm) fun n ↦ hPn _ _⟩
  filter_upwards [hP (φ n) (ψ n), value_ofTestFunctionₗ_top_ae (p := p) k (φ n),
    value_ofTestFunctionₗ_top_ae (p := p) k (ψ n)] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, Pi.mul_apply]

/-- **Multiplication in `W^{k,p}(E)` for `2 ≤ p` and `k p > dim E`**, as a bounded bilinear map:
there is a constant `C`, the norm of `mulOfFinrankLtL hp hk`, with `‖u v‖ ≤ C ‖u‖ ‖v‖`
(`ContinuousLinearMap.le_opNorm₂`). The value of `mulOfFinrankLtL hp hk u v` is the pointwise
product of the values of `u` and `v` (`TauCeti.Wkp.value_mulOfFinrankLtL_ae`), and this determines
it (`TauCeti.Wkp.eq_mulOfFinrankLtL_iff`). -/
def mulOfFinrankLtL (hp : 2 ≤ p) (hk : (finrank ℝ E : ℝ) < k * p.toReal) :
    Wkp (volume : Measure E) ⊤ p k →L[ℝ]
      Wkp (volume : Measure E) ⊤ p k →L[ℝ] Wkp (volume : Measure E) ⊤ p k :=
  bilinOfAeMul k
    (fun u v ↦ by
      obtain ⟨_, hC⟩ := exists_norm_mul_le hp hk
      obtain ⟨w, hw, -⟩ := hC u v
      exact ⟨w, ae_restrict_of_ae hw⟩)
    fun u ↦ by
      -- The value of `u` is bounded by the `L^∞` norm of its image under the Sobolev embedding.
      obtain ⟨J, hJ⟩ := exists_toLpTop (ENNReal.one_lt_two.trans_le hp)
        (ne_top_of_natCast_lt_mul_toReal hk) hk
      refine ⟨‖J u‖, ?_⟩
      filter_upwards [hJ u, Lp.ae_norm_le_norm_top (J u)] with x h₁ h₂
      rwa [← h₁]

/-- The value of the product `mulOfFinrankLtL hp hk u v` is the pointwise product of the values. -/
theorem value_mulOfFinrankLtL_ae (hp : 2 ≤ p) (hk : (finrank ℝ E : ℝ) < k * p.toReal)
    (u v : Wkp (volume : Measure E) ⊤ p k) :
    (value k (mulOfFinrankLtL hp hk u v) : E → ℝ) =ᵐ[volume]
      fun x ↦ value k u x * value k v x := by
  rw [EventuallyEq, ← Measure.ae_restrict_coe_opens_top]
  exact value_bilinOfAeMul_ae u v

/-- The product `mulOfFinrankLtL hp hk u v` is the unique element of `W^{k,p}(E)` whose value is
the pointwise product of the values of `u` and `v`. -/
theorem eq_mulOfFinrankLtL_iff (hp : 2 ≤ p) (hk : (finrank ℝ E : ℝ) < k * p.toReal)
    {u v w : Wkp (volume : Measure E) ⊤ p k} :
    w = mulOfFinrankLtL hp hk u v ↔
      (value k w : E → ℝ) =ᵐ[volume] fun x ↦ value k u x * value k v x := by
  rw [EventuallyEq, ← Measure.ae_restrict_coe_opens_top]
  exact eq_bilinOfAeMul_iff

/-- Multiplication in `W^{k,p}(E)` is commutative. -/
theorem mulOfFinrankLtL_comm (hp : 2 ≤ p) (hk : (finrank ℝ E : ℝ) < k * p.toReal)
    (u v : Wkp (volume : Measure E) ⊤ p k) :
    mulOfFinrankLtL hp hk u v = mulOfFinrankLtL hp hk v u :=
  bilinOfAeMul_comm u v

/-- Multiplication in `W^{k,p}(E)` is associative. -/
theorem mulOfFinrankLtL_assoc (hp : 2 ≤ p) (hk : (finrank ℝ E : ℝ) < k * p.toReal)
    (u v w : Wkp (volume : Measure E) ⊤ p k) :
    mulOfFinrankLtL hp hk (mulOfFinrankLtL hp hk u v) w =
      mulOfFinrankLtL hp hk u (mulOfFinrankLtL hp hk v w) :=
  bilinOfAeMul_assoc u v w

/-- For `p > dim E` and `2 ≤ p`, multiplication `mulOfFinrankLtL` agrees with the supercritical
multiplication `TauCeti.Wkp.mulL` on `W^{j+1,p}(E)`. -/
theorem mulOfFinrankLtL_eq_mulL {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] (hp : 2 ≤ (q : ℝ≥0∞))
    (hq : (finrank ℝ E : ℝ≥0) < q) {j : ℕ}
    (hk : (finrank ℝ E : ℝ) < (j + 1 : ℕ) * (q : ℝ≥0∞).toReal) :
    mulOfFinrankLtL hp hk = mulL (mu := (volume : Measure E)) hq j := by
  ext u v
  exact (eq_mulL_iff hq).2 (value_mulOfFinrankLtL_ae hp hk u v)

end Wkp

/-- **Products of classical functions with `Lᵖ` derivatives.** If `2 ≤ p < ∞` and `k p > dim E`,
there is a constant `C` such that for all functions `f` and `g` that are `Cᵏ` on `E` with
derivatives in `Lᵖ` through order `k`, the derivatives of `f g` through order `k` are in `Lᵖ` and

`∑_{i ≤ k} ‖Dⁱ (f g)‖_p ≤ C (∑_{i ≤ k} ‖Dⁱ f‖_p) (∑_{i ≤ k} ‖Dⁱ g‖_p)`. -/
theorem exists_sum_lpNorm_iteratedFDeriv_mul_le (hp : 2 ≤ p)
    (hk : (finrank ℝ E : ℝ) < k * p.toReal) :
    ∃ C, ∀ f g : E → ℝ, ContDiff ℝ k f → ContDiff ℝ k g →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) p) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) p) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (f * g)) p) ∧
        ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f * g)) p volume ≤
          C * (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) p volume) *
            ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) p volume := by
  have hres : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume :=
    Measure.restrict_coe_opens_top volume
  obtain ⟨C, hC⟩ := Wkp.exists_norm_mul_le (E := E) hp hk
  refine ⟨(k + 1) * max C 0, fun f g hf hg hfm hgm ↦ ?_⟩
  obtain ⟨u, hu, hun⟩ := Wkp.exists_value_ae_eq_and_norm_le hf hfm
  obtain ⟨v, hv, hvn⟩ := Wkp.exists_value_ae_eq_and_norm_le hg hgm
  obtain ⟨w, hw, hwn⟩ := hC u v
  have hfg : ContDiff ℝ k (f * g) := hf.mul hg
  -- `w` represents `f g`.
  have hw' : (Wkp.value k w : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)]
      f * g := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hw, hu, hv] with x hx hux hvx
    rw [hx, hux, hvx, Pi.mul_apply]
  refine ⟨fun i hi ↦ by
    simpa only [hres] using Wkp.memLp_iteratedFDeriv_of_contDiffOn k w hfg.contDiffOn hw' i hi, ?_⟩
  have hle : ∀ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f * g)) p volume ≤ ‖w‖ :=
    fun i hi ↦ by
      simpa only [hres] using Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k w hfg.contDiffOn hw' i
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hSf : 0 ≤ ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) p volume :=
    (norm_nonneg u).trans hun
  have hwC : ‖w‖ ≤ max C 0 *
      (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) p volume) *
        ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) p volume :=
    hwn.trans <| mul_le_mul (mul_le_mul (le_max_left _ _) hun (norm_nonneg _) (le_max_right _ _))
      hvn (norm_nonneg _) (mul_nonneg (le_max_right _ _) hSf)
  calc ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f * g)) p volume
      ≤ ∑ _i ∈ Finset.range (k + 1), ‖w‖ := Finset.sum_le_sum hle
    _ = (k + 1) * ‖w‖ := by simp
    _ ≤ (k + 1) * (max C 0 *
          (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) p volume) *
            ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) p volume) := by
      gcongr
    _ = (k + 1) * max C 0 *
          (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) p volume) *
            ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) p volume := by ring

end TauCeti
