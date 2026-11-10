/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Embedding
public import TauCeti.Analysis.Sobolev.W1p.Density
public import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.Analysis.Sobolev.W1p.HolderEmbedding
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Whole-space and interior Sobolev embeddings

Let `E` be a finite-dimensional real inner product space of dimension `n`, with an additive Haar
measure, let `1 ≤ p < n` and let `p⋆ = np/(n - p)` be the Sobolev conjugate, so that
`1/p⋆ + 1/n = 1/p`. The embedding `W^{1,p}_0(Ω) ↪ L^{p⋆}(Ω)` of
`TauCeti.W1p0.sobolevEmbeddingL` needs vanishing boundary values. This file removes that
hypothesis in the two situations where no boundary regularity is needed.

* **The whole space.** Test functions are dense in `W^{1,p}(E)` for `p < ∞`
  (`TauCeti.W1p.mem_w1p0Submodule_top`), so `W^{1,p}(E) = W^{1,p}_0(E)` and the embedding applies
  to every `u ∈ W^{1,p}(E)`, with the bound `‖u‖_{p⋆} ≤ C ‖∇u‖_p` by the gradient alone.
* **The interior of a domain.** If `V` has compact closure inside an open set `Ω`, a smooth
  cutoff `χ` equal to `1` near `closure V` and compactly supported in `Ω` turns `u ∈ W^{1,p}(Ω)`
  into `χu ∈ W^{1,p}(E)` (`TauCeti.W1p.localizeL`), which agrees with `u` on `V`. The whole-space
  embedding then bounds `u` in `L^{p⋆}(V)` by `C ‖u‖_{W^{1,p}(Ω)}`. Here the full norm is needed
  on the right, since the cutoff produces the term `u ∇χ`.

As `V` has finite measure, Hölder's inequality also gives the bound in `L^q(V)` for every
`q ≤ p⋆`. No boundedness or regularity of `Ω` itself is assumed.

For arbitrary finite source exponents, the interior inclusion into finite `L^s` is also bounded
whenever the source exponent `q` satisfies `q ≤ s` and `1/q - 1/s < 1/n`.
This includes `q = n` and `q > n`. The proof localizes
into a bounded zero-boundary domain and uses the finite-measure Sobolev inequality. For `q > n`,
the native Morrey embedding also gives a bounded interior inclusion into `L^∞`.

## Main declarations

* `TauCeti.W1p.sobolevEmbeddingTopL`: the embedding `W^{1,p}(E) →L[ℝ] L^{p⋆}(E)`, with
  `TauCeti.W1p.coeFn_sobolevEmbeddingTopL` (it does not change the function) and
  `TauCeti.W1p.norm_sobolevEmbeddingTopL_le` (the Gagliardo--Nirenberg--Sobolev bound).
* `TauCeti.W1p.exists_eLpNorm_value_le_of_ae_eq`: a bounded linear map into `L^{p⋆}(V)`
  representing the values gives `L^q(V)` bounds for `q ≤ p⋆` when `V` has finite measure.
* `TauCeti.W1p.exists_lpEmbeddingL_of_eLpNorm_value_le`: conversely, a uniform `L^r(V)` bound on
  the values gives a bounded linear map into `L^r(V)` representing them.
* `TauCeti.W1p.exists_sobolevEmbeddingL_of_isCompact_closure`: the interior embedding
  `W^{1,p}(Ω) →L[ℝ] L^{p⋆}(V)`.
* `TauCeti.W1p.exists_eLpNorm_value_le_of_isCompact_closure` and
  `TauCeti.W1p.memLp_value_of_isCompact_closure`: the interior estimate
  `‖u‖_{L^q(V)} ≤ C ‖u‖_{W^{1,p}(Ω)}` and integrability for `q ≤ p⋆`.

* `TauCeti.W1p.exists_sobolevEmbeddingL_of_subcritical_gain`: the bounded interior inclusion
  for finite source exponent `q` and target exponent `s` with `q ≤ s` and `1/q - 1/s < 1/n`.
* `TauCeti.W1p.exists_lpInftyEmbeddingL_of_isCompact_closure`: the supercritical interior
  inclusion into `L^∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.1, Theorems 1 and 2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.9 and Corollary 9.10.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p pstar : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The whole space -/

/-- **The Sobolev embedding `W^{1,p}(E) ↪ L^{p⋆}(E)` on the whole space.** For `1 ≤ p` and
`1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, inclusion is a continuous linear map. Unlike on a domain, no
boundary condition is needed: every `u ∈ W^{1,p}(E)` is a limit of test functions.
`TauCeti.W1p.coeFn_sobolevEmbeddingTopL` says the image of `u` is `u` itself, and
`TauCeti.W1p.norm_sobolevEmbeddingTopL_le` bounds it by the gradient alone. -/
def W1p.sobolevEmbeddingTopL (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    W1p mu ⊤ p →L[ℝ] Lp ℝ pstar (mu.restrict (⊤ : Opens E)) := by
  letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  exact (W1p0.sobolevEmbeddingL hpstar hexp).comp <|
    (ContinuousLinearMap.id ℝ (W1p mu ⊤ p)).codRestrict (w1p0Submodule mu ⊤ p).toSubmodule
      fun u => (ClosedSubmodule.mem_toSubmodule_iff _ _).2
        (W1p.mem_w1p0Submodule_top (ne_top_of_inv_add_inv_eq_inv hexp) u)

private theorem W1p.sobolevEmbeddingTopL_apply (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p mu ⊤ p) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    W1p.sobolevEmbeddingTopL hpstar hexp u = W1p0.sobolevEmbeddingL hpstar hexp
      ⟨u, (ClosedSubmodule.mem_toSubmodule_iff _ _).2
        (W1p.mem_w1p0Submodule_top (ne_top_of_inv_add_inv_eq_inv hexp) u)⟩ :=
  (rfl)

/-- The whole-space Sobolev embedding does not change the function. -/
theorem W1p.coeFn_sobolevEmbeddingTopL (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p mu ⊤ p) :
    W1p.sobolevEmbeddingTopL hpstar hexp u =ᵐ[mu.restrict (⊤ : Opens E)] W1p.value u := by
  rw [W1p.sobolevEmbeddingTopL_apply]
  exact W1p0.coeFn_sobolevEmbeddingL hpstar hexp _

/-- **The Gagliardo--Nirenberg--Sobolev inequality on `W^{1,p}(E)`.** The image of `u` under the
whole-space Sobolev embedding is bounded in `L^{p⋆}` by the `Lᵖ` norm of the gradient of `u`
alone, with Mathlib's constant `MeasureTheory.SNormLESNormFDerivOfEqConst`. -/
theorem W1p.norm_sobolevEmbeddingTopL_le (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p mu ⊤ p) :
    ‖W1p.sobolevEmbeddingTopL hpstar hexp u‖ ≤
      SNormLESNormFDerivOfEqConst ℝ mu p.toReal * ‖W1p.gradient u‖ := by
  rw [W1p.sobolevEmbeddingTopL_apply]
  exact W1p0.norm_sobolevEmbeddingL_le hpstar hexp _

/-- The whole-space Sobolev embedding is injective. -/
theorem W1p.sobolevEmbeddingTopL_injective (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    Function.Injective (W1p.sobolevEmbeddingTopL (mu := mu) (p := p) hpstar hexp) := by
  intro u v huv
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.coeFn_sobolevEmbeddingTopL hpstar hexp u,
    W1p.coeFn_sobolevEmbeddingTopL hpstar hexp v] with x hu hv
  rw [← hu, ← hv, huv]

/-! ### Lower exponents on a set of finite measure -/

omit [FiniteDimensional ℝ E] in
/-- **Lower exponents on a set of finite measure.** If a bounded linear map
`S : W^{1,p}(Ω) → L^{p⋆}(V)` represents the values, `S u = u` almost everywhere on `V`, and `V`
has finite measure, then `‖u‖_{L^q(V)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for every `q ≤ p⋆`, by Hölder's
inequality on `V`. -/
theorem W1p.exists_eLpNorm_value_le_of_ae_eq [Fact (1 ≤ pstar)] {V : Set E} (hV : mu V ≠ ∞)
    {q : ℝ≥0∞} (hq : q ≤ pstar) (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict V))
    (hS : ∀ u, S u =ᵐ[mu.restrict V] W1p.value u) :
    ∃ C : ℝ≥0, ∀ u : W1p mu Omega p,
      eLpNorm (W1p.value u) q (mu.restrict V) ≤ C * ‖u‖ₑ :=
  exists_eLpNorm_le_mul_enorm_of_ae_eq (by rwa [Measure.restrict_apply_univ]) hq S hS

omit [FiniteDimensional ℝ E] in
/-- **Inclusions from value bounds.** A uniform estimate `‖u‖_{L^r(V)} ≤ C ‖u‖_{W^{1,p}(Ω)}` on a
subset `V ⊆ Ω` makes restricting the values of `u ∈ W^{1,p}(Ω)` to `V` a continuous linear map
`W^{1,p}(Ω) → L^r(V)`. -/
theorem W1p.exists_lpEmbeddingL_of_eLpNorm_value_le {r : ℝ≥0∞} [Fact (1 ≤ r)] {V : Set E}
    (hVΩ : V ⊆ Omega) (hbound : ∃ C : ℝ≥0, ∀ u : W1p mu Omega p,
      eLpNorm (W1p.value u) r (mu.restrict V) ≤ C * ‖u‖ₑ) :
    ∃ S : W1p mu Omega p →L[ℝ] Lp ℝ r (mu.restrict V),
      ∀ u, S u =ᵐ[mu.restrict V] W1p.value u := by
  obtain ⟨C, hC⟩ := hbound
  have hm (u : W1p mu Omega p) : MemLp (W1p.value u) r (mu.restrict V) :=
    (hC u).trans_lt (by finiteness)
  let L : W1p mu Omega p →ₗ[ℝ] Lp ℝ r (mu.restrict V) :=
    { toFun u := (hm u).toLp (W1p.value u)
      map_add' u v := by
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        apply ae_restrict_of_ae_restrict_of_subset hVΩ
        exact W1p.value_add_ae u v
      map_smul' c u := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        apply ae_restrict_of_ae_restrict_of_subset hVΩ
        exact W1p.value_smul_ae c u }
  refine ⟨L.mkContinuous C (fun u ↦ ?_), fun u ↦ (hm u).coeFn_toLp⟩
  -- This bound is for the anonymous linear map L before mkContinuous is constructed.
  -- Its function projection is the chosen toLp representative; exposing that projection
  -- lets the public norm_toLp law apply without unfolding the representative itself.
  change ‖(hm u).toLp (W1p.value u)‖ ≤ _
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm] using
    ENNReal.toReal_mono (by finiteness : C * ‖u‖ₑ ≠ ∞) (hC u)

/-! ### The interior of a domain -/

/-- **The interior Sobolev embedding.** If `V` has compact closure contained in the open set `Ω`,
`1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then restricting `u ∈ W^{1,p}(Ω)` to `V` is a
continuous linear map `W^{1,p}(Ω) → L^{p⋆}(V)`. Neither boundedness nor boundary regularity of
`Ω` is assumed. -/
theorem W1p.exists_sobolevEmbeddingL_of_isCompact_closure (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) {V : Set E}
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ Omega) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict V),
      ∀ u, S u =ᵐ[mu.restrict V] W1p.value u := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨ψ, M, hψ, -, hone, -, hts, hM, hψM, hgM⟩ :=
    hVc.exists_contDiff_cutoff_with_bounds Omega.isOpen hVO
  -- Multiply by the cutoff and extend by zero to the whole space.
  let T := W1p.localizeL (μ := mu) (p := p) (le_top : Omega ≤ ⊤) ψ hψ hM (fun x _ => hψM x)
    (fun x _ => hgM x) (fun x hx => hts hx.2)
  have hle : mu.restrict V ≤ (1 : ℝ≥0∞) • mu.restrict ((⊤ : Opens E) : Set E) := by
    rw [one_smul]
    exact Measure.restrict_mono_set mu (by simp)
  refine ⟨(Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle).comp
    ((W1p.sobolevEmbeddingTopL hpstar hexp).comp T), fun u => ?_⟩
  -- On the open set `W ⊇ V` where `ψ = 1`, the localized function is `u`.
  set W : Set E := interior (ψ ⁻¹' {1}) ∩ Omega
  have hVW : V ⊆ W := fun x hx => ⟨hone (subset_closure hx), hVO (subset_closure hx)⟩
  have hTW : W1p.value (T u) =ᵐ[mu.restrict W] W1p.value u := by
    have hW : MeasurableSet W := (isOpen_interior.inter Omega.isOpen).measurableSet
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (by simp)
        (W1p.value_localizeL_ae (μ := mu) (p := p) (le_top : Omega ≤ ⊤) hψ hM
          (fun x _ => hψM x) (fun x _ => hgM x) (fun x hx => hts hx.2) u),
      ae_restrict_mem hW] with x hx hxW
    have hψx : ψ x = 1 := interior_subset hxW.1
    rw [hx, indicator_of_mem hxW.2, hψx, one_smul]
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle
      (W1p.sobolevEmbeddingTopL hpstar hexp (T u)),
    ae_restrict_of_ae_restrict_of_subset (by simp)
      (W1p.coeFn_sobolevEmbeddingTopL hpstar hexp (T u)),
    ae_restrict_of_ae_restrict_of_subset hVW hTW] with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3]

/-- **The interior Sobolev inequality.** If `V` has compact closure contained in the open set
`Ω`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every `q ≤ p⋆` there is a constant
`C` with `‖u‖_{L^q(V)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for all `u ∈ W^{1,p}(Ω)`. The full Sobolev norm is
needed on the right: on a bounded `Ω`, a nonzero constant has vanishing gradient. -/
theorem W1p.exists_eLpNorm_value_le_of_isCompact_closure (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) {V : Set E}
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ Omega) {q : ℝ≥0∞} (hq : q ≤ pstar) :
    ∃ C : ℝ≥0, ∀ u : W1p mu Omega p,
      eLpNorm (W1p.value u) q (mu.restrict V) ≤ C * ‖u‖ₑ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isCompact_closure (mu := mu) (Omega := Omega)
    (p := p) hpstar hexp hVc hVO
  exact W1p.exists_eLpNorm_value_le_of_ae_eq
    (measure_ne_top_of_subset subset_closure hVc.measure_lt_top.ne) hq S hS

/-- **Interior integrability.** If `V` has compact closure contained in the open set `Ω`, every
`u ∈ W^{1,p}(Ω)` lies in `L^q(V)` for every `q ≤ p⋆`, where `1/p⋆ + 1/n = 1/p` and `p⋆ < ∞`. -/
theorem W1p.memLp_value_of_isCompact_closure (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) {V : Set E}
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ Omega) {q : ℝ≥0∞} (hq : q ≤ pstar)
    (u : W1p mu Omega p) : MemLp (W1p.value u) q (mu.restrict V) := by
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_value_le_of_isCompact_closure (mu := mu) hpstar hexp
    hVc hVO hq
  have hfin : C * ‖u‖ₑ < ∞ := by finiteness
  exact (hC u).trans_lt hfin

end TauCeti

public noncomputable section

namespace TauCeti

open MeasureTheory Metric Set TopologicalSpace Module
open scoped ENNReal NNReal Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {q s : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- Interior Sobolev embedding with any finite subcritical gain, including when the source
exponent equals or exceeds the dimension. -/
theorem W1p.exists_eLpNorm_value_le_of_subcritical_gain
    (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : W1p μ Ω (q : ℝ≥0∞),
      eLpNorm (W1p.value u) s (μ.restrict V) ≤ C * ‖u‖ₑ := by
  obtain ⟨U, hUf, hVU, T, hTrep⟩ :=
    W1p.exists_zeroBoundaryLocalization (μ := μ) (Ω := Ω) (p := (q : ℝ≥0∞))
      ENNReal.coe_ne_top hVc hVΩ
  let δ : ℝ := (q : ℝ)⁻¹ - (s : ℝ)⁻¹
  let A : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ *
    μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
    ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)) *
    μ U ^ ((finrank ℝ E : ℝ)⁻¹ - δ)
  have hAf : A ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hgap.le) hUf)
  refine ⟨(A * ‖T‖ₑ).toNNReal, fun u ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top hAf (by finiteness))]
  calc
    _ = eLpNorm (W1p.value (T u).1) s (μ.restrict V) := eLpNorm_congr_ae (hTrep u).symm
    _ ≤ eLpNorm (W1p.value (T u).1) s (μ.restrict U) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono_set μ hVU)
    _ ≤ A * ‖W1p.gradient (T u).1‖ₑ := by
      exact W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt
        ENNReal.coe_ne_top hUf (by exact_mod_cast hqs)
        (by simp) hgap (T u).2
    _ ≤ A * ‖T u‖ₑ := by
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (W1p.norm_gradient_le (T u).1)
    _ ≤ A * (‖T‖ₑ * ‖u‖ₑ) := by gcongr; exact T.le_opENorm u
    _ = _ := (mul_assoc _ _ _).symm

/-- A bounded linear interior Sobolev inclusion for every finite subcritical gain. -/
theorem W1p.exists_sobolevEmbeddingL_of_subcritical_gain [Fact (1 ≤ (s : ℝ≥0∞))]
    (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ S : W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp ℝ (s : ℝ≥0∞) (μ.restrict V),
      ∀ u, S u =ᵐ[μ.restrict V] W1p.value u :=
  W1p.exists_lpEmbeddingL_of_eLpNorm_value_le (subset_closure.trans hVΩ)
    (W1p.exists_eLpNorm_value_le_of_subcritical_gain hqs hgap hVc hVΩ)

omit [Nontrivial E] in
/-- The supercritical interior inclusion into `L^∞` is bounded and preserves the Sobolev value. -/
theorem W1p.exists_lpInftyEmbeddingL_of_isCompact_closure
    (hq : (finrank ℝ E : ℝ≥0) < q) {V : Set E}
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ S : W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp ℝ ∞ (μ.restrict V),
      ∀ u, S u =ᵐ[μ.restrict V] W1p.value u := by
  obtain ⟨U, -, hVU, T, hT⟩ :=
    W1p.exists_zeroBoundaryLocalization (μ := μ) (Ω := Ω) (p := (q : ℝ≥0∞))
      ENNReal.coe_ne_top hVc hVΩ
  let Z : W1p μ Ω (q : ℝ≥0∞) →L[ℝ] W1p μ ⊤ (q : ℝ≥0∞) :=
    (w1p0Submodule μ ⊤ (q : ℝ≥0∞)).toSubmodule.subtypeL.comp
      ((W1p0.extendByZeroL le_top).comp T)
  let H := (W1p.morreyEmbedding (mu := μ) hq).comp Z
  have hH (u : W1p μ Ω (q : ℝ≥0∞)) :
      H u =ᵐ[μ.restrict V] W1p.value u := by
    have hz := coeFn_extendByZeroLpₗᵢ ℝ U.isOpen.measurableSet
      (show (U : Set E) ⊆ ((⊤ : Opens E) : Set E) from subset_univ _)
      (W1p.value (T u).1)
    rw [← W1p0.value_extendByZeroL (le_top : U ≤ ⊤)] at hz
    have hmor := ae_restrict_of_ae (s := V) (W1p.value_ae_eq_morreyEmbedding hq (Z u))
    have hmem : ∀ᵐ x ∂μ.restrict V, x ∈ U :=
      ae_restrict_of_ae_restrict_of_subset hVU (ae_restrict_mem U.isOpen.measurableSet)
    filter_upwards [hmor, ae_restrict_of_ae_restrict_of_subset (subset_univ V) hz,
      hT u, hmem] with x hm he ht hx
    simp only [H, ContinuousLinearMap.comp_apply]
    rw [← hm]
    simp only [Z, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [he, indicator_of_mem hx, ht]
  apply W1p.exists_lpEmbeddingL_of_eLpNorm_value_le (subset_closure.trans hVΩ)
  refine ⟨‖H‖₊, fun u ↦ ?_⟩
  rw [← eLpNorm_congr_ae (hH u)]
  calc
    _ ≤ ‖(H u).toBoundedContinuousFunction‖ₑ := by
      have hb := eLpNorm_le_of_ae_bound (p := ∞) (μ := μ.restrict V)
        (H u).toBoundedContinuousFunction.continuous.aestronglyMeasurable
        (.of_forall fun x ↦ (H u).toBoundedContinuousFunction.norm_coe_le_norm x)
      have he : ((H u).toBoundedContinuousFunction : E → ℝ) = H u := by
        funext x
        exact HolderSpace.toBoundedContinuousFunction_apply _ _
      rw [he] at hb
      simpa only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul, ofReal_norm] using hb
    _ ≤ ‖H u‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (HolderSpace.norm_toBoundedContinuousFunction_le (H u))
    _ ≤ _ := H.le_opENorm u

end TauCeti
