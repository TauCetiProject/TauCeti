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

/-!
# The Sobolev embedding `W^{1,p} ↪ L^{p⋆}` on the whole space and in the interior

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

## Main declarations

* `TauCeti.W1p.sobolevEmbeddingTopL`: the embedding `W^{1,p}(E) →L[ℝ] L^{p⋆}(E)`, with
  `TauCeti.W1p.coeFn_sobolevEmbeddingTopL` (it does not change the function) and
  `TauCeti.W1p.norm_sobolevEmbeddingTopL_le` (the Gagliardo--Nirenberg--Sobolev bound).
* `TauCeti.W1p.exists_eLpNorm_value_le_of_ae_eq`: a bounded linear map into `L^{p⋆}(V)`
  representing the values gives `L^q(V)` bounds for `q ≤ p⋆` when `V` has finite measure.
* `TauCeti.W1p.exists_sobolevEmbeddingL_of_isCompact_closure`: the interior embedding
  `W^{1,p}(Ω) →L[ℝ] L^{p⋆}(V)`.
* `TauCeti.W1p.exists_eLpNorm_value_le_of_isCompact_closure` and
  `TauCeti.W1p.memLp_value_of_isCompact_closure`: the interior estimate
  `‖u‖_{L^q(V)} ≤ C ‖u‖_{W^{1,p}(Ω)}` and integrability for `q ≤ p⋆`.

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
      eLpNorm (W1p.value u) q (mu.restrict V) ≤ C * ‖u‖ₑ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · refine ⟨0, fun u => ?_⟩
    rw [eLpNorm_exponent_zero ((Lp.aestronglyMeasurable (S u)).congr (hS u))]
    exact zero_le
  have hexp : 0 ≤ 1 / q.toReal - 1 / pstar.toReal := by
    rw [sub_nonneg]
    rcases eq_or_ne pstar ∞ with h | h
    · simp only [h, ENNReal.toReal_top, div_zero]
      positivity
    · exact one_div_le_one_div_of_le (ENNReal.toReal_pos hq0 (ne_top_of_le_ne_top h hq))
        (ENNReal.toReal_mono h hq)
  have hc : mu V ^ (1 / q.toReal - 1 / pstar.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hexp hV
  refine ⟨‖S‖₊ * (mu V ^ (1 / q.toReal - 1 / pstar.toReal)).toNNReal, fun u => ?_⟩
  calc eLpNorm (W1p.value u) q (mu.restrict V)
      ≤ eLpNorm (W1p.value u) pstar (mu.restrict V) *
          mu.restrict V univ ^ (1 / q.toReal - 1 / pstar.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hq (pos_iff_ne_zero.2 hq0)
    _ = ‖S u‖ₑ * mu V ^ (1 / q.toReal - 1 / pstar.toReal) := by
        rw [Lp.enorm_def, eLpNorm_congr_ae (hS u), Measure.restrict_apply_univ]
    _ ≤ ‖S‖ₑ * ‖u‖ₑ * mu V ^ (1 / q.toReal - 1 / pstar.toReal) := by
        gcongr
        exact S.le_opENorm u
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hc, enorm_eq_nnnorm]
        ring

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
