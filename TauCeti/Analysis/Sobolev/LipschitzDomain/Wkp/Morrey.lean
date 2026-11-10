/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Morrey
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Embedding
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Higher-order Morrey embeddings on bounded Lipschitz domains

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n`, let `1 ≤ p` and let `k ≥ 1` with
`n < k p`. Every `u ∈ W^{k,p}(Ω)` has a representative which extends continuously to the closure
of `Ω` and is Hölder there, and the resulting map `W^{k,p}(Ω) → C^{0,γ}(closure Ω)` is a bounded
linear map. In particular members of `W^{k,p}(Ω)` with `n < k p` have continuous representatives
up to the boundary.

The proof lowers the order one step at a time with the Sobolev embedding
`W^{j+1,r}(Ω) → W^{j,s}(Ω)`, valid whenever `1/r ≤ 1/s + 1/n` with `s < ∞`, until it reaches
`W^{1,q}(Ω)` with `n < q < ∞`, and then applies Morrey's embedding
`TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith`. When `1/r < 1/s + 1/n` the step
first lowers the integrability exponent of `W^{1,r}(Ω)`, which is harmless on the bounded set `Ω`;
this avoids the critical exponent `r = n`, where the first-order Sobolev embedding has no finite
target.

* If `k p < n + p` and `(k - 1) p < n`, the exponents `1/q = 1/p - (k - 1)/n` of the exact Sobolev
  chain stay positive and the Hölder exponent is the sharp `1 - n/q = k - n/p`.
* In general, for `n ≥ 2`, the chain with equal steps `1/(k p)` reaches `q = k p` and gives the
  exponent `1 - n/(k p)`. The remaining case `n = 1 = p` is `W^{k,1}` of an interval, which is not
  treated here.

Composed with the compact inclusion of Hölder spaces, the embedding into `C^{0,β}(closure Ω)` is a
compact operator for every small enough `β > 0`.

## Main declarations

* `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] C^{0,1-n/q}(closure Ω)` for `1/q + k/n = 1/p` and `n < q < ∞`.
* `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith`: for `n < k p` a Hölder
  embedding `W^{k,p}(Ω) →L[ℝ] C^{0,γ}(closure Ω)` with some `γ > 0`.
* `TauCeti.Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith`: the embedding into
  `C^{0,β}(closure Ω)` is compact for every `β` below that `γ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6 (ii).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part II, and
  Theorem 6.3, Part IV.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- On a finite measure space, `Lᵖ` includes continuously into `L^q` for `q ≤ p`. -/
private theorem exists_lpInclusionL {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : Measure α} (hμ : μ univ ≠ ∞) {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hqp : q ≤ p) :
    ∃ J : Lp F p μ →L[ℝ] Lp F q μ, ∀ f, J f =ᵐ[μ] f := by
  have : IsFiniteMeasure μ := ⟨hμ.lt_top⟩
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_enorm_of_ae_eq hμ hqp (ContinuousLinearMap.id ℝ _)
    (v := fun f : Lp F p μ ↦ (f : α → F)) (fun f ↦ by simp)
  let J : Lp F p μ →ₗ[ℝ] Lp F q μ :=
    { toFun := fun f ↦ ((Lp.memLp f).mono_exponent hqp).toLp f
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add f g)
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c f) }
  refine ⟨J.mkContinuous C fun f ↦ ?_, fun f ↦ MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hqp)⟩
  have h : ‖J f‖ₑ ≤ C * ‖f‖ₑ := by
    rw [Lp.enorm_def]
    exact (eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hqp))).trans_le (hC f)
  calc ‖J f‖ = ‖J f‖ₑ.toReal := (toReal_enorm _).symm
    _ ≤ (C * ‖f‖ₑ).toReal := ENNReal.toReal_mono (by finiteness) h
    _ = C * ‖f‖ := by simp

/-- On a domain of finite measure, `W^{1,p}(Ω)` includes continuously into `W^{1,q}(Ω)` for
`q ≤ p`, preserving the value. -/
private theorem W1p.exists_inclusionL_of_measure_ne_top {F : Type*} [MeasurableSpace F]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F]
    {mu : Measure F} [mu.IsAddHaarMeasure] {U : Opens F} (hU : mu U ≠ ∞) {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hqp : q ≤ p) :
    ∃ J : W1p mu U p →L[ℝ] W1p mu U q, ∀ u, W1p.value (J u) =ᵐ[mu.restrict U] W1p.value u := by
  have hμ : mu.restrict U univ ≠ ∞ := by rwa [Measure.restrict_apply_univ]
  obtain ⟨Jv, hJv⟩ := exists_lpInclusionL (F := ℝ) hμ hqp
  obtain ⟨Jg, hJg⟩ := exists_lpInclusionL (F := F) hμ hqp
  have hmk (u : W1p mu U p) : HasWeakFDerivOn mu U (Jv (W1p.value u))
      (fun x ↦ innerSL ℝ (Jg (W1p.gradient u) x)) :=
    ((W1p.hasWeakFDerivOn u).congr_ae (hJv _).symm).congr_ae_deriv
      (by filter_upwards [hJg (W1p.gradient u)] with x hx; rw [hx])
  let F' : W1p mu U p → W1p mu U q := fun u ↦
    W1p.mk (Jv (W1p.value u)) (Jg (W1p.gradient u)) (hmk u)
  have hF (u) : W1p.value (F' u) = Jv (W1p.value u) := W1p.value_mk _ _ _
  have hG (u) : W1p.gradient (F' u) = Jg (W1p.gradient u) := W1p.gradient_mk _ _ _
  have hadd (a b : W1p mu U q) : W1p.value (a + b) = W1p.value a + W1p.value b := by
    simp only [← W1p.valueL_apply, map_add]
  have hsmul (c : ℝ) (a : W1p mu U q) : W1p.value (c • a) = c • W1p.value a := by
    simp only [← W1p.valueL_apply, map_smul]
  have haddp (a b : W1p mu U p) : W1p.value (a + b) = W1p.value a + W1p.value b := by
    simp only [← W1p.valueL_apply, map_add]
  have hsmulp (c : ℝ) (a : W1p mu U p) : W1p.value (c • a) = c • W1p.value a := by
    simp only [← W1p.valueL_apply, map_smul]
  let J : W1p mu U p →ₗ[ℝ] W1p mu U q :=
    { toFun := F'
      map_add' := fun u v ↦ W1p.ext_value (by rw [hadd, hF, hF, hF, haddp, map_add])
      map_smul' := fun c u ↦ W1p.ext_value (by
        rw [hsmul, hF, hF, hsmulp, map_smul, RingHom.id_apply]) }
  have hvalue : Continuous fun u ↦ W1p.value (J u) := by
    simp only [J, LinearMap.coe_mk, AddHom.coe_mk, hF]
    exact Jv.continuous.comp ((continuous_congr W1p.valueL_apply).1 W1p.valueL.continuous)
  have hgradient : Continuous fun u ↦ W1p.gradient (J u) := by
    simp only [J, LinearMap.coe_mk, AddHom.coe_mk, hG]
    exact Jg.continuous.comp ((continuous_congr W1p.gradientL_apply).1 W1p.gradientL.continuous)
  have hcont : Continuous J := continuous_iff_continuousAt.2 fun u ↦
    W1p.tendsto_iff_value_gradient.2 ⟨hvalue.continuousAt, hgradient.continuousAt⟩
  exact ⟨⟨J, hcont⟩, fun u ↦ (hF u).symm ▸ hJv _⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A first-order embedding with slack on bounded Lipschitz domains.** For `n ≥ 2`, `1 ≤ q < ∞`
and `1/p ≤ 1/q + 1/n`, the value of `u ∈ W^{1,p}(Ω)` lies in `L^q(Ω)`, continuously in `u`. The
exponent `p` is first lowered to `r` with `1/r = min 1 (1/q + 1/n)`, which is below the critical
exponent `n`, and then the Sobolev embedding `W^{1,r}(Ω) → L^{r⋆}(Ω)` with `q ≤ r⋆` applies. -/
private theorem W1p.exists_lpEmbeddingL_of_inv_le
    (hn : 2 ≤ finrank ℝ (WithLp 2 (ℝ × E)))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞)
    (hexp : p⁻¹ ≤ q⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹) :
    ∃ S : W1p volume Ω p →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u := by
  set n : ℝ≥0∞ := (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) with hn_def
  set a : ℝ≥0∞ := min 1 (q⁻¹ + n⁻¹)
  have hn2 : (2 : ℝ≥0∞) ≤ n := by rw [hn_def]; exact_mod_cast hn
  have hninv : n⁻¹ < 1 :=
    ENNReal.inv_lt_one.2 (lt_of_lt_of_le (by norm_num) hn2)
  have hninv_top : n⁻¹ ≠ ∞ := hninv.ne_top
  have hqinv : 0 < q⁻¹ := ENNReal.inv_pos.2 hq
  have hna : n⁻¹ < a := lt_min hninv (add_comm n⁻¹ q⁻¹ ▸ ENNReal.lt_add_right hninv_top hqinv.ne')
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 Fact.out
  set r : ℝ≥0∞ := a⁻¹
  set rstar : ℝ≥0∞ := (a - n⁻¹)⁻¹
  have hrinv : r⁻¹ = a := inv_inv a
  have hrstar : rstar ≠ ∞ := by
    rw [Ne, ENNReal.inv_eq_top]
    exact (tsub_pos_of_lt hna).ne'
  have hrexp : rstar⁻¹ + n⁻¹ = r⁻¹ := by
    rw [inv_inv, hrinv]
    exact tsub_add_cancel_of_le hna.le
  have : Fact (1 ≤ r) := ⟨by rw [← ENNReal.inv_le_one, hrinv]; exact min_le_left _ _⟩
  have hrp : r ≤ p := by
    rw [← ENNReal.inv_le_inv, hrinv]
    exact le_min hp1 hexp
  have hqr : q ≤ rstar := by
    rw [← ENNReal.inv_le_inv, inv_inv]
    calc a - n⁻¹ ≤ q⁻¹ + n⁻¹ - n⁻¹ := tsub_le_tsub_right (min_le_right _ _) _
      _ = q⁻¹ := ENNReal.add_sub_cancel_right hninv_top
  have : Fact (1 ≤ rstar) := ⟨one_le_of_inv_add_eq_inv hrexp⟩
  have hμ : volume (Ω : Set (WithLp 2 (ℝ × E))) ≠ ∞ := hb.measure_lt_top.ne
  obtain ⟨J, hJ⟩ := W1p.exists_inclusionL_of_measure_ne_top (mu := volume) hμ hrp
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hrstar hrexp hΩ hb
  obtain ⟨I, hI⟩ := exists_lpInclusionL (F := ℝ)
    (by rwa [Measure.restrict_apply_univ]) hqr
  exact ⟨I.comp (S.comp J), fun u ↦ (hI _).trans ((hS _).trans (hJ u))⟩

/-- Iteration of the first-order embedding with steps `t ≤ 1/n` down to `W^{1,q}(Ω)`, where
`1/q + k t = 1/p`. -/
private theorem exists_lipschitzWkpW1pEmbedding
    (hn : 2 ≤ finrank ℝ (WithLp 2 (ℝ × E)))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {t : ℝ≥0∞}
    (ht : t ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹) :
    ∀ (k : ℕ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], q ≠ ∞ → q⁻¹ + k * t = p⁻¹ →
      ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] W1p volume Ω q,
        ∀ u, W1p.value (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 1) u
  | 0, p, q, _, _, _, hexp => by
    obtain rfl : q = p := by simpa using hexp
    refine ⟨Wkp.firstOrderL 0, fun u ↦ ?_⟩
    rw [Wkp.firstOrderL_apply, Wkp.firstOrder_zero, Wkp.value_one]
  | k + 1, p, q, _, _, hq, hexp => by
    set r : ℝ≥0∞ := (q⁻¹ + k * t)⁻¹
    have hrinv : r⁻¹ = q⁻¹ + k * t := inv_inv _
    have hrexp : r⁻¹ + t = p⁻¹ := by
      rw [hrinv, ← hexp]
      push_cast
      ring
    have hr : r ≠ ∞ := by
      rw [← ENNReal.inv_ne_zero, hrinv]
      exact (add_pos_of_pos_of_nonneg (ENNReal.inv_pos.2 hq) zero_le).ne'
    have : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hrexp⟩
    obtain ⟨S, hS⟩ := W1p.exists_lpEmbeddingL_of_inv_le (p := p) hn hΩ hb hr
      (hrexp ▸ add_le_add_right ht _)
    obtain ⟨S', hS'⟩ := Wkp.exists_sobolevEmbeddingL_of_ae_eq S hS (k + 1)
    obtain ⟨T, hT⟩ := exists_lipschitzWkpW1pEmbedding hn hΩ hb ht k (p := r) (q := q) hq
      hrinv.symm
    exact ⟨T.comp S', fun u ↦ (hT (S' u)).trans (hS' u)⟩

/-- **Higher-order Morrey embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p`, and `1/q + k/n = 1/p` with `n < q < ∞`, then every
`u ∈ W^{k+1,p}(Ω)` agrees almost everywhere on `Ω` with a function on `closure Ω` which is Hölder
of exponent `1 - n/q = k + 1 - n/p`, and this representative depends linearly and boundedly on
`u`. The hypotheses say that `k p < n < (k + 1) p` (or `n < p` for `k = 0`), and the exponent is
the sharp one. By `IsOpen.ext_closure_of_ae_eq` the representative is unique. -/
theorem Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0}
    (hq : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < q)
    (hexp : (q : ℝ≥0∞)⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace (1 - finrank ℝ (WithLp 2 (ℝ × E)) / q)
        (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value (k + 1) u x := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Wkp volume Ω p (k + 1) →L[ℝ] W1p volume Ω q,
      ∀ u, W1p.value (T₁ u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        Wkp.value (k + 1) u := by
    rcases k with _ | k
    · obtain rfl : (q : ℝ≥0∞) = p := by simpa using hexp
      refine ⟨Wkp.firstOrderL 0, fun u ↦ ?_⟩
      rw [Wkp.firstOrderL_apply, Wkp.firstOrder_zero, Wkp.value_one]
    · refine exists_lipschitzWkpW1pEmbedding ?_ hΩ hb le_rfl (k + 1) ENNReal.coe_ne_top hexp
      by_contra! h
      have hninv : (1 : ℝ≥0∞) ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.one_le_inv]
        exact_mod_cast Nat.le_of_lt_succ h
      have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 Fact.out
      have hq0 : 0 < (q : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 ENNReal.coe_ne_top
      have : (1 : ℝ≥0∞) < 1 := calc
        (1 : ℝ≥0∞) < (q : ℝ≥0∞)⁻¹ + 1 :=
          add_comm (1 : ℝ≥0∞) _ ▸ ENNReal.lt_add_right ENNReal.one_ne_top hq0.ne'
        _ ≤ (q : ℝ≥0∞)⁻¹ + ((k + 1 : ℕ) : ℝ≥0∞) * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
          gcongr
          calc (1 : ℝ≥0∞) ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := hninv
            _ ≤ _ := le_mul_of_one_le_left zero_le (by exact_mod_cast Nat.succ_pos k)
        _ = p⁻¹ := hexp
        _ ≤ 1 := hp1
      exact lt_irrefl _ this
  obtain ⟨M, hM⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith hq hΩ hb
  refine ⟨M.comp T₁, fun u ↦ ?_⟩
  filter_upwards [hM (T₁ u), (ae_restrict_iff' Ω.isOpen.measurableSet).1 (hT₁ u)]
    with x h₁ h₂ hx
  rw [ContinuousLinearMap.comp_apply, h₁ hx, h₂ hx]

/-- **Hölder embedding of `W^{k,p}` with `n < k p` on bounded Lipschitz domains.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n`, `1 ≤ p < ∞` and `n < k p`, then
there is `γ > 0` such that every `u ∈ W^{k,p}(Ω)` agrees almost everywhere on `Ω` with a function
on `closure Ω` which is Hölder of exponent `γ`, depending linearly and boundedly on `u`. For
`n ≥ 2` one can take `γ = 1 - n/(k p)`, and for `n < p` the Morrey exponent `γ = 1 - n/p`. The
excluded case `n = 1 = p` is `W^{k,1}` of an interval. For the sharp exponent see
`TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`. -/
theorem Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    {k : ℕ} (hkp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < k * p)
    (hn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p ∨ 2 ≤ finrank ℝ (WithLp 2 (ℝ × E)))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ γ : ℝ≥0, 0 < γ ∧ ∃ T : Wkp volume Ω p k →L[ℝ]
        HolderSpace γ (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value k u x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero (by
    rintro rfl
    simp at hkp)
  -- The target exponent `q` of the ladder, with `n < q`.
  obtain ⟨q, hq, _, T₁, hT₁⟩ : ∃ q : ℝ≥0, (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < q ∧
      ∃ _ : Fact (1 ≤ (q : ℝ≥0∞)), ∃ T₁ : Wkp volume Ω p (j + 1) →L[ℝ] W1p volume Ω q,
        ∀ u, W1p.value (T₁ u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (j + 1) u := by
    rcases hn with hn | hn
    · exact ⟨p, hn, inferInstance, Wkp.firstOrderL j, fun u ↦ by
        rw [Wkp.firstOrderL_apply, Wkp.value_firstOrder]⟩
    have hq1 : (1 : ℝ≥0∞) ≤ (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞) := by
      push_cast
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 j) Fact.out
    have : Fact (1 ≤ (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)) := ⟨hq1⟩
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    refine ⟨(j + 1 : ℕ) * p, by exact_mod_cast hkp, this, ?_⟩
    refine exists_lipschitzWkpW1pEmbedding hn hΩ hb (t := (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹)
      ?_ j ENNReal.coe_ne_top ?_
    · rw [ENNReal.inv_le_inv]
      exact_mod_cast hkp.le
    · push_cast
      rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), ← one_add_mul,
        ← mul_assoc, add_comm (1 : ℝ≥0∞), ENNReal.mul_inv_cancel (by positivity) (by simp),
        one_mul]
  have hγ : 0 < 1 - (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) / q :=
    tsub_pos_of_lt ((div_lt_one (zero_le.trans_lt hq)).2 hq)
  obtain ⟨M, hM⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith hq hΩ hb
  refine ⟨_, hγ, M.comp T₁, fun u ↦ ?_⟩
  filter_upwards [hM (T₁ u), (ae_restrict_iff' Ω.isOpen.measurableSet).1 (hT₁ u)]
    with x h₁ h₂ hx
  rw [ContinuousLinearMap.comp_apply, h₁ hx, h₂ hx]

/-- **Hölder compactness of `W^{k,p}` with `n < k p` on bounded Lipschitz domains.** Under the
hypotheses of `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith`, there is `γ > 0`
such that for every `β < γ` the Hölder representative gives a compact operator
`W^{k,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {k : ℕ} (hkp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < k * p)
    (hn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p ∨ 2 ≤ finrank ℝ (WithLp 2 (ℝ × E)))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ γ : ℝ≥0, 0 < γ ∧ ∀ β < γ, ∃ T : Wkp volume Ω p k →L[ℝ]
        HolderSpace β (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value k u x := by
  have : CompactSpace (closure (Ω : Set (WithLp 2 (ℝ × E)))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  obtain ⟨γ, hγ, T, hT⟩ := Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith hkp hn hΩ hb
  refine ⟨γ, hγ, fun β hβ ↦ ⟨(HolderSpace.inclusionL hβ.le).comp T,
    (HolderSpace.isCompactOperator_inclusionL hβ).comp_clm T, fun u ↦ ?_⟩⟩
  filter_upwards [hT u] with x hx hxΩ
  rw [ContinuousLinearMap.comp_apply, HolderSpace.inclusionL_apply, hx hxΩ]

end TauCeti

end
