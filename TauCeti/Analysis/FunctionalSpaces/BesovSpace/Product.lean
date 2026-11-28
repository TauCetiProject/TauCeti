/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Estimate
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Resonant
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Holder

/-!
# The Bony product on Besov spaces

Let `α < 0 < β` with `α + β > 0`. A tempered distribution `u ∈ B^α_{p₁,q₁}` of negative
regularity cannot be multiplied by an arbitrary function, but it can be multiplied by an element
`v ∈ B^β_{p₂,q₂}` of the larger positive regularity `β > -α`: the products `S_M u · S_M v` of the
low-frequency cut-offs `S_M = ∑_{k < M} Δₖ` converge in the tempered distributions, and the limit,
the product `u v`, lies in `B^α_{r,q₁}` for `1/r = 1/p₁ + 1/p₂`, with norm `O(‖u‖ ‖v‖)`. On the
Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}` this is the product map `𝒞^α × 𝒞^β → 𝒞^α`, the
multiplication used to give a meaning to products of distributional fields with Hölder
coefficients in singular stochastic equations.

The proof is Bony's decomposition (`TauCeti.BesovSpace.lowPass_smul_lowPass`): with a gap `N` such
that `φ.rOut < 2^N φ.rIn`, `S_M u · S_M v` is the sum of the truncations of the paraproducts
`T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` and `T_v u = ∑ⱼ Δⱼ u · S_{j-N} v` and of the resonant part
`R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v`, up to the resonant tail pairs `(j, k)` with
`j < M ≤ k`, handled by `TauCeti.BesovSpace.tendsto_sum_block_smul_sum_resonantCLM`. The three
series converge via the bundled operators:

* `T_u v` lies in `B^{α+β}_{r,q₁}` since `α < 0`
  (`TauCeti.BesovSpace.paraproductNegCLM` with `inclusion` of `v` into `B^β_{p₂,∞}`);
* `T_v u` lies in `B^α_{r,q₁}` since `v` is an `L^{p₂}` function for `β > 0`
  (`TauCeti.BesovSpace.toLpCLM` and `TauCeti.BesovSpace.paraproductRightLpCLM`);
* `R(u, v)` lies in `B^{α+β}_{r,q₁}` since `α + β > 0`
  (`TauCeti.BesovSpace.resonantCLM` with `inclusion` of `v` into `B^β_{p₂,∞}`);

and `B^{α+β}_{r,q₁} ⊆ B^α_{r,q₁}` since `β > 0`.

For two factors of the same positive regularity `s > 0` that are also Lebesgue functions, the same
decomposition gives the **tame product estimate**
`‖u v‖_{B^s_{r,q}} ≤ C (‖u‖_{p₃} ‖v‖_{B^s_{p₂,q}} + ‖u‖_{B^s_{p₁,q}} ‖v‖_{p₄})` for
`1/r = 1/p₁ + 1/p₄ = 1/p₃ + 1/p₂` (`TauCeti.BesovSpace.exists_toDistr_eq_smul_and_norm_le`); the
classical case is `p₃ = p₄ = ∞`. Now `T_u v` and `T_v u` are bounded by the paraproduct estimates
with the Lebesgue factor at low frequency (`TauCeti.BesovSpace.paraproductLpCLM`,
`TauCeti.BesovSpace.paraproductRightLpCLM`), and `R(u, v)` by the resonant estimate with
`v ∈ L^{p₄} ⊆ B^0_{p₄,∞}` (`TauCeti.BesovSpace.ofLpCLM`). The products `S_M u · S_M v` converge to
the pointwise product `u v` in `Lʳ`, since `S_M v` is bounded in `L^{p₄}` and `S_M u → u` in
`L^{p₁}`, `S_M v → v` in `L^{p₂}`.

The time-weighted product estimate lives in
`TauCeti.Analysis.FunctionalSpaces.BesovSpace.TimeWeighted`.

## Main declarations

* `TauCeti.BesovSpace.smulL`: the product `B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^α_{r,q₁}` as a continuous
  bilinear map, for `α < 0 < α + β` and `1/r = 1/p₁ + 1/p₂`.
* `TauCeti.BesovSpace.tendsto_lowPass_smul_lowPass` and `TauCeti.BesovSpace.smulL_eq_iff`: the
  product is the limit of `S_M u · S_M v` in the tempered distributions, and is characterized by it.
* `TauCeti.BesovSpace.exists_norm_smulL_apply_le`: the bound `‖u v‖ ≤ C ‖u‖ ‖v‖` with a constant
  depending only on the bump function and the regularities, not on the integrability exponents.
* `TauCeti.BesovSpace.smulL_eq_paraproductNegCLM_add`: identifies `smulL` with
  `T_u^N v + T_v^N u + R_N(u, v)` for any admissible gap `N`.
* Single-block (`toDistr_smulL_of_block_eq_zero`) and constant-`1` (`smulL_one_left`,
  `smulL_one_right`) identities.
* `TauCeti.BesovSpace.exists_toDistr_eq_smul_and_norm_le`: for `s > 0`, the product of
  `u ∈ B^s_{p₁,q} ∩ L^{p₃}` and `v ∈ B^s_{p₂,q} ∩ L^{p₄}` lies in `B^s_{r,q}`, with the tame
  estimate above, uniformly in the exponents.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, §2.8
  (Bony's decomposition and Theorems 2.82 and 2.85, from which the product estimate follows, and
  Corollary 2.86, the tame estimate).
-/

public section

noncomputable section

open MeasureTheory Filter Topology TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)]
  [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r]

/-- Combines the `HasSum` limits of the two paraproduct series and the truncated-resonant
convergence into `S_M u • S_M v → w₁ + w₂ + w₃` in `𝓢'(E, F)`. -/
private theorem tendsto_lowPass_smul_lowPass_of_hasSum {N : ℕ} {q₁' q₂' : ℝ≥0∞}
    {s₁ s₂ : ℝ} (u : BesovSpace ℂ φ s₁ p₁ q₁')
    (v : BesovSpace F φ s₂ p₂ q₂') {w₁ w₂ w₃ : 𝓢'(E, F)}
    (h₁ : HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) w₁)
    (h₂ : HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) w₂)
    (h₃ : Tendsto (fun M ↦ ((∑ j ∈ Finset.range M, (u.block j •
        ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
          Lp F r (volume : Measure E)) : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 w₃)) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (w₁ + w₂ + w₃)) := by
  refine ((h₁.tendsto_sum_nat.add h₂.tendsto_sum_nat).add h₃).congr'
    (Eventually.of_forall fun M ↦ ?_)
  simp_rw [← Lp.toTemperedDistributionCLM_apply]
  rw [← map_sum, ← map_sum, ← map_add, ← map_add, lowPass_smul_lowPass N M u v]

/-- For every admissible gap `N`, `S_M u · S_M v` converges in `𝓢'(E, F)` to
`T_u^N v + T_v^N u + R_N(u, v)`. -/
private theorem tendsto_lowPass_smul_lowPass_paraproductNegCLM_add {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop
      (𝓝 (inclusion F φ r (by linarith) le_rfl
            (paraproductNegCLM r q₁ hN hα u (inclusion F φ p₂ le_rfl le_top v)) +
          paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q₂ (by linarith) v) +
          inclusion F φ r (by linarith) le_rfl
            (resonantCLM r q₁ N hαβ u (inclusion F φ p₂ le_rfl le_top v))).toDistr) := by
  simp only [toDistr_add, toDistr_inclusion]
  set v' : BesovSpace F φ β p₂ ∞ := inclusion F φ p₂ le_rfl le_top v
  have h₁ := hasSum_paraproductNegCLM (r := r) (q := q₁) hN hα u v'
  have h₂ := hasSum_paraproductRightLpCLM_of_toDistr_eq (r := r) hN u
    (coe_toLpCLM (by linarith : 0 < β) v).symm
  have h₃ := tendsto_sum_block_smul_sum_resonantCLM (r := r) (q := q₁) N hαβ u v'
  simp only [v', block_inclusion] at h₁ h₃
  exact tendsto_lowPass_smul_lowPass_of_hasSum u v h₁ h₂ h₃

variable (φ) in
/-- **The product estimate**, with a constant independent of the integrability exponents. -/
private theorem exists_tendsto_lowPass_smul_lowPass_and_norm_le (hα : α < 0) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q₂), ∃ w : BesovSpace F φ α r q₁,
        Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) atTop (𝓝 w.toDistr) ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hβ : 0 < β := by linarith
  set N := φ.exists_rOut_lt_two_pow_mul_rIn.choose
  set hN := φ.exists_rOut_lt_two_pow_mul_rIn.choose_spec
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_paraproductNegCLM_le (F := F) hN hα β
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_paraproductRightLpCLM_le (F := F) hN α
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_resonantCLM_le (F := F) (φ := φ) N α β hαβ
  set K : ℝ := (1 - 2 ^ (-β))⁻¹
  have hK : 0 ≤ K := inv_nonneg.2 <| sub_nonneg.2 <|
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  refine ⟨C₁ + C₂ * K + C₃, by positivity, fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ u v ↦ ?_⟩
  set v' : BesovSpace F φ β p₂ ∞ := inclusion F φ p₂ le_rfl le_top v
  have hv' : ‖v'‖ ≤ ‖v‖ := norm_inclusion_le _ _ v
  set w₁ := inclusion F φ r (by linarith : α ≤ α + β) le_rfl (paraproductNegCLM r q₁ hN hα u v')
  set w₂ := paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q₂ hβ v)
  set w₃ := inclusion F φ r (by linarith : α ≤ α + β) le_rfl (resonantCLM r q₁ N hαβ u v')
  refine ⟨w₁ + w₂ + w₃, tendsto_lowPass_smul_lowPass_paraproductNegCLM_add hN hα hαβ u v, ?_⟩
  have hn₁ : ‖w₁‖ ≤ C₁ * ‖u‖ * ‖v‖ := (norm_inclusion_le _ _ _).trans <|
    ((paraproductNegCLM r q₁ hN hα).le_opNorm₂ u v').trans (by gcongr; exact h₁)
  have hn₂ : ‖w₂‖ ≤ C₂ * K * ‖u‖ * ‖v‖ := by
    refine ((paraproductRightLpCLM r hN).le_opNorm₂ u (toLpCLM F φ p₂ q₂ hβ v)).trans ?_
    calc _ ≤ C₂ * ‖u‖ * (K * ‖v‖) := by gcongr; exacts [h₂, norm_toLpCLM_apply_le hβ v]
      _ = C₂ * K * ‖u‖ * ‖v‖ := by ring
  have hn₃ : ‖w₃‖ ≤ C₃ * ‖u‖ * ‖v‖ := (norm_inclusion_le _ _ _).trans <|
    ((resonantCLM r q₁ N hαβ).le_opNorm₂ u v').trans (by gcongr; exact h₃)
  calc ‖w₁ + w₂ + w₃‖ ≤ ‖w₁‖ + ‖w₂‖ + ‖w₃‖ := norm_add₃_le
    _ ≤ C₁ * ‖u‖ * ‖v‖ + C₂ * K * ‖u‖ * ‖v‖ + C₃ * ‖u‖ * ‖v‖ := add_le_add_three hn₁ hn₂ hn₃
    _ = (C₁ + C₂ * K + C₃) * ‖u‖ * ‖v‖ := by ring

variable (F φ) in
/-- The constant of the product estimate. -/
private def smulBound (hα : α < 0) (hαβ : 0 < α + β) : ℝ :=
  (exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose

variable (r) in
/-- The product, as a function of the two factors. -/
private def smulAux (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) : BesovSpace F φ α r q₁ :=
  ((exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.2
    (r := r) u v).choose

private theorem tendsto_smulAux (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (smulAux r hα hαβ u v).toDistr) :=
  ((exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.2
    (r := r) u v).choose_spec.1

private theorem norm_smulAux_le (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    ‖smulAux r hα hαβ u v‖ ≤ smulBound F φ hα hαβ * ‖u‖ * ‖v‖ :=
  ((exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.2
    (r := r) u v).choose_spec.2

private theorem smulAux_eq_iff (hα : α < 0) (hαβ : 0 < α + β) {u : BesovSpace ℂ φ α p₁ q₁}
    {v : BesovSpace F φ β p₂ q₂} {w : BesovSpace F φ α r q₁} :
    smulAux r hα hαβ u v = w ↔
      Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
        atTop (𝓝 w.toDistr) :=
  ⟨fun h ↦ h ▸ tendsto_smulAux hα hαβ u v,
    fun h ↦ ext (tendsto_nhds_unique (tendsto_smulAux hα hαβ u v) h)⟩

variable (r) in
/-- **The product of Besov elements of negative and positive regularity.** Let `α < 0 < α + β`
and `1/r = 1/p₁ + 1/p₂`. For `u ∈ B^α_{p₁,q₁}` and `v ∈ B^β_{p₂,q₂}`, the product
`u v ∈ B^α_{r,q₁}` is the limit in the tempered distributions of the products `S_M u · S_M v` of
the low-frequency cut-offs
(`TauCeti.BesovSpace.tendsto_lowPass_smul_lowPass`), and `(u, v) ↦ u v` is a continuous bilinear
map. For `p₁ = p₂ = r = q₁ = q₂ = ∞` this is the product map `𝒞^α × 𝒞^β → 𝒞^α` on the
Hölder–Zygmund scale. -/
def smulL (hα : α < 0) (hαβ : 0 < α + β) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ α r q₁ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (smulAux r hα hαβ)
      (fun u₁ u₂ v ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_add]
        refine ((tendsto_smulAux hα hαβ u₁ v).add (tendsto_smulAux hα hαβ u₂ v)).congr fun M ↦ ?_
        simp only [lowPass_add, Lp.smul_add, ← Lp.toTemperedDistributionCLM_apply, map_add])
      (fun c u v ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_smul]
        refine ((tendsto_smulAux hα hαβ u v).const_smul c).congr fun M ↦ ?_
        simp only [lowPass_smul, Lp.smul_assoc, ← Lp.toTemperedDistributionCLM_apply, map_smul])
      (fun u v₁ v₂ ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_add]
        refine ((tendsto_smulAux hα hαβ u v₁).add (tendsto_smulAux hα hαβ u v₂)).congr fun M ↦ ?_
        simp only [lowPass_add, Lp.add_smul, ← Lp.toTemperedDistributionCLM_apply, map_add])
      (fun c u v ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_smul]
        refine ((tendsto_smulAux hα hαβ u v).const_smul c).congr fun M ↦ ?_
        simp only [lowPass_smul, ← Lp.smul_comm, ← Lp.toTemperedDistributionCLM_apply, map_smul]))
    (smulBound F φ hα hαβ) (norm_smulAux_le hα hαβ)

private theorem smulL_apply (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) : smulL r hα hαβ u v = smulAux r hα hαβ u v :=
  (LinearMap.mkContinuous₂_apply _ _ u v).trans (LinearMap.mk₂_apply _ _ u v)

/-- **The product is the limit of the products of the low-frequency cut-offs:**
`S_M u · S_M v → u v` in the tempered distributions. -/
theorem tendsto_lowPass_smul_lowPass (hα : α < 0) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (smulL r hα hαβ u v).toDistr) := by
  rw [smulL_apply]
  exact tendsto_smulAux hα hαβ u v

/-- **Characterization of the product:** `u v = w` exactly when `S_M u · S_M v → w` in the
tempered distributions. -/
theorem smulL_eq_iff (hα : α < 0) (hαβ : 0 < α + β) {u : BesovSpace ℂ φ α p₁ q₁}
    {v : BesovSpace F φ β p₂ q₂} {w : BesovSpace F φ α r q₁} :
    smulL r hα hαβ u v = w ↔
      Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
        atTop (𝓝 w.toDistr) := by
  rw [smulL_apply]
  exact smulAux_eq_iff hα hαβ

variable (F φ) in
/-- **The product estimate.** For `α < 0 < α + β` there
is `C ≥ 0`, depending only on `φ`, `α` and `β`, such that `‖u v‖_{B^α_{r,q₁}} ≤ C ‖u‖ ‖v‖` for
all exponents `1 ≤ p₁, p₂, r, q₁, q₂ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`, all `u ∈ B^α_{p₁,q₁}` and
all `v ∈ B^β_{p₂,q₂}`. -/
theorem exists_norm_smulL_apply_le (hα : α < 0) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q₂), ‖smulL r hα hαβ u v‖ ≤ C * ‖u‖ * ‖v‖ :=
  ⟨smulBound F φ hα hαβ,
    (exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.1,
    fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ u v ↦ by
      rw [smulL_apply]
      exact norm_smulAux_le hα hαβ u v⟩

section BonyDecomposition

/-- **Bony decomposition of `TauCeti.BesovSpace.smulL`.** For every gap `N` satisfying
`φ.rOut < 2 ^ N * φ.rIn`, `smulL r hα hαβ u v` equals `T_u^N v + T_v^N u + R_N(u, v)`. -/
theorem smulL_eq_paraproductNegCLM_add {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    smulL r hα hαβ u v =
      inclusion F φ r (by linarith) le_rfl
          (paraproductNegCLM r q₁ hN hα u (inclusion F φ p₂ le_rfl le_top v)) +
        paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q₂ (by linarith) v) +
        inclusion F φ r (by linarith) le_rfl
          (resonantCLM r q₁ N hαβ u (inclusion F φ p₂ le_rfl le_top v)) :=
  (smulL_eq_iff hα hαβ).2 (tendsto_lowPass_smul_lowPass_paraproductNegCLM_add hN hα hαβ u v)

end BonyDecomposition

section Tame

/-! ### Positive regularity: the tame product estimate -/

variable {s : ℝ} {p₃ p₄ q : ℝ≥0∞}

omit [p₁.HolderTriple p₂ r] in
open scoped FourierTransform in
/-- For `s > 0`, let `u ∈ B^s_{p₁,q}` be represented by `f ∈ L^{p₃}` and `v ∈ B^s_{p₂,q}` by
`g ∈ L^{p₄}`, with `1/r = 1/p₁ + 1/p₄ = 1/p₃ + 1/p₂`. Then `S_M u · S_M g → u g` in `Lʳ`: the
factor `S_M g` is bounded in `L^{p₄}`, and `S_M g - g = S_M v - v` almost everywhere tends to `0`
in `L^{p₂}`, against the factor `f ∈ L^{p₃}`. -/
private theorem tendsto_lowPass_smul_lowPass_ofLpCLM [Fact (1 ≤ p₃)] [Fact (1 ≤ p₄)]
    [Fact (1 ≤ q)] [p₁.HolderTriple p₄ r] [p₃.HolderTriple p₂ r] (hs : 0 < s)
    (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q) {f : Lp ℂ p₃ (volume : Measure E)}
    {g : Lp F p₄ (volume : Measure E)} (hf : u.toDistr = f) (hg : v.toDistr = g) :
    Tendsto (fun M ↦ (u.lowPass M • (ofLpCLM F φ p₄ g).lowPass M : Lp F r (volume : Measure E)))
      atTop (𝓝 (toLpCLM ℂ φ p₁ q hs u • g)) := by
  set U := toLpCLM ℂ φ p₁ q hs u
  set V := toLpCLM F φ p₂ q hs v
  set g' := ofLpCLM F φ p₄ g
  set A := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have hUf : U =ᵐ[volume] f := Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1 <| by
    rw [coe_toLpCLM, hf]
  have hgV : g =ᵐ[volume] V := Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1 <| by
    rw [coe_toLpCLM, hg]
  have hgv : ∀ M, g'.lowPass M =ᵐ[volume] v.lowPass M := fun M ↦
    Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1 <| by
      rw [coe_lowPass, coe_lowPass, toDistr_ofLpCLM, hg]
  -- Split `S_M u · S_M g - U g = (S_M u - U) · S_M g + f · (S_M v - V)`.
  have key : ∀ M, (u.lowPass M • g'.lowPass M - U • g : Lp F r (volume : Measure E)) =
      (u.lowPass M - U) • g'.lowPass M + f • (v.lowPass M - V) := fun M ↦ by
    have h : (U • (g'.lowPass M - g) : Lp F r (volume : Measure E)) = f • (v.lowPass M - V) :=
      Lp.smul_eq_smul_of_ae_eq hUf <| by
        filter_upwards [Lp.coeFn_sub (g'.lowPass M) g, Lp.coeFn_sub (v.lowPass M) V, hgv M, hgV]
          with x h₁ h₂ h₃ h₄
        rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply, h₃, h₄]
    rw [← h, sub_eq_add_neg (u.lowPass M), Lp.smul_add, sub_eq_add_neg (g'.lowPass M),
      Lp.add_smul, Lp.neg_smul, Lp.smul_neg]
    abel
  have hu := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_lowPass hs u)
  have hv := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_lowPass hs v)
  refine tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun M ↦ ?_) (by simpa using (hu.mul_const (A * ‖g‖)).add (hv.const_mul ‖f‖))
  rw [key]
  refine (norm_add_le _ _).trans (add_le_add ((Lp.norm_smul_le _ _).trans ?_)
    (Lp.norm_smul_le _ _))
  exact mul_le_mul_of_nonneg_left (norm_lowPass_le_of_toDistr_eq g' (toDistr_ofLpCLM g) M)
    (norm_nonneg _)

variable (F φ) in
/-- **The tame product estimate on Besov spaces** (Bahouri–Chemin–Danchin, Corollary 2.86). Let
`s > 0`. There is `C ≥ 0`, depending only on `E`, `F`, `φ` and `s`, with the following property
for all exponents `1 ≤ p₁, p₂, p₃, p₄, r, q ≤ ∞` with `1/r = 1/p₁ + 1/p₄ = 1/p₃ + 1/p₂`. If
`u ∈ B^s_{p₁,q}` is represented by `f ∈ L^{p₃}` and `v ∈ B^s_{p₂,q}` by `g ∈ L^{p₄}`, then their
product lies in `B^s_{r,q}` with

`‖u v‖_{B^s_{r,q}} ≤ C (‖f‖_{p₃} ‖v‖_{B^s_{p₂,q}} + ‖u‖_{B^s_{p₁,q}} ‖g‖_{p₄})`.

Here the product is the pointwise product of the `L^{p₁}` function `toLpCLM ℂ φ p₁ q hs u` of `u`
with `g`. Each factor enters the estimate with its full Besov norm only once, against the Lebesgue
norm of the other. The classical case is `p₁ = p₂ = r = p` and `p₃ = p₄ = ∞`: bounded elements of
`B^s_{p,q}` multiply in `B^s_{p,q}`. -/
theorem exists_toDistr_eq_smul_and_norm_le (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ p₃ p₄ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)]
      [Fact (1 ≤ p₃)] [Fact (1 ≤ p₄)] [Fact (1 ≤ r)] [Fact (1 ≤ q)] [p₁.HolderTriple p₄ r]
      [p₃.HolderTriple p₂ r] (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q)
      {f : Lp ℂ p₃ (volume : Measure E)} {g : Lp F p₄ (volume : Measure E)},
      u.toDistr = f → v.toDistr = g →
      ∃ w : BesovSpace F φ s r q,
        w.toDistr = ((toLpCLM ℂ φ p₁ q hs u • g : Lp F r (volume : Measure E)) : 𝓢'(E, F)) ∧
        ‖w‖ ≤ C * (‖f‖ * ‖v‖ + ‖u‖ * ‖g‖) := by
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  have hs₀ : 0 < s + 0 := by simpa using hs
  have hle : s ≤ s + 0 := by simp
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_paraproductLpCLM_le (F := F) hN s
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_paraproductRightLpCLM_le (F := F) hN s
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_resonantCLM_le (F := F) (φ := φ) N s 0 hs₀
  obtain ⟨C₀, hC₀, h₀⟩ := exists_norm_ofLpCLM_le F φ
  refine ⟨C₁ + C₂ + C₃ * C₀, by positivity,
    fun {p₁ p₂ p₃ p₄ r q} _ _ _ _ _ _ _ _ u v f g hf hg ↦ ?_⟩
  -- Bony's decomposition `u g = T_f v + T_g u + R(u, g)`, all three terms in `B^s_{r,q}`.
  set g' := ofLpCLM F φ p₄ g
  set w₁ := paraproductLpCLM (F := F) (β := s) (p₁ := p₃) (p₂ := p₂) (q := q) r hN f v
  set w₂ := paraproductRightLpCLM (F := F) (α := s) (p₁ := p₁) (p₂ := p₄) (q := q) r hN u g
  set w₃ := resonantCLM r q N hs₀ u g'
  refine ⟨w₁ + w₂ + inclusion F φ r hle le_rfl w₃, ?_, ?_⟩
  · have hT₁ : HasSum (fun j ↦ ((u.lowPass (j - N) • g'.block j : Lp F r (volume : Measure E)) :
        𝓢'(E, F))) w₁.toDistr :=
      (hasSum_paraproductLpCLM (r := r) hN f v).congr_fun fun j ↦ congrArg _ <|
        Lp.smul_eq_smul_of_ae_eq
          (Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1 <| by
            rw [coe_lowPass, coe_lowPass, toDistr_ofLpCLM, hf])
          (Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1 <| by
            rw [coe_block, coe_block, toDistr_ofLpCLM, hg])
    have hlim := tendsto_lowPass_smul_lowPass_of_hasSum (r := r) u g' hT₁
      (hasSum_paraproductRightLpCLM (r := r) hN u g)
      (tendsto_sum_block_smul_sum_resonantCLM (r := r) (q := q) N hs₀ u g')
    rw [toDistr_add, toDistr_add, toDistr_inclusion]
    exact tendsto_nhds_unique hlim <| ((Lp.toTemperedDistributionCLM F volume r).continuous.tendsto
      _).comp (tendsto_lowPass_smul_lowPass_ofLpCLM hs u v hf hg)
  · have hn₁ : ‖w₁‖ ≤ C₁ * ‖f‖ * ‖v‖ :=
      ((paraproductLpCLM r hN).le_opNorm₂ f v).trans (by gcongr; exact h₁)
    have hn₂ : ‖w₂‖ ≤ C₂ * ‖u‖ * ‖g‖ :=
      ((paraproductRightLpCLM r hN).le_opNorm₂ u g).trans (by gcongr; exact h₂)
    have hn₃ : ‖inclusion F φ r hle le_rfl w₃‖ ≤ C₃ * ‖u‖ * (C₀ * ‖g‖) :=
      (norm_inclusion_le _ _ _).trans <| ((resonantCLM r q N hs₀).le_opNorm₂ u g').trans
        (by gcongr; exacts [h₃, h₀ g])
    have ha : 0 ≤ ‖f‖ * ‖v‖ := by positivity
    have hb : 0 ≤ ‖u‖ * ‖g‖ := by positivity
    calc _ ≤ ‖w₁‖ + ‖w₂‖ + ‖inclusion F φ r hle le_rfl w₃‖ := norm_add₃_le
      _ ≤ C₁ * ‖f‖ * ‖v‖ + C₂ * ‖u‖ * ‖g‖ + C₃ * ‖u‖ * (C₀ * ‖g‖) :=
          add_le_add_three hn₁ hn₂ hn₃
      _ ≤ (C₁ + C₂ + C₃ * C₀) * (‖f‖ * ‖v‖ + ‖u‖ * ‖g‖) := by
          nlinarith [mul_nonneg (add_nonneg hC₂ (mul_nonneg hC₃ hC₀)) ha, mul_nonneg hC₁ hb]

end Tame

section Checks

/-- **Same-frequency Bony product (`α < 0`, `0 < α + β`).** Both paraproducts vanish and the
resonant term carries `Δ_{j₀} u · Δ_{j₀} v`. -/
theorem toDistr_smulL_of_block_eq_zero (hα : α < 0) (hαβ : 0 < α + β)
    {j₀ : ℕ} {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    (smulL r hα hαβ u v).toDistr =
      ((u.block j₀ • v.block j₀ : Lp F r (volume : Measure E)) : 𝓢'(E, F)) := by
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  have hv' : ∀ k ≠ j₀, (inclusion F φ p₂ le_rfl (le_top : q₂ ≤ ∞) v).block k = 0 := by
    simpa [block_inclusion] using hv
  have hg : ∀ k ≠ j₀,
      littlewoodPaleyBlock F φ k (toLpCLM F φ p₂ q₂ (by linarith) v : 𝓢'(E, F)) = 0 :=
    fun k hk ↦ by rw [coe_toLpCLM, ← coe_block, hv k hk, Lp.toTemperedDistribution_zero]
  rw [smulL_eq_paraproductNegCLM_add hN hα hαβ u v,
    paraproductNegCLM_eq_zero_of_block_eq_zero hN hα hu hv',
    paraproductRightLpCLM_eq_zero_of_block_eq_zero hN hu hg]
  simp [toDistr_resonantCLM_of_block_eq_zero N hαβ hu hv', block_inclusion]

section One

/-- **Unitality of `smulL` on the left (`α < 0`, `0 < α + β`):**
`T_1^N v = v - S_{N + 1} v`, `T_v^N 1 = 0`, and `R_N(1, v) = S_{N + 1} v` sum to `v` in
`B^α_{p₂,q₁}`. -/
@[simp]
theorem smulL_one_left (hα : α < 0) (hαβ : 0 < α + β)
    (v : BesovSpace F φ β p₂ q₂) :
    smulL p₂ hα hαβ (1 : BesovSpace ℂ φ α ∞ q₁) v =
      inclusionOfLT F φ p₂ q₂ q₁ (by linarith) v := by
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  apply ext
  rw [smulL_eq_paraproductNegCLM_add hN hα hαβ 1 v, paraproductRightLpCLM_one_left]
  simp [toDistr_paraproductNegCLM_one_left hN hα]

/-- **Unitality of `smulL` on the right (`α < 0`, `0 < α + β`):** `T_u^N 1 = 0`,
`T_1^N u = u - S_{N + 1} u`, and `R_N(u, 1) = S_{N + 1} u` sum to `u`. -/
@[simp]
theorem smulL_one_right (hα : α < 0) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) :
    smulL p₁ hα hαβ u (1 : BesovSpace ℂ φ β ∞ q₂) = u := by
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  apply ext
  rw [smulL_eq_paraproductNegCLM_add hN hα hαβ u 1, inclusion_one,
    paraproductNegCLM_one_right hN hα u, toLpCLM_one,
    paraproductRightLpCLM_eq_paraproductLpCLM hN u 1]
  simp [toDistr_paraproductLpCLM_one_left hN u]

end One

end Checks

end TauCeti.BesovSpace
