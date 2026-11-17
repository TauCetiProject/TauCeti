/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.KatoRellich
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.Normed.Operator.LinearPMap.RelativeCompact

/-!
# Relatively compact perturbations on Hilbert space

Let `A` be a partial linear map on a Hilbert space `E` with a point `z` in its resolvent set, and
let `V` be `A`-compact (`LinearPMap.IsRelativelyCompact`). Then `V` has `A`-bound zero: for every
`ε > 0` there is an `a` with `‖V x‖ ≤ a ‖x‖ + ε ‖A x‖` on `dom A`
(`LinearPMap.IsRelativelyCompact.exists_isRelativelyBounded`, Teschl, Lemma 6.22).

The proof is by contradiction. A failure at `ε` gives vectors `uₙ` with `‖uₙ‖ + ‖A uₙ‖ = 1` and
`n ‖uₙ‖ + ε ‖A uₙ‖ < ‖V uₙ‖`. Compactness bounds `V uₙ`, so `uₙ → 0`, and gives a subsequence
with `V uₙ → w`, `‖w‖ ≥ ε`. On the other hand `V uₙ = K (z uₙ - A uₙ)` with `K = V (z I - A)⁻¹`
compact, and `z uₙ - A uₙ` tends to zero weakly: `A uₙ` is bounded, and with `R = (z I - A)⁻¹`
the inner products `⟪R* e, A uₙ⟫ = ⟪e, z R uₙ - uₙ⟫` tend to zero, while the range of `R*` is
dense because `R` is injective. Hence every continuous linear functional vanishes at `w`, so
`w = 0`.

Combined with the Kato–Rellich theorem, a symmetric `A`-compact perturbation of a self-adjoint
`A` is self-adjoint on `dom A` (`IsSelfAdjoint.add_of_isRelativelyCompact`), `V` stays compact
relative to `A + V` (Teschl, Lemma 6.23), and the resolvents of `A + V` and `A` differ by a compact
operator off the real axis, the input of Weyl's theorem.

## Main declarations

* `LinearPMap.IsRelativelyCompact.exists_isRelativelyBounded`: relative compactness gives relative
  bound zero.
* `LinearPMap.IsRelativelyCompact.isRelativelyCompact_add`: `V` is `(A + V)`-compact.
* `IsSelfAdjoint.add_of_isRelativelyCompact_of_mem_resolventSet`,
  `IsSelfAdjoint.add_of_isRelativelyCompact`: symmetric relatively compact perturbations of a
  self-adjoint operator are self-adjoint.
* `IsSelfAdjoint.isCompactOperator_resolvent_add_sub_of_isRelativelyCompact`: the resolvent
  difference is compact at every nonreal point.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS (2009), Lemmas 6.22 and 6.23.
* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), §IV.1.3 and
  Theorem V.4.3.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bounded sequence whose inner products with every vector of a dense set tend to zero has
inner products with every vector tending to zero. -/
private theorem tendsto_inner_of_dense {D : Set E} (hD : Dense D) {v : ℕ → E} {M : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ M) (h : ∀ d ∈ D, Tendsto (fun n ↦ ⟪d, v n⟫_𝕜) atTop (𝓝 0)) (k : E) :
    Tendsto (fun n ↦ ⟪k, v n⟫_𝕜) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M' := max M 0 + 1
  have hM' : 0 < M' := by positivity
  obtain ⟨d, hd, hkd⟩ := hD.exists_dist_lt k (show 0 < ε / 2 / M' by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h d hd) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hvn : ‖v n‖ ≤ M' := (hv n).trans (by linarith [le_max_left M 0])
  have h₁ : ‖⟪k - d, v n⟫_𝕜‖ < ε / 2 := by
    calc ‖⟪k - d, v n⟫_𝕜‖ ≤ ‖k - d‖ * M' :=
          (norm_inner_le_norm _ _).trans (by gcongr)
      _ < ε / 2 / M' * M' := by
          gcongr
          rwa [← dist_eq_norm]
      _ = ε / 2 := div_mul_cancel₀ _ hM'.ne'
  have h₂ := hN n hn
  rw [dist_zero_right] at h₂ ⊢
  calc ‖⟪k, v n⟫_𝕜‖ = ‖⟪k - d, v n⟫_𝕜 + ⟪d, v n⟫_𝕜‖ := by rw [← inner_add_left, sub_add_cancel]
    _ ≤ ‖⟪k - d, v n⟫_𝕜‖ + ‖⟪d, v n⟫_𝕜‖ := norm_add_le _ _
    _ < ε := by linarith

/-- If a relative bound fails, it fails at a vector normalized in the graph norm. -/
private theorem exists_normalized_of_not_isRelativelyBounded {A : E →ₗ.[𝕜] E}
    {V : E →ₗ.[𝕜] G} (hle : A.domain ≤ V.domain) {a b : ℝ}
    (h : ¬ V.IsRelativelyBounded A a b) : ∃ u : A.domain, ‖(u : E)‖ + ‖A u‖ = 1 ∧
      a * ‖(u : E)‖ + b * ‖A u‖ < ‖V ⟨u, hle u.2⟩‖ := by
  obtain ⟨x, hx⟩ : ∃ x : A.domain, a * ‖(x : E)‖ + b * ‖A x‖ < ‖V ⟨x, hle x.2⟩‖ := by
    by_contra! hall
    exact h ⟨hle, hall⟩
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    obtain rfl : x = 0 := Subtype.ext h0
    simp only [ZeroMemClass.coe_zero, norm_zero, mul_zero, LinearPMap.map_zero, add_zero] at hx
    exact hx.ne' (by rw [norm_eq_zero]; exact V.map_zero)
  set s := ‖(x : E)‖ + ‖A x‖
  have hs : 0 < s := by positivity
  set c : 𝕜 := ((s⁻¹ : ℝ) : 𝕜)
  have hc : ‖c‖ = s⁻¹ := by rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hs)]
  have hV : V ⟨((c • x : A.domain) : E), hle (c • x).2⟩ = c • V ⟨x, hle x.2⟩ :=
    V.map_smul c ⟨x, hle x.2⟩
  refine ⟨c • x, ?_, ?_⟩
  · rw [A.map_smul, Submodule.coe_smul, norm_smul, norm_smul, hc, ← mul_add]
    exact inv_mul_cancel₀ hs.ne'
  · rw [hV, A.map_smul, Submodule.coe_smul, norm_smul, norm_smul, norm_smul, hc]
    have := mul_lt_mul_of_pos_left hx (inv_pos.2 hs)
    linarith

variable [CompleteSpace E]

/-- Along a sequence `uₙ` of `dom A` with `uₙ → 0` and `‖A uₙ‖ ≤ 1`, the values `f (V uₙ)` of
every continuous linear functional tend to zero, when `V` is `A`-compact and `A` has a resolvent
point `z`. Write `V uₙ = K (z uₙ - A uₙ)` with `K = V (z I - A)⁻¹` compact; the vectors `A uₙ`
tend to zero weakly, since `⟪R* e, A uₙ⟫ = ⟪e, z R uₙ - uₙ⟫` for `R = (z I - A)⁻¹`, and the range
of `R*` is dense because `R` is injective. -/
private theorem tendsto_dual_apply_of_isRelativelyCompact {A : E →ₗ.[𝕜] E} {V : E →ₗ.[𝕜] G}
    (hV : V.IsRelativelyCompact A) {z : 𝕜} (hz : z ∈ A.resolventSet) {u : ℕ → A.domain}
    (hu0 : Tendsto (fun n ↦ ‖(u n : E)‖) atTop (𝓝 0)) (hAu : ∀ n, ‖A (u n)‖ ≤ 1)
    (f : StrongDual 𝕜 G) :
    Tendsto (fun n ↦ f (V ⟨u n, hV.domain_le (u n).2⟩)) atTop (𝓝 0) := by
  obtain ⟨K, -, hK⟩ := hV.exists_isCompactOperator hz
  set R := A.resolvent z
  set k := (InnerProductSpace.toDual 𝕜 E).symm (f.comp K)
  have hsplit (n : ℕ) : f (V ⟨u n, hV.domain_le (u n).2⟩) =
      z * ⟪k, (u n : E)⟫_𝕜 - ⟪k, A (u n)⟫_𝕜 := by
    have hR := resolvent_smul_sub_apply hz (u n)
    have hVu : V ⟨u n, hV.domain_le (u n).2⟩ = K (z • (u n : E) - A (u n)) := by
      rw [← hK]
      congr 2
      exact hR.symm
    rw [hVu, ← inner_smul_right, ← inner_sub_right, InnerProductSpace.toDual_symm_apply]
    rfl
  have hu : Tendsto (fun n ↦ (u n : E)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.2 hu0
  have hRu : Tendsto (fun n ↦ z • R (u n) - (u n : E)) atTop (𝓝 0) := by
    simpa using (((R.continuous.tendsto 0).comp hu).const_smul z).sub hu
  have hker : LinearMap.ker (R : E →ₗ[𝕜] E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy ↦ ?_
    have h₁ := smul_sub_apply_resolvent hz y
    have h₀ : (⟨R y, resolvent_mem_domain hz y⟩ : A.domain) = 0 := Subtype.ext hy
    rw [h₀, LinearPMap.map_zero, sub_zero] at h₁
    have hy' : R y = 0 := hy
    rw [← h₁, hy', smul_zero]
  have hdense : Dense ((ContinuousLinearMap.adjoint R : E →ₗ[𝕜] E).range : Set E) := by
    refine Submodule.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 ?_)
    rw [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_adjoint]
    exact hker
  have hA : Tendsto (fun n ↦ ⟪k, A (u n)⟫_𝕜) atTop (𝓝 0) := by
    refine tendsto_inner_of_dense hdense hAu (fun d hd ↦ ?_) k
    obtain ⟨e, rfl⟩ := hd
    have hd' (n : ℕ) : ⟪ContinuousLinearMap.adjoint R e, A (u n)⟫_𝕜 =
        ⟪e, z • R (u n) - (u n : E)⟫_𝕜 := by
      rw [ContinuousLinearMap.adjoint_inner_left, resolvent_apply_comm hz, apply_resolvent hz]
    have he := (tendsto_const_nhds (x := e)).inner (𝕜 := 𝕜) hRu
    rw [inner_zero_right] at he
    exact he.congr fun n ↦ (hd' n).symm
  have hnorm : Tendsto (fun n ↦ ⟪k, (u n : E)⟫_𝕜) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := k)).inner (𝕜 := 𝕜) hu
  simp_rw [hsplit]
  simpa using (hnorm.const_mul z).sub hA

/-- **A relatively compact map has relative bound zero** (Teschl, Lemma 6.22). Let `A` be a
partial linear map on a Hilbert space with a point `z` in its resolvent set. If `V` is
`A`-compact, then for every `ε > 0` there is an `a` with `‖V x‖ ≤ a ‖x‖ + ε ‖A x‖` on `dom A`. -/
theorem IsRelativelyCompact.exists_isRelativelyBounded {A : E →ₗ.[𝕜] E} {V : E →ₗ.[𝕜] G}
    (hV : V.IsRelativelyCompact A) {z : 𝕜} (hz : z ∈ A.resolventSet) {ε : ℝ} (hε : 0 < ε) :
    ∃ a, V.IsRelativelyBounded A a ε := by
  by_contra! hcon
  choose u hu1 hu2 using fun n : ℕ ↦
    exists_normalized_of_not_isRelativelyBounded hV.domain_le (hcon n)
  obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact 1
  have hmem (n : ℕ) : V ⟨u n, hV.domain_le (u n).2⟩ ∈ K := hKV (u n) (hu1 n).le
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hAu (n : ℕ) : ‖A (u n)‖ ≤ 1 := by linarith [hu1 n, norm_nonneg (u n : E)]
  have hu0 : Tendsto (fun n ↦ ‖(u n : E)‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat M)
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    nlinarith [hu2 n, hM _ (hmem n), mul_nonneg hε.le (norm_nonneg (A (u n)))]
  obtain ⟨w, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hw : ε ≤ ‖w‖ := by
    have h₁ : Tendsto (fun n ↦ ε * (1 - ‖(u (φ n) : E)‖)) atTop (𝓝 ε) := by
      simpa using ((hu0.comp hφ.tendsto_atTop).const_sub 1).const_mul ε
    refine le_of_tendsto_of_tendsto' h₁ hlim.norm fun n ↦ ?_
    have h₂ : 1 - ‖(u (φ n) : E)‖ = ‖A (u (φ n))‖ := by linarith [hu1 (φ n)]
    rw [h₂]
    have := hu2 (φ n)
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (φ n)) (norm_nonneg (u (φ n) : E))
    simp only [Function.comp_apply]
    linarith
  have hw0 : w = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero fun f ↦
    tendsto_nhds_unique ((f.continuous.tendsto w).comp hlim)
      ((tendsto_dual_apply_of_isRelativelyCompact hV hz hu0 hAu f).comp
        hφ.tendsto_atTop)
  rw [hw0, norm_zero] at hw
  linarith

/-- **A relatively compact perturbation stays relatively compact** (Teschl, Lemma 6.23). If
`V` is `A`-compact and `A` has a point `z` in its resolvent set, then `V` is `(A + V)`-compact. -/
theorem IsRelativelyCompact.isRelativelyCompact_add {A V : E →ₗ.[𝕜] E}
    (hV : V.IsRelativelyCompact A) {z : 𝕜} (hz : z ∈ A.resolventSet) :
    V.IsRelativelyCompact (A + V) := by
  obtain ⟨a, ha⟩ := hV.exists_isRelativelyBounded hz one_half_pos
  exact hV.add_of_isRelativelyBounded ha (by norm_num)

end LinearPMap

open LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A V : E →ₗ.[𝕜] E}

/-- **Relatively compact perturbations preserve self-adjointness.** If `A` is self-adjoint with a
point `z` in its resolvent set and `V` is symmetric and `A`-compact, then `A + V`, with domain
`dom A`, is self-adjoint. -/
theorem IsSelfAdjoint.add_of_isRelativelyCompact_of_mem_resolventSet (hA : IsSelfAdjoint A)
    (hV : V.IsFormalAdjoint V) (hAV : V.IsRelativelyCompact A) {z : 𝕜}
    (hz : z ∈ A.resolventSet) : IsSelfAdjoint (A + V) := by
  obtain ⟨a, ha⟩ := hAV.exists_isRelativelyBounded hz one_half_pos
  exact hA.add_of_isRelativelyBounded hV ha (by norm_num)

/-- **Compact resolvent difference of a relatively compact perturbation.** If `A` is
self-adjoint and `V` is symmetric and `A`-compact, then at every `z` with nonzero imaginary part
`R_{A+V}(z) - R_A(z)` is a compact operator. -/
theorem IsSelfAdjoint.isCompactOperator_resolvent_add_sub_of_isRelativelyCompact
    (hA : IsSelfAdjoint A) (hV : V.IsFormalAdjoint V) (hAV : V.IsRelativelyCompact A) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) : IsCompactOperator ((A + V).resolvent z - A.resolvent z) := by
  have hzA := hA.mem_resolventSet_of_im_ne_zero hz
  exact hAV.isCompactOperator_resolvent_add_sub hzA
    ((hA.add_of_isRelativelyCompact_of_mem_resolventSet hV hAV hzA).mem_resolventSet_of_im_ne_zero
      hz)

/-- **Relatively compact perturbations preserve self-adjointness** over `ℂ`: if `A` is
self-adjoint and `V` is symmetric and `A`-compact, then `A + V`, with domain `dom A`, is
self-adjoint. -/
theorem IsSelfAdjoint.add_of_isRelativelyCompact {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {A V : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hV : V.IsFormalAdjoint V) (hAV : V.IsRelativelyCompact A) : IsSelfAdjoint (A + V) :=
  hA.add_of_isRelativelyCompact_of_mem_resolventSet hV hAV hA.I_mem_resolventSet
