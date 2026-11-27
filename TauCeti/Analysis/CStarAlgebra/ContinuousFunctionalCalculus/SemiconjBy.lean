/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Intertwining self-adjoint elements through the real functional calculus

Let `a` and `b` be self-adjoint elements of a (possibly nonunital) C⋆-algebra and `x` an element
with `x a = b x`. Then `x` intertwines every real continuous function of `a` and `b`:
`x g(a) = g(b) x` (`SemiconjBy.mul_cfcₙ_real`). For real functions no condition on adjoints is
needed. The symbols on the union of the two quasispectra that are intertwined contain the
identity and are closed under sums, products, scalar multiples and limits, so by the nonunital
Stone–Weierstrass theorem they are all symbols vanishing at `0`.

The main case is `a = x⋆x`, `b = xx⋆`: for every real function `g`,
`x g(x⋆x) = g(xx⋆) x` (`mul_cfcₙ_star_mul_self`); the two quasispectra coincide
(`quasispectrum.mul_comm`), so this holds with no hypothesis on `g`.

As a consequence, for `h` continuous on the quasispectrum of `x⋆x` with `h(0) = 0` there is `y`
with `y⋆y = h(x⋆x)²` and `yy⋆ = h(xx⋆)²` (`exists_star_mul_self_eq_and_mul_star_self_eq`). With
`k_n(t) = h(t) / √(max t εₙ)` and `y_n = x k_n(x⋆x)`, the intertwining gives `y_n⋆ y_n = H_n(x⋆x)²`
and `y_n y_n⋆ = H_n(xx⋆)²` for `H_n(t) = √t k_n(t)`, and `‖y_m - y_n‖ = ‖H_m(x⋆x) - H_n(x⋆x)‖`.
As `εₙ → 0`, `H_n → h` uniformly on the quasispectrum, so `y_n` converges to the required `y`.

## Main statements

* `SemiconjBy.mul_cfcₙ_real`: `x a = b x` gives `x g(a) = g(b) x`.
* `mul_cfcₙ_star_mul_self`: `x g(x⋆x) = g(xx⋆) x`.
* `exists_star_mul_self_eq_and_mul_star_self_eq`: `h(x⋆x)² = y⋆y` and `h(xx⋆)² = yy⋆`.

## References

* Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier (Grenoble) 13 (1963),
  219–262. Chapitre I: Lemme 3, p. 226.
-/

public section

open scoped ContinuousMapZero

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- **Intertwining through the real functional calculus.** If `x a = b x` for self-adjoint `a`
and `b`, then `x g(a) = g(b) x` for every real function `g` continuous on both quasispectra. -/
theorem SemiconjBy.mul_cfcₙ_real {x a b : A} (h : SemiconjBy x a b) (g : ℝ → ℝ)
    (hga : ContinuousOn g (quasispectrum ℝ a) := by cfc_cont_tac)
    (hgb : ContinuousOn g (quasispectrum ℝ b) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) (hb : IsSelfAdjoint b := by cfc_tac) :
    x * cfcₙ g a = cfcₙ g b * x := by
  by_cases hg0 : g 0 = 0
  swap
  · rw [cfcₙ_apply_of_not_map_zero a hg0, cfcₙ_apply_of_not_map_zero b hg0, mul_zero, zero_mul]
  -- Both calculi are read on symbols on the common compact set `K`, which contains `0`.
  set K := quasispectrum ℝ a ∪ quasispectrum ℝ b
  have hca := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℝ)
    (p := IsSelfAdjoint) a
  have hcb := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℝ)
    (p := IsSelfAdjoint) b
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hca.union hcb)
  have : Fact ((0 : ℝ) ∈ K) := ⟨Or.inl (quasispectrum.zero_mem ℝ a)⟩
  let ιa : C(quasispectrum ℝ a, K)₀ :=
    ⟨⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩, rfl⟩
  let ιb : C(quasispectrum ℝ b, K)₀ :=
    ⟨⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩, rfl⟩
  let φa := (cfcₙHom ha).comp (ContinuousMapZero.nonUnitalStarAlgHom_precomp ℝ ιa)
  let φb := (cfcₙHom hb).comp (ContinuousMapZero.nonUnitalStarAlgHom_precomp ℝ ιb)
  have hφa : Continuous φa :=
    (cfcₙHom_continuous ha).comp (ContinuousMapZero.continuous_precomp ιa)
  have hφb : Continuous φb :=
    (cfcₙHom_continuous hb).comp (ContinuousMapZero.continuous_precomp ιb)
  have hφa_id : φa (.id K) = a := by
    rw [← cfcₙHom_id (R := ℝ) ha]
    exact congrArg (cfcₙHom ha) (ContinuousMapZero.ext fun _ ↦ rfl)
  have hφb_id : φb (.id K) = b := by
    rw [← cfcₙHom_id (R := ℝ) hb]
    exact congrArg (cfcₙHom hb) (ContinuousMapZero.ext fun _ ↦ rfl)
  have key (G : C(K, ℝ)₀) : x * φa G = φb G * x := by
    induction G using ContinuousMapZero.induction_on_of_compact with
    | zero => rw [map_zero, map_zero, mul_zero, zero_mul]
    | id => rw [hφa_id, hφb_id]; exact h
    | star_id => rw [star_trivial, hφa_id, hφb_id]; exact h
    | add f g hf hg => rw [map_add, map_add, mul_add, add_mul, hf, hg]
    | mul f g hf hg => rw [map_mul, map_mul, ← mul_assoc, hf, mul_assoc, hg, mul_assoc]
    | smul r f hf => rw [map_smul, map_smul, mul_smul_comm, smul_mul_assoc, hf]
    | frequently f hf =>
      have hclosed : IsClosed {G : C(K, ℝ)₀ | x * φa G = φb G * x} :=
        isClosed_eq (continuous_const.mul hφa) (hφb.mul continuous_const)
      exact hclosed.closure_subset_iff.mpr subset_rfl (mem_closure_iff_frequently.mpr hf)
  -- `cfcₙ g a` and `cfcₙ g b` are the two calculi at the restriction of `g` to `K`.
  have hg : ContinuousOn g K := hga.union_of_isClosed hgb hca.isClosed hcb.isClosed
  let G : C(K, ℝ)₀ := ⟨⟨_, hg.domRestrict⟩, hg0⟩
  have hGa : cfcₙ g a = φa G := by
    rw [cfcₙ_apply g a]
    exact congrArg (cfcₙHom ha) (ContinuousMapZero.ext fun _ ↦ rfl)
  have hGb : cfcₙ g b = φb G := by
    rw [cfcₙ_apply g b]
    exact congrArg (cfcₙHom hb) (ContinuousMapZero.ext fun _ ↦ rfl)
  rw [hGa, hGb, key]

/-- **`x` intertwines `x⋆x` and `xx⋆` through the real functional calculus**:
`x g(x⋆x) = g(xx⋆) x` for every real function `g`. -/
theorem mul_cfcₙ_star_mul_self (x : A) (g : ℝ → ℝ) :
    x * cfcₙ g (star x * x) = cfcₙ g (x * star x) * x := by
  have hσ : quasispectrum ℝ (star x * x) = quasispectrum ℝ (x * star x) :=
    quasispectrum.mul_comm _ _
  by_cases hg : ContinuousOn g (quasispectrum ℝ (star x * x))
  · exact SemiconjBy.mul_cfcₙ_real (mul_assoc x (star x) x).symm g hg (hσ ▸ hg)
  · rw [cfcₙ_apply_of_not_continuousOn _ hg,
      cfcₙ_apply_of_not_continuousOn _ (hσ ▸ hg : ¬ ContinuousOn g _), mul_zero, zero_mul]

section Order

variable [PartialOrder A] [StarOrderedRing A]

open Filter Topology

/-- For `a = x⋆x` and `y = x k(a)`, `y⋆y = H(a)²` with `H(t) = √t k(t)`. -/
private theorem star_mul_self_mul_cfcₙ (x : A) (k : ℝ → ℝ)
    (hk : ContinuousOn k (quasispectrum ℝ (star x * x))) (hk0 : k 0 = 0) :
    star (x * cfcₙ k (star x * x)) * (x * cfcₙ k (star x * x)) =
      cfcₙ (fun t ↦ √t * k t) (star x * x) * cfcₙ (fun t ↦ √t * k t) (star x * x) := by
  have hnn := quasispectrum_nonneg_of_nonneg (𝕜 := ℝ) _ (star_mul_self_nonneg x)
  have hs : ContinuousOn (fun t : ℝ ↦ √t) (quasispectrum ℝ (star x * x)) :=
    Real.continuous_sqrt.continuousOn
  have hsk : ContinuousOn (fun t ↦ √t * k t) (quasispectrum ℝ (star x * x)) := hs.mul hk
  have ha : IsSelfAdjoint (star x * x) := .star_mul_self x
  have hkid : ContinuousOn (fun t ↦ k t * t) (quasispectrum ℝ (star x * x)) :=
    hk.mul continuousOn_id
  calc star (x * cfcₙ k (star x * x)) * (x * cfcₙ k (star x * x))
      = cfcₙ k (star x * x) * (star x * x) * cfcₙ k (star x * x) := by
        rw [star_mul, (cfcₙ_predicate k (star x * x)).star_eq]; noncomm_ring
    _ = cfcₙ (fun t ↦ k t * t * k t) (star x * x) := by
        rw [cfcₙ_mul (fun t ↦ k t * t) k (star x * x) (hf := hkid) (hf0 := by simp [hk0])
          (hg := hk) (hg0 := hk0), cfcₙ_mul k (fun t ↦ t) (star x * x) (hf := hk) (hf0 := hk0),
          cfcₙ_id' ℝ (star x * x)]
    _ = cfcₙ (fun t ↦ (√t * k t) * (√t * k t)) (star x * x) := by
        refine cfcₙ_congr fun t ht ↦ ?_
        have := Real.mul_self_sqrt (hnn t ht)
        linear_combination (k t * k t) * this.symm
    _ = _ := cfcₙ_mul _ _ (hf := hsk) (hf0 := by simp [hk0]) (hg := hsk)
        (hg0 := by simp [hk0])

/-- For `b = xx⋆` and `y = x k(x⋆x)`, `yy⋆ = H(b)²` with `H(t) = √t k(t)`. -/
private theorem mul_star_self_mul_cfcₙ (x : A) (k : ℝ → ℝ)
    (hk : ContinuousOn k (quasispectrum ℝ (star x * x))) (hk0 : k 0 = 0) :
    (x * cfcₙ k (star x * x)) * star (x * cfcₙ k (star x * x)) =
      cfcₙ (fun t ↦ √t * k t) (x * star x) * cfcₙ (fun t ↦ √t * k t) (x * star x) := by
  have hσ : quasispectrum ℝ (star x * x) = quasispectrum ℝ (x * star x) :=
    quasispectrum.mul_comm _ _
  have hnn := quasispectrum_nonneg_of_nonneg (𝕜 := ℝ) _ (mul_star_self_nonneg x)
  have hk' : ContinuousOn k (quasispectrum ℝ (x * star x)) := hσ ▸ hk
  have hs : ContinuousOn (fun t : ℝ ↦ √t) (quasispectrum ℝ (x * star x)) :=
    Real.continuous_sqrt.continuousOn
  have hsk : ContinuousOn (fun t ↦ √t * k t) (quasispectrum ℝ (x * star x)) := hs.mul hk'
  have hb : IsSelfAdjoint (x * star x) := .mul_star_self x
  have hkk : ContinuousOn (fun t ↦ k t * k t) (quasispectrum ℝ (x * star x)) := hk'.mul hk'
  calc (x * cfcₙ k (star x * x)) * star (x * cfcₙ k (star x * x))
      = x * (cfcₙ k (star x * x) * cfcₙ k (star x * x)) * star x := by
        rw [star_mul, (cfcₙ_predicate k (star x * x)).star_eq]; noncomm_ring
    _ = cfcₙ (fun t ↦ k t * k t) (x * star x) * (x * star x) := by
        rw [← cfcₙ_mul k k (star x * x) (hf := hk) (hf0 := hk0) (hg := hk) (hg0 := hk0),
          mul_cfcₙ_star_mul_self, mul_assoc]
    _ = cfcₙ (fun t ↦ k t * k t * t) (x * star x) := by
        rw [cfcₙ_mul (fun t ↦ k t * k t) (fun t ↦ t) (x * star x) (hf := hkk)
          (hf0 := by simp [hk0]), cfcₙ_id' ℝ (x * star x)]
    _ = cfcₙ (fun t ↦ (√t * k t) * (√t * k t)) (x * star x) := by
        refine cfcₙ_congr fun t ht ↦ ?_
        have := Real.mul_self_sqrt (hnn t ht)
        linear_combination (k t * k t) * this.symm
    _ = _ := cfcₙ_mul _ _ (hf := hsk) (hf0 := by simp [hk0]) (hg := hsk)
        (hg0 := by simp [hk0])

/-- The functions `H ε t = √t h(t) / √(max t ε)` converge to `h` uniformly on a set of
nonnegative reals as `ε → 0`, for `h` continuous at `0` with `h 0 = 0`. -/
private theorem tendstoUniformlyOn_sqrt_mul_div {s : Set ℝ} (hs : ∀ t ∈ s, 0 ≤ t)
    {h : ℝ → ℝ} (hh : ContinuousWithinAt h s 0) (hh0 : h 0 = 0) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n t ↦ √t * (h t / √(max t (ε n)))) h atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨η, hη, hηh⟩ := Metric.continuousWithinAt_iff.1 hh δ hδ
  filter_upwards [hε0.eventually (gt_mem_nhds hη)] with n hn t ht
  have ht0 := hs t ht
  have hmax : 0 < √(max t (ε n)) := Real.sqrt_pos.2 (lt_max_of_lt_right (hε n))
  have hc0 : 0 ≤ √t / √(max t (ε n)) := div_nonneg (Real.sqrt_nonneg _) hmax.le
  have hc1 : √t / √(max t (ε n)) ≤ 1 :=
    (div_le_one hmax).2 (Real.sqrt_le_sqrt (le_max_left _ _))
  have heq : √t * (h t / √(max t (ε n))) = h t * (√t / √(max t (ε n))) := by ring
  rw [heq, Real.dist_eq, show h t - h t * (√t / √(max t (ε n))) =
    h t * (1 - √t / √(max t (ε n))) by ring, abs_mul,
    abs_of_nonneg (show 0 ≤ 1 - √t / √(max t (ε n)) by linarith)]
  rcases le_or_gt (ε n) t with hεt | hεt
  · rw [max_eq_left hεt, div_self (Real.sqrt_pos.2 ((hε n).trans_le hεt)).ne', sub_self,
      mul_zero]
    exact hδ
  · have hht : |h t| < δ := by
      have := hηh ht (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]; linarith)
      rwa [hh0, Real.dist_eq, sub_zero] at this
    calc |h t| * (1 - √t / √(max t (ε n))) ≤ |h t| * 1 := by gcongr; linarith
      _ < δ := by rwa [mul_one]

/-- **`f(x⋆x)` and `f(xx⋆)` are `y⋆y` and `yy⋆`.** For every real function `h` continuous on the
quasispectrum of `x⋆x` with `h 0 = 0`, there is `y` with `y⋆y = h(x⋆x)²` and `yy⋆ = h(xx⋆)²`.
The element `y` is the limit of `x k_n(x⋆x)` with `k_n(t) = h(t) / √(max t εₙ)`, `εₙ → 0`. -/
theorem exists_star_mul_self_eq_and_mul_star_self_eq (x : A) (h : ℝ → ℝ)
    (hh : ContinuousOn h (quasispectrum ℝ (star x * x))) (hh0 : h 0 = 0) :
    ∃ y : A, star y * y = cfcₙ (fun t ↦ h t * h t) (star x * x) ∧
      y * star y = cfcₙ (fun t ↦ h t * h t) (x * star x) := by
  set a := star x * x
  set b := x * star x
  have hσ : quasispectrum ℝ a = quasispectrum ℝ b := quasispectrum.mul_comm _ _
  have hnna := quasispectrum_nonneg_of_nonneg (𝕜 := ℝ) _ (star_mul_self_nonneg x)
  have hhb : ContinuousOn h (quasispectrum ℝ b) := hσ ▸ hh
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ Nat.one_div_pos_of_nat
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set k : ℕ → ℝ → ℝ := fun n t ↦ h t / √(max t (ε n))
  set H : ℕ → ℝ → ℝ := fun n t ↦ √t * k n t
  have hk : ∀ n, ContinuousOn (k n) (quasispectrum ℝ a) := fun n ↦
    hh.div (Real.continuous_sqrt.comp (continuous_id.max continuous_const)).continuousOn
      fun t _ ↦ (Real.sqrt_pos.2 (lt_max_of_lt_right (hε n))).ne'
  have hk0 : ∀ n, k n 0 = 0 := fun n ↦ by simp [k, hh0]
  have hHa : ∀ n, ContinuousOn (H n) (quasispectrum ℝ a) := fun n ↦
    Real.continuous_sqrt.continuousOn.mul (hk n)
  have hHb : ∀ n, ContinuousOn (H n) (quasispectrum ℝ b) := fun n ↦ hσ ▸ hHa n
  have hH0 : ∀ n, H n 0 = 0 := fun n ↦ by simp [H, hk0]
  have hunia : TendstoUniformlyOn H h atTop (quasispectrum ℝ a) :=
    tendstoUniformlyOn_sqrt_mul_div hnna (hh.continuousWithinAt (quasispectrum.zero_mem ℝ a))
      hh0 hε hε0
  have hwa : Tendsto (fun n ↦ cfcₙ (H n) a) atTop (𝓝 (cfcₙ h a)) :=
    tendsto_cfcₙ_fun hunia (.of_forall hHa) (.of_forall hH0)
  have hwb : Tendsto (fun n ↦ cfcₙ (H n) b) atTop (𝓝 (cfcₙ h b)) :=
    tendsto_cfcₙ_fun (hσ ▸ hunia) (.of_forall hHb) (.of_forall hH0)
  set u : ℕ → A := fun n ↦ x * cfcₙ (k n) a
  -- `‖u m - u n‖ = ‖H_m(a) - H_n(a)‖`, so `u` is Cauchy.
  have hdist : ∀ m n, dist (u m) (u n) = dist (cfcₙ (H m) a) (cfcₙ (H n) a) := fun m n ↦ by
    have hkmn : ContinuousOn (fun t ↦ k m t - k n t) (quasispectrum ℝ a) := (hk m).sub (hk n)
    have hsub : u m - u n = x * cfcₙ (fun t ↦ k m t - k n t) a := by
      simp only [u]
      rw [cfcₙ_sub (k m) (k n) a, mul_sub]
    have hHsub : cfcₙ (H m) a - cfcₙ (H n) a = cfcₙ (fun t ↦ √t * (k m t - k n t)) a := by
      rw [← cfcₙ_sub (H m) (H n) a]
      exact cfcₙ_congr fun t _ ↦ by simp only [H]; ring
    have key := star_mul_self_mul_cfcₙ x _ hkmn (by simp [hk0])
    rw [← hsub, ← hHsub] at key
    rw [dist_eq_norm, dist_eq_norm]
    have hsa : IsSelfAdjoint (cfcₙ (H m) a - cfcₙ (H n) a) :=
      IsSelfAdjoint.sub (cfcₙ_predicate _ a) (cfcₙ_predicate _ a)
    have h1 := congrArg norm key
    nth_rewrite 1 [← hsa.star_eq] at h1
    rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at h1
    nlinarith [norm_nonneg (u m - u n), norm_nonneg (cfcₙ (H m) a - cfcₙ (H n) a),
      mul_self_eq_mul_self_iff.1 h1]
  have hu : CauchySeq u := Metric.cauchySeq_iff.2 fun δ hδ ↦
    (Metric.cauchySeq_iff.1 hwa.cauchySeq δ hδ).imp fun N hN m hm n hn ↦
      (hdist m n) ▸ hN m hm n hn
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨y, ?_, ?_⟩
  · have h1 : Tendsto (fun n ↦ star (u n) * u n) atTop (𝓝 (star y * y)) := hy.star.mul hy
    have h2 : Tendsto (fun n ↦ star (u n) * u n) atTop (𝓝 (cfcₙ h a * cfcₙ h a)) :=
      (hwa.mul hwa).congr fun n ↦ (star_mul_self_mul_cfcₙ x (k n) (hk n) (hk0 n)).symm
    rw [tendsto_nhds_unique h1 h2, ← cfcₙ_mul h h a (hf := hh) (hf0 := hh0) (hg := hh)
      (hg0 := hh0)]
  · have h1 : Tendsto (fun n ↦ u n * star (u n)) atTop (𝓝 (y * star y)) := hy.mul hy.star
    have h2 : Tendsto (fun n ↦ u n * star (u n)) atTop (𝓝 (cfcₙ h b * cfcₙ h b)) :=
      (hwb.mul hwb).congr fun n ↦ (mul_star_self_mul_cfcₙ x (k n) (hk n) (hk0 n)).symm
    rw [tendsto_nhds_unique h1 h2, ← cfcₙ_mul h h b (hf := hhb) (hf0 := hh0) (hg := hhb)
      (hg0 := hh0)]

end Order
