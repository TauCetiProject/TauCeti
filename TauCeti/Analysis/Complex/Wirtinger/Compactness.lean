/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Morrey
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder bounds and compactness from `Lᵖ` bounds on `\bar∂`, `p > 2`

Let `2 < p < ∞` and let `U ⊆ ℂ` be open. For a map `u` smooth on `U` with values in a complex
Hilbert space, the interior Calderón–Zygmund estimate
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`) bounds the `Lᵖ` norm
of the derivative of `u` on a compact subset of `U` by the `Lᵖ(U)` norms of `\bar∂u` and `u`, and
Morrey's inequality (`TauCeti.enorm_sub_le_of_mem_ball_of_finrank_lt`) turns an `Lᵖ` bound on the
derivative, `p > 2`, into a Hölder bound of exponent `1 - 2 / p`. Together they give a local Hölder
estimate controlled by `\bar∂u` and `u` alone
(`TauCeti.exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`): for `K ⊆ U` compact there are
`C` and `δ > 0` with

`‖u x - u y‖ ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)}) |x - y| ^ (1 - 2 / p)`

for all `x ∈ K` and `|x - y| < δ`.

Consequently a family of maps that is bounded on compact subsets of `U`, and whose `\bar∂` is
bounded in `Lᵖ` on compact subsets of `U`, is Hölder continuous of exponent `1 - 2 / p` on each
compact subset with a common constant
(`TauCeti.exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le`).
By the Arzelà–Ascoli theorem a sequence of such maps, with values in a proper space, has a
subsequence converging locally uniformly on `U`; the limit is continuous on `U` and Hölder of the
same exponent on each compact subset
(`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le`).

This is the compactness step for functions solving a scalar Cauchy–Riemann equation with an `Lᵖ`
forcing, such as `\bar∂b = -ν b + f` with `ν` bounded and `f` bounded in `Lᵖ`. In Taubes's analysis
of Seiberg–Witten solutions concentrating along a pseudoholomorphic curve, the symmetric
coefficients `b_j` of the local branches satisfy such equations with `p = 2 + 2 / m`, whose Hölder
exponent `1 - 2 / p` is `1 / (m + 1)`; given uniform bounds on the `b_j` and on their forcing, the
compactness theorem gives a subsequence converging uniformly on compact subsets of a chart.

## Main results

* `TauCeti.exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`: the local Hölder estimate.
* `TauCeti.exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le`: a common Hölder constant on each
  compact subset for a family with locally bounded values and locally `Lᵖ`-bounded `\bar∂`.
* `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le`: a sequence
  of such maps has a locally uniformly convergent subsequence with a locally Hölder limit.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (the Calderón–Zygmund inequality and its use with Morrey's embedding).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Local Hölder estimate from the Cauchy–Riemann operator.** Let `2 < p < ∞`, let `U ⊆ ℂ` be
open and let `K ⊆ U` be compact. There are a constant `C` and a radius `δ > 0` such that every map
`u` smooth on `U`, with values in a complex Hilbert space, satisfies

`‖u x - u y‖ ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)}) |x - y| ^ (1 - 2 / p)`

for all `x ∈ K` and all `y` with `|x - y| < δ`. -/
theorem exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm {p : ℝ≥0} (hp : 2 < p)
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∃ δ : ℝ≥0, 0 < δ ∧ ∀ u : ℂ → F, ContDiffOn ℝ ∞ u U → ∀ x ∈ K, ∀ y,
      dist x y < δ → edist (u x) (u y) ≤
        C * (eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict U) +
          eLpNorm u p (volume.restrict U)) * edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  have hp₁ : (1 : ℝ≥0∞) < p := by exact_mod_cast one_lt_two.trans hp
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm (F := F)
    hp₁ ENNReal.coe_ne_top hU hK.cthickening hδ₀U
  have hfin : (Module.finrank ℝ ℂ : ℝ≥0) < p := by
    rwa [Complex.finrank_real_complex, Nat.cast_ofNat]
  -- Morrey's inequality on a ball of radius `r` has the constant `M (2 r) ^ α`.
  have hα : ((1 - 2 / p : ℝ≥0) : ℝ) = 1 - 2 / (p : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (two_pos.trans hp)).2 hp.le)]
    simp
  set α : ℝ := ((1 - 2 / p : ℝ≥0) : ℝ)
  set M : ℝ := 2 ^ (Module.finrank ℝ ℂ + 1) /
      (Module.finrank ℝ ℂ * volume.real (ball (0 : ℂ) 1)) *
      (Module.finrank ℝ ℂ * volume.real (ball (0 : ℂ) 1) * (p - 1) /
        (p - Module.finrank ℝ ℂ)) ^ (1 - 1 / (p : ℝ))
  refine ⟨(M * 2 ^ α).toNNReal * C₁, (δ₀ / 2).toNNReal, by simpa using hδ₀,
    fun u hu x hx y hxy ↦ ?_⟩
  rcases eq_or_ne x y with rfl | hne
  · simp
  have hxy' : dist x y < δ₀ / 2 := by
    simpa [Real.coe_toNNReal _ (half_pos hδ₀).le] using hxy
  -- Both points lie in the ball of radius `r = |x - y|` about their midpoint, which lies in the
  -- `δ₀`-thickening of `K`.
  set r := dist x y
  have hr : 0 < r := dist_pos.2 hne
  set z := midpoint ℝ x y
  have hzx : dist z x = r / 2 := by
    rw [dist_comm, dist_left_midpoint, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    ring
  have hxz : x ∈ ball z r := by
    rw [mem_ball, dist_comm, hzx]
    linarith
  have hyz : y ∈ ball z r := by
    rw [mem_ball, dist_right_midpoint, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have hball : ball z r ⊆ cthickening δ₀ K := fun w hw ↦
    mem_cthickening_of_dist_le w x δ₀ K hx (by
      linarith [dist_triangle w z x, mem_ball.1 hw])
  have hu₁ : ContDiffOn ℝ 1 u (ball z r) :=
    (hu.mono (hball.trans hδ₀U)).of_le (by exact_mod_cast le_top)
  have hmorrey := enorm_sub_le_of_mem_ball_of_finrank_lt (μ := volume) hu₁ hxz hyz hfin
  have hDu : eLpNorm (fderiv ℝ u) p (volume.restrict (ball z r)) ≤
      eLpNorm (fderiv ℝ u) p (volume.restrict (cthickening δ₀ K)) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)
  -- The constant of Morrey's inequality splits as `M 2 ^ α` times `r ^ α`.
  have hconst : ENNReal.ofReal (M * (2 * r) ^ (1 - (Module.finrank ℝ ℂ : ℝ) / p)) =
      ((M * 2 ^ α).toNNReal : ℝ≥0∞) * edist x y ^ α := by
    rw [Complex.finrank_real_complex, Nat.cast_ofNat, ← hα, Real.mul_rpow (by norm_num) hr.le,
      ← mul_assoc, ENNReal.ofReal_mul' (Real.rpow_nonneg hr.le α), edist_dist,
      ENNReal.ofReal_rpow_of_nonneg hr.le (NNReal.coe_nonneg _)]
    rfl
  rw [eDist_eq_eNorm_sub]
  calc ‖u x - u y‖ₑ
      ≤ ENNReal.ofReal (M * (2 * r) ^ (1 - (Module.finrank ℝ ℂ : ℝ) / p)) *
          eLpNorm (fderiv ℝ u) p (volume.restrict (ball z r)) := hmorrey
    _ ≤ ENNReal.ofReal (M * (2 * r) ^ (1 - (Module.finrank ℝ ℂ : ℝ) / p)) *
          (C₁ * (eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict U) +
            eLpNorm u p (volume.restrict U))) := by
      gcongr
      exact hDu.trans (hC₁ u hu)
    _ = _ := by
      rw [hconst, ENNReal.coe_mul]
      ring

/-- **A common Hölder constant on compact sets.** Let `2 < p < ∞` and let `U ⊆ ℂ` be open. Let
`u i` be maps smooth on `U`, with values in a complex Hilbert space, that are bounded on each
compact subset of `U` uniformly in `i`, and whose conjugate Wirtinger derivatives `\bar∂(u i)` are
bounded in `Lᵖ` on each compact subset of `U` uniformly in `i`. Then on each compact `K ⊆ U` the
maps `u i` are Hölder continuous of exponent `1 - 2 / p` with a common constant. -/
theorem exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le {ι : Type*} {p : ℝ≥0} (hp : 2 < p)
    {U : Set ℂ} (hU : IsOpen U) {u : ι → ℂ → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ, ∀ i, ∀ z ∈ K, ‖u i z‖ ≤ B)
    (hdbar : ∀ K ⊆ U, IsCompact K → ∃ A : ℝ≥0∞, A ≠ (∞ : ℝ≥0∞) ∧
      ∀ i, eLpNorm (fun z ↦ conjWirtingerDeriv (u i) z 1) p (volume.restrict K) ≤ A)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ i, HolderOnWith C (1 - 2 / p) (u i) K := by
  -- Work on the open `δ₀`-thickening `V` of `K`, whose closure is a compact subset of `U`.
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  set V := thickening δ₀ K
  have hKV : K ⊆ V := self_subset_thickening hδ₀ K
  have hVK' : V ⊆ cthickening δ₀ K := thickening_subset_cthickening δ₀ K
  obtain ⟨A, hA, hAle⟩ := hdbar _ hδ₀U hK.cthickening
  obtain ⟨B, hB⟩ := hbdd _ hδ₀U hK.cthickening
  obtain ⟨C₀, δ, hδ, hC₀⟩ :=
    exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm (F := F) hp isOpen_thickening hK hKV
  have hVfin : volume V ≠ (∞ : ℝ≥0∞) := (hK.isBounded.thickening.measure_lt_top).ne
  -- The `Lᵖ(V)` norms of `\bar∂(u i)` and `u i` are bounded uniformly in `i`.
  set N : ℝ≥0∞ := A + volume V ^ (p : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal B
  have hN : N ≠ (∞ : ℝ≥0∞) := ENNReal.add_ne_top.2 ⟨hA, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hVfin) ENNReal.ofReal_ne_top⟩
  have hNle (i : ι) : eLpNorm (fun z ↦ conjWirtingerDeriv (u i) z 1) p (volume.restrict V) +
      eLpNorm (u i) p (volume.restrict V) ≤ N := by
    refine add_le_add ((eLpNorm_mono_measure _ (Measure.restrict_mono hVK' le_rfl)).trans
      (hAle i)) ?_
    have hmeas : AEStronglyMeasurable (u i) (volume.restrict V) :=
      ((hu i).continuousOn.mono (hVK'.trans hδ₀U)).aestronglyMeasurable
        isOpen_thickening.measurableSet
    have h := eLpNorm_le_of_ae_bound (p := p) hmeas
      ((ae_restrict_iff' isOpen_thickening.measurableSet).2
        (Eventually.of_forall fun z hz ↦ hB i z (hVK' hz)))
    rwa [Measure.restrict_apply_univ] at h
  -- Nearby points: the local Hölder estimate. Distant points: the uniform bound on values.
  set α : ℝ≥0 := 1 - 2 / p
  have hnear (i : ι) : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      dist (u i x) (u i y) ≤ ((C₀ * N).toNNReal : ℝ) * dist x y ^ (α : ℝ) := by
    intro x hx y _ hxy
    have h : edist (u i x) (u i y) ≤ C₀ * N * edist x y ^ (α : ℝ) :=
      (hC₀ (u i) ((hu i).mono (hVK'.trans hδ₀U)) x hx y hxy).trans (by gcongr; exact hNle i)
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
      ← ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hN),
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h
    simpa [ENNReal.toReal_mul, ENNReal.coe_toNNReal_eq_toReal] using
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hfar (i : ι) : ∀ x ∈ K, ∀ y ∈ K, dist (u i x) (u i y) ≤ ((2 * B).toNNReal : ℝ) := by
    intro x hx y hy
    rw [dist_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    have h₁ := hB i x (hKV.trans hVK' hx)
    have h₂ := hB i y (hKV.trans hVK' hy)
    exact (by linarith : ‖u i x‖ + ‖u i y‖ ≤ 2 * B).trans (Real.le_coe_toNNReal _)
  exact ⟨_, fun i ↦ HolderOnWith.of_dist_lt_of_dist_le hδ (hnear i) (hfar i)⟩

/-- **Compactness from `Lᵖ` bounds on `\bar∂`, `p > 2`.** Let `2 < p < ∞`, let `U ⊆ ℂ` be open,
and let `u n` be maps smooth on `U`, with values in a proper complex Hilbert space, that are bounded
on each compact subset of `U` uniformly in `n`, and whose conjugate Wirtinger derivatives
`\bar∂(u n)` are bounded in `Lᵖ` on each compact subset of `U` uniformly in `n`. Then a subsequence
of the `u n` converges locally uniformly on `U` to a map `v` that is continuous on `U` and Hölder
continuous of exponent `1 - 2 / p` on each compact subset of `U`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le [ProperSpace F]
    {p : ℝ≥0} (hp : 2 < p) {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → F}
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) U)
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ, ∀ n, ∀ z ∈ K, ‖u n z‖ ≤ B)
    (hdbar : ∀ K ⊆ U, IsCompact K → ∃ A : ℝ≥0∞, A ≠ (∞ : ℝ≥0∞) ∧
      ∀ n, eLpNorm (fun z ↦ conjWirtingerDeriv (u n) z 1) p (volume.restrict K) ≤ A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F, ContinuousOn v U ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U ∧
      ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) v K := by
  classical
  have := hU.locallyCompactSpace
  set α : ℝ≥0 := 1 - 2 / p
  have hα : (0 : ℝ) < α :=
    NNReal.coe_pos.2 (tsub_pos_of_lt ((div_lt_one (two_pos.trans hp)).2 hp))
  have hholder := fun K (hKU : K ⊆ U) (hK : IsCompact K) ↦
    exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le hp hU hu hbdd hdbar hK hKU
  -- The restrictions of the `u n` to `U` are equicontinuous: near each point of `U` they share a
  -- Hölder bound.
  set G : ℕ → C(U, F) := fun n ↦ ⟨U.domRestrict (u n), (hu n).continuousOn.domRestrict⟩
  have hGeq : Equicontinuous fun n ↦ ⇑(G n) := by
    intro x₀
    obtain ⟨ε, hε, hεU⟩ := isOpen_iff.1 hU x₀ x₀.2
    have hcb : closedBall (x₀ : ℂ) (ε / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεU
    obtain ⟨C, hC⟩ := hholder _ hcb (isCompact_closedBall _ _)
    refine Metric.equicontinuousAt_of_continuity_modulus
      (fun y : U ↦ C * dist (x₀ : ℂ) y ^ (α : ℝ)) ?_ _ ?_
    · have hcont : Continuous fun y : U ↦ (C : ℝ) * dist (x₀ : ℂ) y ^ (α : ℝ) :=
        continuous_const.mul ((Real.continuous_rpow_const α.coe_nonneg).comp
          (continuous_const.dist continuous_subtype_val))
      have h₀ : (C : ℝ) * dist (x₀ : ℂ) x₀ ^ (α : ℝ) = 0 := by
        rw [dist_self, Real.zero_rpow hα.ne', mul_zero]
      exact h₀ ▸ hcont.tendsto x₀
    · have hmem : ∀ᶠ y : U in 𝓝 x₀, (y : ℂ) ∈ closedBall (x₀ : ℂ) (ε / 2) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds
          (closedBall_mem_nhds _ (half_pos hε))
      filter_upwards [hmem] with y hy n
      exact (hC n).dist_le (mem_closedBall_self (half_pos hε).le) hy
  -- At each point the values lie in a closed ball, which is compact since `F` is proper.
  have hpt (x : U) : ∃ Q, IsCompact Q ∧ ∀ n, G n x ∈ Q := by
    obtain ⟨B, hB⟩ := hbdd {(x : ℂ)} (singleton_subset_iff.2 x.2) isCompact_singleton
    exact ⟨closedBall 0 B, isCompact_closedBall _ _,
      fun n ↦ mem_closedBall_zero_iff.2 (hB n x rfl)⟩
  -- Arzelà–Ascoli in `C(U, F)` gives a subsequence converging locally uniformly on `U`.
  obtain ⟨g, -, φ, hφ, hlim⟩ :=
    (ArzelaAscoli.isCompact_closure_range_of_equicontinuous hGeq hpt).tendsto_subseq
      fun n ↦ subset_closure (mem_range_self n)
  set v : ℂ → F := fun z ↦ if hz : z ∈ U then g ⟨z, hz⟩ else 0
  have hvg : U.domRestrict v = g := funext fun z ↦ by simp [v, z.2]
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have h := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hlim
    rwa [← hvg] at h
  refine ⟨φ, hφ, v, ?_, hconv, fun K hKU hK ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, hvg]
    exact g.continuous
  -- The common Hölder bound passes to the pointwise limit.
  obtain ⟨C, hC⟩ := hholder K hKU hK
  exact ⟨C, fun x hx y hy ↦ le_of_tendsto'
    ((hconv.tendsto_at (hKU hx)).edist (hconv.tendsto_at (hKU hy))) fun n ↦ hC (φ n) x hx y hy⟩

end TauCeti
