/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder bounds and compactness from `Lᵖ` bounds on `\bar∂`, `p > 2`

Let `2 < p < ∞` and let `U ⊆ ℂ` be open. For a map `u` smooth on `U` with values in a complex
Hilbert space, the interior Calderón–Zygmund estimate
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`) bounds the `Lᵖ` norm
of the derivative of `u` on a compact subset of `U` by the `Lᵖ(U)` norms of `\bar∂u` and `u`, and
Morrey's inequality (`TauCeti.edist_le_of_contDiffOn_ball_midpoint_of_finrank_lt`) turns an `Lᵖ`
bound on the derivative, `p > 2`, into a Hölder bound of exponent `1 - 2 / p`. Together they give a
local Hölder estimate controlled by `\bar∂u` and `u` alone
(`TauCeti.exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`): for `K ⊆ U` compact there are
`C` and `δ > 0` with

`‖u x - u y‖ ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)}) |x - y| ^ (1 - 2 / p)`

for all `x ∈ K` and `|x - y| < δ`.

Consequently a family of maps that is bounded on compact subsets of `U`, and whose `\bar∂` is
bounded in `Lᵖ` on compact subsets of `U`, is Hölder continuous of exponent `1 - 2 / p` on each
compact subset with a common constant
(`TauCeti.exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le`).
By the Arzelà–Ascoli theorem for locally Hölder families
(`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_holderOnWith`) a sequence of such maps, with
values in a proper space, has a subsequence converging locally uniformly on `U`; the limit is
continuous on `U` and Hölder of the same exponent on each compact subset
(`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le`).

This is the compactness step for functions solving a scalar Cauchy–Riemann equation with an `Lᵖ`
forcing, such as `\bar∂b = -ν b + f` with `ν` bounded and `f` bounded in `Lᵖ`. For `p = 2 + 2 / m`
the Hölder exponent `1 - 2 / p` is `1 / (m + 1)`. This is the exponent that arises if the symmetric
coefficients of the local branches of Seiberg–Witten solutions concentrating along a
pseudoholomorphic curve, the setting of Taubes's *SW ⇒ Gr*, satisfy such equations with that `p`;
no such equation is proved here.

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
  set M : ℝ := 2 ^ (Module.finrank ℝ ℂ + 1) /
      (Module.finrank ℝ ℂ * volume.real (ball (0 : ℂ) 1)) *
      (Module.finrank ℝ ℂ * volume.real (ball (0 : ℂ) 1) * (p - 1) /
        (p - Module.finrank ℝ ℂ)) ^ (1 - 1 / (p : ℝ)) *
      2 ^ (1 - Module.finrank ℝ ℂ / (p : ℝ))
  refine ⟨M.toNNReal * C₁, (δ₀ / 2).toNNReal, by simpa using hδ₀, fun u hu x hx y hxy ↦ ?_⟩
  have hxy' : dist x y < δ₀ / 2 := by
    simpa [Real.coe_toNNReal _ (half_pos hδ₀).le] using hxy
  -- The ball of radius `|x - y|` about the midpoint of `x` and `y` lies in the `δ₀`-thickening
  -- of `K`.
  set z := midpoint ℝ x y
  have hzx : dist z x = dist x y / 2 := by
    rw [dist_comm, dist_left_midpoint, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    ring
  have hball : ball z (dist x y) ⊆ cthickening δ₀ K := fun w hw ↦
    mem_cthickening_of_dist_le w x δ₀ K hx (by
      linarith [dist_triangle w z x, mem_ball.1 hw, dist_nonneg (x := x) (y := y)])
  have hmorrey := edist_le_of_contDiffOn_ball_midpoint_of_finrank_lt (μ := volume)
    ((hu.mono (hball.trans hδ₀U)).of_le (by exact_mod_cast le_top)) hfin
  rw [show ((Module.finrank ℝ ℂ : ℕ) : ℝ≥0) = 2 by simp] at hmorrey
  calc edist (u x) (u y)
      ≤ ENNReal.ofReal M * eLpNorm (fderiv ℝ u) p (volume.restrict (ball z (dist x y))) *
          edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) := hmorrey
    _ ≤ ENNReal.ofReal M * (C₁ * (eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p
          (volume.restrict U) + eLpNorm u p (volume.restrict U))) *
          edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) := by
      gcongr
      exact (eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)).trans (hC₁ u hu)
    _ = _ := by
      rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
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
    have h : edist (u i x) (u i y) ≤ (C₀ * N).toNNReal * edist x y ^ (α : ℝ) := by
      rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hN)]
      exact (hC₀ (u i) ((hu i).mono (hVK'.trans hδ₀U)) x hx y hxy).trans (by gcongr; exact hNle i)
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h
    rw [dist_nndist, dist_nndist]
    exact_mod_cast h
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
  have hholder := fun K (hKU : K ⊆ U) (hK : IsCompact K) ↦
    exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le hp hU hu hbdd hdbar hK hKU
  -- At each point the values lie in a closed ball, which is compact since `F` is proper.
  have hpt (x : ℂ) (hx : x ∈ U) : ∃ Q, IsCompact Q ∧ ∀ n, u n x ∈ Q := by
    obtain ⟨B, hB⟩ := hbdd {x} (singleton_subset_iff.2 hx) isCompact_singleton
    exact ⟨closedBall 0 B, isCompact_closedBall _ _,
      fun n ↦ mem_closedBall_zero_iff.2 (hB n x rfl)⟩
  obtain ⟨φ, hφ, v, hv, hconv, hlim⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_holderOnWith hU
    (tsub_pos_of_lt ((div_lt_one (two_pos.trans hp)).2 hp)) hholder hpt
  refine ⟨φ, hφ, v, hv, hconv, fun K hKU hK ↦ ?_⟩
  obtain ⟨C, hC⟩ := hholder K hKU hK
  exact ⟨C, hlim K hKU C hC⟩

end TauCeti
