/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Embedding
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey
import TauCeti.Analysis.Sobolev.Morrey.Exponent

/-!
# Morrey's embedding for Sobolev sections of every order

Let `M` be a compact smooth manifold without boundary, given by a finite bundle atlas `A` of a
Hausdorff manifold modelled on a real inner product space `E` of finite dimension `n`, and let
`V → M` be a smooth real vector bundle with finite-dimensional model fibre `F`. This file proves
Morrey's embedding for the Sobolev spaces `W^{k,p}(V)` of `TauCeti.SobolevSection` in every
dimension and every order, under Morrey's condition `k p > n`:

* **Continuity.** For `1 < p ≤ ∞` and `k p > n`, every element of `W^{k,p}(V)` has a continuous
  representative (`TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt_mul`).
* **Hölder continuity with the Morrey exponent.** If `(k - 1) p < n < k p`, the chart expressions
  of the continuous representative of `w ∈ W^{k,p}(V)` are `α`-Hölder on compact subsets of the
  chart images, with `α = k - n/p` and constant `C ‖w‖`
  (`TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection_of_mul_lt_of_lt_mul`).
  With `TauCeti.SobolevSection.coordHolderL` this is a bounded operator
  `W^{k,p}(V) → C^{0,α}(K; F)`, compact into `C^{0,β}(K; F)` for `β < α`. In dimension `3`,
  `W^{2,2}(V) → C^{0,1/2}(K; F)`.
* **The integer margin.** If `(k - 1) p = n`, so that `k - n/p = 1`, the chart expressions are
  `β`-Hölder for every `0 < β < 1`
  (`TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection_of_mul_eq`); the Lipschitz
  endpoint `β = 1` is not claimed, and fails in general. In dimension `2` this applies to
  `W^{2,2}(V)`.

The proofs reduce to order one. If `p ≤ n`, the Sobolev embedding
`W^{k+1,p₀}(V) → W^{k,q}(V)`, `1/q + 1/n = 1/p₀`, for an exponent `p₀ ≤ p` that is `p` itself
unless `p = n`, keeps the chart data (`TauCeti.SobolevSection.exists_sobolevEmbeddingL`), and
`k q > n` again; by induction on `k` this ends at order one above the dimension, where
`TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt` applies. Continuous
representatives transfer back along maps keeping the chart data
(`TauCeti.SobolevSection.HasContinuousRepresentatives.of_chartValueL_ae_eq`). For the Hölder bound,
`r = k - 1` embeddings at once give `W^{k,p}(V) → W^{1,q}(V)` with `1/q + r/n = 1/p`
(`TauCeti.SobolevSection.exists_sobolevEmbeddingL_of_inv_add_eq`), and `n < q` with the same
Morrey exponent `1 - n/q = k - n/p`, so the order-one Hölder bound
`TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection` applies. At the integer
margin, lowering `p` to `p₀ = n / (k - β)` reaches the exponent `k - n/p₀ = β`. The exponent
arithmetic is in `TauCeti.Analysis.Sobolev.Morrey.Exponent`.

## Main results

* `TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt_mul`: continuous
  representatives in `W^{k,p}(V)` for `1 < p` and `k p > n`.
* `TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection_of_mul_lt_of_lt_mul`: the
  Hölder bound with exponent `k - n/p` for `(k - 1) p < n < k p`.
* `TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection_of_mul_eq`: Hölder bounds
  with every exponent `β < 1` for `(k - 1) p = n`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press (2003),
  Theorem 4.12, Part II.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.26.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Theorem 2.21
  (the Sobolev embeddings on compact manifolds).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {A : FiniteBundleAtlas E M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace SobolevSection

/-- **Morrey's embedding for Sobolev sections: continuous representatives.** For `1 < p ≤ ∞` and
Morrey's condition `k p > n`, where `n` is the dimension, every element `w` of `W^{k,p}(V)` has a
continuous representative: a continuous section `s` of `V` whose chart expression `A.coord i s`
agrees, for every chart `i`, almost everywhere on `A.image i` with the chart data of `w`. -/
theorem HasContinuousRepresentatives.of_finrank_lt_mul (hp : 1 < p)
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p) : HasContinuousRepresentatives A μ p k := by
  induction k generalizing p with
  | zero => simp at hkp
  | succ k ih =>
    rcases lt_or_ge (finrank ℝ E : ℝ≥0∞) p with hnp | hpn
    · -- Above the dimension, order one suffices.
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact .of_finrank_lt hnp
      · exact (ih hp (hnp.trans_le (le_mul_of_one_le_left' (by exact_mod_cast hk)))).mono le_rfl
          k.le_succ
    · -- Otherwise one Sobolev embedding `W^{k+1,p₀}(V) → W^{k,q}(V)` keeps `k q > n`.
      obtain ⟨p₀, q, hp₀, hp₀p, hq, hexp, hq1, hkq⟩ :=
        exists_le_and_ne_top_and_inv_add_inv_eq_and_lt_mul hp hpn hkp
      have : Fact (1 ≤ p₀) := ⟨hp₀⟩
      have : Fact (1 ≤ q) := ⟨hq1.le⟩
      obtain ⟨T, hT⟩ := exists_sobolevEmbeddingL A μ hq hexp k
      exact ((ih hq1 hkq).of_chartValueL_ae_eq T hT).mono hp₀p le_rfl

/-- **Morrey's embedding for Sobolev sections: Hölder continuity in charts.** If
`(k - 1) p < n < k p`, where `n` is the dimension, then on every compact subset `K` of the image of
chart `i` the chart expression of the continuous representative of `w ∈ W^{k,p}(V)` is Hölder
continuous with exponent `k - n / p` and constant `C ‖w‖`, where `C` depends on `K` but not on
`w`. -/
theorem exists_forall_holderOnWith_coord_toSection_of_mul_lt_of_lt_mul
    (hk : ((k - 1 : ℕ) : ℝ≥0∞) * p < finrank ℝ E) (hkp : (finrank ℝ E : ℝ≥0∞) < k * p)
    (i : Fin A.n) {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k, HolderOnWith (C * ‖w‖₊)
      ((k : ℝ≥0∞) - finrank ℝ E / p).toNNReal (A.coord i (toSection w)) K := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hkp
  obtain ⟨r, rfl⟩ : ∃ r, k = 1 + r := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel_left] at hk
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.add_zero, Nat.cast_one, one_mul] at hkp ⊢
    exact exists_forall_holderOnWith_coord_toSection hkp i hK hKi
  -- `r` Sobolev embeddings at once give `W^{1+r,p}(V) → W^{1,q}(V)` with `n < q`.
  rw [Nat.add_comm] at hkp
  obtain ⟨q, hq, hexp, hnq, hα⟩ := exists_inv_add_mul_inv_eq_and_lt_and_sub_div_eq hr.ne' hk hkp
  rw [Nat.add_comm r 1] at hα
  have : Fact (1 ≤ q) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  obtain ⟨T, hT⟩ := exists_sobolevEmbeddingL_of_inv_add_eq A μ 1 r hq hexp
  obtain ⟨C, hC⟩ := exists_forall_holderOnWith_coord_toSection (μ := μ) hnq i hK hKi
  refine ⟨C * ‖T‖₊, fun w ↦ ?_⟩
  have h := hC (T w)
  rw [toSection_eq_of_chartValueL_ae_eq (.of_finrank_lt hnq) (hT w), hα] at h
  refine h.mono_const ?_
  rw [mul_assoc]
  gcongr
  exact T.le_opNNNorm w

/-- **Morrey's embedding for Sobolev sections at an integer margin.** If `1 < p` and
`(k - 1) p = n`, where `n` is the dimension, so that the Morrey exponent `k - n / p` is `1`, then
for every `0 < β < 1`, on every compact subset `K` of the image of chart `i`, the chart expression
of the continuous representative of `w ∈ W^{k,p}(V)` is Hölder continuous with exponent `β` and
constant `C ‖w‖`, where `C` depends on `β` and `K` but not on `w`. -/
theorem exists_forall_holderOnWith_coord_toSection_of_mul_eq (hp : 1 < p)
    (hkp : ((k - 1 : ℕ) : ℝ≥0∞) * p = finrank ℝ E) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β < 1)
    (i : Fin A.n) {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) β (A.coord i (toSection w)) K := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · -- In dimension zero, `K` has at most one point.
    have : Subsingleton E := finrank_zero_iff.1 hn
    exact ⟨0, fun w ↦ subsingleton_of_subsingleton.holderOnWith _ _ _⟩
  -- Lower `p` to `p₀ = n / (k - β)`, whose Morrey exponent is `β`.
  obtain ⟨p₀, hp₀, hp₀p, hk₀, hkp₀, hβ⟩ :=
    exists_mul_lt_and_lt_mul_and_sub_div_eq hn hp hkp hβ0 hβ1
  have : Fact (1 ≤ p₀) := ⟨hp₀.le⟩
  obtain ⟨C, hC⟩ :=
    exists_forall_holderOnWith_coord_toSection_of_mul_lt_of_lt_mul (μ := μ) hk₀ hkp₀ i hK hKi
  rw [hβ, ENNReal.toNNReal_coe] at hC
  let T := A.sectionChartData.ofExponentLEL μ k hp₀p
  refine ⟨C * ‖T‖₊, fun w ↦ ?_⟩
  have h := hC (T w)
  rw [toSection_ofExponentLEL hp₀p
    ((HasContinuousRepresentatives.of_finrank_lt_mul hp₀ hkp₀).mono hp₀p le_rfl)] at h
  refine h.mono_const ?_
  rw [mul_assoc]
  gcongr
  exact T.le_opNNNorm w

/-- **Check.** In dimension `3`, `W^{2,2}(V)` embeds continuously into the Hölder space
`C^{0,1/2}(K; F)` on every compact subset `K` of a chart image: `(2 - 1) · 2 < 3 < 2 · 2` and the
Morrey exponent is `2 - 3/2 = 1/2`. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (hE : finrank ℝ E = 3) (i : Fin A.n) (K : Set E)
    [CompactSpace K] (hKi : K ⊆ A.image i) :
    ∃ T : SobolevSection A μ 2 2 →L[ℝ] HolderSpace (1 / 2) K F,
      ∀ w (y : K), T w y = A.coord i (toSection w) y := by
  have hk : (((2 - 1 : ℕ) : ℝ≥0∞)) * 2 < finrank ℝ E := by rw [hE]; norm_num
  have hkp : (finrank ℝ E : ℝ≥0∞) < (2 : ℕ) * 2 := by rw [hE]; norm_num
  have hα : (((2 : ℕ) : ℝ≥0∞) - finrank ℝ E / 2).toNNReal = 1 / 2 := by
    have h : ((2 : ℕ) : ℝ≥0∞) - ((3 : ℕ) : ℝ≥0∞) / 2 = ENNReal.ofReal (1 / 2) := by
      rw [show ((3 : ℕ) : ℝ≥0∞) / 2 = ENNReal.ofReal (3 / 2) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
        show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_sub _ (by norm_num)]
      norm_num
    rw [hE, h, ENNReal.ofReal, ENNReal.toNNReal_coe]
    ext
    norm_num
  obtain ⟨C, hC⟩ := exists_forall_holderOnWith_coord_toSection_of_mul_lt_of_lt_mul (μ := μ)
    hk hkp i (isCompact_iff_compactSpace.2 ‹_›) hKi
  rw [hα] at hC
  exact ⟨coordHolderL (.of_finrank_lt_mul (by norm_num) hkp) i K hKi ⟨C, hC⟩,
    coordHolderL_apply_apply _ i K hKi _⟩

/-- **Check.** In dimension `2`, `(2 - 1) · 2 = 2`, so the Morrey exponent of `W^{2,2}(V)` is the
integer `1`: its chart expressions are `β`-Hölder on compact subsets of the chart images for every
`0 < β < 1`. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (hE : finrank ℝ E = 2) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β < 1)
    (i : Fin A.n) {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ 2 2,
      HolderOnWith (C * ‖w‖₊) β (A.coord i (toSection w)) K :=
  exists_forall_holderOnWith_coord_toSection_of_mul_eq (by norm_num) (by rw [hE]; norm_num) hβ0 hβ1
    i hK hKi

end SobolevSection

end TauCeti
