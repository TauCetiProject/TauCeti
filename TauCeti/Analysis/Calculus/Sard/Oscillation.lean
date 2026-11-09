/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Null images of sets with a small oscillation modulus

Let `A` be a bounded subset of `Fin n → ℝ` and `f` a map into a nontrivial finite-dimensional
real normed space `F`. If `f` has a uniform little-o modulus of order `k` on `A`, that is
`‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k` for nearby points of `A` and every `ε > 0`, and
`n ≤ k * finrank ℝ F`, then `f '' A` is null for every additive Haar measure on `F`.

On a small piece of `A` the map is Hölder of exponent `k` with constant `ε`, so
`HolderOnWith.hausdorffMeasure_image_le` bounds the `finrank ℝ F`-dimensional Hausdorff measure of
the image of the piece by `ε ^ finrank ℝ F` times the `k * finrank ℝ F`-dimensional Hausdorff
measure of the piece, which is at most its `n`-dimensional one, Lebesgue measure. Partitioning a
containing ball into small Borel pieces and letting `ε` tend to zero gives the claim. Neither the
set nor its image needs to be measurable.

This is the measure estimate of the Morse--Sard theorem: on the pieces of the Morse decomposition
of a set where the derivative of a `C^k` map vanishes, the map has such a modulus of order `k`
(`TauCeti.exists_cover_of_critical`). The input statement is adapted from KLS at commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`, `Analysis/Sard/QuadraticCover.lean`, which treats
real-valued maps with `k = n`; the proof uses Mathlib's Hausdorff-measure API instead of its
coordinate grid count. See A. Norton, *A critical set with nonnull image has large Hausdorff
dimension*, Trans. Amer. Math. Soc. 296 (1986), Section 5, Lemma 1.
-/

public section

open Set MeasureTheory Filter Topology
open scoped MeasureTheory NNReal ENNReal

namespace TauCeti

/-- A uniform little-o modulus of order `k` on `A` passes through a continuous linear map: if
`‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k` for nearby points of `A` and every `ε > 0`, then the same holds
for `L ∘ f`. -/
theorem _root_.ContinuousLinearMap.oscillation_pow_comp {E F G : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {A : Set E} {f : E → F} {k : ℕ}
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → ‖L (f y) - L (f x)‖ ≤ ε * ‖y - x‖ ^ k := by
  intro ε hε
  have hC : 0 < ‖L‖ + 1 := by positivity
  obtain ⟨δ, hδ, hd⟩ := hosc (ε / (‖L‖ + 1)) (div_pos hε hC)
  refine ⟨δ, hδ, fun x hx y hy hxy ↦ ?_⟩
  calc ‖L (f y) - L (f x)‖ = ‖L (f y - f x)‖ := by rw [map_sub]
    _ ≤ ‖L‖ * ‖f y - f x‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * (ε / (‖L‖ + 1) * ‖y - x‖ ^ k) :=
        mul_le_mul (by linarith) (hd x hx y hy hxy) (norm_nonneg _) hC.le
    _ = ε * ‖y - x‖ ^ k := by field_simp

/-- The case of `TauCeti.addHaar_image_eq_zero_of_oscillation_pow` with target `Fin p → ℝ` and
Lebesgue measure, where the target measure is the `p`-dimensional Hausdorff measure. -/
private theorem volume_image_eq_zero_of_oscillation_pow {n k p : ℕ} (hp : p ≠ 0)
    {A : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → Fin p → ℝ} (hA : Bornology.IsBounded A)
    (hdim : n ≤ k * p)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k) :
    volume (f '' A) = 0 := by
  classical
  have : Nonempty (Fin p) := ⟨⟨0, Nat.pos_of_ne_zero hp⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- With `k = 0` the source is a point.
    obtain rfl : n = 0 := by simpa using hdim
    exact (Set.Subsingleton.image (fun a _ b _ ↦ Subsingleton.elim a b) f).measure_zero _
  obtain ⟨R, hR, hAR⟩ := hA.exists_pos_norm_le
  let B : Set (Fin n → ℝ) := Metric.closedBall 0 R
  have hAB : A ⊆ B := fun x hx ↦ by
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hAR x hx
  have hμ : volume B ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  -- A measurable partition of a containing ball bounds the outer measures of the pieces.
  have key (ε : ℝ≥0) (hε : 0 < ε) : volume (f '' A) ≤ ((ε ^ p : ℝ≥0) : ℝ≥0∞) * volume B := by
    obtain ⟨δ, hδ, hd⟩ := hosc ε hε
    obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq (Fin n → ℝ)
    let T : ℕ → Set (Fin n → ℝ) := disjointed fun j ↦ Metric.ball (c j) (δ / 2)
    have hTsub : ∀ j, T j ⊆ Metric.ball (c j) (δ / 2) := disjointed_subset _
    have hTunion : ⋃ j, T j = univ := by
      rw [iUnion_disjointed, eq_univ_iff_forall]
      intro y
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hc y (δ / 2) (by linarith)
      exact mem_iUnion.2 ⟨j, hj⟩
    have hhol (j : ℕ) : HolderOnWith ε (k : ℝ≥0) f (A ∩ T j) := by
      intro x hx y hy
      have hdist : dist y x < δ := by
        have h1 := hTsub j hx.2
        have h2 := hTsub j hy.2
        calc dist y x ≤ dist y (c j) + dist x (c j) := dist_triangle_right _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add h2 h1
          _ = δ := by ring
      have hreal : dist (f x) (f y) ≤ (ε : ℝ) * dist x y ^ k := by
        simpa [dist_eq_norm, norm_sub_rev] using
          hd x hx.1 y hy.1 (by simpa [dist_eq_norm] using hdist)
      simpa only [edist_dist, ENNReal.ofReal_mul ε.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow dist_nonneg,
        NNReal.coe_natCast, ENNReal.rpow_natCast] using ENNReal.ofReal_le_ofReal hreal
    -- On each piece, the image has `p`-dimensional measure at most `ε ^ p` times the
    -- `k * p`-dimensional, hence at most the `n`-dimensional, measure of the piece.
    have hpiece (j : ℕ) :
        volume (f '' (A ∩ T j)) ≤ ((ε ^ p : ℝ≥0) : ℝ≥0∞) * volume (B ∩ T j) := by
      have hh := (hhol j).hausdorffMeasure_image_le (by exact_mod_cast hk) (d := p)
        (Nat.cast_nonneg _)
      have hmono : μH[((k : ℝ≥0) : ℝ) * p] (A ∩ T j) ≤ μH[n] (A ∩ T j) :=
        Measure.hausdorffMeasure_mono (by push_cast; exact_mod_cast hdim) _
      have hvol : ∀ (m : ℕ) (s : Set (Fin m → ℝ)), μH[m] s = volume s := fun m s ↦ by
        simpa using congrArg (fun μ : Measure (Fin m → ℝ) ↦ μ s)
          (hausdorffMeasure_pi_real (ι := Fin m))
      rw [hvol, ENNReal.rpow_natCast] at hh
      rw [hvol] at hmono
      calc volume (f '' (A ∩ T j)) ≤ (ε : ℝ≥0∞) ^ p * volume (A ∩ T j) :=
            hh.trans (mul_le_mul_right hmono _)
        _ ≤ ((ε ^ p : ℝ≥0) : ℝ≥0∞) * volume (B ∩ T j) := by
            rw [ENNReal.coe_pow]
            exact mul_le_mul_right (measure_mono (inter_subset_inter_left _ hAB)) _
    calc volume (f '' A)
        ≤ volume (⋃ j, f '' (A ∩ T j)) := by
          apply measure_mono
          rw [← image_iUnion, ← inter_iUnion, hTunion, inter_univ]
      _ ≤ ∑' j, volume (f '' (A ∩ T j)) := measure_iUnion_le _
      _ ≤ ∑' j, ((ε ^ p : ℝ≥0) : ℝ≥0∞) * volume (B ∩ T j) := tsum_le_tsum hpiece
      _ = ((ε ^ p : ℝ≥0) : ℝ≥0∞) * volume B := by
          rw [ENNReal.tsum_mul_left, ← measure_iUnion
            (fun i j hij ↦ (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right)
            (fun j ↦ measurableSet_closedBall.inter
              (MeasurableSet.disjointed (fun _ ↦ measurableSet_ball) j)),
            ← inter_iUnion, hTunion, inter_univ]
  -- The containing ball has finite measure, so arbitrarily small Hölder constants force nullity.
  have htend : Tendsto (fun ε : ℝ≥0 ↦ ((ε ^ p : ℝ≥0) : ℝ≥0∞) * volume B) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ≥0 ↦ ((ε ^ p : ℝ≥0) : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
      simpa [zero_pow hp, Function.comp_def] using
        (ENNReal.continuous_coe.comp (continuous_pow p)).tendsto (0 : ℝ≥0)
    simpa using (ENNReal.Tendsto.mul_const h0 (Or.inr hμ)).mono_left nhdsWithin_le_nhds
  exact le_antisymm (ge_of_tendsto htend (eventually_nhdsWithin_of_forall key)) bot_le

/-- A bounded subset of `Fin n → ℝ` on which a map into a nontrivial finite-dimensional space `F`
has a uniform little-o modulus of order `k` has null image for every additive Haar measure on `F`,
provided `n ≤ k * finrank ℝ F`. The set need not be measurable. -/
theorem addHaar_image_eq_zero_of_oscillation_pow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
    (ν : Measure F) [ν.IsAddHaarMeasure] {n k : ℕ} {A : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → F}
    (hA : Bornology.IsBounded A) (hdim : n ≤ k * Module.finrank ℝ F)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k) :
    ν (f '' A) = 0 := by
  -- Read `f` in coordinates `e : F ≃L[ℝ] (Fin p → ℝ)`, which carry the modulus along.
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hnull : volume ((e ∘ f) '' A) = 0 :=
    volume_image_eq_zero_of_oscillation_pow Module.finrank_pos.ne' hA hdim (by
      simpa using (e : F →L[ℝ] (Fin (Module.finrank ℝ F) → ℝ)).oscillation_pow_comp hosc)
  have hpre : ν (e ⁻¹' ((e ∘ f) '' A)) = 0 := by
    simpa only [ContinuousLinearEquiv.toContinuousAddEquiv_coe] using
      (e.toContinuousAddEquiv.quasiMeasurePreserving_addHaar ν volume).preimage_null hnull
  rwa [image_comp, Set.preimage_image_eq _ e.injective] at hpre

end TauCeti
