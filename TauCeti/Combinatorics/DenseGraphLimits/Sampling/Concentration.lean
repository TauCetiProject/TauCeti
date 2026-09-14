/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Exposure
import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Unbiased
import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Closeness
import TauCeti.Probability.McDiarmid

/-!
# Concentration of sampled homomorphism densities

For a fixed finite graph `F`, its ordinary homomorphism density in a graphon sample `G(n, W)`
concentrates exponentially around the graphon homomorphism density. The proof applies McDiarmid's
bounded-differences inequality to the padded vertex exposure: its coordinates are independent, its
pushforward is the sampling law, and changing one coordinate moves the density by at most
`|V(F)| / n`.

McDiarmid centers the estimator at its finite-sample mean. The ordinary density is not exactly
unbiased because vertex maps may collide, so the proof compares it to the injective density. The
latter is unbiased, while their pointwise difference is at most `|V(F)|.choose 2 / n`. The stated
side condition absorbs this collision bias.

## Main result

* `TauCeti.DenseGraphLimits.sampleGraph_homDensityFin_concentration` — the probability of a
  deviation of at least `ε` is at most `2 * exp (-ε²n / (2|V(F)|²))`.
* `TauCeti.DenseGraphLimits.tsum_sampleGraph_homDensityFin_tail_ne_top` — these deviation
  probabilities are summable for every positive `ε`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`.
  The centering, collision-bias transfer, and two-tail calculation are adapted from that file.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integration along the padded exposure agrees with integration under the graphon sampling law.
This is the integral form of `map_exposedSample`. -/
private theorem integral_homDensityFin_exposedSample {V : Type*} [Fintype V]
    (F : SimpleGraph V) (W : Graphon Ω μ) (n : ℕ) :
    (∫ x, homDensityFin F (exposedSample W x) ∂exposureMeasure μ n) =
      ∫ G, homDensityFin F G ∂sampleGraph W n := by
  have hG : Measurable fun G : SimpleGraph (Fin n) => homDensityFin F G :=
    measurable_of_finite _
  rw [← map_exposedSample W n,
    integral_map (measurable_exposedSample W).aemeasurable hG.aestronglyMeasurable]

/-- The mean ordinary homomorphism density differs from the graphon density by no more than the
collision probability bound, whenever the sample has enough vertices for the injective density. -/
private theorem abs_integral_homDensityFin_sampleGraph_sub_le {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ}
    (hVn : Fintype.card V ≤ n) :
    |(∫ G, homDensityFin F G ∂sampleGraph W n) - homDensity F W| ≤
      ((Fintype.card V).choose 2 : ℝ) / n := by
  rw [← integral_injHomDensity_sampleGraph W F hVn, ← integral_sub]
  · calc
      |∫ G, homDensityFin F G - injHomDensity F G ∂sampleGraph W n|
          ≤ ∫ G, |homDensityFin F G - injHomDensity F G| ∂sampleGraph W n :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _G, ((Fintype.card V).choose 2 : ℝ) / n ∂sampleGraph W n := by
        refine integral_mono Integrable.of_finite (integrable_const _) fun G => ?_
        simpa only [Fintype.card_fin] using homDensityFin_sub_injHomDensity_le F G
      _ = ((Fintype.card V).choose 2 : ℝ) / n := by simp
  · exact Integrable.of_finite
  · exact Integrable.of_finite

/-- **Exponential concentration of a sampled homomorphism density.** Let `F` have `q` vertices.
If `2q² ≤ εn`, then under the graphon sampling law `G(n, W)`,

`P(|t(F, G(n, W)) - t(F, W)| ≥ ε) ≤ 2 exp(-ε²n / (2q²))`.

The side condition is eventual in `n` for fixed `F` and positive `ε`; it absorbs the collision
bias between the mean ordinary homomorphism density and the graphon density. -/
theorem sampleGraph_homDensityFin_concentration {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn : 2 * (Fintype.card V : ℝ) ^ 2 ≤ ε * n) :
    ((sampleGraph W n) {G | ε ≤ |homDensityFin F G - homDensity F W|}).toReal ≤
      2 * Real.exp (-(ε ^ 2 * n) / (2 * (Fintype.card V : ℝ) ^ 2)) := by
  rw [← Measure.real_def]
  let q := Fintype.card V
  rcases Nat.eq_zero_or_pos q with hq | hq
  · have hmass : (sampleGraph W n).real
        {G | ε ≤ |homDensityFin F G - homDensity F W|} ≤ 1 := by
      calc
        _ ≤ (sampleGraph W n).real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp
    calc
      _ ≤ 1 := hmass
      _ ≤ 2 * Real.exp (-(ε ^ 2 * n) / (2 * (Fintype.card V : ℝ) ^ 2)) := by
        have hcard : (Fintype.card V : ℝ) = 0 := by simp [q, hq]
        rw [hcard]
        norm_num
  · by_cases hε1 : ε ≤ 1
    · have hnpos : 0 < n := Nat.pos_of_ne_zero fun hn0 => by
        subst n
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq
        norm_num at hn
        nlinarith
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hVnR : (q : ℝ) ≤ n := by
        have hεn : ε * (n : ℝ) ≤ n := by nlinarith
        have htwo : 2 * (q : ℝ) ^ 2 ≤ n := hn.trans hεn
        nlinarith
      have hVn : Fintype.card V ≤ n := by exact_mod_cast hVnR
      let ν : Measure (Ω × (Fin n → ℝ)) :=
        μ.prod (Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1)
      let f : (Fin n → Ω × (Fin n → ℝ)) → ℝ :=
        fun x => homDensityFin F (exposedSample W x)
      have hf : Measurable f :=
        (measurable_of_finite fun G : SimpleGraph (Fin n) => homDensityFin F G).comp
          (measurable_exposedSample W)
      let σ : ℝ≥0 :=
        (n : ℝ≥0) * (Real.toNNReal ((q : ℝ) / (n : ℝ)) / 2) ^ 2
      have hsub : ProbabilityTheory.HasSubgaussianMGF
          (fun x => f x - ∫ y, f y ∂Measure.pi fun _ : Fin n => ν) σ
          (Measure.pi fun _ : Fin n => ν) := by
        simpa only [σ] using
          Probability.hasSubgaussianMGF_of_bounded_differences_fin ν f hf
            ((q : ℝ) / n) fun x i y => by
              simpa [f, q] using abs_homDensityFin_exposedSample_update_le F W x i y
      have hν : Measure.pi (fun _ : Fin n => ν) = exposureMeasure μ n := by
        simp only [ν, exposureMeasure_def]
      rw [hν] at hsub
      have htail₁ := hsub.measure_ge_le (ε := ε / 2) (half_pos hε).le
      have htail₂ := hsub.neg.measure_ge_le (ε := ε / 2) (half_pos hε).le
      have hc : (σ : ℝ) =
          (n : ℝ) * (((q : ℝ) / (n : ℝ)) / 2) ^ 2 := by
        simp only [σ, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
          Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ (q : ℝ) / (n : ℝ)),
          NNReal.coe_natCast, NNReal.coe_ofNat]
      have hexp : -(ε / 2) ^ 2 / (2 * (σ : ℝ)) =
          -(ε ^ 2 * (n : ℝ)) / (2 * (q : ℝ) ^ 2) := by
        rw [hc]
        field_simp
      have hchoose : ((q.choose 2 : ℕ) : ℝ) ≤ (q : ℝ) ^ 2 := by
        have hsubq : ((q - 1 : ℕ) : ℝ) ≤ q := by
          exact_mod_cast Nat.sub_le q 1
        rw [Nat.cast_choose_two]
        nlinarith [Nat.cast_nonneg (α := ℝ) (q - 1)]
      have hbias : |(∫ y, f y ∂exposureMeasure μ n) - homDensity F W| ≤ ε / 2 := by
        simp only [f]
        rw [integral_homDensityFin_exposedSample F W n]
        calc
          |(∫ G, homDensityFin F G ∂sampleGraph W n) - homDensity F W|
              ≤ (q.choose 2 : ℝ) / n := by
            simpa [q] using abs_integral_homDensityFin_sampleGraph_sub_le F W hVn
          _ ≤ (q : ℝ) ^ 2 / n := by gcongr
          _ ≤ ε / 2 := (div_le_iff₀ hnR).2 (by nlinarith [hn])
      rw [← map_exposedSample W n,
        map_measureReal_apply (measurable_exposedSample W) MeasurableSet.of_discrete]
      have hincl : exposedSample W ⁻¹'
          {G | ε ≤ |homDensityFin F G - homDensity F W|} ⊆
          {x | ε / 2 ≤ f x - ∫ y, f y ∂exposureMeasure μ n} ∪
            {x | ε / 2 ≤ -(f x - ∫ y, f y ∂exposureMeasure μ n)} := by
        intro x hx
        rw [Set.mem_preimage, Set.mem_ofPred_eq] at hx
        have hcenter : ε / 2 ≤ |f x - ∫ y, f y ∂exposureMeasure μ n| := by
          have htri : |f x - homDensity F W| ≤
              |f x - ∫ y, f y ∂exposureMeasure μ n| +
                |(∫ y, f y ∂exposureMeasure μ n) - homDensity F W| :=
            abs_sub_le _ _ _
          have hx' : ε ≤ |f x - homDensity F W| := by simpa only [f] using hx
          linarith [abs_nonneg (f x - ∫ y, f y ∂exposureMeasure μ n)]
        rcases le_abs.mp hcenter with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc
        (exposureMeasure μ n).real
            (exposedSample W ⁻¹' {G | ε ≤ |homDensityFin F G - homDensity F W|})
            ≤ (exposureMeasure μ n).real
                ({x | ε / 2 ≤ f x - ∫ y, f y ∂exposureMeasure μ n} ∪
                  {x | ε / 2 ≤ -(f x - ∫ y, f y ∂exposureMeasure μ n)}) :=
          measureReal_mono hincl
        _ ≤ (exposureMeasure μ n).real
              {x | ε / 2 ≤ f x - ∫ y, f y ∂exposureMeasure μ n} +
            (exposureMeasure μ n).real
              {x | ε / 2 ≤ -(f x - ∫ y, f y ∂exposureMeasure μ n)} :=
          measureReal_union_le _ _
        _ ≤ Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) +
              Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) :=
          add_le_add htail₁ htail₂
        _ = 2 * Real.exp (-(ε ^ 2 * (n : ℝ)) / (2 * (q : ℝ) ^ 2)) := by
          rw [hexp]
          ring
        _ = 2 * Real.exp (-(ε ^ 2 * (n : ℝ)) /
            (2 * (Fintype.card V : ℝ) ^ 2)) := by simp only [q]
    · have hset : {G : SimpleGraph (Fin n) |
          ε ≤ |homDensityFin F G - homDensity F W|} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun G hG => ?_
        rw [Set.mem_ofPred_eq] at hG
        have hdiff : |homDensityFin F G - homDensity F W| ≤ 1 := by
          rw [abs_le]
          constructor <;>
            linarith [homDensityFin_nonneg F G, homDensityFin_le_one F G,
              homDensity_nonneg F W, homDensity_le_one F W]
        exact (not_le.mpr (lt_of_not_ge hε1)) (hG.trans hdiff)
      rw [hset, measureReal_empty]
      positivity

/-- For a fixed finite graph `F` and graphon `W`, the probabilities that the homomorphism density
of `G(n, W)` differs from `t(F, W)` by at least a fixed positive `ε` are summable in `n`.

This is the summability bridge from `sampleGraph_homDensityFin_concentration` to the first
Borel--Cantelli lemma. Sampling at `n + 1` vertices avoids the degenerate zero-vertex host. -/
theorem tsum_sampleGraph_homDensityFin_tail_ne_top {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, (sampleGraph W (n + 1))
      {G | ε ≤ |homDensityFin F G - homDensity F W|}) ≠ ⊤ := by
  let q := Fintype.card V
  let p : ℕ → ℝ≥0∞ := fun n => (sampleGraph W (n + 1))
    {G | ε ≤ |homDensityFin F G - homDensity F W|}
  change (∑' n, p n) ≠ ⊤
  rcases Nat.eq_zero_or_pos q with hq | hq
  · let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp hq
    have hF : F = ⊥ := Subsingleton.elim _ _
    subst F
    have hgraphon : homDensity (⊥ : SimpleGraph V) W = 1 := by
      rw [homDensity_def]
      calc
        _ = ∫ _ : V → Ω, (1 : ℝ) ∂Measure.pi fun _ : V => μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact Finset.prod_eq_one fun _ he => by simp at he
        _ = 1 := by simp
    have hfinite : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
        homDensityFin (⊥ : SimpleGraph V) G = 1 := by
      intro n G
      rw [homDensityFin_def]
      simp
    have hp : p = 0 := by
      funext n
      simp only [p, Pi.zero_apply]
      have hset : {G : SimpleGraph (Fin (n + 1)) |
          ε ≤ |homDensityFin (⊥ : SimpleGraph V) G - homDensity (⊥ : SimpleGraph V) W|} = ∅ := by
        ext G
        simp [hfinite n G, hgraphon, hε]
      simp [hset]
    simp [hp]
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    let c : ℝ := -(ε ^ 2) / (2 * (q : ℝ) ^ 2)
    have hc : c < 0 := by
      dsimp [c]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hε)) (by positivity)
    have hgeom : Summable (fun n : ℕ => 2 * Real.exp ((n : ℝ) * c)) :=
      (Real.summable_exp_nat_mul_iff.mpr hc).mul_left 2
    have hside : ∀ᶠ n : ℕ in Filter.atTop,
        2 * (q : ℝ) ^ 2 ≤ ε * (n + 1) := by
      have htendsto : Filter.Tendsto (fun n : ℕ => ε * ((n : ℝ) + 1))
          Filter.atTop Filter.atTop :=
        (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop).const_mul_atTop hε
      simpa only [Nat.cast_add, Nat.cast_one] using
        htendsto.eventually (Filter.eventually_ge_atTop (2 * (q : ℝ) ^ 2))
    have hbound : ∀ᶠ n : ℕ in Filter.atTop,
        ‖(p n).toReal‖ ≤ 2 * Real.exp ((n : ℝ) * c) := by
      filter_upwards [hside] with n hn
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      calc
        (p n).toReal ≤
            2 * Real.exp (-(ε ^ 2 * (n + 1 : ℕ)) / (2 * (q : ℝ) ^ 2)) := by
          simpa only [p, q] using
            sampleGraph_homDensityFin_concentration (n := n + 1) F W hε
              (by simpa only [q, Nat.cast_add, Nat.cast_one] using hn)
        _ ≤ 2 * Real.exp ((n : ℝ) * c) := by
          gcongr
          rw [Nat.cast_add, Nat.cast_one]
          rw [show -(ε ^ 2 * ((n : ℝ) + 1)) / (2 * (q : ℝ) ^ 2) =
              ((n : ℝ) + 1) * c by
            simp only [c]
            field_simp]
          exact mul_le_mul_of_nonpos_right (by norm_num) hc.le
    have hsum : Summable fun n => (p n).toReal :=
      hgeom.of_norm_bounded_eventually_nat hbound
    have hp_ne_top (n : ℕ) : p n ≠ ⊤ := by
      exact (measure_lt_top (sampleGraph W (n + 1)) _).ne
    have hp_eq : p = fun n => ENNReal.ofReal (p n).toReal := by
      funext n
      exact (ENNReal.ofReal_toReal (hp_ne_top n)).symm
    rw [hp_eq]
    exact hsum.tsum_ofReal_ne_top

end DenseGraphLimits

end TauCeti
