/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality.L2
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous

/-!
# Doob's L² inequality in continuous time

The expected squared running maximum of a nonnegative submartingale is at most four
times its terminal second moment. We first allow arbitrary finite sampling sets, then
countable sets, and finally all times up to a horizon for almost surely right-continuous
paths. The martingale form controls the running maximum of the norm.

Only the terminal value needs a second moment. No completeness of the probability
space, right continuity of the filtration, or everywhere path regularity is assumed.
The running maximum is extended-nonnegative-valued, so the bounds also prove its
finiteness almost surely. These estimates control uniform approximation of continuous
stochastic integral processes from elementary integrals. The finite-set estimate reuses
`MeasureTheory.Submartingale.integral_sq_partialSups_le`, the discrete Doob inequality.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, Theorem 3.8.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m} {f : ι → Ω → ℝ}

/-- Doob's L² bound on an arbitrary finite sampling set before a terminal time.
The terminal time need not belong to the sampled set. -/
theorem lintegral_iSup_mem_ofReal_sq_le (hf : Submartingale f ℱ μ)
    (hpos : ∀ t, 0 ≤ᵐ[μ] f t) {T : ι} (hT : MemLp (f T) 2 μ) (F : Finset ι)
    (hF : ∀ t ∈ F, t ≤ T) :
    ∫⁻ ω, ⨆ t ∈ F, ENNReal.ofReal (f t ω) ^ 2 ∂μ ≤
      4 * ENNReal.ofReal (∫ ω, f T ω ^ 2 ∂μ) := by
  classical
  -- Adjoin the terminal time and enumerate the resulting finite set in increasing order.
  let G := insert T F
  have hne : G.Nonempty := ⟨T, Finset.mem_insert_self _ _⟩
  let n := G.card - 1
  have hcard : G.card = n + 1 := (Nat.sub_add_cancel hne.card_pos).symm
  let e := G.orderEmbOfFin hcard
  let τ : ℕ → ι := fun j ↦ e ⟨min j n, by omega⟩
  have hτ : Monotone τ := fun i j hij ↦ e.monotone (Fin.mk_le_mk.2 (min_le_min_right _ hij))
  have hτT : τ n = T := by
    have hlast : τ n = G.max' hne := by
      simpa [τ, e] using Finset.orderEmbOfFin_last hcard (Nat.succ_pos n)
    rw [hlast]
    apply le_antisymm
    · apply Finset.max'_le
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact le_rfl
      · exact hF t ht
    · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  let 𝒢 : Filtration ℕ m := ⟨fun j ↦ ℱ (τ j), fun _ _ hij ↦ ℱ.mono (hτ hij), fun _ ↦ ℱ.le _⟩
  have hg : Submartingale (fun j ↦ f (τ j)) 𝒢 μ :=
    ⟨fun j ↦ hf.stronglyAdapted (τ j), fun _ _ hij ↦ hf.ae_le_condExp (hτ hij),
      fun j ↦ hf.integrable (τ j)⟩
  have hn : MemLp (f (τ n)) 2 μ := by rwa [hτT]
  -- Establish the maximum's second moment before translating the discrete integral bound.
  have hmax : MemLp (partialSups (fun j ↦ f (τ j)) n) 2 μ := by
    rw [partialSups_apply]
    exact Finset.sup'_induction _ _ (p := fun g ↦ MemLp g 2 μ)
      (fun _ ha _ hb ↦ ha.sup hb) (fun j hj ↦
        hg.memLp_of_le (Finset.mem_Iic.1 hj) (hpos _) (by norm_num) hn)
  have hbound := hg.integral_sq_partialSups_le (fun j ↦ hpos _) n hn
  -- Every sampled value is below this discrete maximum; pass its bound to lower integrals.
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (partialSups (fun j ↦ f (τ j)) n ω) ^ 2 ∂μ := by
      apply lintegral_mono
      intro ω
      refine iSup₂_le fun t ht ↦ ?_
      obtain ⟨i, hi⟩ : t ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_insert_of_mem ht
      have hiτ : τ i = t := by simpa [τ, min_eq_left (by omega : (i : ℕ) ≤ n)] using hi
      have hle : f t ω ≤ partialSups (fun j ↦ f (τ j)) n ω := by
        rw [← hiτ]
        exact le_partialSups_of_le (fun j ↦ f (τ j)) (by omega : (i : ℕ) ≤ n) ω
      exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hle) 2
    _ = ∫⁻ ω, ENNReal.ofReal (partialSups (fun j ↦ f (τ j)) n ω ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos (τ n)] with ω hω
      exact (ENNReal.ofReal_pow (hω.trans
        (le_partialSups (fun j ↦ f (τ j)) n ω)) 2).symm
    _ = ENNReal.ofReal (∫ ω, partialSups (fun j ↦ f (τ j)) n ω ^ 2 ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hmax.integrable_sq
        (.of_forall fun _ ↦ sq_nonneg _)).symm
    _ ≤ _ := by
      rw [hτT] at hbound
      simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hbound

/-- Doob's L² bound for a countable set of observation times. -/
theorem lintegral_iSup_ofReal_sq_le_of_countable (hf : Submartingale f ℱ μ)
    (hpos : ∀ t, 0 ≤ᵐ[μ] f t) {T : ι} (hT : MemLp (f T) 2 μ) {S : Set ι} (hS : S.Countable)
    (hST : ∀ t ∈ S, t ≤ T) :
    ∫⁻ ω, ⨆ t ∈ S, ENNReal.ofReal (f t ω) ^ 2 ∂μ ≤
      4 * ENNReal.ofReal (∫ ω, f T ω ^ 2 ∂μ) := by
  classical
  have := hS.to_subtype
  let g (F : Finset S) (ω : Ω) : ℝ≥0∞ := ⨆ t ∈ F, ENNReal.ofReal (f t ω) ^ 2
  have hm (F : Finset S) : Measurable (g F) := by
    exact Measurable.biSup (F : Set S) F.countable_toSet fun t _ ↦
      ((hf.stronglyAdapted t).mono (ℱ.le t)).measurable.ennreal_ofReal.pow_const 2
  have hd : Directed (· ≤ ·) g := fun F G ↦ ⟨F ∪ G,
    fun ω ↦ iSup₂_le fun t ht ↦ le_iSup₂_of_le t (Finset.mem_union_left _ ht) le_rfl,
    fun ω ↦ iSup₂_le fun t ht ↦ le_iSup₂_of_le t (Finset.mem_union_right _ ht) le_rfl⟩
  have heq (ω : Ω) : (⨆ t ∈ S, ENNReal.ofReal (f t ω) ^ 2) = ⨆ F, g F ω := by
    simpa only [g, iSup_subtype'] using
      (iSup_eq_iSup_finset (fun t : S ↦ ENNReal.ofReal (f t ω) ^ 2))
  simp_rw [heq]
  rw [lintegral_iSup_directed_of_measurable hm hd]
  refine iSup_le fun F ↦ ?_
  have hb := hf.lintegral_iSup_mem_ofReal_sq_le hpos hT
    (F.map (Function.Embedding.subtype _)) (by
      intro t ht
      obtain ⟨⟨t, htS⟩, _, rfl⟩ := Finset.mem_map.1 ht
      exact hST t htS)
  have heqF (ω : Ω) : (⨆ t ∈ F.map (Function.Embedding.subtype _),
      ENNReal.ofReal (f t ω) ^ 2) = g F ω := by
    simp only [g, ← Finset.sup_eq_iSup, Finset.sup_map, Function.comp_def,
      Function.Embedding.coe_subtype]
  simpa only [heqF] using hb

section ContinuousTime

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- **Doob's L² inequality in continuous time.** The expected squared running maximum of a
nonnegative submartingale with almost surely right-continuous paths is bounded by four times
its terminal second moment. The filtration and ambient measure need not be complete. -/
theorem lintegral_iSup_le_ofReal_sq_le (hf : Submartingale f ℱ μ)
    (hpos : ∀ t, 0 ≤ᵐ[μ] f t) {T : ι} (hT : MemLp (f T) 2 μ)
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (f t ω) ^ 2 ∂μ ≤
      4 * ENNReal.ofReal (∫ ω, f T ω ^ 2 ∂μ) := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ≥0∞) T
  have heq : (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω) ^ 2) =ᵐ[μ]
      (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω) ^ 2) := by
    filter_upwards [hcont] with ω hω
    refine le_antisymm ?_ (iSup₂_le fun s hs ↦ le_iSup₂_of_le s (hST hs) le_rfl)
    refine iSup₂_le fun t ht ↦ le_of_forall_lt fun a ha ↦ ?_
    obtain ⟨s, hs, has⟩ := hS (g := fun u ↦ ENNReal.ofReal (f u ω) ^ 2)
      (fun u hu ↦ ENNReal.Tendsto.pow (ENNReal.tendsto_ofReal (hω u hu))) ht ha
    exact has.trans_le (le_iSup₂_of_le s hs le_rfl)
  rw [lintegral_congr_ae heq]
  exact hf.lintegral_iSup_ofReal_sq_le_of_countable hpos hT hSc (fun _ hs ↦ hST hs)

end ContinuousTime

end MeasureTheory.Submartingale

namespace MeasureTheory.Martingale

variable {Ω ι E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι m} {X : ι → Ω → E} {T : ι}

/-- **Doob's L² inequality for a Banach-valued martingale in continuous time.**
Only the terminal value needs to be square integrable; path right continuity is required
outside one common null set. This bounds uniform path errors by terminal mean-square errors. -/
theorem lintegral_iSup_le_ofReal_norm_sq_le (hX : Martingale X ℱ μ)
    (hT : MemLp (X T) 2 μ)
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal ‖X t ω‖ ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ‖X T ω‖ ^ 2 ∂μ := by
  have hb := hX.norm.lintegral_iSup_le_ofReal_sq_le
    (fun t ↦ .of_forall fun ω ↦ norm_nonneg _) hT.norm
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm)
  rw [ofReal_integral_eq_lintegral_ofReal hT.norm.integrable_sq
    (.of_forall fun _ ↦ sq_nonneg _)] at hb
  simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using hb

/-- Terminal mean-square convergence of right-continuous martingales implies mean-square
convergence of their uniform path errors on a finite horizon. Applied to differences of
approximate stochastic integrals, this is the uniform approximation estimate. -/
theorem tendsto_lintegral_iSup_le_ofReal_norm_sq_zero {κ : Type*} {l : Filter κ}
    {Y : κ → ι → Ω → E} (hY : ∀ k, Martingale (Y k) ℱ μ)
    (hT : ∀ k, MemLp (Y k T) 2 μ)
    (hcont : ∀ k, ∀ᵐ ω ∂μ, ∀ t < T,
      ContinuousWithinAt (fun u ↦ Y k u ω) (Ioi t) t)
    (hlim : Tendsto (fun k ↦ ∫⁻ ω, ENNReal.ofReal ‖Y k T ω‖ ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun k ↦ ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal ‖Y k t ω‖ ^ 2 ∂μ) l (nhds 0) := by
  have hb : Tendsto (fun k ↦ 4 * ∫⁻ ω, ENNReal.ofReal ‖Y k T ω‖ ^ 2 ∂μ) l (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ∞))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ ↦ bot_le) (fun k ↦ (hY k).lintegral_iSup_le_ofReal_norm_sq_le (hT k) (hcont k))

end MeasureTheory.Martingale
