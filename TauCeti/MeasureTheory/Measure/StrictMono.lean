/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.StrictMono
public import TauCeti.Order.Interval.SeparatedBox
public import Mathlib.MeasureTheory.Constructions.Pi
import TauCeti.Algebra.BigOperators.Fin

/-!
# Measure extensionality on the strictly increasing positive chamber

A measure on `Fin n → ℝ≥0` concentrated on strictly increasing tuples with positive coordinates
is determined by its values on separated left-open, right-closed boxes `∏ᵢ (aᵢ, bᵢ]` satisfying
`aᵢ ≤ bᵢ` for all `i` and `bᵢ ≤ aⱼ` whenever `i < j`, provided the first measure is locally
finite (or, more generally, finite on all separated boxes).

Separated boxes form a π-system on the strictly increasing positive chamber, and their rational
subfamily countably covers the chamber and generates its subtype Borel σ-algebra. This avoids
multivariate coordinate changes when comparing ordered arrival-time laws with order-statistic or
renewal partial-sum laws. Moreover, cumulative sums of independent `ℝ≥0`-valued variables with
σ-finite almost-everywhere positive marginals concentrate on this chamber
(`MeasureTheory.Measure.ae_pos_and_strictMono_map_sum_Iic_pi`).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

private abbrev PosStrictMono (n : ℕ) : Set (Fin n → ℝ≥0) :=
  {s | (∀ i, 0 < s i) ∧ StrictMono s}

private def separatedBoxSystem (n : ℕ) : Set (Set ↥(PosStrictMono n)) :=
  {A | ∃ a b : Fin n → ℝ≥0, IsSeparatedBox a b ∧
    A = ((↑) : ↥(PosStrictMono n) → Fin n → ℝ≥0) ⁻¹' (univ.pi fun i => Ioc (a i) (b i))}

private def ratSeparatedBox (n : ℕ) (p : (Fin n → ℚ) × (Fin n → ℚ)) :
    Set ↥(PosStrictMono n) :=
  ((↑) : ↥(PosStrictMono n) → Fin n → ℝ≥0) ⁻¹'
    (univ.pi fun i => Ioc (Real.toNNReal (p.1 i)) (Real.toNNReal (p.2 i)))

private theorem isPiSystem_separatedBoxSystem (n : ℕ) :
    IsPiSystem (separatedBoxSystem n) := by
  let coeΔ : ↥(PosStrictMono n) → Fin n → ℝ≥0 := Subtype.val
  rintro _ ⟨a₁, b₁, h₁, rfl⟩ _ ⟨a₂, b₂, -, rfl⟩ hne
  let a : Fin n → ℝ≥0 := fun i => max (a₁ i) (a₂ i)
  let b : Fin n → ℝ≥0 := fun i => min (b₁ i) (b₂ i)
  have hinter : (coeΔ ⁻¹' (univ.pi fun i => Ioc (a₁ i) (b₁ i))) ∩
      (coeΔ ⁻¹' (univ.pi fun i => Ioc (a₂ i) (b₂ i))) =
      coeΔ ⁻¹' (univ.pi fun i => Ioc (a i) (b i)) := by
    ext x
    simp only [coeΔ, a, b, mem_inter_iff, mem_preimage, mem_univ_pi, mem_Ioc, max_lt_iff,
      le_min_iff]
    exact ⟨fun ⟨hx₁, hx₂⟩ i => ⟨⟨(hx₁ i).1, (hx₂ i).1⟩, (hx₁ i).2, (hx₂ i).2⟩,
      fun hx => ⟨fun i => ⟨(hx i).1.1, (hx i).2.1⟩, fun i => ⟨(hx i).1.2, (hx i).2.2⟩⟩⟩
  rw [hinter] at hne ⊢
  obtain ⟨x, hx⟩ := hne
  refine ⟨a, b, IsSeparatedBox.mk (fun i => ?_) (fun i j hij => ?_), rfl⟩
  · have hxi : x.val i ∈ Ioc (a i) (b i) := hx i (mem_univ i)
    exact hxi.1.le.trans hxi.2
  · exact (min_le_left _ _).trans ((h₁.le_of_lt hij).trans (le_max_left _ _))

private theorem exists_rat_separatedBox_mem {n : ℕ} (x : ↥(PosStrictMono n))
    (L : Fin n → ℝ≥0) (hL : ∀ i, L i < x.val i) :
    ∃ qa qb : Fin n → ℚ,
      IsSeparatedBox (fun i => Real.toNNReal (qa i)) (fun i => Real.toNNReal (qb i)) ∧
      (∀ i, L i ≤ Real.toNNReal (qa i)) ∧
      x ∈ ratSeparatedBox n (qa, qb) := by
  have hxpos := x.property.1
  have hxmono := x.property.2
  let low : Fin n → ℝ := fun i =>
    max (L i : ℝ)
      (if h : 0 < (i : ℕ) then ((x.val ⟨(i : ℕ) - 1, by omega⟩ : ℝ) + x.val i) / 2 else 0)
  let high : Fin n → ℝ := fun i =>
    if h : (i : ℕ) + 1 < n then ((x.val i : ℝ) + x.val ⟨(i : ℕ) + 1, h⟩) / 2 else (x.val i : ℝ) + 1
  have hlow_nonneg (i : Fin n) : 0 ≤ low i := (L i).coe_nonneg.trans (le_max_left _ _)
  have hlow_lt (i : Fin n) : low i < x.val i := by
    refine max_lt (by exact_mod_cast hL i) ?_
    split_ifs with h
    · have hidx : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) < i := Fin.mk_lt_mk.mpr (by omega)
      have hlt : (x.val ⟨(i : ℕ) - 1, by omega⟩ : ℝ) < x.val i := by exact_mod_cast hxmono hidx
      linarith
    · exact_mod_cast hxpos i
  have hhigh_gt (i : Fin n) : (x.val i : ℝ) < high i := by
    dsimp only [high]
    split_ifs with h
    · have hidx : i < (⟨(i : ℕ) + 1, h⟩ : Fin n) := Fin.mk_lt_mk.mpr (by omega)
      have hlt : (x.val i : ℝ) < x.val ⟨(i : ℕ) + 1, h⟩ := by exact_mod_cast hxmono hidx
      linarith
    · linarith
  choose qa hqa_low hqa_lt using fun i => exists_rat_btwn (hlow_lt i)
  choose qb hqb_gt hqb_high using fun i => exists_rat_btwn (hhigh_gt i)
  have hqa_nonneg (i : Fin n) : 0 ≤ (qa i : ℝ) := (hlow_nonneg i).trans (hqa_low i).le
  have hqb_nonneg (i : Fin n) : 0 ≤ (qb i : ℝ) :=
    (x.val i).coe_nonneg.trans (hqb_gt i).le
  refine ⟨qa, qb, IsSeparatedBox.mk (fun i => ?_) (fun i j hij => ?_),
    fun i => ?_, fun i _ => ⟨?_, ?_⟩⟩
  · exact Real.toNNReal_mono ((hqa_lt i).trans (hqb_gt i)).le
  · have hi : (i : ℕ) + 1 < n := by omega
    have hj : 0 < (j : ℕ) := by omega
    have hidx1 : i ≤ (⟨(j : ℕ) - 1, by omega⟩ : Fin n) := Fin.mk_le_mk.mpr (by omega)
    have hidx2 : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≤ j := Fin.mk_le_mk.mpr (by omega)
    have h1 : (x.val i : ℝ) ≤ x.val ⟨(j : ℕ) - 1, by omega⟩ := by
      exact_mod_cast hxmono.monotone hidx1
    have h2 : (x.val ⟨(i : ℕ) + 1, hi⟩ : ℝ) ≤ x.val j := by
      exact_mod_cast hxmono.monotone hidx2
    have hmid : high i ≤ low j := by
      have hmid' : high i ≤ ((x.val ⟨(j : ℕ) - 1, by omega⟩ : ℝ) + x.val j) / 2 := by
        simp only [high, hi, ↓reduceDIte]
        linarith
      exact hmid'.trans (by simp only [low, hj, ↓reduceDIte]; exact le_max_right _ _)
    exact (Real.toNNReal_le_toNNReal_iff (hqa_nonneg j)).2
      (((hqb_high i).le.trans hmid).trans (hqa_low j).le)
  · exact (Real.le_toNNReal_iff_coe_le (hqa_nonneg i)).2
      ((le_max_left _ _).trans (hqa_low i).le)
  · simpa [Real.toNNReal_coe] using
      (Real.toNNReal_lt_toNNReal_iff (by exact_mod_cast hxpos i)).2 (hqa_lt i)
  · exact (Real.le_toNNReal_iff_coe_le (hqb_nonneg i)).2 (hqb_gt i).le

private theorem generateFrom_separatedBoxSystem (n : ℕ) :
    (inferInstance : MeasurableSpace ↥(PosStrictMono n)) =
      MeasurableSpace.generateFrom (separatedBoxSystem n) := by
  apply le_antisymm
  · rw [Subtype.instMeasurableSpace, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i₀ => ?_
    rw [MeasurableSpace.comap_comp]
    let : MeasurableSpace ↥(PosStrictMono n) :=
      MeasurableSpace.generateFrom (separatedBoxSystem n)
    apply Measurable.comap_le (f := fun x : ↥(PosStrictMono n) => x.val i₀)
    refine measurable_of_Ioi fun t => ?_
    let P_rat : Set ((Fin n → ℚ) × (Fin n → ℚ)) :=
      {p | IsSeparatedBox (fun i => Real.toNNReal (p.1 i)) (fun i => Real.toNNReal (p.2 i)) ∧
        t ≤ Real.toNNReal (p.1 i₀)}
    have heq : {x : ↥(PosStrictMono n) | t < x.val i₀} =
        ⋃ p : P_rat, ratSeparatedBox n p.val := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, Subtype.exists]
      constructor
      · intro htx
        classical
        let L : Fin n → ℝ≥0 := Function.update 0 i₀ t
        have hL (i : Fin n) : L i < x.val i := by
          by_cases hi : i = i₀
          · subst hi; simpa [L] using htx
          · simpa [L, hi] using x.property.1 i
        obtain ⟨qa, qb, hsep, hqa, hx⟩ := exists_rat_separatedBox_mem x L hL
        exact ⟨(qa, qb), ⟨hsep, by simpa [L] using hqa i₀⟩, hx⟩
      · rintro ⟨⟨qa, qb⟩, ⟨_, htqa⟩, hx⟩
        exact htqa.trans_lt (hx i₀ (mem_univ i₀)).1
    rw [Ioi, preimage_ofPred_eq, heq]
    exact MeasurableSet.iUnion fun p =>
      MeasurableSpace.measurableSet_generateFrom ⟨_, _, p.property.1, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨a, b, _, rfl⟩
    exact measurable_subtypeVal (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

/-- Two measures concentrated on the strictly increasing positive chamber of `Fin n → ℝ≥0`
are equal if the first is finite on all separated boxes and they agree on all separated
left-open, right-closed boxes. No finiteness assumption on the second measure is required. -/
theorem ext_of_Ioc_strictMono' {n : ℕ} {μ ν : Measure (Fin n → ℝ≥0)}
    (hμ : ∀ᵐ s ∂μ, (∀ i, 0 < s i) ∧ StrictMono s)
    (hν : ∀ᵐ s ∂ν, (∀ i, 0 < s i) ∧ StrictMono s)
    (hfin : ∀ a b : Fin n → ℝ≥0, IsSeparatedBox a b →
      μ (univ.pi fun i => Ioc (a i) (b i)) ≠ ∞)
    (hbox : ∀ a b : Fin n → ℝ≥0, IsSeparatedBox a b →
      μ (univ.pi fun i => Ioc (a i) (b i)) = ν (univ.pi fun i => Ioc (a i) (b i))) :
    μ = ν := by
  let coeΔ : ↥(PosStrictMono n) → Fin n → ℝ≥0 := Subtype.val
  have hΔ : MeasurableSet (PosStrictMono n) := measurableSet_setOf_pos_and_strictMono n
  have he : MeasurableEmbedding coeΔ := MeasurableEmbedding.subtypeVal hΔ
  have hμ_eq : (μ.comap coeΔ).map coeΔ = μ := by
    rw [he.map_comap, Subtype.range_coe, Measure.restrict_eq_self_of_ae_mem hμ]
  have hν_eq : (ν.comap coeΔ).map coeΔ = ν := by
    rw [he.map_comap, Subtype.range_coe, Measure.restrict_eq_self_of_ae_mem hν]
  rw [← hμ_eq, ← hν_eq]
  congr 1
  let Q : Set ((Fin n → ℚ) × (Fin n → ℚ)) :=
    {p | IsSeparatedBox (fun i => Real.toNNReal (p.1 i)) (fun i => Real.toNNReal (p.2 i))}
  let T : Set (Set ↥(PosStrictMono n)) := ratSeparatedBox n '' Q
  apply ext_of_generateFrom_of_cover_subset (S := separatedBoxSystem n) (T := T)
    (generateFrom_separatedBoxSystem n) (isPiSystem_separatedBoxSystem n)
  · rintro _ ⟨⟨qa, qb⟩, hp, rfl⟩
    exact ⟨_, _, hp, rfl⟩
  · exact (to_countable Q).image _
  · rw [sUnion_eq_univ_iff]
    intro x
    obtain ⟨qa, qb, hsep, _, hx⟩ := exists_rat_separatedBox_mem x 0 fun i => x.property.1 i
    exact ⟨ratSeparatedBox n (qa, qb), ⟨(qa, qb), hsep, rfl⟩, hx⟩
  · rintro A ⟨⟨qa, qb⟩, hp, rfl⟩
    rw [he.comap_apply]
    dsimp only [ratSeparatedBox]
    rw [Subtype.image_preimage_coe]
    exact ne_top_of_le_ne_top (hfin _ _ hp) (measure_mono inter_subset_right)
  · rintro _ ⟨a, b, hsep, rfl⟩
    have hB : MeasurableSet (univ.pi fun i => Ioc (a i) (b i)) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    rw [he.comap_apply, Subtype.image_preimage_coe, inter_comm, ← Measure.restrict_apply hB,
      Measure.restrict_eq_self_of_ae_mem hμ,
      he.comap_apply, Subtype.image_preimage_coe, inter_comm, ← Measure.restrict_apply hB,
      Measure.restrict_eq_self_of_ae_mem hν]
    exact hbox a b hsep

/-- Two measures concentrated on the strictly increasing positive chamber of `Fin n → ℝ≥0`
are equal if the first is locally finite and they agree on all separated left-open,
right-closed boxes. No finiteness assumption on the second measure is required. -/
theorem ext_of_Ioc_strictMono {n : ℕ} {μ ν : Measure (Fin n → ℝ≥0)} [IsLocallyFiniteMeasure μ]
    (hμ : ∀ᵐ s ∂μ, (∀ i, 0 < s i) ∧ StrictMono s)
    (hν : ∀ᵐ s ∂ν, (∀ i, 0 < s i) ∧ StrictMono s)
    (hbox : ∀ a b : Fin n → ℝ≥0, IsSeparatedBox a b →
      μ (univ.pi fun i => Ioc (a i) (b i)) = ν (univ.pi fun i => Ioc (a i) (b i))) :
    μ = ν :=
  ext_of_Ioc_strictMono' hμ hν (fun a b _ => by
    have hsub : (univ.pi fun i => Ioc (a i) (b i)) ⊆ Icc a b :=
      fun x hx => ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2⟩
    exact ((measure_mono hsub).trans_lt measure_Icc_lt_top).ne) hbox

/-- Cumulative sums of `m` independent `ℝ≥0`-valued variables with σ-finite marginals concentrated
on `(0, ∞)` are almost surely strictly positive and strictly increasing. -/
theorem ae_pos_and_strictMono_map_sum_Iic_pi {m : ℕ} (ν : Fin m → Measure ℝ≥0)
    [∀ i, SigmaFinite (ν i)] (hν : ∀ i, ∀ᵐ x ∂ν i, 0 < x) :
    ∀ᵐ s ∂((Measure.pi ν).map fun x i => ∑ j ∈ Finset.Iic i, x j),
      (∀ i, 0 < s i) ∧ StrictMono s := by
  have hsum : Measurable (fun (x : Fin m → ℝ≥0) (i : Fin m) => ∑ j ∈ Finset.Iic i, x j) :=
    measurable_pi_iff.mpr fun i => Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  rw [ae_map_iff hsum.aemeasurable (measurableSet_setOf_pos_and_strictMono m)]
  have hae_coord : ∀ᵐ x ∂Measure.pi ν, ∀ i, 0 < x i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval ν i).ae (hν i)
  filter_upwards [hae_coord] with x hx
  have hsm := Fin.strictMono_partialSum hx
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← Fin.partialSum_succ_eq_sum_Iic, ← Fin.partialSum_zero x]
    exact hsm (Fin.succ_pos i)
  · dsimp only
    rw [← Fin.partialSum_succ_eq_sum_Iic, ← Fin.partialSum_succ_eq_sum_Iic]
    exact hsm (Fin.succ_lt_succ_iff.mpr hij)

end MeasureTheory.Measure
