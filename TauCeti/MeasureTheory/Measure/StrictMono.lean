/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.StrictMono
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Measure extensionality on the strictly increasing positive chamber

A measure on `Fin n → ℝ≥0` concentrated on strictly increasing tuples with positive coordinates
is determined by its values on separated half-open boxes `∏ᵢ (aᵢ, bᵢ]` satisfying
`aᵢ ≤ bᵢ` for all `i` and `bᵢ ≤ aⱼ` whenever `i < j`, provided the first measure is finite.

Separated half-open boxes form a π-system on the strictly increasing positive chamber, and
their rational subfamily countably covers the chamber and generates its subtype Borel σ-algebra.
This avoids multivariate coordinate changes when comparing ordered arrival-time laws with
order-statistic or renewal partial-sum laws.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- Half-open box endpoints `a, b : Fin n → ℝ≥0` are separated when each interval is
well-ordered (`a i ≤ b i`) and earlier right endpoints do not exceed later left endpoints. -/
def IsSeparatedBox {n : ℕ} (a b : Fin n → ℝ≥0) : Prop :=
  (∀ i, a i ≤ b i) ∧ ∀ ⦃i j : Fin n⦄, i < j → b i ≤ a j

/-- Explicit characterization of separated half-open box endpoints. -/
theorem isSeparatedBox_iff {n : ℕ} {a b : Fin n → ℝ≥0} :
    IsSeparatedBox a b ↔ (∀ i, a i ≤ b i) ∧ ∀ ⦃i j : Fin n⦄, i < j → b i ≤ a j :=
  (Iff.rfl)

/-- Construct `IsSeparatedBox` from coordinatewise order and strict-index separation. -/
theorem IsSeparatedBox.mk {n : ℕ} {a b : Fin n → ℝ≥0} (hle : ∀ i, a i ≤ b i)
    (hsep : ∀ ⦃i j : Fin n⦄, i < j → b i ≤ a j) : IsSeparatedBox a b :=
  ⟨hle, hsep⟩

/-- Separated box endpoints satisfy `a i ≤ b i` in every coordinate. -/
theorem IsSeparatedBox.le {n : ℕ} {a b : Fin n → ℝ≥0} (h : IsSeparatedBox a b) (i : Fin n) :
    a i ≤ b i :=
  h.1 i

/-- Separated box endpoints place `b i` at or before `a j` whenever `i < j`. -/
theorem IsSeparatedBox.le_of_lt {n : ℕ} {a b : Fin n → ℝ≥0} (h : IsSeparatedBox a b)
    {i j : Fin n} (hij : i < j) : b i ≤ a j :=
  h.2 hij

private abbrev PosStrictMono (n : ℕ) : Set (Fin n → ℝ≥0) :=
  {s | (∀ i, 0 < s i) ∧ StrictMono s}

/-- Strictly increasing `Fin n`-tuples with strictly positive coordinates form a measurable set. -/
theorem measurableSet_setOf_pos_and_strictMono (n : ℕ) :
    MeasurableSet {s : Fin n → ℝ≥0 | (∀ i, 0 < s i) ∧ StrictMono s} := by
  have hpos : MeasurableSet {s : Fin n → ℝ≥0 | ∀ i, 0 < s i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioi
  exact hpos.inter measurableSet_setOf_strictMono

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
  refine ⟨a, b, ⟨fun i => ?_, fun i j hij => ?_⟩, rfl⟩
  · have hxi : x.1 i ∈ Ioc (a i) (b i) := hx i (mem_univ i)
    exact hxi.1.le.trans hxi.2
  · exact (min_le_left _ _).trans ((h₁.le_of_lt hij).trans (le_max_left _ _))

private theorem exists_rat_separatedBox_mem {n : ℕ} (x : ↥(PosStrictMono n))
    (L : Fin n → ℝ≥0) (hL : ∀ i, L i < x.1 i) :
    ∃ qa qb : Fin n → ℚ,
      IsSeparatedBox (fun i => Real.toNNReal (qa i)) (fun i => Real.toNNReal (qb i)) ∧
      (∀ i, L i ≤ Real.toNNReal (qa i)) ∧
      x ∈ ratSeparatedBox n (qa, qb) := by
  have hxpos := x.2.1
  have hxmono := x.2.2
  let low : Fin n → ℝ := fun i =>
    max (L i : ℝ)
      (if h : 0 < (i : ℕ) then ((x.1 ⟨(i : ℕ) - 1, by omega⟩ : ℝ) + x.1 i) / 2 else 0)
  let high : Fin n → ℝ := fun i =>
    if h : (i : ℕ) + 1 < n then ((x.1 i : ℝ) + x.1 ⟨(i : ℕ) + 1, h⟩) / 2 else (x.1 i : ℝ) + 1
  have hlow_nonneg (i : Fin n) : 0 ≤ low i := (L i).coe_nonneg.trans (le_max_left _ _)
  have hlow_lt (i : Fin n) : low i < x.1 i := by
    refine max_lt (by exact_mod_cast hL i) ?_
    split_ifs with h
    · have hidx : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) < i := Fin.mk_lt_mk.mpr (by omega)
      have hlt : (x.1 ⟨(i : ℕ) - 1, by omega⟩ : ℝ) < x.1 i := by exact_mod_cast hxmono hidx
      linarith
    · exact_mod_cast hxpos i
  have hhigh_gt (i : Fin n) : (x.1 i : ℝ) < high i := by
    dsimp only [high]
    split_ifs with h
    · have hidx : i < (⟨(i : ℕ) + 1, h⟩ : Fin n) := Fin.mk_lt_mk.mpr (by omega)
      have hlt : (x.1 i : ℝ) < x.1 ⟨(i : ℕ) + 1, h⟩ := by exact_mod_cast hxmono hidx
      linarith
    · linarith
  choose qa hqa_low hqa_lt using fun i => exists_rat_btwn (hlow_lt i)
  choose qb hqb_gt hqb_high using fun i => exists_rat_btwn (hhigh_gt i)
  have hqa_nonneg (i : Fin n) : 0 ≤ (qa i : ℝ) := (hlow_nonneg i).trans (hqa_low i).le
  have hqb_nonneg (i : Fin n) : 0 ≤ (qb i : ℝ) :=
    (x.1 i).coe_nonneg.trans (hqb_gt i).le
  refine ⟨qa, qb, ⟨fun i => ?_, fun i j hij => ?_⟩, fun i => ?_, fun i _ => ⟨?_, ?_⟩⟩
  · exact Real.toNNReal_mono ((hqa_lt i).trans (hqb_gt i)).le
  · have hi : (i : ℕ) + 1 < n := by omega
    have hj : 0 < (j : ℕ) := by omega
    have hidx1 : i ≤ (⟨(j : ℕ) - 1, by omega⟩ : Fin n) := Fin.mk_le_mk.mpr (by omega)
    have hidx2 : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≤ j := Fin.mk_le_mk.mpr (by omega)
    have h1 : (x.1 i : ℝ) ≤ x.1 ⟨(j : ℕ) - 1, by omega⟩ := by
      exact_mod_cast hxmono.monotone hidx1
    have h2 : (x.1 ⟨(i : ℕ) + 1, hi⟩ : ℝ) ≤ x.1 j := by
      exact_mod_cast hxmono.monotone hidx2
    have hmid : high i ≤ low j := by
      have hmid' : high i ≤ ((x.1 ⟨(j : ℕ) - 1, by omega⟩ : ℝ) + x.1 j) / 2 := by
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
    apply Measurable.comap_le (f := fun x : ↥(PosStrictMono n) => x.1 i₀)
    refine measurable_of_Ioi fun t => ?_
    let P_rat : Set ((Fin n → ℚ) × (Fin n → ℚ)) :=
      {p | IsSeparatedBox (fun i => Real.toNNReal (p.1 i)) (fun i => Real.toNNReal (p.2 i)) ∧
        t ≤ Real.toNNReal (p.1 i₀)}
    have heq : {x : ↥(PosStrictMono n) | t < x.1 i₀} =
        ⋃ p : P_rat, ratSeparatedBox n p.1 := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, Subtype.exists]
      constructor
      · intro htx
        classical
        let L : Fin n → ℝ≥0 := Function.update 0 i₀ t
        have hL (i : Fin n) : L i < x.1 i := by
          by_cases hi : i = i₀
          · subst hi; simpa [L] using htx
          · simpa [L, hi] using x.2.1 i
        obtain ⟨qa, qb, hsep, hqa, hx⟩ := exists_rat_separatedBox_mem x L hL
        exact ⟨(qa, qb), ⟨hsep, by simpa [L] using hqa i₀⟩, hx⟩
      · rintro ⟨⟨qa, qb⟩, ⟨_, htqa⟩, hx⟩
        exact htqa.trans_lt (hx i₀ (mem_univ i₀)).1
    rw [Ioi, preimage_ofPred_eq, heq]
    exact MeasurableSet.iUnion fun p =>
      MeasurableSpace.measurableSet_generateFrom ⟨_, _, p.2.1, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨a, b, _, rfl⟩
    exact measurable_subtype_coe (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

/-- Two measures concentrated on the strictly increasing positive chamber of `Fin n → ℝ≥0`
are equal if the first is finite and they agree on all separated half-open boxes. No
finiteness assumption on the second measure is required. -/
theorem ext_of_Ioc_strictMono {n : ℕ} {μ ν : Measure (Fin n → ℝ≥0)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ s ∂μ, (∀ i, 0 < s i) ∧ StrictMono s)
    (hν : ∀ᵐ s ∂ν, (∀ i, 0 < s i) ∧ StrictMono s)
    (hbox : ∀ a b : Fin n → ℝ≥0, IsSeparatedBox a b →
      μ (univ.pi fun i => Ioc (a i) (b i)) = ν (univ.pi fun i => Ioc (a i) (b i))) :
    μ = ν := by
  let coeΔ : ↥(PosStrictMono n) → Fin n → ℝ≥0 := Subtype.val
  have hΔ : MeasurableSet (PosStrictMono n) := measurableSet_setOf_pos_and_strictMono n
  have he : MeasurableEmbedding coeΔ := MeasurableEmbedding.subtype_coe hΔ
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
    obtain ⟨qa, qb, hsep, _, hx⟩ := exists_rat_separatedBox_mem x 0 fun i => x.2.1 i
    exact ⟨ratSeparatedBox n (qa, qb), ⟨(qa, qb), hsep, rfl⟩, hx⟩
  · rintro A ⟨⟨qa, qb⟩, _, rfl⟩
    rw [he.comap_apply]
    exact ((measure_mono (subset_univ _)).trans_lt (measure_lt_top μ univ)).ne
  · rintro _ ⟨a, b, hsep, rfl⟩
    have hB : MeasurableSet (univ.pi fun i => Ioc (a i) (b i)) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    rw [he.comap_apply, Subtype.image_preimage_coe, inter_comm, ← Measure.restrict_apply hB,
      Measure.restrict_eq_self_of_ae_mem hμ,
      he.comap_apply, Subtype.image_preimage_coe, inter_comm, ← Measure.restrict_apply hB,
      Measure.restrict_eq_self_of_ae_mem hν]
    exact hbox a b hsep

end MeasureTheory.Measure
