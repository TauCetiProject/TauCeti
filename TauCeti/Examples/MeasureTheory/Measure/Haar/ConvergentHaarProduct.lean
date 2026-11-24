/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct
public import TauCeti.MeasureTheory.Measure.Count.Topology
public import Mathlib.Topology.Instances.ZMod

/-!
# Examples for convergent restricted products of local Haar measures

Checks for `TauCeti.convergentHaarProduct`, the convergent restricted product of local Haar
measures `μ i` on `Πʳ i, [G i, B i]` with exceptional set `S`:

* when every tail mass `μ i (B i)` is `1`, it is `restrictedHaar`, and the integral box has mass
  `∏ i ∈ S, μ i (B i)`; for one copy of `C₄ = ZMod 4` with counting measure, `B = {0, 2}` and `S`
  the whole index set, the integral box has mass `2`;
* the `SL_2` tail factors `1 - q_v⁻²` have a positive infinite product, strictly less than `1`
  when the tail is nonempty;
* rescaling the local measure at one index by `c ≠ 0` rescales the product by `c`;
* a single tail factor of mass `2` is normalized to `2⁻¹ • μ`, while the product keeps the
  compensating factor `2`;
* on one copy of `C₄` with counting measure, changing the restricting subgroup from `C₄` to `{0}`
  transports a measure of total mass `4` to one of total mass `4`, and on two copies the total
  mass is `16`.
-/

public section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct Set TauCeti
open scoped ENNReal NNReal RestrictedProduct

section General

variable {ι : Type*} [Countable ι]
  {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]
  (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
  (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
  (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
  (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (B i.val)).toReal - 1|)

-- When every tail mass is `1`, the convergent product is the restricted product `∏ʳ μ i`.
example (hμB : ∀ i ∉ S, μ i (B i) = 1) :
    convergentHaarProduct B S hBcompact μ hconv =
      restrictedHaar B μ (Filter.Eventually.mono S.finite_toSet.compl_mem_cofinite fun i hi ↦
        hμB i (Finset.mem_coe.not.mp hi)) :=
  convergentHaarProduct_eq_restrictedHaar ..

-- When every tail mass is `1`, the integral box has mass `∏ i ∈ S, μ i (B i)`.
example (hμB : ∀ i ∉ S, μ i (B i) = 1) :
    convergentHaarProduct B S hBcompact μ hconv (box fun i ↦ (B i : Set (G i))) =
      ∏ i ∈ S, μ i (B i) := by
  rw [convergentHaarProduct_box B S hBcompact μ hconv subset_rfl fun _ _ ↦ rfl]
  simp [fun i : {i // i ∉ S} ↦ hμB i.val i.property]

-- Rescaling the local Haar measure at one index `j` by `c ≠ 0` rescales the convergent product
-- by `c`, whether or not `j` is exceptional.
example [DecidableEq ι] (j : ι) (c : ℝ≥0) (hc : c ≠ 0)
    (hconv' : Summable fun i : {i // i ∉ S} ↦
      |(Function.update μ j (c • μ j) i.val (B i.val)).toReal - 1|) :
    have : ∀ i, (Function.update μ j (c • μ j) i).IsHaarMeasure := fun i ↦ by
      rcases eq_or_ne i j with rfl | hi
      · simpa using IsHaarMeasure.nnreal_smul (μ i) hc
      · simpa [hi] using inferInstanceAs (μ i).IsHaarMeasure
    convergentHaarProduct B S hBcompact (Function.update μ j (c • μ j)) hconv' =
      c • convergentHaarProduct B S hBcompact μ hconv := by
  intro _
  exact convergentHaarProduct_eq_smul_of_eq_smul B S hBcompact μ _ hconv hconv'
    (Function.update_self ..) fun _ hi ↦ Function.update_of_ne hi ..

end General

-- The `SL_2` tail factors `1 - q_v⁻²`, for `q_v > 1` with `∑ q_v⁻² < ∞`, have a positive
-- infinite product.
example {ι : Type*} (q : ι → ℝ) (hq : ∀ v, 1 < q v) (hsum : Summable fun v ↦ (q v ^ 2)⁻¹) :
    0 < ∏' v, (1 - (q v ^ 2)⁻¹) := by
  refine tprod_pos_of_summable_abs_sub_one (fun v ↦ ?_) (by simpa using hsum.abs)
  have : (q v ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (hq v) two_ne_zero)
  linarith

-- The product of the `SL_2` tail factors is strictly less than `1` when the tail is nonempty.
example {ι : Type*} (q : ι → ℝ) (hq : ∀ v, 1 < q v) (hsum : Summable fun v ↦ (q v ^ 2)⁻¹)
    (v₀ : ι) : ∏' v, (1 - (q v ^ 2)⁻¹) < 1 := by
  have hlt (v : ι) : (q v ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (hq v) two_ne_zero)
  have hpos (v : ι) : 0 < (q v ^ 2)⁻¹ := inv_pos.2 (pow_pos (zero_lt_one.trans (hq v)) 2)
  have hconv : Summable fun v ↦ |1 - (q v ^ 2)⁻¹ - 1| := by simpa using hsum.abs
  rw [tprod_eq_rexp_tsum_log_of_summable_abs_sub_one (fun v ↦ by linarith [hlt v]) hconv,
    Real.exp_lt_one_iff, ← neg_pos, ← tsum_neg]
  refine (summable_log_of_summable_abs_sub_one hconv).neg.tsum_pos (fun v ↦ ?_) v₀ ?_
  · exact neg_nonneg.2 (Real.log_nonpos (by linarith [hlt v]) (by linarith [hpos v]))
  · exact neg_pos.2 (Real.log_neg (by linarith [hlt v₀]) (by linarith [hpos v₀]))

namespace TauCeti.ConvergentHaarProductExamples

/-! ### Counting measure on `C₄ = ZMod 4` -/

/-- The subgroup `2ℤ/4 = {0, 2}` of `ZMod 4`. -/
local notation "twoZMod4" => AddSubgroup.zmultiples (2 : ZMod 4)

/-- `2ℤ/4 = {0, 2}` has counting measure `2`. -/
lemma count_zmultiples_two : count (twoZMod4 : Set (ZMod 4)) = 2 := by
  have h : addOrderOf (2 : ZMod 4) = 2 := by
    simpa using ZMod.addOrderOf_coe (n := 4) 2 four_ne_zero
  rw [count_apply .of_discrete, ← ENat.card_coe_set_eq]
  simp [← Nat.card_eq_fintype_card, h]

/-- Every index outside `Finset.univ` satisfies any predicate, since there is no such index. -/
lemma forall_notMem_univ {ι : Type*} [Fintype ι] {p : ι → Prop} :
    ∀ i ∉ (Finset.univ : Finset ι), p i :=
  fun i hi ↦ absurd (Finset.mem_univ i) hi

/-- No index lies outside `Finset.univ`. -/
local instance isEmpty_notMem_univ {ι : Type*} [Fintype ι] :
    IsEmpty {i // i ∉ (Finset.univ : Finset ι)} :=
  ⟨fun i ↦ i.property (Finset.mem_univ _)⟩


/-- Every subset of `ZMod 4` is open. -/
local instance factIsOpenZModFour {ι : Type} (U : ι → AddSubgroup (ZMod 4)) :
    Fact (∀ i, IsOpen (U i : Set (ZMod 4))) :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- With the whole finite index set as exceptional set, the convergent product of counting
measures on copies of `ZMod 4` gives the restricted product total mass `4 ^ card ι`, for any
family of restricting subgroups. -/
lemma convergentAddHaarProduct_count_univ {ι : Type} [Fintype ι]
    (U : ι → AddSubgroup (ZMod 4)) :
    convergentAddHaarProduct U Finset.univ forall_notMem_univ
      (fun _ ↦ count) (.of_finite) univ = 4 ^ Fintype.card ι := by
  have hbox : (univ : Set (Πʳ i, [ZMod 4, (U i : Set (ZMod 4))])) =
      box fun _ ↦ (univ : Set (ZMod 4)) := by
    ext x
    simp
  rw [hbox, convergentAddHaarProduct_box _ _ _ _ _ subset_rfl forall_notMem_univ]
  simp [count_univ]

-- One copy of `C₄` with counting measure, `B = {0, 2}` and the whole index set exceptional: the
-- tail is empty and the integral box has mass `2`.
example : convergentAddHaarProduct (fun _ : Unit ↦ twoZMod4) Finset.univ
      forall_notMem_univ (fun _ ↦ count) (.of_finite)
      (box fun _ ↦ (twoZMod4 : Set (ZMod 4))) = 2 := by
  rw [convergentAddHaarProduct_box _ _ _ _ _ subset_rfl forall_notMem_univ]
  simp [count_zmultiples_two]

/-- `{0, 2}` has mass `1` for half counting measure. -/
lemma half_count_zmultiples_two :
    ((2 : ℝ≥0)⁻¹ • (count : Measure (ZMod 4))) (twoZMod4 : Set (ZMod 4)) = 1 := by
  rw [coe_nnreal_smul_apply, count_zmultiples_two, ENNReal.coe_inv two_ne_zero]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Half counting measure is a Haar measure on `ZMod 4`. -/
local instance isAddHaarMeasure_half_count_zmodFour :
    IsAddHaarMeasure ((2 : ℝ≥0)⁻¹ • (count : Measure (ZMod 4))) :=
  IsAddHaarMeasure.nnreal_smul _ (by norm_num)

-- A tail factor of mass `2`: for one copy of `C₄` with counting measure, `B = {0, 2}` and empty
-- exceptional set, the normalized local factor is `2⁻¹ • count`, while the convergent product keeps
-- the compensating global factor `2`.
example : convergentAddHaarProduct (fun _ : Unit ↦ twoZMod4) ∅
      (fun _ _ ↦ (Set.toFinite _).isCompact) (fun _ ↦ count) (.of_finite) =
      (2 : ℝ≥0) • restrictedAddHaar (fun _ : Unit ↦ twoZMod4) (fun _ ↦ (2 : ℝ≥0)⁻¹ • count)
        (.of_forall fun _ ↦ half_count_zmultiples_two) := by
  rw [convergentAddHaarProduct_eq_smul_restrictedAddHaar _ _ _ _ _ (fun _ ↦ (2 : ℝ≥0)⁻¹ • count)
    (fun _ h ↦ absurd h (Finset.notMem_empty _))
    (fun _ _ ↦ by rw [count_zmultiples_two, ENNReal.toNNReal_ofNat])
    (.of_forall fun _ ↦ half_count_zmultiples_two)]
  congr
  rw [tprod_eq_mulSingle ⟨(), Finset.notMem_empty _⟩ fun b hb ↦ absurd (Subsingleton.elim _ _) hb,
    count_zmultiples_two]
  norm_num

-- On one copy of `C₄`, the identity change of restricting subgroup preserves total mass `4`.
example : convergentAddHaarProduct (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 4))) Finset.univ
      forall_notMem_univ (fun _ ↦ count) (.of_finite)
      univ = 4 := by
  simpa using convergentAddHaarProduct_count_univ (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 4)))

-- On one copy of `C₄`, changing the restricting subgroup from `C₄` to `{0}` transports counting
-- measure of total mass `4` to a measure of total mass `4`.
example : ((convergentAddHaarProduct (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 4))) Finset.univ
      forall_notMem_univ (fun _ ↦ count) (.of_finite)).map
      (addRestrictedProductCongr _ (fun _ ↦ ⊥) (by simp))) univ = 4 := by
  rw [map_addRestrictedProductCongr_convergentAddHaarProduct _ _ Finset.univ Finset.univ _ _
    forall_notMem_univ _ _ (.of_finite)]
  simpa using convergentAddHaarProduct_count_univ (fun _ : Unit ↦ (⊥ : AddSubgroup (ZMod 4)))

-- On two copies of `C₄`, changing both restricting subgroups from `C₄` to `{0}` preserves total
-- mass `16`.
example : ((convergentAddHaarProduct (fun _ : Fin 2 ↦ (⊤ : AddSubgroup (ZMod 4))) Finset.univ
      forall_notMem_univ (fun _ ↦ count) (.of_finite)).map
      (addRestrictedProductCongr _ (fun _ ↦ ⊥) (by simp))) univ = 16 := by
  rw [map_addRestrictedProductCongr_convergentAddHaarProduct _ _ Finset.univ Finset.univ _ _
    forall_notMem_univ _ _ (.of_finite)]
  rw [convergentAddHaarProduct_count_univ]
  norm_num

end TauCeti.ConvergentHaarProductExamples
