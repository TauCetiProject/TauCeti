/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct
public import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.InfiniteSum.Group

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
  -- Enlarge the exceptional set to contain `j`; the tails outside it then agree.
  let T₀ := insert j S
  have hBcompact₀ (i : ι) (hi : i ∉ T₀) : IsCompact (B i : Set (G i)) :=
    hBcompact i fun h ↦ hi (Finset.mem_insert_of_mem h)
  have hconv₀ := summable_notMem_of_subset (Finset.subset_insert j S)
    (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
  have hconv₀' := summable_notMem_of_subset (Finset.subset_insert j S)
    (fun i ↦ |(Function.update μ j (c • μ j) i (B i)).toReal - 1|) hconv'
  rw [convergentHaarProduct_eq_of_subset B (Finset.subset_insert j S) hBcompact hBcompact₀ μ
      hconv hconv₀,
    convergentHaarProduct_eq_of_subset B (Finset.subset_insert j S) hBcompact hBcompact₀ _
      hconv' hconv₀']
  have : (c • convergentHaarProduct B T₀ hBcompact₀ μ hconv₀).IsHaarMeasure :=
    IsHaarMeasure.nnreal_smul _ hc
  refine (convergentHaarProduct_unique B T₀ hBcompact₀ _ hconv₀' fun T hT C _ hCB ↦ ?_).symm
  have hjT : j ∈ T := hT (Finset.mem_insert_self j S)
  have htail : (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) =
      ∏' i : {i // i ∉ T}, (Function.update μ j (c • μ j) i.val (B i.val)).toReal :=
    tprod_congr fun i ↦ by
      rw [Function.update_of_ne fun h ↦ i.property (by rw [h]; exact hjT)]
  have hprod : ∏ i ∈ T, Function.update μ j (c • μ j) i (C i) = c * ∏ i ∈ T, μ i (C i) := by
    rw [← Finset.mul_prod_erase T _ hjT, ← Finset.mul_prod_erase T _ hjT, Function.update_self,
      coe_nnreal_smul_apply, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [coe_nnreal_smul_apply, convergentHaarProduct_box B T₀ hBcompact₀ μ hconv₀ hT hCB, htail,
    hprod, mul_assoc]

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

/-- Counting measure is a Haar measure on the finite discrete group `ZMod 4`. -/
local instance isAddHaarMeasure_count_zmodFour : IsAddHaarMeasure (count : Measure (ZMod 4)) where
  lt_top_of_isCompact _ _ := measure_lt_top _ _
  open_pos _ _ hU := count_ne_zero_iff.2 hU

/-- The subgroup `2ℤ/4 = {0, 2}` of `ZMod 4`. -/
local notation "twoZMod4" => AddSubgroup.zmultiples (2 : ZMod 4)

/-- `2ℤ/4 = {0, 2}` has counting measure `2`. -/
lemma count_zmultiples_two : count (twoZMod4 : Set (ZMod 4)) = 2 := by
  rw [count_apply (MeasurableSet.of_discrete), ← Set.Finite.cast_ncard_eq (Set.toFinite _),
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zmultiples,
    show (2 : ZMod 4) = ((2 : ℕ) : ZMod 4) from rfl, ZMod.addOrderOf_coe _ (by norm_num)]
  rfl

/-- Every subset of `ZMod 4` is open. -/
local instance factIsOpenZModFour {ι : Type} (U : ι → AddSubgroup (ZMod 4)) :
    Fact (∀ i, IsOpen (U i : Set (ZMod 4))) :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- With the whole finite index set as exceptional set, the convergent product of counting
measures on copies of `ZMod 4` gives the restricted product total mass `4 ^ card ι`, for any
family of restricting subgroups. -/
lemma convergentAddHaarProduct_count_univ {ι : Type} [Fintype ι]
    (U : ι → AddSubgroup (ZMod 4)) :
    convergentAddHaarProduct U Finset.univ (fun i hi ↦ absurd (Finset.mem_univ i) hi)
      (fun _ ↦ count) (.of_finite) univ = 4 ^ Fintype.card ι := by
  have : IsEmpty {i // i ∉ (Finset.univ : Finset ι)} := ⟨fun i ↦ i.property (Finset.mem_univ _)⟩
  have hbox : (univ : Set (Πʳ i, [ZMod 4, (U i : Set (ZMod 4))])) =
      box fun _ ↦ (univ : Set (ZMod 4)) := by
    ext x
    simp
  rw [hbox, convergentAddHaarProduct_box _ _ _ _ _ subset_rfl fun i hi ↦
    absurd (Finset.mem_univ i) hi]
  simp [count_univ]

-- One copy of `C₄` with counting measure, `B = {0, 2}` and the whole index set exceptional: the
-- tail is empty and the integral box has mass `2`.
example : convergentAddHaarProduct (fun _ : Unit ↦ twoZMod4) Finset.univ
      (fun i hi ↦ absurd (Finset.mem_univ i) hi) (fun _ ↦ count) (.of_finite)
      (box fun _ ↦ (twoZMod4 : Set (ZMod 4))) = 2 := by
  have : IsEmpty {i // i ∉ (Finset.univ : Finset Unit)} := ⟨fun i ↦ i.property (Finset.mem_univ _)⟩
  rw [convergentAddHaarProduct_box _ _ _ _ _ subset_rfl fun i hi ↦
    absurd (Finset.mem_univ i) hi]
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
    (fun _ _ ↦ by rw [count_zmultiples_two]; rfl) (.of_forall fun _ ↦ half_count_zmultiples_two)]
  congr
  rw [tprod_eq_mulSingle ⟨(), Finset.notMem_empty _⟩ fun b hb ↦ absurd (Subsingleton.elim _ _) hb,
    count_zmultiples_two]
  norm_num

-- On one copy of `C₄`, the identity change of restricting subgroup preserves total mass `4`.
example : convergentAddHaarProduct (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 4))) Finset.univ
      (fun i hi ↦ absurd (Finset.mem_univ i) hi) (fun _ ↦ count) (.of_finite)
      univ = 4 := by
  simpa using convergentAddHaarProduct_count_univ (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 4)))

-- On one copy of `C₄`, changing the restricting subgroup from `C₄` to `{0}` transports counting
-- measure of total mass `4` to a measure of total mass `4`.
example : ((convergentAddHaarProduct (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 4))) Finset.univ
      (fun i hi ↦ absurd (Finset.mem_univ i) hi) (fun _ ↦ count) (.of_finite)).map
      (addRestrictedProductCongr _ (fun _ ↦ ⊥) (by
        rw [Filter.cofinite_eq_bot]; exact Filter.eventually_bot))) univ = 4 := by
  rw [map_addRestrictedProductCongr_convergentAddHaarProduct _ _ Finset.univ Finset.univ _ _
    (fun i hi ↦ absurd (Finset.mem_univ i) hi) _ _ (.of_finite)]
  simpa using convergentAddHaarProduct_count_univ (fun _ : Unit ↦ (⊥ : AddSubgroup (ZMod 4)))

-- On two copies of `C₄`, changing both restricting subgroups from `C₄` to `{0}` preserves total
-- mass `16`.
example : ((convergentAddHaarProduct (fun _ : Fin 2 ↦ (⊤ : AddSubgroup (ZMod 4))) Finset.univ
      (fun i hi ↦ absurd (Finset.mem_univ i) hi) (fun _ ↦ count) (.of_finite)).map
      (addRestrictedProductCongr _ (fun _ ↦ ⊥) (by
        rw [Filter.cofinite_eq_bot]; exact Filter.eventually_bot))) univ = 16 := by
  rw [map_addRestrictedProductCongr_convergentAddHaarProduct _ _ Finset.univ Finset.univ _ _
    (fun i hi ↦ absurd (Finset.mem_univ i) hi) _ _ (.of_finite)]
  rw [convergentAddHaarProduct_count_univ]
  norm_num

end TauCeti.ConvergentHaarProductExamples
