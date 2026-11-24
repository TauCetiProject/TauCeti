/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.MilnorJoin.Basic
public import TauCeti.Topology.Homotopy.Extension.Ball
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.Homotopy.Path
import Mathlib.Algebra.BigOperators.Field
import TauCeti.Topology.Homotopy.HomotopyGroup.Basic

/-!
# Weak contractibility of the strong-coordinate Milnor join

Following Milnor (*Construction of universal bundles, II*, §3) and tom Dieck (*Algebraic Topology*,
§14.4.3), we prove weak contractibility of `TauCeti.MilnorTotalSpace G` directly from the strong
coordinate topology: for any map `f : C(X, MilnorTotalSpace G)` with compact image, compactness
selects a uniform cutoff `N` with `1 / 2 < S_N(f x)`, scaling the tail weights (`i ≥ N`) to zero
while renormalizing the retained weights (`i < N`) deforms `f` to `tailTruncationMap`, and linear
interpolation cones it to `vertex N a` at the fresh index.

## Main definitions and results

* `TauCeti.MilnorTotalSpace.partialWeightSum`, `tailTruncationMap`, `tailTruncationHomotopy`,
  `weight_tailTruncationHomotopy`, `label_tailTruncationHomotopy`, `coneAtFreshIndexHomotopy`,
  `weight_coneAtFreshIndexHomotopy`, `label_coneAtFreshIndexHomotopy_self`,
  `label_coneAtFreshIndexHomotopy_of_ne`,
  `exists_one_half_lt_partialWeightSum_of_isCompact_range`.
* `ContinuousMap.nullhomotopic_to_milnorTotalSpace_of_isCompact_range`,
  `ContinuousMap.nullhomotopic_to_milnorTotalSpace`, `HomotopyGroup.subsingleton_milnorTotalSpace`,
  `ContinuousMap.exists_extension_closedBall_milnorTotalSpace`,
  `ContinuousMap.homotopicRel_const_singleton_sphere_milnorTotalSpace`.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. (2) 63 (1956), 430–436, §3.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, §14.4.3.
-/

public section

noncomputable section

open HomotopyGroup Metric Set Topology unitInterval
open scoped Topology.Homotopy

universe u v

namespace TauCeti

namespace MilnorTotalSpace

/-! ### Partial weight sums and compact tail bounds -/

section PartialWeightSum

variable (G : Type u) [TopologicalSpace G]

/-- Continuous partial sum `S_N(p) = ∑_{i < N} t_i(p)` of the first `N` barycentric weights. -/
def partialWeightSum (N : ℕ) : C(MilnorTotalSpace G, ℝ) where
  toFun p := ∑ i ∈ Finset.range N, weight i p
  continuous_toFun := by fun_prop

variable {G}

@[simp] theorem partialWeightSum_apply (N : ℕ) (p : MilnorTotalSpace G) :
    partialWeightSum G N p = ∑ i ∈ Finset.range N, weight i p := (rfl)
theorem partialWeightSum_zero (p : MilnorTotalSpace G) : partialWeightSum G 0 p = 0 := by simp

theorem partialWeightSum_nonneg (N : ℕ) (p : MilnorTotalSpace G) :
    0 ≤ partialWeightSum G N p := by
  rw [partialWeightSum_apply]; exact Finset.sum_nonneg fun i _ ↦ weight_nonneg i p

theorem partialWeightSum_mono {M N : ℕ} (hMN : M ≤ N) (p : MilnorTotalSpace G) :
    partialWeightSum G M p ≤ partialWeightSum G N p := by
  simp_rw [partialWeightSum_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) fun i _ _ ↦ weight_nonneg i p

theorem partialWeightSum_le_one (N : ℕ) (p : MilnorTotalSpace G) :
    partialWeightSum G N p ≤ 1 :=
  sum_le_hasSum (Finset.range N) (fun i _ ↦ weight_nonneg i p) (hasSum_weight p)

theorem exists_partialWeightSum_eq_one (p : MilnorTotalSpace G) :
    ∃ N, partialWeightSum G N p = 1 :=
  let supp := (finite_support_weight p).toFinset
  ⟨supp.sup id + 1, sum_weight_of_support_subset fun _ hi ↦
    weight_eq_zero_of_notMem fun hmem ↦
      hi (Finset.mem_range.mpr (Nat.lt_succ_of_le (supp.le_sup (f := id) hmem)))⟩

/-- Every point of `MilnorTotalSpace G` has some cutoff `N` with
`1 / 2 < partialWeightSum G N p`. -/
theorem exists_one_half_lt_partialWeightSum (p : MilnorTotalSpace G) :
    ∃ N, 1 / 2 < partialWeightSum G N p := by
  obtain ⟨N, hN⟩ := exists_partialWeightSum_eq_one p; exact ⟨N, by linarith⟩

/-- **Compact tail bound:** a single cutoff `N` satisfies `1 / 2 < S_N(f x)` for all `x : X`. -/
theorem exists_one_half_lt_partialWeightSum_of_isCompact_range {X : Type v} [TopologicalSpace X]
    {f : C(X, MilnorTotalSpace G)} (hf : IsCompact (Set.range f)) :
    ∃ N, ∀ x, 1 / 2 < partialWeightSum G N (f x) := by
  obtain ⟨N, hN⟩ := hf.elim_directed_cover
    (fun N ↦ {p : MilnorTotalSpace G | 1 / 2 < partialWeightSum G N p})
    (fun N ↦ isOpen_lt continuous_const (partialWeightSum G N).continuous)
    (fun p _ ↦ Set.mem_iUnion.mpr (exists_one_half_lt_partialWeightSum p))
    (directed_of_isDirected_le fun _ _ h _ hp ↦ lt_of_lt_of_le hp (partialWeightSum_mono h _))
  exact ⟨N, fun x ↦ hN (Set.mem_range_self x)⟩

/-- For a continuous map `f` from a compact space `X`, a single cutoff `N` satisfies
`1 / 2 < S_N(f x)` for all `x : X`. -/
theorem exists_one_half_lt_partialWeightSum_of_compactSpace {X : Type v} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, MilnorTotalSpace G)) :
    ∃ N, ∀ x, 1 / 2 < partialWeightSum G N (f x) :=
  exists_one_half_lt_partialWeightSum_of_isCompact_range (isCompact_range f.continuous)

end PartialWeightSum

/-! ### Tail-truncation homotopy and fresh-vertex cone homotopy -/

section Homotopies

variable {G : Type u} [TopologicalSpace G] {X : Type v} [TopologicalSpace X]

private def tailDenom (N : ℕ) (f : C(X, MilnorTotalSpace G)) (z : I × X) : ℝ :=
  partialWeightSum G N (f z.2) + (1 - (z.1 : ℝ)) * (1 - partialWeightSum G N (f z.2))

private theorem tailDenom_pos {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) : 0 < tailDenom N f z :=
  add_pos_of_pos_of_nonneg (hf z.2)
    (mul_nonneg (sub_nonneg.mpr z.1.property.2)
      (sub_nonneg.mpr (partialWeightSum_le_one N (f z.2))))

private def tailWeight (N : ℕ) (f : C(X, MilnorTotalSpace G)) (z : I × X) (i : ℕ) : ℝ :=
  (if i < N then weight i (f z.2) else (1 - (z.1 : ℝ)) * weight i (f z.2)) / tailDenom N f z

private theorem tailWeight_nonneg {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) (i : ℕ) :
    0 ≤ tailWeight N f z i := by
  refine div_nonneg ?_ (tailDenom_pos hf z).le; split_ifs
  exacts [weight_nonneg i (f z.2),
    mul_nonneg (sub_nonneg.mpr z.1.property.2) (weight_nonneg i (f z.2))]

private theorem weight_pos_of_tailWeight_pos {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    {z : I × X} {i : ℕ} (hz : 0 < tailWeight N f z i) : 0 < weight i (f z.2) := by
  by_contra hle; simp [tailWeight, le_antisymm (not_lt.mp hle) (weight_nonneg i (f z.2))] at hz

private theorem sum_tailWeight {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) :
    ∑ i ∈ (finite_support_weight (f z.2)).toFinset ∪ Finset.range N, tailWeight N f z i = 1 := by
  let S := (finite_support_weight (f z.2)).toFinset ∪ Finset.range N
  have hsum_one : ∑ i ∈ S, weight i (f z.2) = 1 := sum_weight_of_support_subset fun i hi ↦
    weight_eq_zero_of_notMem fun hm ↦ hi (Finset.mem_union_left _ hm)
  have hfilter : S.filter (· < N) = Finset.range N := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    exact fun hi ↦ Finset.mem_union_right _ (Finset.mem_range.mpr hi)
  have hsplit := Finset.sum_filter_add_sum_filter_not S (· < N) (fun i ↦ weight i (f z.2))
  rw [hfilter, ← partialWeightSum_apply, hsum_one] at hsplit
  unfold tailWeight
  rw [← Finset.sum_div, Finset.sum_ite, hfilter, ← partialWeightSum_apply, ← Finset.mul_sum,
    eq_sub_of_add_eq' hsplit, ← tailDenom, div_self (tailDenom_pos hf z).ne']

private def tailTruncationPt (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) : MilnorTotalSpace G :=
  ofFinsetCoord ((finite_support_weight (f z.2)).toFinset ∪ Finset.range N)
    (tailWeight N f z) (fun i ↦ label i (f z.2))
    (fun i _ ↦ tailWeight_nonneg hf z i) (sum_tailWeight hf z)

private theorem weight_tailTruncationPt (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) (i : ℕ) :
    weight i (tailTruncationPt N f hf z) = tailWeight N f z i := by
  unfold tailTruncationPt; rw [weight_ofFinsetCoord]
  split_ifs with hi
  · rfl
  · simp [tailWeight, weight_eq_zero_of_notMem fun hm ↦ hi (Finset.mem_union_left _ hm)]

private theorem label_tailTruncationPt (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {z : I × X} {i : ℕ}
    (hz : 0 < tailWeight N f z i) : label i (tailTruncationPt N f hf z) = label i (f z.2) :=
  label_ofFinsetCoord _ _ _ _ _ (Finset.mem_union_left _
    ((finite_support_weight (f z.2)).mem_toFinset.mpr (weight_pos_of_tailWeight_pos hz).ne')) hz

private def tailTruncationHomotopyFun (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) : C(I × X, MilnorTotalSpace G) where
  toFun := tailTruncationPt N f hf
  continuous_toFun := by
    have hden : Continuous (tailDenom N f) := by unfold tailDenom; fun_prop
    refine continuous_iff.mpr ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp_rw [weight_tailTruncationPt]; unfold tailWeight
      by_cases hi : i < N <;> simp only [hi, ↓reduceIte]
      · exact ((continuous_weight i).comp (f.continuous.comp continuous_snd)).div
          hden fun z ↦ (tailDenom_pos hf z).ne'
      · exact (((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).mul
          ((continuous_weight i).comp (f.continuous.comp continuous_snd)))).div
          hden fun z ↦ (tailDenom_pos hf z).ne'
    · simp_rw [weight_tailTruncationPt]
      exact ((continuousOn_label i).comp (f.continuous.comp continuous_snd).continuousOn
        fun _ hz ↦ mem_coordSet_iff.mpr (weight_pos_of_tailWeight_pos hz)).congr fun _ hz ↦
        label_tailTruncationPt N f hf hz

private theorem tailTruncationHomotopyFun_apply (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) :
    tailTruncationHomotopyFun N f hf z = tailTruncationPt N f hf z := rfl

/-- Truncated map (`s = 1`): renormalizes weights `< N` by `S_N(f x)` and zeros weights `≥ N`. -/
def tailTruncationMap (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) : C(X, MilnorTotalSpace G) :=
  (tailTruncationHomotopyFun N f hf).comp ⟨fun x ↦ (1, x), by fun_prop⟩

private theorem tailTruncationMap_apply (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (x : X) :
    tailTruncationMap N f hf x = tailTruncationPt N f hf (1, x) := rfl

@[simp] theorem weight_tailTruncationMap (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (i : ℕ) (x : X) :
    weight i (tailTruncationMap N f hf x) =
      if i < N then weight i (f x) / partialWeightSum G N (f x) else 0 := by
  rw [tailTruncationMap_apply, weight_tailTruncationPt]
  by_cases hi : i < N <;> simp [hi, tailWeight, tailDenom]

theorem weight_tailTruncationMap_of_le (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {i : ℕ} (hi : N ≤ i) (x : X) :
    weight i (tailTruncationMap N f hf x) = 0 := by
  rw [weight_tailTruncationMap, ite_eq_right (not_lt.mpr hi)]

@[simp] theorem label_tailTruncationMap (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {i : ℕ} {x : X} (hi : i < N)
    (hx : f x ∈ coordSet G i) : label i (tailTruncationMap N f hf x) = label i (f x) :=
  label_tailTruncationPt N f hf (z := (1, x)) (by
    simp only [tailWeight, hi, ↓reduceIte]
    exact div_pos (mem_coordSet_iff.mp hx) (tailDenom_pos hf (1, x)))

/-- **Renormalized tail-truncation homotopy** from `f` to `tailTruncationMap N f hf`. -/
def tailTruncationHomotopy (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) : f.Homotopy (tailTruncationMap N f hf) where
  toContinuousMap := tailTruncationHomotopyFun N f hf
  map_zero_left x := by
    rw [ContinuousMap.toFun_eq_coe, tailTruncationHomotopyFun_apply]
    exact ext_coord
      (fun i ↦ by rw [weight_tailTruncationPt]; simp [tailWeight, tailDenom])
      (fun i hi ↦ label_tailTruncationPt N f hf
        (by simpa [weight_tailTruncationPt] using mem_coordSet_iff.mp hi))
  map_one_left _ := rfl

/-- The `i`-th barycentric weight along `tailTruncationHomotopy N f hf` at `(s, x)`. -/
@[simp] theorem weight_tailTruncationHomotopy (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (s : I) (x : X) (i : ℕ) :
    weight i (tailTruncationHomotopy N f hf (s, x)) =
      (if i < N then weight i (f x) else (1 - (s : ℝ)) * weight i (f x)) /
        (partialWeightSum G N (f x) + (1 - (s : ℝ)) * (1 - partialWeightSum G N (f x))) :=
  weight_tailTruncationPt N f hf (s, x) i

/-- Along `tailTruncationHomotopy N f hf`, every positive-weight coordinate retains the original
vertex label `label i (f x)`. -/
@[simp] theorem label_tailTruncationHomotopy (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {s : I} {x : X} {i : ℕ}
    (h : tailTruncationHomotopy N f hf (s, x) ∈ coordSet G i) :
    label i (tailTruncationHomotopy N f hf (s, x)) = label i (f x) :=
  label_tailTruncationPt N f hf
    (weight_tailTruncationPt N f hf (s, x) i ▸ mem_coordSet_iff.mp h)

private def coneWeight (N : ℕ) (g : C(X, MilnorTotalSpace G)) (z : I × X) (i : ℕ) : ℝ :=
  if i = N then (z.1 : ℝ) else (1 - (z.1 : ℝ)) * weight i (g z.2)

private theorem weight_pos_of_coneWeight_pos {N : ℕ} {g : C(X, MilnorTotalSpace G)}
    {z : I × X} {i : ℕ} (hiN : i ≠ N) (hz : 0 < coneWeight N g z i) : 0 < weight i (g z.2) := by
  by_contra hle; simp [coneWeight, hiN, le_antisymm (not_lt.mp hle) (weight_nonneg i (g z.2))] at hz

private def conePt (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) (z : I × X) : MilnorTotalSpace G :=
  let S := (finite_support_weight (g z.2)).toFinset
  have hN : N ∉ S := fun hm ↦ (finite_support_weight (g z.2)).mem_toFinset.mp hm (hg z.2)
  ofFinsetCoord (insert N S) (coneWeight N g z) (fun i ↦ if i = N then a else label i (g z.2))
    (fun i _ ↦ by
      unfold coneWeight; split_ifs
      exacts [z.1.property.1, mul_nonneg (sub_nonneg.mpr z.1.property.2) (weight_nonneg i (g z.2))])
    (by
      unfold coneWeight
      rw [Finset.sum_insert hN, ite_eq_left rfl,
        Finset.sum_congr rfl fun _ hi ↦ ite_eq_right (ne_of_mem_of_not_mem hi hN),
        ← Finset.mul_sum, sum_weight_of_support_subset fun _ ↦ weight_eq_zero_of_notMem,
        mul_one, add_sub_cancel])

private theorem weight_conePt (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) (z : I × X) (i : ℕ) :
    weight i (conePt N a g hg z) = coneWeight N g z i := by
  unfold conePt; rw [weight_ofFinsetCoord]
  by_cases hiN : i = N
  · simp [hiN]
  · simp only [Finset.mem_insert, hiN, false_or]
    split_ifs with hi
    · rfl
    · simp [coneWeight, hiN, weight_eq_zero_of_notMem hi]

private theorem label_conePt_self (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) {z : I × X} (hs : 0 < (z.1 : ℝ)) :
    label N (conePt N a g hg z) = a := by
  unfold conePt
  rw [label_ofFinsetCoord _ _ _ _ _ (Finset.mem_insert_self N _) (by simp [coneWeight, hs])]
  exact ite_eq_left rfl

private theorem label_conePt_of_ne (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) {z : I × X} {i : ℕ} (hiN : i ≠ N)
    (hz : 0 < coneWeight N g z i) : label i (conePt N a g hg z) = label i (g z.2) := by
  unfold conePt
  rw [label_ofFinsetCoord _ _ _ _ _ (Finset.mem_insert_of_mem
    ((finite_support_weight (g z.2)).mem_toFinset.mpr
      (weight_pos_of_coneWeight_pos hiN hz).ne')) hz]
  exact ite_eq_right hiN

/-- **Cone homotopy at an unused index** to the constant map at `vertex N a`. -/
def coneAtFreshIndexHomotopy (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) : g.Homotopy (ContinuousMap.const X (vertex N a)) where
  toFun := conePt N a g hg
  continuous_toFun := continuous_iff.mpr ⟨fun i ↦ by
      simp_rw [weight_conePt]; unfold coneWeight
      by_cases hiN : i = N <;> simp only [hiN, ↓reduceIte]
      exacts [continuous_subtypeVal.comp continuous_fst, by fun_prop], fun i ↦ by
      simp_rw [weight_conePt]
      by_cases hiN : i = N
      · subst hiN; exact (continuousOn_const (c := a)).congr fun _ hz ↦
          label_conePt_self i a g hg (by simpa [coneWeight] using hz)
      · exact ((continuousOn_label i).comp (g.continuous.comp continuous_snd).continuousOn
          fun _ hz ↦ mem_coordSet_iff.mpr (weight_pos_of_coneWeight_pos hiN hz)).congr fun _ hz ↦
          label_conePt_of_ne N a g hg hiN hz⟩
  map_zero_left x := by
    rw [ContinuousMap.coe_mk]
    refine (ext_coord
      (fun i ↦ by
        rw [weight_conePt]; by_cases hiN : i = N
        · subst hiN; simp [coneWeight, hg x]
        · simp [coneWeight, hiN])
      (fun i hi ↦ by
        have hiN : i ≠ N := fun h ↦ (mem_coordSet_iff.mp hi).ne' (h ▸ hg x)
        exact (label_conePt_of_ne N a g hg hiN (z := (0, x))
          (by simpa [coneWeight, hiN] using mem_coordSet_iff.mp hi)).symm)).symm
  map_one_left x := by
    rw [ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe, ContinuousMap.const_apply]
    refine ext_coord
      (fun i ↦ by
        rw [weight_conePt, weight_vertex]; by_cases hiN : i = N <;> simp [coneWeight, hiN])
      (fun i hi ↦ by
        have hi' : 0 < coneWeight N g (1, x) i :=
          weight_conePt N a g hg (1, x) i ▸ mem_coordSet_iff.mp hi
        by_cases hiN : i = N
        · subst hiN; exact (label_conePt_self i a g hg zero_lt_one).trans (label_vertex i a).symm
        · simp [coneWeight, hiN] at hi')

/-- The `i`-th barycentric weight along `coneAtFreshIndexHomotopy N a g hg` at `(s, x)`. -/
@[simp] theorem weight_coneAtFreshIndexHomotopy (N : ℕ) (a : G)
    (g : C(X, MilnorTotalSpace G)) (hg : ∀ x, weight N (g x) = 0) (s : I) (x : X) (i : ℕ) :
    weight i (coneAtFreshIndexHomotopy N a g hg (s, x)) =
      if i = N then (s : ℝ) else (1 - (s : ℝ)) * weight i (g x) :=
  weight_conePt N a g hg (s, x) i

/-- When `0 < (s : ℝ)`, the label at the fresh index `N` along `coneAtFreshIndexHomotopy` is
`a`. -/
@[simp] theorem label_coneAtFreshIndexHomotopy_self (N : ℕ) (a : G)
    (g : C(X, MilnorTotalSpace G)) (hg : ∀ x, weight N (g x) = 0) {s : I} (hs : 0 < (s : ℝ))
    (x : X) :
    label N (coneAtFreshIndexHomotopy N a g hg (s, x)) = a :=
  label_conePt_self N a g hg (z := (s, x)) hs

/-- For `i ≠ N`, every positive-weight coordinate along `coneAtFreshIndexHomotopy N a g hg`
retains the original vertex label `label i (g x)`. -/
@[simp] theorem label_coneAtFreshIndexHomotopy_of_ne (N : ℕ) (a : G)
    (g : C(X, MilnorTotalSpace G)) (hg : ∀ x, weight N (g x) = 0) {s : I} {x : X} {i : ℕ}
    (hiN : i ≠ N) (h : coneAtFreshIndexHomotopy N a g hg (s, x) ∈ coordSet G i) :
    label i (coneAtFreshIndexHomotopy N a g hg (s, x)) = label i (g x) :=
  label_conePt_of_ne N a g hg hiN
    (weight_conePt N a g hg (s, x) i ▸ mem_coordSet_iff.mp h)

end Homotopies

end MilnorTotalSpace

end TauCeti

namespace ContinuousMap

open TauCeti

variable {X : Type v} [TopologicalSpace X] {G : Type u} [TopologicalSpace G]

/-- **Every continuous map with compact image into `MilnorTotalSpace G` is null-homotopic** when
`G` is nonempty. -/
theorem nullhomotopic_to_milnorTotalSpace_of_isCompact_range [Nonempty G]
    {f : C(X, MilnorTotalSpace G)} (hf : IsCompact (Set.range f)) : f.Nullhomotopic := by
  obtain ⟨a⟩ := ‹Nonempty G›
  obtain ⟨N, hN⟩ := MilnorTotalSpace.exists_one_half_lt_partialWeightSum_of_isCompact_range hf
  have hN_pos (x) : 0 < MilnorTotalSpace.partialWeightSum G N (f x) := by linarith [hN x]
  exact ⟨MilnorTotalSpace.vertex N a, ⟨(MilnorTotalSpace.tailTruncationHomotopy N f hN_pos).trans
    (MilnorTotalSpace.coneAtFreshIndexHomotopy N a (MilnorTotalSpace.tailTruncationMap N f hN_pos)
      fun x ↦ MilnorTotalSpace.weight_tailTruncationMap_of_le N f hN_pos le_rfl x)⟩⟩

/-- Every continuous map from a compact space `X` into `MilnorTotalSpace G` is null-homotopic
when `G` is nonempty. -/
theorem nullhomotopic_to_milnorTotalSpace [CompactSpace X] [Nonempty G]
    (f : C(X, MilnorTotalSpace G)) : f.Nullhomotopic :=
  nullhomotopic_to_milnorTotalSpace_of_isCompact_range (isCompact_range f.continuous)

end ContinuousMap

namespace TauCeti

section ConnectivityAndHomotopyGroups

variable (G : Type u) [TopologicalSpace G]

instance instSimplyConnectedSpaceMilnorTotalSpace [Nonempty G] :
    SimplyConnectedSpace (MilnorTotalSpace G) :=
  simplyConnectedSpace_of_compact_nullhomotopic fun f ↦ f.nullhomotopic_to_milnorTotalSpace

end ConnectivityAndHomotopyGroups

end TauCeti

namespace HomotopyGroup

open TauCeti

/-- **Weak contractibility of `MilnorTotalSpace G`:** all homotopy groups and `π₀` vanish. -/
instance subsingleton_milnorTotalSpace
    {G : Type u} [TopologicalSpace G] (N : Type*) (x : MilnorTotalSpace G) :
    Subsingleton (HomotopyGroup N (MilnorTotalSpace G) x) := by
  classical
  have : Nonempty G := MilnorTotalSpace.nonempty_of_milnorTotalSpace x
  by_cases hfin : Finite N
  · by_cases hemp : IsEmpty N
    · have : Subsingleton (ZerothHomotopy (MilnorTotalSpace G)) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
      exact (homotopyGroupEquivZerothHomotopyOfIsEmpty N x).subsingleton
    · have : Nonempty N := not_isEmpty_iff.mp hemp
      exact subsingleton_homotopyGroup_of_compact_nullhomotopic N x
        fun f ↦ f.nullhomotopic_to_milnorTotalSpace
  · have : Infinite N := not_finite_iff_infinite.mp hfin; infer_instance

end HomotopyGroup

namespace ContinuousMap

open TauCeti

variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {G : Type u} [TopologicalSpace G]

/-- Every continuous map from the unit sphere of a proper real seminormed space `E` into
`MilnorTotalSpace G` extends continuously over the closed unit ball when `G` is nonempty. -/
theorem exists_extension_closedBall_milnorTotalSpace [Nonempty G]
    (g : C(sphere (0 : E) 1, MilnorTotalSpace G)) :
    ∃ G' : C(closedBall (0 : E) 1, MilnorTotalSpace G),
      ∀ y : sphere (0 : E) 1, G' ⟨y, sphere_subset_closedBall y.property⟩ = g y :=
  g.nullhomotopic_iff_exists_extension_closedBall.mp g.nullhomotopic_to_milnorTotalSpace

/-- Every continuous map `g` from the unit sphere of a proper real seminormed space `E` into
`MilnorTotalSpace G` is homotopic relative to a chosen base point `s₀` on the sphere to the
constant map at `g s₀`. -/
theorem homotopicRel_const_singleton_sphere_milnorTotalSpace
    (g : C(sphere (0 : E) 1, MilnorTotalSpace G)) (s₀ : sphere (0 : E) 1) :
    g.HomotopicRel (ContinuousMap.const _ (g s₀)) {s₀} :=
  have := MilnorTotalSpace.nonempty_of_milnorTotalSpace (g s₀)
  (g.homotopicRel_const_singleton_sphere_iff_nullhomotopic s₀).mpr
    g.nullhomotopic_to_milnorTotalSpace

end ContinuousMap
