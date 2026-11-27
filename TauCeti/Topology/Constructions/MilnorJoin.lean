/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Indexed
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Topology.Order.Lattice

/-!
# Milnor's join with the strong coordinate topology

A point of the join of `ι` copies of a space `G` is a finitely supported family of weights
`tᵢ ≥ 0` with `∑ tᵢ = 1`, together with a label `gᵢ ∈ G` at every index of positive weight. The
underlying set is the realization of the indexed join `TauCeti.indexedJoin fun _ : ι => G`, whose
vertices over the index `i` are the labelled pairs `⟨i, g⟩`; its barycentric coordinates have at
most one nonzero entry over each index.

`TauCeti.MilnorJoin ι G` is a type copy of that realization carrying Milnor's *strong* topology:
the coarsest topology for which every weight `x ↦ tᵢ(x)` is continuous and every label
`x ↦ gᵢ(x)` is continuous on the open set `{tᵢ > 0}`. When `G` is a monoid, it acts on the right
by multiplying every label, and this action is jointly continuous as soon as multiplication on `G`
is; no metric on `G` is involved. With `ι = ℕ` and `G` a topological group this is the total space
`EG` of Milnor's universal principal `G`-bundle. The weak topology of the realization
(`TauCeti.universalGSpace`) ignores any topology on the labels, and is a different topology.

The continuity criterion `TauCeti.MilnorJoin.continuous_iff` describes the maps into the join
from an arbitrary space, for instance from a product with an interval or with `G`, through these
coordinates. Points are built from weights and labels with `TauCeti.MilnorJoin.mk`, and a map of
label spaces induces `TauCeti.MilnorJoin.map`. Although infinitely many weights may be positive
near a point, all weights outside the finite support at that point are small nearby; hence the
largest weight `m = maxᵢ tᵢ`, which is positive and invariant under the action, is continuous.

## Main declarations

* `TauCeti.MilnorJoin`: the join of `ι` copies of `G`.
* `TauCeti.MilnorJoin.weights`, `TauCeti.MilnorJoin.label`: its coordinates.
* `TauCeti.MilnorJoin.mk`: the point with prescribed weights and labels, and
  `TauCeti.MilnorJoin.ext`: points are determined by their weights and their labels at the
  indices of positive weight.
* `TauCeti.MilnorJoin.continuous_iff`: the continuity criterion in coordinates, and
  `TauCeti.MilnorJoin.continuous_mk` for maps built from continuous weights and labels.
* `TauCeti.MilnorJoin.instMulActionMulOpposite`: the right action relabelling `gᵢ ↦ gᵢ g`, with
  `TauCeti.MilnorJoin.weights_op_smul` and `TauCeti.MilnorJoin.label_op_smul`; the left action
  `gᵢ ↦ g gᵢ`; and `TauCeti.MilnorJoin.map_inv_smul`: label inversion carries the left action
  of `g⁻¹` to the right action of `g`.
* `TauCeti.MilnorJoin.instContinuousSMulMulOpposite`: the right action is jointly continuous
  when multiplication on `G` is continuous.
* `TauCeti.MilnorJoin.eventually_forall_weights_apply_lt`: finite-support tail control, and
  `TauCeti.MilnorJoin.continuous_maxWeight`: the largest weight is continuous.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430–436, §§2–3.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Section 14.4.
-/

public section

noncomputable section

open Set Topology MulOpposite AbstractSimplicialComplex

namespace TauCeti

universe u v w

/-- Milnor's join of `ι` copies of `G`: a type copy of the realization of the indexed join
`TauCeti.indexedJoin fun _ : ι => G`. A point is a finitely supported family of weights summing to
one, labelled by an element of `G` at each index of positive weight. It carries the strong
coordinate topology rather than the weak topology of the realization. -/
structure MilnorJoin (ι : Type u) (G : Type v) : Type (max u v) where
  /-- The point of the join with the given point of the realization as barycentric coordinates. -/
  ofRealization ::
  /-- The point of the realization of the indexed join underlying a point of the join. -/
  toRealization : (indexedJoin fun _ : ι => G).Realization

namespace MilnorJoin

variable {ι : Type u} {G : Type v} {H : Type w}

/-- The vertex `⟨i, l i⟩` over each index `i`; distinct indices give distinct vertices. -/
private theorem sigmaMk_injective (l : ι → G) :
    Function.Injective fun i : ι => (⟨i, l i⟩ : Σ _ : ι, G) :=
  Function.LeftInverse.injective (g := Sigma.fst) fun _ => rfl

/-! ### Weights and points from weights and labels -/

/-- The weights `tᵢ` of a point of the join. The weight at `i` is the total barycentric
coordinate of the vertices over `i`, of which at most one is nonzero. -/
def weights (x : MilnorJoin ι G) : ι →₀ ℝ :=
  Finsupp.mapDomain Sigma.fst x.toRealization.val

/-- The weights of a point of the join are nonnegative. -/
theorem weights_nonneg (x : MilnorJoin ι G) (i : ι) : 0 ≤ weights x i := by
  rw [weights, Finsupp.mapDomain_apply]
  exact Finset.sum_nonneg fun v _ => Finsupp.single_nonneg.2 (Realization.nonneg _ _ _) i

/-- The weights of a point of the join sum to one. -/
@[simp]
theorem sum_weights (x : MilnorJoin ι G) : (weights x).sum (fun _ r => r) = 1 := by
  rw [weights, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Realization.sum_eq_one _ x.toRealization

/-- Weights summing to one, placed on the vertices labelled by a family `l`, form a point of the
realization of the indexed join. -/
private theorem mapDomain_mem_realization {w : ι →₀ ℝ} (hw₀ : ∀ i, 0 ≤ w i)
    (hw₁ : w.sum (fun _ r => r) = 1) (l : ι → G) :
    Finsupp.mapDomain (fun i => (⟨i, l i⟩ : Σ _ : ι, G)) w ∈
      (indexedJoin fun _ : ι => G).standardGeometricComplex.space := by
  have hl := sigmaMk_injective l
  refine mem_indexedJoin_realization_iff.2 ⟨fun v => ?_, ?_, fun v v' hv hv' hvv' => ?_⟩
  · by_cases hv : v ∈ Set.range fun i => (⟨i, l i⟩ : Σ _ : ι, G)
    · obtain ⟨i, rfl⟩ := hv
      rw [Finsupp.mapDomain_apply_of_injective hl]
      exact hw₀ i
    · rw [Finsupp.mapDomain_of_notMem_range _ _ hv]
  · rwa [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  · obtain ⟨i, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hv
    obtain ⟨j, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hv'
    obtain rfl : i = j := hvv'
    rfl

/-- The point of the join with weights `w` and labels `l`; the labels at indices of weight zero
are forgotten. -/
def mk (w : ι →₀ ℝ) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : w.sum (fun _ r => r) = 1) (l : ι → G) :
    MilnorJoin ι G :=
  ofRealization ⟨_, mapDomain_mem_realization hw₀ hw₁ l⟩

section mk

variable {w : ι →₀ ℝ} {hw₀ : ∀ i, 0 ≤ w i} {hw₁ : w.sum (fun _ r => r) = 1} {l : ι → G}

/-- The barycentric coordinates of `TauCeti.MilnorJoin.mk`. -/
theorem toRealization_val_mk :
    (mk w hw₀ hw₁ l).toRealization.val = Finsupp.mapDomain (fun i => ⟨i, l i⟩) w :=
  (rfl)

/-- The weights of `TauCeti.MilnorJoin.mk w _ _ l` are `w`. -/
@[simp]
theorem weights_mk : weights (mk w hw₀ hw₁ l) = w := by
  rw [weights, toRealization_val_mk, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_id

end mk

/-- The weights of a point of the join over any finite set of indices sum to at most one. -/
theorem sum_weights_le_one (x : MilnorJoin ι G) (s : Finset ι) : ∑ i ∈ s, weights x i ≤ 1 := by
  classical
  calc ∑ i ∈ s, weights x i ≤ ∑ i ∈ s ∪ (weights x).support, weights x i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun i _ _ =>
          weights_nonneg x i
    _ = 1 := by
        rw [← sum_weights x, Finsupp.sum_of_support_subset _ Finset.subset_union_right _
          fun _ _ => rfl]

/-- The largest weight `m(x) = maxᵢ tᵢ(x)` of a point of the join. -/
def maxWeight (x : MilnorJoin ι G) : ℝ :=
  ⨆ i, weights x i

/-- Every weight of a point of the join is at most its largest weight. -/
theorem weights_apply_le_maxWeight (x : MilnorJoin ι G) (i : ι) : weights x i ≤ maxWeight x :=
  le_ciSup ⟨1, Set.forall_mem_range.2 fun j => by
    simpa using sum_weights_le_one x {j}⟩ i

/-- The largest weight of a point of the join is attained, at an index of positive weight. -/
theorem exists_weights_apply_eq_maxWeight (x : MilnorJoin ι G) :
    ∃ i, 0 < weights x i ∧ weights x i = maxWeight x := by
  have hne : (weights x).support.Nonempty := Finsupp.support_nonempty_iff.2 fun h => by
    simpa [h] using sum_weights x
  obtain ⟨i, hi, hmax⟩ := (weights x).support.exists_max_image (weights x) hne
  have : Nonempty ι := ⟨i⟩
  refine ⟨i, (weights_nonneg x i).lt_of_ne' (Finsupp.mem_support_iff.1 hi),
    le_antisymm (weights_apply_le_maxWeight x i) (ciSup_le fun j => ?_)⟩
  by_cases hj : j ∈ (weights x).support
  · exact hmax j hj
  · rw [Finsupp.notMem_support_iff.1 hj]
    exact weights_nonneg x i

/-- The largest weight of a point of the join is positive. -/
theorem maxWeight_pos (x : MilnorJoin ι G) : 0 < maxWeight x := by
  obtain ⟨i, hi, hix⟩ := exists_weights_apply_eq_maxWeight x
  exact hix ▸ hi

/-- Over a finite set of indices with total weight above `1 - ε`, every other weight is below
`ε`. -/
private theorem weights_apply_lt_of_one_sub_lt_sum (x : MilnorJoin ι G) {s : Finset ι} {i : ι}
    (hi : i ∉ s) {ε : ℝ} (h : 1 - ε < ∑ j ∈ s, weights x j) : weights x i < ε := by
  classical
  have := sum_weights_le_one x (insert i s)
  rw [Finset.sum_insert hi] at this
  linarith

/-! ### Labels -/

section Label

variable [Nonempty G]

/-- The label `gᵢ` of a point of the join at the index `i`: the label of the vertex over `i` with
nonzero barycentric coordinate. It is meaningful only where `0 < weights x i`
(`TauCeti.MilnorJoin.label_mk`); elsewhere it is an unspecified element of `G`. -/
def label (i : ι) (x : MilnorJoin ι G) : G :=
  Classical.epsilon fun g => x.toRealization.val ⟨i, g⟩ ≠ 0

/-- A vertex over `i` with nonzero coordinate carries the label at `i`. -/
private theorem label_eq_of_ne_zero {x : MilnorJoin ι G} {i : ι} {g : G}
    (h : x.toRealization.val ⟨i, g⟩ ≠ 0) : label i x = g := by
  have hl : x.toRealization.val ⟨i, label i x⟩ ≠ 0 := Classical.epsilon_spec (p := fun g =>
    x.toRealization.val ⟨i, g⟩ ≠ 0) ⟨g, h⟩
  by_contra hne
  rcases realization_apply_eq_zero_of_fst_eq (x := x.toRealization) (v := ⟨i, label i x⟩)
    (w := ⟨i, g⟩) rfl (by simpa using hne) with h' | h'
  exacts [hl h', h h']

/-- The weight at `i` is the coordinate of the vertex over `i` carrying the label at `i`. -/
private theorem weights_apply (x : MilnorJoin ι G) (i : ι) :
    weights x i = x.toRealization.val ⟨i, label i x⟩ := by
  by_cases h : x.toRealization.val ⟨i, label i x⟩ = 0
  · rw [h, weights, Finsupp.mapDomain_of_notMem_image_support]
    rintro ⟨⟨j, g⟩, hg, rfl⟩
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hg
    exact hg (label_eq_of_ne_zero hg ▸ h)
  · exact Finsupp.mapDomain_apply' _ _ subset_rfl (realization_support_injOn_fst _)
      (Finsupp.mem_support_iff.2 h)

/-- The barycentric coordinates of a point of the join are its weights, placed on the vertices
labelled by its labels. -/
theorem toRealization_val (x : MilnorJoin ι G) :
    x.toRealization.val = Finsupp.mapDomain (fun i => ⟨i, label i x⟩) (weights x) := by
  ext ⟨i, g⟩
  by_cases hg : g = label i x
  · subst hg
    rw [Finsupp.mapDomain_apply_of_injective (sigmaMk_injective fun i => label i x),
      weights_apply]
  · rw [Finsupp.mapDomain_of_notMem_range]
    · by_contra h
      exact hg (label_eq_of_ne_zero h).symm
    · rintro ⟨j, hj⟩
      simp only [Sigma.mk.inj_iff, heq_iff_eq] at hj
      obtain ⟨rfl, hj⟩ := hj
      exact hg hj.symm

/-- At an index of positive weight, the label of `TauCeti.MilnorJoin.mk w _ _ l` is given
by `l`. -/
theorem label_mk {w : ι →₀ ℝ} {hw₀ : ∀ i, 0 ≤ w i} {hw₁ : w.sum (fun _ r => r) = 1}
    {l : ι → G} {i : ι} (hi : 0 < w i) : label i (mk w hw₀ hw₁ l) = l i := by
  refine label_eq_of_ne_zero ?_
  rw [toRealization_val_mk, Finsupp.mapDomain_apply_of_injective (sigmaMk_injective l)]
  exact hi.ne'

/-- Two points of the join are equal when they have the same weights and the same labels at
every index of positive weight. -/
@[ext]
theorem ext {x y : MilnorJoin ι G} (hw : weights x = weights y)
    (hl : ∀ i, 0 < weights x i → label i x = label i y) : x = y := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  congr 1
  refine Subtype.ext ?_
  rw [toRealization_val ⟨x⟩, toRealization_val ⟨y⟩]
  refine Finsupp.mapDomain_congr hw fun i hi => ?_
  rw [hl i ((weights_nonneg _ i).lt_of_ne' (Finsupp.mem_support_iff.1 hi))]

/-- Every point of the join is built from its weights and labels. -/
@[simp]
theorem mk_weights_label (x : MilnorJoin ι G) :
    mk (weights x) (weights_nonneg x) (sum_weights x) (fun i => label i x) = x :=
  ext weights_mk fun _ hi => label_mk (by rwa [weights_mk] at hi)

end Label

/-! ### Relabelling -/

section Map

variable [Nonempty G]

/-- The map of joins induced by a map of label spaces: it keeps the weights and applies `f` to
every label. -/
def map (f : G → H) (x : MilnorJoin ι G) : MilnorJoin ι H :=
  mk (weights x) (weights_nonneg x) (sum_weights x) fun i => f (label i x)

/-- Relabelling keeps the weights. -/
@[simp]
theorem weights_map (f : G → H) (x : MilnorJoin ι G) : weights (map f x) = weights x :=
  weights_mk

/-- At an index of positive weight, relabelling applies the map to the label. -/
theorem label_map [Nonempty H] (f : G → H) {x : MilnorJoin ι G} {i : ι} (hi : 0 < weights x i) :
    label i (map f x) = f (label i x) :=
  label_mk hi

/-- Relabelling by the identity is the identity. -/
@[simp]
theorem map_id (x : MilnorJoin ι G) : map id x = x :=
  mk_weights_label x

/-- Relabelling is functorial. -/
theorem map_map [Nonempty H] {K : Type*} [Nonempty K] (g : H → K) (f : G → H) (x : MilnorJoin ι G) :
    map g (map f x) = map (g ∘ f) x :=
  ext (by simp) fun i hi => by
    rw [weights_map, weights_map] at hi
    rw [label_map _ (by rwa [weights_map]), label_map _ hi, label_map _ hi, Function.comp_apply]

end Map

/-! ### The group actions -/

section Monoid

variable [Monoid G]

/-- The right action of a monoid on the join of copies of itself, `x • g`, written
`MulOpposite.op g • x`, multiplying every label on the right by `g`. -/
instance instMulActionMulOpposite : MulAction Gᵐᵒᵖ (MilnorJoin ι G) where
  smul g x := map (· * g.unop) x
  one_smul x := by
    -- the action being defined is relabelling; unfold it to state the law for `map`
    change map _ x = x
    simp only [unop_one, mul_one]
    exact map_id x
  mul_smul a b x := by
    -- the action being defined is relabelling; unfold it to reduce to `map_map`
    change map _ x = map _ (map _ x)
    rw [map_map]
    congr 1
    funext g
    simp [mul_assoc]

/-- The right action is relabelling by right multiplication. -/
theorem op_smul_eq_map (g : G) (x : MilnorJoin ι G) : op g • x = map (· * g) x :=
  (rfl)

/-- The right action preserves the weight at every index. -/
@[simp]
theorem weights_op_smul (g : G) (x : MilnorJoin ι G) : weights (op g • x) = weights x :=
  weights_map _ x

/-- The right action preserves the largest weight. -/
@[simp]
theorem maxWeight_op_smul (g : G) (x : MilnorJoin ι G) : maxWeight (op g • x) = maxWeight x := by
  simp [maxWeight]

/-- At an index of positive weight, the right action multiplies the label on the right. -/
theorem label_op_smul (g : G) {x : MilnorJoin ι G} {i : ι} (hi : 0 < weights x i) :
    label i (op g • x) = label i x * g :=
  label_map _ hi

/-- The left action of a monoid on the join of copies of itself, multiplying every label on the
left. -/
instance instMulAction : MulAction G (MilnorJoin ι G) where
  smul g x := map (g * ·) x
  one_smul x := by
    -- the action being defined is relabelling; unfold it to state the law for `map`
    change map _ x = x
    simp only [one_mul]
    exact map_id x
  mul_smul a b x := by
    -- the action being defined is relabelling; unfold it to reduce to `map_map`
    change map _ x = map _ (map _ x)
    rw [map_map]
    congr 1
    funext g
    simp [mul_assoc]

/-- The left action is relabelling by left multiplication. -/
theorem smul_eq_map (g : G) (x : MilnorJoin ι G) : g • x = map (g * ·) x :=
  (rfl)

/-- The left action preserves the weight at every index. -/
@[simp]
theorem weights_smul (g : G) (x : MilnorJoin ι G) : weights (g • x) = weights x :=
  weights_map _ x

/-- At an index of positive weight, the left action multiplies the label on the left. -/
theorem label_smul (g : G) {x : MilnorJoin ι G} {i : ι} (hi : 0 < weights x i) :
    label i (g • x) = g * label i x :=
  label_map _ hi

end Monoid

/-- Label inversion carries the left action of `g⁻¹` to the right action of `g`. -/
theorem map_inv_smul [DivisionMonoid G] (g : G) (x : MilnorJoin ι G) :
    map (·⁻¹) (g⁻¹ • x) = op g • map (·⁻¹) x :=
  ext (by simp) fun i hi => by
    simp only [weights_map, weights_smul] at hi
    rw [label_map _ (by rwa [weights_smul]), label_smul _ hi,
      label_op_smul _ (by rwa [weights_map]), label_map _ hi, mul_inv_rev, inv_inv]

/-! ### The strong coordinate topology -/

section Topology

variable [Nonempty G] [TopologicalSpace G]

/-- The strong coordinate topology on the join: the coarsest topology for which every weight is
continuous and every label is continuous on the open set where its weight is positive. -/
instance : TopologicalSpace (MilnorJoin ι G) :=
  (⨅ i, .induced (fun x => weights x i) inferInstance) ⊓
    .generateFrom {s | ∃ i, ∃ V : Set G, IsOpen V ∧ s = {x | 0 < weights x i ∧ label i x ∈ V}}

/-- Every weight of the join is continuous. -/
@[fun_prop]
theorem continuous_weights_apply (i : ι) : Continuous fun x : MilnorJoin ι G => weights x i :=
  continuous_iff_le_induced.2 (inf_le_left.trans (iInf_le _ i))

/-- The points with positive weight at `i` form an open set. -/
theorem isOpen_setOf_pos_weights (i : ι) : IsOpen {x : MilnorJoin ι G | 0 < weights x i} :=
  isOpen_lt continuous_const (continuous_weights_apply i)

/-- The points with positive weight at `i` and label at `i` in an open set form an open set. -/
theorem isOpen_setOf_pos_weights_and_label_mem (i : ι) {V : Set G} (hV : IsOpen V) :
    IsOpen {x : MilnorJoin ι G | 0 < weights x i ∧ label i x ∈ V} :=
  TopologicalSpace.le_def.1 inf_le_right _
    (TopologicalSpace.isOpen_generateFrom_of_mem ⟨i, V, hV, rfl⟩)

/-- The label at `i` is continuous on the open set where the weight at `i` is positive. -/
theorem continuousOn_label (i : ι) :
    ContinuousOn (label i) {x : MilnorJoin ι G | 0 < weights x i} :=
  (continuousOn_open_iff (isOpen_setOf_pos_weights i)).2 fun _ hV =>
    isOpen_setOf_pos_weights_and_label_mem i hV

/-- **The continuity criterion for the strong topology.** A map from an arbitrary space into the
join is continuous exactly when every weight of it is continuous and every label of it is
continuous where the corresponding weight is positive. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → MilnorJoin ι G} :
    Continuous f ↔ (∀ i, Continuous fun x => weights (f x) i) ∧
      ∀ i, ContinuousOn (fun x => label i (f x)) {x | 0 < weights (f x) i} := by
  refine ⟨fun hf => ⟨fun i => (continuous_weights_apply i).comp hf, fun i =>
    (continuousOn_label i).comp hf.continuousOn fun _ hx => hx⟩, fun ⟨hw, hl⟩ => ?_⟩
  refine continuous_inf_rng.2 ⟨continuous_iInf_rng.2 fun i => continuous_induced_rng.2 (hw i),
    continuous_generateFrom_iff.2 ?_⟩
  rintro _ ⟨i, V, hV, rfl⟩
  exact (hl i).isOpen_inter_preimage (isOpen_lt continuous_const (hw i)) hV

/-- A map into the join built from continuous weights and from labels continuous where their
weights are positive is continuous. -/
theorem continuous_mk {X : Type*} [TopologicalSpace X] {w : X → ι →₀ ℝ}
    (hw₀ : ∀ x i, 0 ≤ w x i) (hw₁ : ∀ x, (w x).sum (fun _ r => r) = 1) {l : X → ι → G}
    (hw : ∀ i, Continuous fun x => w x i)
    (hl : ∀ i, ContinuousOn (fun x => l x i) {x | 0 < w x i}) :
    Continuous fun x => mk (w x) (hw₀ x) (hw₁ x) (l x) := by
  refine continuous_iff.2 ⟨fun i => by simpa using hw i, fun i => ?_⟩
  simp only [weights_mk]
  exact (hl i).congr fun x hx => label_mk hx

/-- **Finite-support tail control.** Near a point `x` of the join, every weight at an index
outside the support of the weights of `x` is small. -/
theorem eventually_forall_weights_apply_lt (x : MilnorJoin ι G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ i ∉ (weights x).support, weights y i < ε := by
  have hx : ∑ j ∈ (weights x).support, weights x j = 1 := sum_weights x
  have hopen : IsOpen {y : MilnorJoin ι G | 1 - ε < ∑ j ∈ (weights x).support, weights y j} :=
    isOpen_lt continuous_const (continuous_finsetSum _ fun j _ => continuous_weights_apply j)
  filter_upwards [hopen.mem_nhds (by rw [mem_ofPred_eq, hx]; linarith)] with y hy i hi
  exact weights_apply_lt_of_one_sub_lt_sum y hi hy

/-- Near a point `x` of the join, the largest weight is attained over the support of the weights
of `x`. -/
private theorem eventually_maxWeight_eq (x : MilnorJoin ι G) :
    ∀ᶠ y in 𝓝 x, maxWeight y = ⨆ i : (weights x).support, weights y i.val := by
  obtain ⟨i₀, hi₀, hi₀x⟩ := exists_weights_apply_eq_maxWeight x
  have hi₀s : i₀ ∈ (weights x).support := Finsupp.mem_support_iff.2 hi₀.ne'
  have : Nonempty (weights x).support := ⟨⟨i₀, hi₀s⟩⟩
  have : Nonempty ι := ⟨i₀⟩
  have hε : 0 < maxWeight x / 2 := half_pos (maxWeight_pos x)
  filter_upwards [eventually_forall_weights_apply_lt x hε,
    (isOpen_lt continuous_const (continuous_weights_apply i₀)).mem_nhds
      (show maxWeight x / 2 < weights x i₀ by linarith)] with y hy hyi₀
  have hbdd := (Set.finite_range fun i : (weights x).support => weights y i.val).bddAbove
  have hle : weights y i₀ ≤ ⨆ i : (weights x).support, weights y i.val :=
    le_ciSup hbdd ⟨i₀, hi₀s⟩
  refine le_antisymm (ciSup_le fun i => ?_)
    (ciSup_le fun i => weights_apply_le_maxWeight y i)
  by_cases hi : i ∈ (weights x).support
  · exact le_ciSup hbdd ⟨i, hi⟩
  · exact ((hy i hi).trans hyi₀).le.trans hle

/-- The largest weight is continuous on the join. -/
@[fun_prop]
theorem continuous_maxWeight : Continuous (maxWeight : MilnorJoin ι G → ℝ) :=
  continuous_iff_continuousAt.2 fun x =>
    (continuous_ciSup_of_finite fun i : (weights x).support =>
      continuous_weights_apply i.val).continuousAt.congr
        ((eventually_maxWeight_eq x).mono fun _ h => h.symm)

/-- The join of copies of a Hausdorff space is Hausdorff: points with different weights are
separated by a weight, and points with the same weights by a label. -/
instance [T2Space G] : T2Space (MilnorJoin ι G) := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases hw : weights x = weights y
  · obtain ⟨i, hi, hl⟩ : ∃ i, 0 < weights x i ∧ label i x ≠ label i y := by
      by_contra! h
      exact hxy (ext hw h)
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hl
    refine ⟨_, _, isOpen_setOf_pos_weights_and_label_mem i hU,
      isOpen_setOf_pos_weights_and_label_mem i hV, ⟨hi, hxU⟩, ⟨hw ▸ hi, hyV⟩, ?_⟩
    exact Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 hUV hz.2 hz'.2
  · obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 hw
    exact separated_by_continuous (continuous_weights_apply i) hi

/-- A continuous map of label spaces induces a continuous map of joins. -/
@[fun_prop]
theorem continuous_map [Nonempty H] [TopologicalSpace H] {f : G → H} (hf : Continuous f) :
    Continuous (map (ι := ι) f) :=
  continuous_mk _ _ (fun i => continuous_weights_apply i) fun i =>
    hf.comp_continuousOn (continuousOn_label i)

end Topology

section ContinuousMul

variable [Monoid G] [TopologicalSpace G] [ContinuousMul G]

/-- The right action of a monoid with continuous multiplication on the join is jointly
continuous. -/
instance instContinuousSMulMulOpposite : ContinuousSMul Gᵐᵒᵖ (MilnorJoin ι G) where
  continuous_smul := by
    refine continuous_iff.2 ⟨fun i => ?_, fun i => ?_⟩
    · exact ((continuous_weights_apply i).comp continuous_snd).congr fun p => by
        rw [Function.comp_apply, ← op_unop p.1, weights_op_smul]
    · have hl : ContinuousOn (fun p : Gᵐᵒᵖ × MilnorJoin ι G => label i p.2 * p.1.unop)
          {p | 0 < weights (p.1 • p.2) i} :=
        ((continuousOn_label i).comp continuous_snd.continuousOn fun p hp => by
          rwa [mem_ofPred_eq, ← op_unop p.1, weights_op_smul] at hp).mul
            (continuous_unop.comp continuous_fst).continuousOn
      refine hl.congr fun p hp => ?_
      obtain ⟨g, x⟩ := p
      rw [← op_unop g] at hp ⊢
      simp only [mem_ofPred_eq, weights_op_smul] at hp
      exact label_op_smul _ hp

/-- The left action of a monoid with continuous multiplication on the join is jointly
continuous. -/
instance instContinuousSMul : ContinuousSMul G (MilnorJoin ι G) where
  continuous_smul := by
    refine continuous_iff.2 ⟨fun i => ?_, fun i => ?_⟩
    · simp only [weights_smul]
      fun_prop
    · have hl : ContinuousOn (fun p : G × MilnorJoin ι G => p.1 * label i p.2)
          {p | 0 < weights (p.1 • p.2) i} :=
        continuous_fst.continuousOn.mul ((continuousOn_label i).comp continuous_snd.continuousOn
          fun p hp => by simpa using hp)
      refine hl.congr fun p hp => ?_
      simp only [mem_ofPred_eq, weights_smul] at hp
      exact label_smul _ hp

end ContinuousMul

end MilnorJoin

end TauCeti
