/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Isometry

/-!
# Clusters for a weighted measure

Let `E` be a finite-dimensional real inner product space and `W : E → ℝ` a weight, with measure
`μ = e^{−W} · volume` (`TauCeti.weightedMeasure`). For `q ≥ 1`, a **`q`-cluster**
(`TauCeti.Cluster W q`) is a `q`-tuple `(Ω_1, …, Ω_q)` of Lebesgue-measurable cells that are
pairwise disjoint, cover `E` up to a `volume`-null set, and have finite weighted perimeter. Cells
may be empty or disconnected. Its **total perimeter** is `P_μ(Ω) = ½ Σᵢ P_μ(Ω_i)`
(`TauCeti.Cluster.perimeter`), each interface being counted once. The measure of a union of
cells is the sum of their measures (`TauCeti.Cluster.weightedMeasure_biUnion_cell`), so when
`μ(E) = 1` the measures of the cells form a point of the probability simplex
(`TauCeti.Cluster.sum_weightedMeasure_cell`).
Two clusters are equivalent when corresponding cells agree up to null sets
(`TauCeti.Cluster.IsEquivalent`). Conversely, for an almost everywhere measurable weight whose
measure `μ` is finite, measurable sets of finite weighted perimeter that pairwise meet in null sets
and whose measures add up to `μ(E)` agree up to null sets with the cells of a cluster
(`TauCeti.exists_cluster_ae_eq`).

* Equivalent clusters have the same total perimeter and the same cell measures.
* Permuting the cells gives a cluster with the same total perimeter (`TauCeti.Cluster.permute`).
* For a `C¹` weight, grouping the cells along a map `f : Fin q → Fin p` gives a `p`-cluster whose
  total perimeter is at most that of the original one (`TauCeti.Cluster.coarsen`,
  `TauCeti.Cluster.perimeter_coarsen_le`), by subadditivity of the weighted perimeter over disjoint
  unions (`TauCeti.weightedPerimeter_biUnion_le`). Merging two
  cells of a `q`-cluster into a `(q − 1)`-cluster is the case of a map identifying two indices.
* There are no `0`-clusters; up to equivalence, the only `1`-cluster is `(E)`, of total perimeter
  `0` for a `C¹` weight; and for a `C¹` weight a `2`-cluster has total perimeter
  `P_μ(Ω_1) = P_μ(Ω_2)`, by complement invariance.
* A linear isometry equivalence carries clusters for `W` to clusters for the transported weight
  with the same total perimeter (`TauCeti.Cluster.map`); the Gaussian weight is invariant, so
  this carries Gaussian clusters to Gaussian clusters
  (`Ω.map e (LinearIsometryEquiv.gaussianWeight_comp e)`).

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Sections 1 and 3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A **`q`-cluster** for the weight `W`: `q` Lebesgue-measurable cells, pairwise disjoint,
covering `E` up to a `volume`-null set (for an almost everywhere measurable weight, equivalently up
to a null set for `e^{−W} · volume`, by `TauCeti.weightedMeasure_absolutelyContinuous` and
`TauCeti.volume_absolutelyContinuous_weightedMeasure`), and each of finite weighted perimeter.
Cells may be empty or disconnected. -/
@[ext]
structure Cluster (W : E → ℝ) (q : ℕ) where
  /-- The cells `Ω_1, …, Ω_q`. -/
  cell : Fin q → Set E
  /-- Every cell is Lebesgue measurable. -/
  nullMeasurableSet_cell : ∀ i, NullMeasurableSet (cell i) volume
  /-- The cells are pairwise disjoint. -/
  pairwise_disjoint : Pairwise fun i j => Disjoint (cell i) (cell j)
  /-- The cells cover `E` up to a null set. -/
  volume_compl_iUnion : volume (⋃ i, cell i)ᶜ = 0
  /-- Every cell has finite weighted perimeter. -/
  weightedPerimeter_lt_top : ∀ i, weightedPerimeter W ⊤ (cell i) < ⊤

variable {W : E → ℝ} {p q : ℕ}

/-- **A null modification of almost disjoint cells is a cluster.** For an almost everywhere
measurable weight with finite measure, measurable sets `t i` that pairwise meet in null sets, whose
measures add up to `μ(E)` and which have finite weighted perimeters, agree up to null sets with
the cells of a cluster. -/
theorem exists_cluster_ae_eq (hW : AEMeasurable W volume)
    [IsFiniteMeasure (weightedMeasure W)] {t : Fin q → Set E} (ht : ∀ i, MeasurableSet (t i))
    (hdisj : Pairwise fun i j => volume (t i ∩ t j) = 0)
    (hsum : ∑ i, weightedMeasure W (t i) = weightedMeasure W univ)
    (hP : ∀ i, weightedPerimeter W ⊤ (t i) < ⊤) :
    ∃ Ω : Cluster W q, ∀ i, Ω.cell i =ᵐ[volume] t i := by
  -- Measurable, pairwise disjoint sets agreeing with the `t i` up to null sets.
  obtain ⟨u, -, htu, hm, hud⟩ :=
    exists_subordinate_pairwise_disjoint (μ := volume) (fun i => (ht i).nullMeasurableSet) hdisj
  have hae (i : Fin q) : u i =ᵐ[volume] t i := (htu i).symm
  have hμ (i : Fin q) : weightedMeasure W (u i) = weightedMeasure W (t i) :=
    measure_congr (weightedMeasure_absolutelyContinuous.ae_le (hae i))
  -- The union of the cells has full measure.
  have hcov : weightedMeasure W (⋃ i, u i)ᶜ = 0 := by
    rw [measure_compl (.iUnion hm) (measure_ne_top _ _), measure_iUnion hud hm, tsum_fintype]
    simp [hμ, hsum]
  exact ⟨{ cell := u
           nullMeasurableSet_cell := fun i => (hm i).nullMeasurableSet
           pairwise_disjoint := hud
           volume_compl_iUnion := volume_absolutelyContinuous_weightedMeasure hW hcov
           weightedPerimeter_lt_top := fun i => by
             rw [weightedPerimeter_congr_ae (by simpa using hae i)]
             exact hP i }, hae⟩

namespace Cluster

/-- The **total perimeter** `P_μ(Ω) = ½ Σᵢ P_μ(Ω_i)` of a cluster, each interface counted
once. -/
def perimeter (Ω : Cluster W q) : ℝ≥0∞ :=
  (∑ i, weightedPerimeter W ⊤ (Ω.cell i)) / 2

/-- The total perimeter is half the sum of the cell perimeters. -/
theorem perimeter_def (Ω : Cluster W q) :
    Ω.perimeter = (∑ i, weightedPerimeter W ⊤ (Ω.cell i)) / 2 :=
  (rfl)

/-- The total perimeter of a cluster is finite. -/
theorem perimeter_lt_top (Ω : Cluster W q) : Ω.perimeter < ⊤ :=
  ENNReal.div_lt_top (ENNReal.sum_ne_top.2 fun i _ => (Ω.weightedPerimeter_lt_top i).ne)
    two_ne_zero

/-- The measure of a union of cells of a cluster for `μ = e^{−W} · volume` is the sum of their
measures. -/
theorem weightedMeasure_biUnion_cell (Ω : Cluster W q) (t : Finset (Fin q)) :
    weightedMeasure W (⋃ i ∈ t, Ω.cell i) = ∑ i ∈ t, weightedMeasure W (Ω.cell i) :=
  measure_biUnion_finset₀ (fun _ _ _ _ hij => (Ω.pairwise_disjoint hij).aedisjoint)
    fun i _ => (Ω.nullMeasurableSet_cell i).mono_ac weightedMeasure_absolutelyContinuous

/-- **The cell measures add up to `μ(E)`.** The measures of the cells of a cluster for
`μ = e^{−W} · volume` add up to `μ(E)`, so they lie on the probability simplex when `μ(E) = 1`. -/
theorem sum_weightedMeasure_cell (Ω : Cluster W q) :
    ∑ i, weightedMeasure W (Ω.cell i) = weightedMeasure W univ := by
  rw [← Ω.weightedMeasure_biUnion_cell Finset.univ]
  simp only [Finset.mem_univ, iUnion_true]
  exact measure_congr (ae_eq_univ.2 (weightedMeasure_absolutelyContinuous Ω.volume_compl_iUnion))

/-- There are no `0`-clusters: the empty family does not cover `E`. -/
instance instIsEmptyZero : IsEmpty (Cluster W 0) :=
  ⟨fun Ω => NeZero.ne (volume : Measure E) (by simpa using Ω.volume_compl_iUnion)⟩

/-! ### Equivalence -/

/-- Two clusters are **equivalent** when corresponding cells agree up to null sets. -/
def IsEquivalent (Ω Ω' : Cluster W q) : Prop :=
  ∀ i, Ω.cell i =ᵐ[volume] Ω'.cell i

/-- Unfolding the equivalence of clusters. -/
theorem isEquivalent_iff {Ω Ω' : Cluster W q} :
    Ω.IsEquivalent Ω' ↔ ∀ i, Ω.cell i =ᵐ[volume] Ω'.cell i :=
  (Iff.rfl)

/-- Every cluster is equivalent to itself. -/
@[refl]
theorem IsEquivalent.refl (Ω : Cluster W q) : Ω.IsEquivalent Ω :=
  isEquivalent_iff.2 fun _ => .rfl

/-- The equivalence of clusters is symmetric. -/
theorem IsEquivalent.symm {Ω Ω' : Cluster W q} (h : Ω.IsEquivalent Ω') : Ω'.IsEquivalent Ω :=
  isEquivalent_iff.2 fun i => (isEquivalent_iff.1 h i).symm

/-- The equivalence of clusters is transitive. -/
theorem IsEquivalent.trans {Ω Ω' Ω'' : Cluster W q} (h : Ω.IsEquivalent Ω')
    (h' : Ω'.IsEquivalent Ω'') : Ω.IsEquivalent Ω'' :=
  isEquivalent_iff.2 fun i => (isEquivalent_iff.1 h i).trans (isEquivalent_iff.1 h' i)

/-- The equivalence of clusters is an equivalence relation. -/
theorem isEquivalent_equivalence : Equivalence (IsEquivalent (W := W) (q := q)) :=
  ⟨IsEquivalent.refl, IsEquivalent.symm, IsEquivalent.trans⟩

/-- Equivalent clusters have the same total perimeter. -/
theorem IsEquivalent.perimeter_eq {Ω Ω' : Cluster W q} (h : Ω.IsEquivalent Ω') :
    Ω.perimeter = Ω'.perimeter := by
  rw [perimeter_def, perimeter_def]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    weightedPerimeter_congr_ae (by simpa using isEquivalent_iff.1 h i)

/-- Equivalent clusters have the same cell measures. -/
theorem IsEquivalent.weightedMeasure_cell_eq {Ω Ω' : Cluster W q} (h : Ω.IsEquivalent Ω')
    (i : Fin q) : weightedMeasure W (Ω.cell i) = weightedMeasure W (Ω'.cell i) := by
  have hi := ae_eq_set.1 (isEquivalent_iff.1 h i)
  exact measure_congr (ae_eq_set.2 ⟨weightedMeasure_absolutelyContinuous hi.1,
    weightedMeasure_absolutelyContinuous hi.2⟩)

/-! ### Permuting and grouping cells -/

/-- A union of cells of a cluster is null-measurable. -/
theorem nullMeasurableSet_biUnion_cell (Ω : Cluster W q) (t : Finset (Fin q)) :
    NullMeasurableSet (⋃ i ∈ t, Ω.cell i) volume :=
  .biUnion (Finset.countable_toSet t) fun i _ => Ω.nullMeasurableSet_cell i

/-- For a `C¹` weight, the weighted perimeter of a union of cells is at most the sum of their
weighted perimeters. -/
theorem weightedPerimeter_biUnion_cell_le (hW : ContDiff ℝ 1 W) (Ω : Cluster W q)
    (t : Finset (Fin q)) :
    weightedPerimeter W ⊤ (⋃ i ∈ t, Ω.cell i) ≤ ∑ i ∈ t, weightedPerimeter W ⊤ (Ω.cell i) :=
  weightedPerimeter_biUnion_le hW t
    (fun i _ => (Ω.nullMeasurableSet_cell i).mono Measure.restrict_le_self)
    fun _ _ _ _ hij => Ω.pairwise_disjoint hij

/-- For a `C¹` weight, a union of cells of a cluster has finite weighted perimeter. -/
theorem weightedPerimeter_biUnion_cell_lt_top (hW : ContDiff ℝ 1 W) (Ω : Cluster W q)
    (t : Finset (Fin q)) : weightedPerimeter W ⊤ (⋃ i ∈ t, Ω.cell i) < ⊤ :=
  (Ω.weightedPerimeter_biUnion_cell_le hW t).trans_lt
    (ENNReal.sum_lt_top.2 fun i _ => Ω.weightedPerimeter_lt_top i)

/-- The cluster with its cells permuted by `σ`: the `i`-th cell is `Ω_{σ i}`. -/
def permute (Ω : Cluster W q) (σ : Equiv.Perm (Fin q)) : Cluster W q where
  cell i := Ω.cell (σ i)
  nullMeasurableSet_cell i := Ω.nullMeasurableSet_cell (σ i)
  pairwise_disjoint _ _ h := Ω.pairwise_disjoint (σ.injective.ne h)
  volume_compl_iUnion := by
    rw [σ.surjective.iUnion_comp Ω.cell]
    exact Ω.volume_compl_iUnion
  weightedPerimeter_lt_top i := Ω.weightedPerimeter_lt_top (σ i)

/-- The cells of a permuted cluster. -/
@[simp]
theorem permute_cell (Ω : Cluster W q) (σ : Equiv.Perm (Fin q)) (i : Fin q) :
    (Ω.permute σ).cell i = Ω.cell (σ i) :=
  (rfl)

/-- Permuting the cells does not change the total perimeter. -/
@[simp]
theorem perimeter_permute (Ω : Cluster W q) (σ : Equiv.Perm (Fin q)) :
    (Ω.permute σ).perimeter = Ω.perimeter := by
  simp only [perimeter_def, permute_cell]
  rw [Equiv.sum_comp σ (fun i => weightedPerimeter W ⊤ (Ω.cell i))]

/-- **Grouping cells.** For a `C¹` weight and a map `f : Fin q → Fin p`, the `p`-cluster whose
`k`-th cell is the union of the cells `Ω_i` with `f i = k`. Merging two cells is the case of a map
identifying two indices. -/
def coarsen (hW : ContDiff ℝ 1 W) (Ω : Cluster W q) (f : Fin q → Fin p) : Cluster W p where
  cell k := ⋃ i ∈ Finset.univ.filter (f · = k), Ω.cell i
  nullMeasurableSet_cell _ := Ω.nullMeasurableSet_biUnion_cell _
  pairwise_disjoint k l hkl := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, disjoint_iUnion_left,
      disjoint_iUnion_right]
    rintro i rfl j rfl
    exact Ω.pairwise_disjoint fun h => hkl (h ▸ rfl)
  volume_compl_iUnion := by
    have : (⋃ k, ⋃ i ∈ Finset.univ.filter (f · = k), Ω.cell i) = ⋃ i, Ω.cell i := by
      ext x
      simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
      exact ⟨fun ⟨_, i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨f i, i, rfl, hx⟩⟩
    rw [this]
    exact Ω.volume_compl_iUnion
  weightedPerimeter_lt_top _ := Ω.weightedPerimeter_biUnion_cell_lt_top hW _

/-- The cells of a grouped cluster. -/
@[simp]
theorem coarsen_cell (hW : ContDiff ℝ 1 W) (Ω : Cluster W q) (f : Fin q → Fin p) (k : Fin p) :
    (Ω.coarsen hW f).cell k = ⋃ i ∈ Finset.univ.filter (f · = k), Ω.cell i :=
  (rfl)

/-- Grouping cells does not increase the total perimeter. -/
theorem perimeter_coarsen_le (hW : ContDiff ℝ 1 W) (Ω : Cluster W q) (f : Fin q → Fin p) :
    (Ω.coarsen hW f).perimeter ≤ Ω.perimeter := by
  rw [perimeter_def, perimeter_def]
  gcongr
  calc ∑ k, weightedPerimeter W ⊤ ((Ω.coarsen hW f).cell k)
      ≤ ∑ k, ∑ i ∈ Finset.univ.filter (f · = k), weightedPerimeter W ⊤ (Ω.cell i) :=
        Finset.sum_le_sum fun _ _ => Ω.weightedPerimeter_biUnion_cell_le hW _
    _ = ∑ i, weightedPerimeter W ⊤ (Ω.cell i) := Finset.sum_fiberwise _ f _

/-! ### One and two cells -/

/-- For a `C¹` weight, the whole space is a `1`-cluster. -/
def univ (hW : ContDiff ℝ 1 W) : Cluster W 1 where
  cell _ := Set.univ
  nullMeasurableSet_cell _ := .univ
  pairwise_disjoint i j h := (h (Subsingleton.elim i j)).elim
  volume_compl_iUnion := by rw [iUnion_const, compl_univ, measure_empty]
  weightedPerimeter_lt_top _ := by simp [weightedPerimeter_univ hW]

/-- The cell of the whole-space `1`-cluster. -/
@[simp]
theorem univ_cell (hW : ContDiff ℝ 1 W) (i : Fin 1) : (Cluster.univ hW).cell i = Set.univ :=
  (rfl)

/-- The cell of a `1`-cluster is the whole space up to a null set. -/
theorem cell_ae_eq_univ (Ω : Cluster W 1) (i : Fin 1) : Ω.cell i =ᵐ[volume] Set.univ := by
  have h : (⋃ j, Ω.cell j) = Ω.cell i := by
    ext x
    simp [Fin.exists_fin_one, Subsingleton.elim i 0]
  exact ae_eq_univ.2 (h ▸ Ω.volume_compl_iUnion)

/-- Up to equivalence, the only `1`-cluster is the whole space. -/
theorem isEquivalent_univ (hW : ContDiff ℝ 1 W) (Ω : Cluster W 1) :
    Ω.IsEquivalent (Cluster.univ hW) :=
  isEquivalent_iff.2 Ω.cell_ae_eq_univ

/-- For a `C¹` weight, every `1`-cluster has total perimeter `0`. -/
theorem perimeter_eq_zero_of_one (hW : ContDiff ℝ 1 W) (Ω : Cluster W 1) : Ω.perimeter = 0 := by
  rw [(Ω.isEquivalent_univ hW).perimeter_eq, perimeter_def]
  simp [weightedPerimeter_univ hW]

/-- The second cell of a `2`-cluster is the complement of the first up to a null set. -/
theorem cell_one_ae_eq_compl (Ω : Cluster W 2) : Ω.cell 1 =ᵐ[volume] (Ω.cell 0)ᶜ := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · rw [sdiff_compl, (Ω.pairwise_disjoint (by decide : (1 : Fin 2) ≠ 0)).inter_eq, measure_empty]
  · refine measure_mono_null (fun x hx => ?_) Ω.volume_compl_iUnion
    simp only [mem_compl_iff, mem_iUnion, not_exists, Fin.forall_fin_two]
    exact ⟨hx.1, hx.2⟩

/-- For a `C¹` weight, the two cells of a `2`-cluster have the same weighted perimeter. -/
theorem weightedPerimeter_cell_one (hW : ContDiff ℝ 1 W) (Ω : Cluster W 2) :
    weightedPerimeter W ⊤ (Ω.cell 1) = weightedPerimeter W ⊤ (Ω.cell 0) := by
  rw [weightedPerimeter_congr_ae (by simpa using Ω.cell_one_ae_eq_compl),
    weightedPerimeter_compl hW]

/-- For a `C¹` weight, a `2`-cluster has total perimeter `P_μ(Ω_1) = P_μ(Ω_2)`. -/
theorem perimeter_eq_weightedPerimeter_cell_zero (hW : ContDiff ℝ 1 W) (Ω : Cluster W 2) :
    Ω.perimeter = weightedPerimeter W ⊤ (Ω.cell 0) := by
  rw [perimeter_def, Fin.sum_univ_two, Ω.weightedPerimeter_cell_one hW, ← two_mul, mul_comm,
    ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

/-! ### Linear isometries -/

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']

/-- The image of a cluster for `W` under a linear isometry equivalence `e : E ≃ E'` is a cluster
for the transported weight `W' = W ∘ e⁻¹`, given here through `W' ∘ e = W`. For the Gaussian
weight, `Ω.map e e.gaussianWeight_comp` carries Gaussian clusters to Gaussian clusters. -/
def map (e : E ≃ₗᵢ[ℝ] E') {W' : E' → ℝ} (hW' : W' ∘ e = W) (Ω : Cluster W q) :
    Cluster W' q where
  cell i := e '' Ω.cell i
  nullMeasurableSet_cell i := by
    rw [e.image_eq_preimage_symm]
    exact (Ω.nullMeasurableSet_cell i).preimage e.symm.measurePreserving.quasiMeasurePreserving
  pairwise_disjoint _ _ h := (disjoint_image_iff e.injective).2 (Ω.pairwise_disjoint h)
  volume_compl_iUnion := by
    rw [← image_iUnion, e.image_eq_preimage_symm, ← preimage_compl,
      e.symm.measurePreserving.measure_preimage
        (NullMeasurableSet.iUnion Ω.nullMeasurableSet_cell).compl]
    exact Ω.volume_compl_iUnion
  weightedPerimeter_lt_top i :=
    (e.weightedPerimeter_top_image_of_comp_eq hW' _).trans_lt (Ω.weightedPerimeter_lt_top i)

/-- The cells of the image of a cluster. -/
@[simp]
theorem map_cell (e : E ≃ₗᵢ[ℝ] E') {W' : E' → ℝ} (hW' : W' ∘ e = W) (Ω : Cluster W q)
    (i : Fin q) : (Ω.map e hW').cell i = e '' Ω.cell i :=
  (rfl)

/-- A linear isometry equivalence preserves the total perimeter of a cluster. -/
@[simp]
theorem perimeter_map (e : E ≃ₗᵢ[ℝ] E') {W' : E' → ℝ} (hW' : W' ∘ e = W) (Ω : Cluster W q) :
    (Ω.map e hW').perimeter = Ω.perimeter := by
  simp only [perimeter_def, map_cell, e.weightedPerimeter_top_image_of_comp_eq hW']

end Cluster

end TauCeti
