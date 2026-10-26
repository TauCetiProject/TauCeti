/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.OpenCell
public import Mathlib.Topology.DiscreteSubset

/-!
# Closure finiteness for categorical relative CW complexes

The boundary of each cell of a categorical relative CW complex is contained in the base together
with finitely many closed cells of strictly smaller dimension. No separation condition on the
base is needed. This gives the closure-finiteness condition used when reading a classical relative
CW structure from the categorical cell attachments.

We first show that a compact subset of a finite stage is covered by the base and finitely many
closed cells. The argument selects one point in each open cell it meets: at a single attachment,
every subset of the selected points is closed, since its preimage in any attached disk has at most
one point. The resulting compact discrete set is finite.

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.1.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

open CategoryTheory Limits Topology
open HomotopicalAlgebra.RelativeCellComplex

universe u

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)

private lemma cell_boundary_mem_range (n : ℕ) (i : (c.attachCells n (not_isMax n)).ι)
    (z : 𝔻 n) (hz : z ∈ Set.range (diskBoundaryInclusion n)) :
    (c.attachCells n (not_isMax n)).cell i z ∈
      Set.range (c.F.map (homOfLE (Order.le_succ n))) := by
  obtain ⟨z, rfl⟩ := hz
  let a := c.attachCells n (not_isMax n)
  refine ⟨a.g₁ (a.cofan₁.inj i z), ?_⟩
  have h := congrArg (fun g ↦ g z) (a.hm i)
  have hw := ConcreteCategory.congr_hom a.isPushout.w (a.cofan₁.inj i z)
  simpa only [ConcreteCategory.comp_apply, HomotopicalAlgebra.AttachCells.cell_def] using
    hw.trans (congrArg a.g₂ h)

private theorem finite_setOf_nonempty_inter_image_cell (n : ℕ)
    {K : Set (c.F.obj (Order.succ n))} (hK : IsCompact K) :
    {i : (c.attachCells n (not_isMax n)).ι |
      (K ∩ (c.attachCells n (not_isMax n)).cell i ''
        (Set.range (diskBoundaryInclusion n))ᶜ).Nonempty}.Finite := by
  classical
  let a := c.attachCells n (not_isMax n)
  let A := {i : a.ι | (K ∩ a.cell i '' (Set.range (diskBoundaryInclusion n))ᶜ).Nonempty}
  choose x hx using fun i : A ↦ i.2
  have hxK (i : A) : x i ∈ K := (hx i).1
  have hxO (i : A) : x i ∈ a.cell i.1 '' (Set.range (diskBoundaryInclusion n))ᶜ :=
    (hx i).2
  have hxout (i : A) : x i ∉ Set.range (c.F.map (homOfLE (Order.le_succ n))) := by
    exact a.compl_range_eq_iUnion_image_cell.symm.subset
      (Set.mem_iUnion_of_mem i.1 (hxO i))
  have hxinj : Function.Injective x := by
    intro i j hij
    by_contra h
    exact (a.disjoint_image_cell (Subtype.val_injective.ne h)).ne_of_mem (hxO i) (hxO j) hij
  -- Every subset of the selected points is closed: its old-stage preimage is empty,
  -- and its preimage in each attached disk has at most one point.
  have hclosed (S : Set (c.F.obj (Order.succ n))) (hS : S ⊆ Set.range x) : IsClosed S := by
    have hpre (i : a.ι) : (a.cell i ⁻¹' S).Subsingleton := by
      intro z hz z' hz'
      obtain ⟨j, hj⟩ := hS hz
      obtain ⟨j', hj'⟩ := hS hz'
      have hzi : z ∈ (Set.range (diskBoundaryInclusion n))ᶜ := by
        intro h
        exact hxout j (hj ▸ c.cell_boundary_mem_range n i z h)
      have hz'i : z' ∈ (Set.range (diskBoundaryInclusion n))ᶜ := by
        intro h
        exact hxout j' (hj' ▸ c.cell_boundary_mem_range n i z' h)
      have hij : i = j.1 := by
        by_contra h
        exact Set.disjoint_left.1 (a.disjoint_image_cell h) ⟨z, hzi, rfl⟩ (hj ▸ hxO j)
      have hij' : i = j'.1 := by
        by_contra h
        exact Set.disjoint_left.1 (a.disjoint_image_cell h) ⟨z', hz'i, rfl⟩ (hj' ▸ hxO j')
      have hjj' : j = j' := Subtype.ext (hij.symm.trans hij')
      have heq : a.cell i z = a.cell i z' := hj.symm.trans (hjj' ▸ hj')
      have hzz' : (⟨z, hzi⟩ : ↥((Set.range (diskBoundaryInclusion n))ᶜ)) = ⟨z', hz'i⟩ :=
        (a.isOpenEmbedding_domRestrict_cell
          (fun _ ↦ (TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion n).isClosed_range)
          i).injective heq
      exact congrArg Subtype.val hzz'
    refine (TauCeti.TopCat.isClosed_iff_of_isPushout a.isPushout S).2 ⟨?_, ?_⟩
    · have hempty : c.F.map (homOfLE (Order.le_succ n)) ⁻¹' S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro z hz
        obtain ⟨i, hi⟩ := hS hz
        exact hxout i ⟨z, hi.symm⟩
      rw [hempty]
      exact isClosed_empty
    · refine (TopCat.isClosed_iff_of_isColimit _ a.isColimit₂ _).2 ?_
      rintro ⟨i⟩
      exact (hpre i).finite.isClosed
  -- The selected points form a compact discrete subspace, hence a finite set.
  have hc : IsClosed (Set.range x) := hclosed _ subset_rfl
  have hd : IsDiscrete (Set.range x) :=
    isDiscrete_iff_forall_mem_exists_isClosed.2 fun S hS ↦
      ⟨S, hclosed S hS, Set.inter_eq_left.2 hS⟩
  have hk : IsCompact (Set.range x) :=
    hK.of_isClosed_subset hc (by rintro _ ⟨i, rfl⟩; exact hxK i)
  have : Finite A := (Set.finite_range_iff hxinj).1 (hk.finite hd)
  exact Set.toFinite A

/-- A compact subset of a finite stage is covered by the base and finitely many closed cells
of dimension below that stage. The base space need not satisfy any separation axiom. -/
theorem exists_finite_cells_of_isCompact {K : Set Y} (hK : IsCompact K) (n : ℕ)
    (hKn : K ⊆ Set.range (c.incl.app n)) :
    ∃ s : Finset c.Cells, (∀ γ ∈ s, γ.j < n) ∧
      K ⊆ Set.range f ∪ ⋃ γ ∈ s, Set.range γ.ι := by
  classical
  induction n generalizing K with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    have h0 := c.range_incl_app_eq_union_iUnion_range_cells_ι 0
    simp only [Nat.not_lt_zero, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] at h0
    simpa using h0 ▸ hKn
  | succ n ih =>
    let a := c.attachCells n (not_isMax n)
    let K' := c.incl.app (Order.succ n) ⁻¹' K
    have hK' : IsCompact K' := (c.isClosedEmbedding_incl_app _).isCompact_preimage hK
    let I := {i : a.ι | (K' ∩ a.cell i '' (Set.range (diskBoundaryInclusion n))ᶜ).Nonempty}
    have hI : I.Finite := c.finite_setOf_nonempty_inter_image_cell n hK'
    have hK0 : IsCompact (K ∩ Set.range (c.incl.app n)) :=
      hK.inter_right (c.isClosedEmbedding_incl_app n).isClosed_range
    obtain ⟨s, hs, hKs⟩ := ih hK0 Set.inter_subset_right
    let cell (i : a.ι) : c.Cells := ⟨n, not_isMax n, i⟩
    refine ⟨s ∪ hI.toFinset.image cell, ?_, ?_⟩
    · intro γ hγ
      rcases Finset.mem_union.1 hγ with hγ | hγ
      · exact Nat.lt_succ_of_lt (hs γ hγ)
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hγ
        exact Nat.lt_succ_self n
    · intro y hy
      by_cases hyo : y ∈ Set.range (c.incl.app n)
      · rcases hKs ⟨hy, hyo⟩ with hyf | hys
        · exact Or.inl hyf
        · exact Or.inr (Set.iUnion₂_subset
            (fun γ hγ ↦ Set.subset_iUnion₂_of_subset γ (Finset.mem_union_left _ hγ) subset_rfl) hys)
      · obtain ⟨z, rfl⟩ := hKn hy
        have hz : z ∉ Set.range (c.F.map (homOfLE (Order.le_succ n))) := by
          rintro ⟨w, rfl⟩
          apply hyo
          refine ⟨w, ?_⟩
          exact (ConcreteCategory.congr_hom (c.incl.naturality
            (homOfLE (Order.le_succ n))) w).symm
        obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.1
          (a.compl_range_eq_iUnion_image_cell.subset hz)
        have hi : i ∈ hI.toFinset := hI.mem_toFinset.2 ⟨_, hy, ⟨w, hw, rfl⟩⟩
        refine Or.inr (Set.mem_iUnion₂_of_mem (i := cell i)
          (Finset.mem_union_right _ (Finset.mem_image_of_mem cell hi)) ?_)
        exact ⟨w, rfl⟩

/-- The boundary of a cell in a categorical relative CW complex lies in the base and finitely
many closed cells of strictly smaller dimension. No separation hypothesis is required. -/
theorem exists_finite_cells_boundary (γ : c.Cells) :
    ∃ s : Finset c.Cells, (∀ δ ∈ s, δ.j < γ.j) ∧
      Set.range (diskBoundaryInclusion γ.j ≫ γ.ι) ⊆
        Set.range f ∪ ⋃ δ ∈ s, Set.range δ.ι := by
  have hK : IsCompact (Set.range (diskBoundaryInclusion γ.j ≫ γ.ι)) :=
    isCompact_range (diskBoundaryInclusion γ.j ≫ γ.ι).hom.continuous
  apply c.exists_finite_cells_of_isCompact hK γ.j
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := c.cell_boundary_mem_range γ.j γ.k
    (diskBoundaryInclusion γ.j z) ⟨z, rfl⟩
  refine ⟨w, ?_⟩
  have h := ConcreteCategory.congr_hom
    (c.incl.naturality (homOfLE (Order.le_succ γ.j))) w
  exact h.symm.trans (congrArg (c.incl.app (Order.succ γ.j)) hw)

end TopCat.RelativeCWComplex
