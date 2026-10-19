/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Basic
public import TauCeti.Topology.Connected.Basic
public import TauCeti.Topology.Order.FiniteFamily

/-!
# Partitions of a cylinder into sections and sectors

A stack over a base `X` is given by a single ordered list of functions `θ₀ < ⋯ < θₖ₋₁`, and its
cells are their graphs and the open bands between consecutive graphs. A cell-by-cell description
is weaker a priori: each cell of a partition of `X × ℝ` might be a graph or a band of its own
stack, with no common list of functions. Over a preconnected base the two descriptions agree.
If finitely many pairwise disjoint sets cover `X × ℝ`, and each is a section or a sector of some
continuous, strictly ordered real stack, then together they are exactly the sections and sectors
of one such stack.

The graphs in the partition have pairwise distinct values everywhere, so over a preconnected base
they are strictly ordered by their values at any single point. They form the common stack. Every
other cell is open, preconnected and nonempty, misses all the graphs, and so lies in one sector
of the common stack. That sector is preconnected and covered by the open cells of the partition,
so it is exactly that cell.

This is the comparison between the cell-wise definition of a cylindrical algebraic decomposition
(each cell is a graph or a band over a lower cell) and the stack-wise one.

## Main declarations

* `IsPreconnected.exists_subset_sectorSet`: a preconnected set missing every section of a
  continuous ordered stack lies in a single sector.
* `TauCeti.exists_eq_range_sectionSet_union_range_sectorSet`: a finite partition of the cylinder
  over a nonempty preconnected base into sections and sectors of continuous, strictly ordered
  real stacks consists of the sections and sectors of a single such stack.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Definition 5.1.
-/

public section

open Function Set TauCeti

variable {X α : Type*} [TopologicalSpace X] {k : ℕ}

/-- A preconnected subset of the cylinder `X × α` that misses every section of a stack of
continuous, pointwise monotone functions lies in a single sector of the stack. -/
theorem IsPreconnected.exists_subset_sectorSet [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {s : Set (X × α)} (hs : IsPreconnected s) {θ : Fin k → X → α}
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ x, Monotone fun i ↦ θ i x)
    (hsec : ∀ i, Disjoint (sectionSet θ i) s) : ∃ j, s ⊆ sectorSet θ j := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · exact ⟨0, empty_subset _⟩
  have hsub : s ⊆ ⋃ j, sectorSet θ j := fun w hw ↦ by
    have hw' : w ∈ (⋃ i, sectionSet θ i) ∪ ⋃ j, sectorSet θ j := by
      rw [iUnion_sectionSet_union_iUnion_sectorSet hθ]
      exact mem_univ w
    refine hw'.resolve_left fun h ↦ ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (hsec i) hi hw
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hsub hz)
  exact ⟨j, hs.subset_of_subset_iUnion (isOpen_sectorSet hc) (pairwise_disjoint_sectorSet θ) hsub
    ⟨z, hz, hj⟩⟩

namespace TauCeti

/-- **One stack from a partition into stack cells.** Let `𝒜` be a finite set of pairwise
disjoint subsets of `X × ℝ` covering it, over a nonempty preconnected base `X`. If each member of
`𝒜` is a section or a sector of some stack of continuous, pointwise strictly ordered real
functions on `X`, then `𝒜` is exactly the set of sections and sectors of a single such stack. -/
theorem exists_eq_range_sectionSet_union_range_sectorSet [PreconnectedSpace X] [Nonempty X]
    {𝒜 : Set (Set (X × ℝ))} (hfin : 𝒜.Finite) (hdisj : 𝒜.PairwiseDisjoint id)
    (hcover : ⋃₀ 𝒜 = univ)
    (hcell : ∀ A ∈ 𝒜, ∃ k, ∃ θ : Fin k → X → ℝ, (∀ i, Continuous (θ i)) ∧
      (∀ x, StrictMono fun i ↦ θ i x) ∧ A ∈ range (sectionSet θ) ∪ range (sectorSet θ)) :
    ∃ k, ∃ θ : Fin k → X → ℝ, (∀ i, Continuous (θ i)) ∧ (∀ x, StrictMono fun i ↦ θ i x) ∧
      𝒜 = range (sectionSet θ) ∪ range (sectorSet θ) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hgraph {k : ℕ} (θ : Fin k → X → ℝ) (i : Fin k) : sectionSet θ i = (θ i).graph := by
    ext ⟨x, t⟩
    simp
  -- The continuous functions whose graphs are cells are pointwise distinct, so they form the
  -- common stack.
  set G := {g : X → ℝ | Continuous g ∧ g.graph ∈ 𝒜}
  obtain ⟨k, θ, hθG, hθ⟩ := exists_strictMono_range_eq (G := G)
    (hfin.preimage graph_injective.injOn |>.subset fun _ hg ↦ hg.2) (fun _ hg ↦ hg.1)
    fun f hf g hg hfg x hx ↦ hfg <| graph_injective <| hdisj.elim hf.2 hg.2 <|
      not_disjoint_iff.2 ⟨(x, f x), by simp, by simp [hx]⟩
  have hc (i : Fin k) : Continuous (θ i) := (hθG ▸ mem_range_self i : θ i ∈ G).1
  have hsection : range (sectionSet θ) = {A ∈ 𝒜 | ∃ g : X → ℝ, Continuous g ∧ A = g.graph} := by
    ext A
    refine ⟨?_, fun ⟨hA, g, hg, hAg⟩ ↦ ?_⟩
    · rintro ⟨i, rfl⟩
      have hi : θ i ∈ G := hθG ▸ mem_range_self i
      exact ⟨hgraph θ i ▸ hi.2, θ i, hi.1, hgraph θ i⟩
    · obtain ⟨i, hi⟩ : g ∈ range θ := hθG ▸ ⟨hg, hAg ▸ hA⟩
      exact ⟨i, by rw [hAg, ← hi, hgraph]⟩
  -- A cell that is not a graph is a sector of its own stack, hence open and preconnected.
  have hsector (A : Set (X × ℝ)) (hA : A ∈ 𝒜) (hAS : A ∉ range (sectionSet θ)) :
      IsOpen A ∧ IsPreconnected A := by
    obtain ⟨k', θ', hc', hθ', ⟨i, rfl⟩ | ⟨j, rfl⟩⟩ := hcell A hA
    · exact absurd (hsection ▸ ⟨hA, θ' i, hc' i, hgraph θ' i⟩) hAS
    · exact ⟨isOpen_sectorSet hc' j, isPreconnected_sectorSet hc' hθ' j⟩
  -- A point of a sector of the common stack lies in a cell that is not a graph.
  have hmem {w : X × ℝ} {j : Fin (k + 1)} (hw : w ∈ sectorSet θ j) :
      ∃ B ∈ 𝒜, B ∉ range (sectionSet θ) ∧ w ∈ B := by
    obtain ⟨B, hB, hwB⟩ := mem_sUnion.1 (hcover ▸ mem_univ w)
    refine ⟨B, hB, ?_, hwB⟩
    rintro ⟨i, rfl⟩
    exact disjoint_left.1 (disjoint_sectionSet_sectorSet θ i j) hwB hw
  -- A cell that is not a graph is exactly one sector of the common stack.
  have hcellSector (B : Set (X × ℝ)) (hB : B ∈ 𝒜) (hBS : B ∉ range (sectionSet θ))
      (hBne : B.Nonempty) : ∃ j, sectorSet θ j = B := by
    obtain ⟨hBo, hBc⟩ := hsector B hB hBS
    obtain ⟨j, hj⟩ := hBc.exists_subset_sectorSet hc (fun x ↦ (hθ x).monotone) fun i ↦
      hdisj (hsection ▸ mem_range_self i).1 hB fun h ↦ hBS (h ▸ mem_range_self i)
    refine ⟨j, Subset.antisymm ?_ hj⟩
    -- The preconnected sector `j` is covered by the open cells that are not graphs.
    let 𝒪 := {C | C ∈ 𝒜 ∧ C ∉ range (sectionSet θ)}
    refine (isPreconnected_sectorSet hc hθ j).subset_of_subset_iUnion (u := ((↑) : 𝒪 → _))
      (i := ⟨B, hB, hBS⟩) (fun C ↦ (hsector C C.2.1 C.2.2).1)
      (fun C C' hCC' ↦ hdisj C.2.1 C'.2.1 (Subtype.coe_injective.ne hCC')) (fun w hw ↦ ?_)
      (hBne.mono fun w hw ↦ ⟨hj hw, hw⟩)
    obtain ⟨C, hC, hCS, hwC⟩ := hmem hw
    exact mem_iUnion.2 ⟨⟨C, hC, hCS⟩, hwC⟩
  refine ⟨k, θ, hc, hθ, Subset.antisymm (fun B hB ↦ ?_) (union_subset ?_ ?_)⟩
  · by_cases hBS : B ∈ range (sectionSet θ)
    · exact Or.inl hBS
    · rcases B.eq_empty_or_nonempty with rfl | hBne
      · -- The empty set is not a cell, since sectors are nonempty.
        obtain ⟨k', θ', -, hθ', ⟨i, hi⟩ | ⟨j, hj⟩⟩ := hcell ∅ hB
        · exact absurd hi (nonempty_of_mem (mem_sectionSet.2 rfl :
            (x₀, θ' i x₀) ∈ sectionSet θ' i)).ne_empty
        · obtain ⟨z, hz, -⟩ : x₀ ∈ Prod.fst '' sectorSet θ' j := by
            rw [fst_image_sectorSet hθ' j]
            exact mem_univ x₀
          exact absurd hj (nonempty_of_mem hz).ne_empty
      · exact Or.inr (hcellSector B hB hBS hBne)
  · exact hsection.trans_subset (sep_subset _ _)
  · rintro _ ⟨j, rfl⟩
    obtain ⟨w, hw, -⟩ : x₀ ∈ Prod.fst '' sectorSet θ j := by
      rw [fst_image_sectorSet hθ j]
      exact mem_univ x₀
    obtain ⟨B, hB, hBS, hwB⟩ := hmem hw
    obtain ⟨j', rfl⟩ := hcellSector B hB hBS ⟨w, hwB⟩
    rwa [pairwise_disjoint_sectorSet θ |>.eq (not_disjoint_iff.2 ⟨w, hwB, hw⟩)] at hB

end TauCeti
