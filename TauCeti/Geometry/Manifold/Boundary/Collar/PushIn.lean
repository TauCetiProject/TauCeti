/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation
public import TauCeti.Geometry.Manifold.Boundary.Collar.Retraction

/-!
# Compact sets off a collared boundary, and embeddings onto its complement

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`) in a Hausdorff space `M`,
with compact boundary parameter space `N`, as for the boundary of a compact manifold with boundary
or with corners. The collar of depth at most `t < 1` is then compact
(`TauCeti.IsCollar.isCompact_image_le`), and a compact set missing the boundary `f(N)` misses the
collar of some positive depth (`TauCeti.IsCollar.exists_disjoint_collarPart`).

The inclusion of the complement of the boundary is a homotopy equivalence
(`TauCeti.IsCollar.complHomotopyEquiv`), and so is every embedding with image the complement of
the boundary (`TauCeti.IsCollar.homotopyEquivOfRangeEq`): the interior of a compact manifold
with boundary is homotopy equivalent to the manifold. This is how the homology of a compact
manifold with collared boundary is read in its interior, as in Lefschetz duality.

## Main definitions

* `TauCeti.IsCollar.homotopyEquivOfRangeEq`: an embedding onto `M ∖ f(N)` as a homotopy
  equivalence.

## Main results

* `TauCeti.IsCollar.exists_disjoint_collarPart`: a compact set missing the boundary misses the
  collar of some positive depth.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, proof of
  Theorem 3.43, where the collar identifies a compact manifold with boundary with its interior up
  to homotopy.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

namespace IsCollar

variable (hc : IsCollar f c)
include hc

/-- **A compact set missing the boundary misses the collar of some positive depth.** -/
lemma exists_disjoint_collarPart [CompactSpace N] [T2Space M] {S : Set M} (hS : IsCompact S)
    (hSf : Disjoint S (range f)) : ∃ t, 0 < t ∧ Disjoint S (collarPart c t) := by
  -- The complements of the collars of depth at most `s ∈ (0, 1)` form a directed open cover of
  -- the complement of the boundary.
  let U : Ioo (0 : ℝ) 1 → Set M := fun s ↦ (c '' {p | (p.2 : ℝ) ≤ s})ᶜ
  have hU (s : Ioo (0 : ℝ) 1) : IsOpen (U s) :=
    (hc.isCompact_image_le s.property.2).isClosed.isOpen_compl
  have hmono {s s' : Ioo (0 : ℝ) 1} (h : (s : ℝ) ≤ s') : U s' ⊆ U s :=
    compl_subset_compl.2 (image_mono fun _ hp ↦ le_trans hp h)
  have hdir : Directed (· ⊆ ·) U := fun s s' ↦
    ⟨⟨min s s', lt_min s.property.1 s'.property.1,
        (min_le_left _ _).trans_lt s.property.2⟩,
      hmono (min_le_left _ _), hmono (min_le_right _ _)⟩
  have hcover : S ⊆ ⋃ s, U s := by
    intro x hx
    rw [mem_iUnion]
    by_cases hxc : x ∈ range c
    · obtain ⟨q, rfl⟩ := hxc
      have hq : 0 < (q.2 : ℝ) := lt_of_le_of_ne q.2.property.1 fun h ↦
        hSf.notMem_of_mem_left hx ((hc.apply_mem_range_iff).2 h.symm)
      refine ⟨⟨q.2 / 2, half_pos hq, by linarith [q.2.property.2]⟩, ?_⟩
      rintro ⟨p, hp, hpq⟩
      rw [hc.isOpenEmbedding.injective hpq] at hp
      exact absurd hp (not_le.2 (half_lt_self hq))
    · exact ⟨⟨1 / 2, by norm_num, by norm_num⟩, fun ⟨p, _, hp⟩ ↦ hxc ⟨p, hp⟩⟩
  have : Nonempty (Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨s, hs⟩ := hS.elim_directed_cover U hU hcover hdir
  refine ⟨s, s.property.1, disjoint_left.2 fun x hx hxc ↦ ?_⟩
  obtain ⟨p, hp, rfl⟩ := mem_collarPart_iff.1 hxc
  exact hs hx ⟨p, hp.le, rfl⟩

variable [CompactSpace N] [T2Space M]

/-- **An embedding onto the complement of a collared boundary is a homotopy equivalence**, for a
compact boundary parameter space in a Hausdorff space: the interior of a compact manifold with
collared boundary is homotopy equivalent to the manifold. -/
def homotopyEquivOfRangeEq {P : Type*} [TopologicalSpace P] {ι : P → M} (hι : IsEmbedding ι)
    (hιf : range ι = (range f)ᶜ) : ContinuousMap.HomotopyEquiv P M :=
  ((hι.toHomeomorph.trans (Homeomorph.setCongr hιf)).toHomotopyEquiv).trans hc.complHomotopyEquiv

/-- The homotopy equivalence of an embedding onto the complement of the boundary is the
embedding. -/
@[simp]
lemma coe_homotopyEquivOfRangeEq {P : Type*} [TopologicalSpace P] {ι : P → M}
    (hι : IsEmbedding ι) (hιf : range ι = (range f)ᶜ) :
    ⇑(hc.homotopyEquivOfRangeEq hι hιf) = ι := by
  rw [homotopyEquivOfRangeEq]
  exact funext fun x ↦ congrFun hc.coe_complHomotopyEquiv _

end IsCollar

end TauCeti
