/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Slices of proper actions of discrete groups

Let a discrete group `G` act properly on a topological space `X`, in the sense of Mathlib's
`ProperSMul`: the map `(g, y) ↦ (g • y, y)` is proper. This file constructs the local model of the
action near a point `x`: arbitrarily small open neighbourhoods `U` of `x`, invariant under the
stabilizer of `x`, such that every element of `G` carrying a point of `U` into `U` fixes `x`
(`ProperSMul.exists_slice`). Such a `U` is a slice at `x` for the stabilizer, so near the orbit of
`x` the quotient `[X/G]` is the finite quotient `[U/G_x]`. The stabilizer keeps every element
fixing `x`, including those acting trivially on all of `U`.

Two facts make this work. First, a proper action of a discrete group is properly discontinuous
(`ProperSMul.properlyDiscontinuousSMul`), so stabilizers are finite. Second, properness excludes
all other group elements near `(x, x)`: the image of the closed set of pairs `(g, y)` with
`g • x ≠ x` under the closed map `(g, y) ↦ (g • y, y)` is closed and misses `(x, x)`, so some
neighbourhood `U` of `x` has no such `g` moving a point of `U` into `U`
(`ProperSMul.exists_nhds_image_smul_eq_self`). Intersecting the translates of a smaller open
neighbourhood by the finitely many elements of the stabilizer makes it invariant.

Mathlib proves the properly discontinuous version
`ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self` for locally compact Hausdorff spaces,
and the equivalence `properlyDiscontinuousSMul_iff_properSMul` for Hausdorff spaces whose square
is compactly coherent. The statements here assume neither: properness is used directly.

## Main results

* `ProperSMul.properlyDiscontinuousSMul`: a proper action of a discrete group is properly
  discontinuous.
* `ProperSMul.exists_nhds_image_smul_eq_self`: some neighbourhood of `x` is moved into itself
  only by elements fixing `x`.
* `ProperSMul.exists_slice`: every neighbourhood of `x` contains an open slice at `x` for its
  stabilizer.

## References

* R. S. Palais, *On the existence of slices for actions of non-compact Lie groups*, Ann. of
  Math. 73 (1961), 295--323, for slices of proper actions.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2, for the local isotropy
  model of a proper étale groupoid.
-/

public section

open Set Filter Topology MulAction
open scoped Pointwise

namespace ProperSMul

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace X] [ProperSMul G X]

variable (G X) in
/-- A proper action of a discrete group is properly discontinuous: only finitely many elements
move a compact set to meet another. -/
theorem properlyDiscontinuousSMul : ProperlyDiscontinuousSMul G X :=
  properlyDiscontinuousSMul_iff.mpr fun hK hL =>
    (ProperSMul.isCompact_setOfPred_inter_nonempty hK hL).finite_of_discrete

variable (G) in
/-- For a proper action of a discrete group, some neighbourhood `U` of `x` is moved to meet itself
only by elements fixing `x`. No local compactness or separation of `X` is needed. -/
theorem exists_nhds_image_smul_eq_self (x : X) :
    ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g • x = x := by
  let Φ : G × X → X × X := fun p => (p.1 • p.2, p.2)
  have hΦ : IsClosedMap Φ := (ProperSMul.isProperMap_smul_pair (G := G) (X := X)).isClosedMap
  -- The pairs with a label not fixing `x` form a closed set, since `G` is discrete.
  have hclosed : IsClosed (Φ '' {p | p.1 • x ≠ x}) :=
    hΦ _ ((isClosed_discrete {g : G | g • x ≠ x}).preimage continuous_fst)
  have hx : (x, x) ∉ Φ '' {p | p.1 • x ≠ x} := by
    rintro ⟨⟨g, y⟩, hg, hgy⟩
    obtain ⟨h₁, rfl⟩ := Prod.ext_iff.mp hgy
    exact hg h₁
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hclosed.isOpen_compl.mem_nhds hx)
  refine ⟨U ∩ V, inter_mem hU hV, fun g ⟨_, ⟨y, hy, rfl⟩, hgy⟩ => ?_⟩
  by_contra hg
  exact hUV ⟨hgy.1, hy.2⟩ ⟨⟨g, y⟩, hg, rfl⟩

variable (G) in
/-- **Slices of proper actions of discrete groups.** Every neighbourhood `W` of `x` contains an
open neighbourhood `U` of `x`, invariant under the stabilizer of `x`, such that every element of
`G` carrying a point of `U` into `U` fixes `x`. -/
theorem exists_slice (x : X) {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ U : SubMulAction (stabilizer G x) X, IsOpen (U : Set X) ∧ x ∈ U ∧ (U : Set X) ⊆ W ∧
      ∀ (g : G) (y : X), y ∈ U → g • y ∈ U → g ∈ stabilizer G x := by
  have := properlyDiscontinuousSMul G X
  obtain ⟨U₀, hU₀, hslice⟩ := exists_nhds_image_smul_eq_self G x
  set V := interior (U₀ ∩ W)
  have hxV : x ∈ V := mem_interior_iff_mem_nhds.mpr (inter_mem hU₀ hW)
  -- The intersection of the translates of `V` by the finite stabilizer is invariant.
  let U : SubMulAction (stabilizer G x) X :=
    { carrier := ⋂ h ∈ stabilizer G x, h • V
      smul_mem' := fun k y hy => by
        simp only [mem_iInter₂] at hy ⊢
        intro h hh
        have := hy ((k : G)⁻¹ * h) (mul_mem (inv_mem k.2) hh)
        rwa [mul_smul, ← smul_mem_smul_set_iff (a := (k : G)), smul_inv_smul] at this }
  have hUV : (U : Set X) ⊆ V := biInter_subset_of_mem (one_mem _) |>.trans (one_smul G V).subset
  refine ⟨U, ?_, ?_, hUV.trans (interior_subset.trans inter_subset_right), ?_⟩
  · exact (ProperlyDiscontinuousSMul.finite_stabilizer x).isOpen_biInter fun h _ =>
      isOpenMap_smul h V isOpen_interior
  · refine mem_iInter₂.mpr fun h hh => ?_
    simpa [mem_smul_set_iff_inv_smul_mem, inv_smul_eq_iff.mpr (hh : h • x = x).symm] using hxV
  · intro g y hy hgy
    have hU₀V : (U : Set X) ⊆ U₀ := hUV.trans (interior_subset.trans inter_subset_left)
    exact hslice g ⟨g • y, ⟨y, hU₀V hy, rfl⟩, hU₀V hgy⟩

end ProperSMul
