/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing locally finite sums of sections of abelian sheaves

Given a family of sections `a i` of an abelian sheaf `G` over an open subset `U` such that each
`a i` vanishes on all opens inside an open `V i`, and an open cover `N k ≤ U` of `U` on each member
of which only finitely many `i ∈ S k` fail to satisfy `N k ≤ V i`, the finite sums
`∑ i ∈ S k, a i|_{N k}` are compatible on overlaps and glue to a section of `G` over `U`
(`TopCat.Sheaf.exists_gluing_finset_sum`).

## Main results

* `TopCat.Sheaf.exists_gluing_finset_sum`: gluing of locally finite sums of sections of an abelian
  sheaf over an open subset `U`.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

/-- Gluing a locally finite sum of sections of an abelian sheaf `G` over `U`: if each `a i`
vanishes on opens inside `V i`, and `N` covers `U` with `N k ≤ V i` for all `i ∉ S k`, then the
finite sums `∑ i ∈ S k, a i|_{N k}` glue to a section `b` over `U`. -/
theorem exists_gluing_finset_sum {X : TopCat.{u}} (G : X.Sheaf AddCommGrpCat.{u}) {U : Opens X}
    {ι κ : Type*} (V : ι → Opens X) (a : ι → G.obj.obj (op U))
    (ha : ∀ i ⦃W : Opens X⦄ (hWU : W ≤ U), W ≤ V i → G.obj.map (homOfLE hWU).op (a i) = 0)
    (N : κ → Opens X) (hNU : ∀ k, N k ≤ U) (hN : U ≤ ⨆ k, N k) (S : κ → Finset ι)
    (hSV : ∀ k i, i ∉ S k → N k ≤ V i) :
    ∃ b : G.obj.obj (op U), ∀ k,
      G.obj.map (homOfLE (hNU k)).op b =
        ∑ i ∈ S k, G.obj.map (homOfLE (hNU k)).op (a i) := by
  classical
  let sf : ∀ k : κ, G.obj.obj (op (N k)) :=
    fun k ↦ ∑ i ∈ S k, G.obj.map (homOfLE (hNU k)).op (a i)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj N sf := by
    intro k₁ k₂
    let W := N k₁ ⊓ N k₂
    have hWU : W ≤ U := inf_le_left.trans (hNU k₁)
    have hrestrict (k : κ) (hWN : W ≤ N k) (hs : S k ⊆ S k₁ ∪ S k₂) :
        G.obj.map (homOfLE hWN).op (sf k) =
          ∑ i ∈ S k₁ ∪ S k₂, G.obj.map (homOfLE hWU).op (a i) := by
      simp only [sf, map_sum]
      have hterm (i : ι) :
          G.obj.map (homOfLE hWN).op (G.obj.map (homOfLE (hNU k)).op (a i)) =
            G.obj.map (homOfLE hWU).op (a i) := by
        rw [← Functor.map_comp_apply]
        exact congrArg (fun f : W ⟶ U ↦ G.obj.map f.op (a i)) (Subsingleton.elim _ _)
      simp_rw [hterm]
      exact Finset.sum_subset hs fun i _ hi ↦ ha i hWU (hWN.trans (hSV k i hi))
    exact (hrestrict k₁ inf_le_left Finset.subset_union_left).trans
      (hrestrict k₂ inf_le_right Finset.subset_union_right).symm
  obtain ⟨b, hb, -⟩ := G.existsUnique_gluing' N U (fun k ↦ homOfLE (hNU k)) hN sf hcompat
  exact ⟨b, hb⟩

end TopCat.Sheaf
