/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution

/-!
# Continuous cohomology of a trivial group vanishes in positive degrees

Let `G` be a topological group with at most one element and `X` a topological representation of
`G`, with no topological hypothesis on `X`. Then `Hⁿ⁺¹(G, X) = continuousCohomology (n + 1) X`
vanishes for every `n`. Evaluation at the identity contracts the coinduced resolution
`X → C(G, X) → C(G, C(G, X)) → ⋯` (`TopRep.d_sum_apply_add_sum_d_apply` at the single point `1`),
and over a trivial group every element of the resolution is invariant, so the contraction descends
to the homogeneous cochains and exhibits every cocycle of positive degree as a coboundary.

## Main results

* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_succ_of_subsingleton`:
  `Hⁿ⁺¹(G, X)` vanishes when `G` is a subsingleton.
-/

public section

open CategoryTheory TopRep

namespace TauCeti.ContinuousCohomology

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- **A trivial group has no continuous cohomology in positive degrees.** For a topological group
`G` with at most one element and any topological representation `X` of `G`, `Hⁿ⁺¹(G, X)` vanishes:
evaluation at the identity contracts the coinduced resolution, and every element is invariant. -/
instance subsingleton_continuousCohomology_succ_of_subsingleton [Subsingleton G] (X : TopRep k G)
    (n : ℕ) : Subsingleton (continuousCohomology (n + 1) X) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  set K := homogeneousCochains X
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective (n + 1) x
  set c := K.iCycles (n + 1) z
  set f : C(G, (resolutionX X (n + 1)).V) := c.1
  -- the cocycle condition `dₙ₊₂ f = 0`
  have hcocycle : (d X (n + 2)).hom f = 0 := by
    have h := ConcreteCategory.congr_hom (K.iCycles_d (n + 1) (n + 2)) z
    simp only [ConcreteCategory.comp_apply] at h
    exact (homogeneousCochains.d_apply X (n + 1) c).symm.trans (congrArg Subtype.val h)
  -- the value of `f` at the identity is a homogeneous cochain of degree `n`: over a trivial group
  -- every element is invariant
  let b : K.X n := ⟨f 1, fun g => by rw [Subsingleton.elim g 1, map_one, one_apply_eq_self]⟩
  have hb : K.toCycles n (n + 1) b = z := by
    refine K.iCycles_injective (n + 1) (Subtype.ext ?_)
    have h := ConcreteCategory.congr_hom (K.toCycles_i n (n + 1)) b
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, homogeneousCochains.d_apply]
    -- evaluation at the single point `1` contracts the resolution: `dₙ₊₁ (f 1) + (dₙ₊₂ f) 1 = f`
    have hsum := d_sum_apply_add_sum_d_apply X (fun _ : Unit => (1 : G)) (n + 1) f
    simp only [hcocycle, ContinuousMap.zero_apply, Fintype.sum_unique, Fintype.card_unique,
      one_smul, add_zero] at hsum
    exact hsum
  rw [← hb]
  exact (K.homologyπ_eq_zero_iff (n + 1) (by simp)).2 ⟨b, rfl⟩

end TauCeti.ContinuousCohomology
