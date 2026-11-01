/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Deformation retractions of the ambient space and relative singular homology

Let `s ⊆ c ⊆ t` be subsets of a topological space, and suppose that `t` strong deformation
retracts onto `c`: there is a retraction `r : t → c` such that the composite `t → c ⊆ t` is
homotopic to the identity of `t` relative to `c`. Then the inclusion of pairs
`(c, s) ⟶ (t, s)` induces isomorphisms on relative singular homology in every degree
(`TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel`). The retraction
fixes `s ⊆ c`, so it is a map of pairs `(t, s) ⟶ (c, s)`, and it is a homotopy inverse of the
inclusion as a map of pairs, because the homotopy is stationary on `s`.

This is how a deformation retraction of a space onto a subspace with cells attached, such as a
sublevel set across a critical level of a Morse function, computes relative homology of the
original pair by cellular homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.19 and the relative form of Corollary 2.11.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable {X : TopCat.{w}} {s c t : Set X} (hsc : s ⊆ c) (hct : c ⊆ t)

/-- **A strong deformation retraction of the ambient space induces isomorphisms on relative
singular homology.** If `s ⊆ c ⊆ t` and `t` deformation retracts onto `c` relative to `c`, the
inclusion `(c, s) ⟶ (t, s)` induces isomorphisms on relative singular homology. -/
theorem isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel (r : C(t, c))
    (G : ((ContinuousMap.inclusion hct).comp r).HomotopyRel (ContinuousMap.id t)
      {x | (x : X) ∈ c})
    {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Preadditive A] [CategoryWithHomology A]
    (R : A) (n : ℕ) :
    IsIso ((ofInclusion hsc).singularHomologyMap
      (ofInclusionMap hsc (hsc.trans hct) (ContinuousMap.inclusion hct)
        fun _ hx ↦ by simpa using hx) R n) := by
  -- The retraction fixes every point of `c`, in particular every point of `s`.
  have hrc (x : t) (hx : (x : X) ∈ c) : (r x : X) = x :=
    congrArg Subtype.val (G.fst_eq_snd (x := x) hx)
  have hrs (x : t) (hx : (x : X) ∈ s) : (r x : X) ∈ s := (hrc x (hsc hx)).symm ▸ hx
  refine isIso_singularHomologyMap _ (ofInclusionMap (hsc.trans hct) hsc r hrs) ?_ ?_ R n
  · rw [← ofInclusionMap_comp, ← ofInclusionMap_id]
    have hid : r.comp (ContinuousMap.inclusion hct) = ContinuousMap.id c := by
      ext x
      exact hrc _ x.2
    simp only [hid]
    exact Homotopy.refl _
  · rw [← ofInclusionMap_comp, ← ofInclusionMap_id]
    -- The homotopy is stationary on `c ⊇ s`, so it keeps `s` inside `s`.
    refine ofInclusionHomotopy G.toHomotopy fun τ x hx ↦ ?_
    have h : G.toHomotopy (τ, x) = _ := G.eq_fst τ (hsc hx)
    exact h ▸ hrs x hx

end TopPair
