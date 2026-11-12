/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.Geometry.Manifold.Boundary.Collar.Retraction

/-!
# Relative homology modulo a collar

Let `A` be a subset of a space `X` with a collar `c : A × [0, 1) → X` (`TauCeti.IsCollar`), for
instance the boundary of a compact manifold (`TauCeti.isCollared_subtypeVal_boundary`). The image
`U = c (A × [0, 1))` of the collar is an open neighbourhood of `A` which deformation retracts onto
it (`TauCeti.IsCollar.homotopyEquivRange`). So the inclusion of pairs `(X, A) → (X, U)`, the
identity of `X`, induces isomorphisms on relative singular homology in every degree
(`TauCeti.IsCollar.isIso_singularHomologyMap`): it is an isomorphism on the homology of `X` and of
the subspaces, and the five lemma applies.

For a compact manifold `M` with boundary and an open collar `U` of `∂M`, the boundary lies in the
interior of `U`, so excising it identifies `H_*(M, U)` with the homology of the interior of `M`
relative to the complement of the compact set `M ∖ U`. Combined with the comparison here, this
reads `H_*(M, ∂M)` in the interior of `M`, which has no boundary; this is how a class relative to
the boundary, such as the fundamental class of `M`, is built from the local homology of the
interior.

## Main results

* `TauCeti.IsCollar.isIso_singularHomologyMap`: for a collar `c` of `A ⊆ X`, the map
  `H_n(X, A) → H_n(X, c (A × [0, 1)))` is an isomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (the fundamental
  class of a compact manifold with boundary, through a collar of the boundary).
-/

public section

open CategoryTheory Set

universe w v u

namespace TauCeti.IsCollar

variable {X : TopCat.{w}} {A : Set X} {c : A × Ico (0 : ℝ) 1 → X}
  {C : Type u} [Category.{v} C] [Limits.HasCoproducts.{w} C] [Abelian C]

/-- **Relative homology modulo a collar.** If `c` is a collar of `A ⊆ X`, the inclusion of pairs
`(X, A) → (X, c (A × [0, 1)))` induces an isomorphism `H_n(X, A) ≅ H_n(X, c (A × [0, 1)))` on
relative singular homology, in every degree and for every coefficient object. -/
theorem isIso_singularHomologyMap (h : IsCollar ((↑) : A → X) c) (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (𝟙 X) fun x hx ↦ h.range_subset_range ⟨⟨x, hx⟩, rfl⟩) R n) := by
  -- On the ambient space the map of pairs is the identity, and on the subspaces it is the zero
  -- slice of the collar, a homotopy equivalence.
  refine TopPair.isIso_singularHomologyMap_of_homotopyEquiv _ (.refl X) h.homotopyEquivRange
    (TopPair.ofSubsetMap_fst _ _) ?_ R n
  ext x
  exact Subtype.ext ((TopPair.ofSubsetMap_snd_apply _ _ x).trans
    (h.coe_homotopyEquivRange_apply x).symm)

end TauCeti.IsCollar
