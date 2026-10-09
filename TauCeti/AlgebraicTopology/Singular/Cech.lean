/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.OrderedCech
public import TauCeti.Algebra.Homology.TotalComplex

/-!
# The Čech double complex of singular chains of an open cover

Let `U : ι → Opens X` be a family of open subsets of a topological space `X`, indexed by a
linearly ordered type, and let `R` be a coefficient object of a preadditive category with
coproducts. For a finite set `s` of indices write `U_s = ⋂_{i ∈ s} U i`, so that `U_∅` is all of
`X`. The
Čech double complex of `U` has in bidegree `(p, q)` the sum of the singular chain groups
`C_q(U_s; R)` over the sets `s = {i₀ < ⋯ < iₚ}` with `p + 1` elements. Its horizontal
differential is the alternating Čech differential `∑ₖ (-1)ᵏ`, which deletes one index `iₖ` and maps
by the inclusion `U_s ⊆ U_{s \ {iₖ}}`. Its vertical differential is the singular boundary. In the
total complex the vertical differential acquires the sign `(-1)ᵖ`, by the convention of Mathlib's
`HomologicalComplex₂.total` (see `TauCeti.Algebra.Homology.TotalComplex`).

For two indices `a < b` the horizontal differential `C(U_a ∩ U_b) ⟶ C(U_a) ⊞ C(U_b)` is
`(-i_a, i_b)`, by `CategoryTheory.Functor.ι_orderedCechComplex_d_pair`. This is the standard Čech
sign; it is the negative of the first map `(i_U, -i_V)` of the Mayer–Vietoris sequence of
`TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic` for `U = U_a` and `V = U_b`.

The double complex is the ordered Čech complex `CategoryTheory.Functor.orderedCechComplex` of the
functor `s ↦ C(U_s; R)`. It is augmented to the singular chains of `X` by the maps induced by the
inclusions `U i ⊆ X`, and this augmentation induces a chain map from the total complex to
`C(X; R)`. When the `U i` cover `X`, that chain map is a quasi-isomorphism, and the filtration by
columns gives the Čech spectral sequence with `E¹_{p,q} = ⨁_{i₀ < ⋯ < iₚ} H_q(U_{i₀ ⋯ iₚ}; R)`;
neither is proved in this file.

## Main definitions

* `TauCeti.cechSingularChains U R`: the functor `s ↦ C(U_s; R)` on finite sets of indices.
* `TauCeti.cechDoubleComplex U R`: the Čech double complex of singular chains of `U`.
* `TauCeti.cechAugmentation U R`: the augmentation of its column `p = 0` to `C(X; R)`, vanishing on
  the image of the horizontal differential (`TauCeti.cechDoubleComplex_d_comp_cechAugmentation`).
* `TauCeti.cechTotalAugmentation U R`: the induced chain map from the total complex to `C(X; R)`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, §8 (the generalized Mayer–Vietoris principle).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X : TopCat.{w}} {ι : Type w} (U : ι → Opens X) (R : C)

/-- The singular chains with coefficients in `R` of the finite intersections of a family `U` of
open sets, as a functor of the finite set `s` of indices: `s` goes to `C(⋂_{i ∈ s} U i; R)`, and an
inclusion `t ⊆ s` to the chain map induced by the inclusion of `⋂_{i ∈ s} U i` in
`⋂_{i ∈ t} U i`. The empty set goes to the chains of the top open set. -/
-- Reducible, so that its values are syntactically singular chain complexes of open sets.
@[simps]
abbrev cechSingularChains : (Finset ι)ᵒᵖ ⥤ ChainComplex C ℕ where
  obj s := ((singularChainComplexFunctor C).obj R).obj ((Opens.toTopCat X).obj (s.unop.inf U))
  map f := ((singularChainComplexFunctor C).obj R).map
    ((Opens.toTopCat X).map (homOfLE (Finset.inf_mono (leOfHom f.unop))))
  map_id s := (congrArg ((singularChainComplexFunctor C).obj R).map
    ((Opens.toTopCat X).map_id (s.unop.inf U))).trans (CategoryTheory.Functor.map_id _ _)
  map_comp f g := (congrArg ((singularChainComplexFunctor C).obj R).map
    ((Opens.toTopCat X).map_comp (homOfLE (Finset.inf_mono (leOfHom f.unop)))
      (homOfLE (Finset.inf_mono (leOfHom g.unop))))).trans
        (CategoryTheory.Functor.map_comp _ _ _)

/-- Restricting from `C(U_s; R)` to `C(U_∅; R)` and then including in `C(X; R)` is the map
induced by the inclusion of `U_s` in `X`. -/
private lemma cechSingularChains_map_comp_inclusion' (s : Finset ι) :
    (cechSingularChains U R).map (homOfLE s.empty_subset).op ≫
        ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' ((∅ : Finset ι).inf U)) =
      ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.inf U)) := by
  rw [cechSingularChains_map]
  exact (CategoryTheory.Functor.map_comp _ _ _).symm

variable [LinearOrder ι]

/-- **The Čech double complex of singular chains** of a family `U` of open sets indexed by a
linearly ordered type. Its column `p` is the sum of the singular chain complexes
`C(U_{i₀} ∩ ⋯ ∩ U_{iₚ}; R)` over `i₀ < ⋯ < iₚ`, its horizontal differential is the alternating
Čech differential, and its vertical differential is the singular boundary. -/
abbrev cechDoubleComplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (cechSingularChains U R).orderedCechComplex

/-- The augmentation of the column `p = 0` of the Čech double complex: on the summand
`C(U i; R)` it is the chain map induced by the inclusion `U i ⊆ X`. -/
def cechAugmentation :
    (cechDoubleComplex U R).X 0 ⟶ ((singularChainComplexFunctor C).obj R).obj X :=
  (cechSingularChains U R).orderedCechAugmentation ≫
    ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' ((∅ : Finset ι).inf U))

/-- The augmentation maps the summand `C(U_s; R)`, for a one-element set `s`, by the inclusion of
`U_s` in `X`. -/
@[reassoc (attr := simp)]
lemma ι_cechAugmentation (s : {s : Finset ι // s.card = 0 + 1}) :
    (cechSingularChains U R).orderedCechComplexι s ≫ cechAugmentation U R =
      ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.1.inf U)) := by
  rw [cechAugmentation, Functor.ι_orderedCechAugmentation_assoc,
    cechSingularChains_map_comp_inclusion']

/-- The augmentation vanishes on the image of the horizontal differential. -/
@[reassoc (attr := simp)]
lemma cechDoubleComplex_d_comp_cechAugmentation :
    (cechDoubleComplex U R).d 1 0 ≫ cechAugmentation U R = 0 := by
  rw [cechAugmentation, Functor.orderedCechComplex_d_comp_orderedCechAugmentation_assoc,
    zero_comp]

/-- The augmentation of the total complex of the Čech double complex to the singular chains of `X`:
on the summand `C_q(U i; R)` of total degree `q` it is the map induced by the inclusion `U i ⊆ X`,
and it vanishes on the columns `p ≥ 1`. -/
abbrev cechTotalAugmentation :
    (cechDoubleComplex U R).total (ComplexShape.down ℕ) ⟶
      ((singularChainComplexFunctor C).obj R).obj X :=
  (cechDoubleComplex U R).totalAugmentation (cechAugmentation U R)
    (cechDoubleComplex_d_comp_cechAugmentation U R)

end TauCeti
