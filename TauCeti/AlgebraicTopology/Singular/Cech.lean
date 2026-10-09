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
`C(X; R)`. When `C` is abelian, so that homology is defined, and the `U i` cover `X`, that chain
map is a quasi-isomorphism, and the filtration by columns gives the Čech spectral sequence whose
`E¹_{p,q}` is the `q`-th homology of column `p`. That homology is
`⨁_{i₀ < ⋯ < iₚ} H_q(U_{i₀ ⋯ iₚ}; R)` when `ι` is finite or coproducts in `C` are exact, since then
homology commutes with the coproduct defining the column. None of this is proved in this file.

## Main definitions

* `TauCeti.cechSingularChains U R`: the functor `s ↦ C(U_s; R)` on finite sets of indices.
* `TauCeti.cechDoubleComplex U R`: the Čech double complex of singular chains of `U`, with the
  summand inclusions `TauCeti.cechDoubleComplexι U R s`. Its horizontal and vertical differentials
  are described by `TauCeti.ι_cechDoubleComplex_d` and `TauCeti.cechDoubleComplexι_f_comp_d`, and
  it vanishes from the column of the number of open sets on
  (`TauCeti.isZero_cechDoubleComplex_X`).
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
open scoped Finset

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
Čech differential, and its vertical differential is the singular boundary. It is characterised by
the summand inclusions `TauCeti.cechDoubleComplexι` and by `TauCeti.ι_cechDoubleComplex_d`. -/
def cechDoubleComplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (cechSingularChains U R).orderedCechComplex

/-- The inclusion of the summand `C(U_s; R)` into the column `p` of the Čech double complex, for a
set `s = {i₀ < ⋯ < iₚ}` of `p + 1` indices. -/
def cechDoubleComplexι {p : ℕ} (s : {s : Finset ι // #s = p + 1}) :
    (cechSingularChains U R).obj (op s.1) ⟶ (cechDoubleComplex U R).X p :=
  (cechSingularChains U R).orderedCechComplexι s

/-- Morphisms out of a column of the Čech double complex agree when they agree on every summand. -/
@[ext]
lemma cechDoubleComplex_hom_ext {p : ℕ} {A : ChainComplex C ℕ}
    {f g : (cechDoubleComplex U R).X p ⟶ A}
    (h : ∀ s, cechDoubleComplexι U R s ≫ f = cechDoubleComplexι U R s ≫ g) : f = g :=
  Functor.orderedCechComplex_hom_ext _ h

/-- The term of bidegree `(p, q)` of the Čech double complex is the sum of the `C_q(U_s; R)` over
the sets `s` of `p + 1` indices: morphisms out of it agree when they agree on every summand. -/
@[ext]
lemma cechDoubleComplex_X_X_hom_ext {p q : ℕ} {A : C}
    {f g : ((cechDoubleComplex U R).X p).X q ⟶ A}
    (h : ∀ s, (cechDoubleComplexι U R s).f q ≫ f = (cechDoubleComplexι U R s).f q ≫ g) :
    f = g :=
  -- Coproducts of chain complexes are computed degreewise.
  (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.down ℕ) q)
    ((cechSingularChains U R).isColimitOrderedCechComplexCofan p)).hom_ext fun ⟨s⟩ ↦ h s

/-- The horizontal differential of the Čech double complex on the summand of
`s = {i₀ < ⋯ < iₚ₊₁}` is the alternating sum of the maps induced by the inclusions
`U_s ⊆ U_{s \ {i}}`, with sign `(-1)` to the number of elements of `s` below `i`. -/
@[reassoc]
lemma ι_cechDoubleComplex_d {p : ℕ} (s : {s : Finset ι // #s = p + 1 + 1}) :
    cechDoubleComplexι U R s ≫ (cechDoubleComplex U R).d (p + 1) p =
      ∑ i : s.1, ((-1 : ℤ) ^ #{j ∈ s.1 | j < i.1}) •
        (cechSingularChains U R).map (homOfLE (s.1.erase_subset i.1)).op ≫
          cechDoubleComplexι U R
            ⟨s.1.erase i, by rw [Finset.card_erase_of_mem i.2, s.2, Nat.add_sub_cancel]⟩ :=
  (cechSingularChains U R).ι_orderedCechComplex_d s

/-- The vertical differential of the Čech double complex is the singular boundary on each
summand. -/
@[reassoc]
lemma cechDoubleComplexι_f_comp_d {p : ℕ} (s : {s : Finset ι // #s = p + 1}) (q : ℕ) :
    (cechDoubleComplexι U R s).f (q + 1) ≫ ((cechDoubleComplex U R).X p).d (q + 1) q =
      ((cechSingularChains U R).obj (op s.1)).d (q + 1) q ≫ (cechDoubleComplexι U R s).f q :=
  (cechDoubleComplexι U R s).comm (q + 1) q

/-- The Čech double complex of a cover by finitely many open sets vanishes from the column of the
number of open sets on, as there is no set of `p + 1` indices. -/
lemma isZero_cechDoubleComplex_X [Fintype ι] {p : ℕ} (hp : Fintype.card ι ≤ p) :
    IsZero ((cechDoubleComplex U R).X p) :=
  (cechSingularChains U R).isZero_orderedCechComplex_X hp

/-- The augmentation of the column `p = 0` of the Čech double complex: on the summand
`C(U i; R)` it is the chain map induced by the inclusion `U i ⊆ X`. -/
def cechAugmentation :
    (cechDoubleComplex U R).X 0 ⟶ ((singularChainComplexFunctor C).obj R).obj X :=
  (cechSingularChains U R).orderedCechAugmentation ≫
    ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' ((∅ : Finset ι).inf U))

/-- The augmentation maps the summand `C(U_s; R)`, for a one-element set `s`, by the inclusion of
`U_s` in `X`. -/
@[reassoc (attr := simp)]
lemma ι_cechAugmentation (s : {s : Finset ι // #s = 0 + 1}) :
    cechDoubleComplexι U R s ≫ cechAugmentation U R =
      ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.1.inf U)) := by
  rw [← cechSingularChains_map_comp_inclusion']
  exact (cechSingularChains U R).ι_orderedCechAugmentation_assoc s _

/-- The augmentation vanishes on the image of the horizontal differential. -/
@[reassoc (attr := simp)]
lemma cechDoubleComplex_d_comp_cechAugmentation :
    (cechDoubleComplex U R).d 1 0 ≫ cechAugmentation U R = 0 :=
  ((cechSingularChains U R).orderedCechComplex_d_comp_orderedCechAugmentation_assoc _).trans
    zero_comp

/-- The augmentation of the total complex of the Čech double complex to the singular chains of `X`:
on the summand `C_q(U i; R)` of total degree `q` it is the map induced by the inclusion `U i ⊆ X`
(`TauCeti.cechDoubleComplexι_f_ιTotal_cechTotalAugmentation_f`), and it vanishes on the columns
`p ≥ 1` (`TauCeti.ιTotal_cechTotalAugmentation_f_succ`). -/
def cechTotalAugmentation :
    (cechDoubleComplex U R).total (ComplexShape.down ℕ) ⟶
      ((singularChainComplexFunctor C).obj R).obj X :=
  (cechDoubleComplex U R).totalAugmentation (cechAugmentation U R)
    (cechDoubleComplex_d_comp_cechAugmentation U R)

/-- On the column `0`, the augmentation of the total complex is the augmentation of the column. -/
@[reassoc (attr := simp)]
lemma ιTotal_cechTotalAugmentation_f_zero (q : ℕ) :
    (cechDoubleComplex U R).ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫
        (cechTotalAugmentation U R).f q =
      (cechAugmentation U R).f q :=
  HomologicalComplex₂.ιTotal_totalAugmentation_f_zero _ _ _ q

/-- The augmentation of the total complex maps the summand `C_q(U_s; R)`, for a one-element set
`s`, by the inclusion of `U_s` in `X`. -/
@[reassoc]
lemma cechDoubleComplexι_f_ιTotal_cechTotalAugmentation_f (s : {s : Finset ι // #s = 0 + 1})
    (q : ℕ) :
    (cechDoubleComplexι U R s).f q ≫
        (cechDoubleComplex U R).ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫
          (cechTotalAugmentation U R).f q =
      (((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.1.inf U))).f q := by
  rw [ιTotal_cechTotalAugmentation_f_zero, ← HomologicalComplex.comp_f, ι_cechAugmentation]

/-- The augmentation of the total complex vanishes on the columns `p + 1`. -/
@[reassoc (attr := simp)]
lemma ιTotal_cechTotalAugmentation_f_succ (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p + 1, q) = n) :
    (cechDoubleComplex U R).ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫
        (cechTotalAugmentation U R).f n = 0 :=
  HomologicalComplex₂.ιTotal_totalAugmentation_f_succ _ _ _ p q n h

end TauCeti
