/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The relative singular cochain sequence of a triple

For a triple `B ⊆ A ⊆ X` of topological spaces, the relative singular chains form the short exact
sequence `0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0`
(`TauCeti.TopTriple.shortExact_singularChainComplexShortComplex`). In each degree its first map is
a split monomorphism (`TauCeti.TopTriple.isSplitMono_singularChainComplexMap_innerToTotal_f`): a
retraction lifts a relative chain of `(X, B)` to a chain of `X` by the splitting of the pair
`(X, B)`, retracts it to a chain of `A` by the splitting of the inclusion of `A`, and takes its
class modulo `B`. Applying `Hom(-, M)` to this degreewise split sequence therefore gives a short
exact sequence of relative singular cochain complexes

`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`

(`TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`), whose long exact cohomology
sequence is the long exact sequence of the triple in singular cohomology. Its first map is
induced by the map of pairs `(X, B) ⟶ (X, A)` and its second by the map of pairs
`(A, B) ⟶ (X, B)`.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (T : TopTriple.{w})
  (R : C)

/-- The retraction identity behind
`TauCeti.TopTriple.isSplitMono_singularChainComplexMap_innerToTotal_f`, in a preadditive
category: if `πX ≫ s = 𝟙 - r ≫ iX` with `iX = iB ≫ iA`, and `rA` retracts `iA` while `πA` kills
`iB`, then `iA ≫ πX ≫ s ≫ rA ≫ πA = πA`. -/
private lemma comp_comp_comp_comp_eq_of_splitting {D : Type*} [Category* D] [Preadditive D]
    {A X X' B Z : D} {iA : A ⟶ X} {πX : X ⟶ X'} {s : X' ⟶ X} {r : X ⟶ B} {iX : B ⟶ X}
    {iB : B ⟶ A} {rA : X ⟶ A} {πA : A ⟶ Z} (h₂ : πX ≫ s = 𝟙 X - r ≫ iX) (h₃ : iX = iB ≫ iA)
    (hrA : iA ≫ rA = 𝟙 A) (h₄ : iB ≫ πA = 0) :
    iA ≫ πX ≫ s ≫ rA ≫ πA = πA := by
  rw [reassoc_of% h₂, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    reassoc_of% hrA, h₃, Category.assoc, Category.assoc, reassoc_of% hrA, h₄, comp_zero,
    comp_zero, sub_zero]

/-- In each degree, the map `Cₙ(A, B) ⟶ Cₙ(X, B)` of relative singular chains of a triple
`(X, A, B)` is a split monomorphism. -/
instance isSplitMono_singularChainComplexMap_innerToTotal_f (n : ℕ) :
    IsSplitMono ((TopPair.singularChainComplexMap (innerToTotal.app T) R).f n) := by
  -- The splitting of `0 ⟶ Cₙ(B) ⟶ Cₙ(X) ⟶ Cₙ(X, B) ⟶ 0` and a retraction `rA` of
  -- `Cₙ(A) ⟶ Cₙ(X)`.
  let S := SSetPair.chainComplexXSplitting R (TopPair.toSSetPair.obj (totalPair.obj T)) n
  obtain ⟨rA, hrA⟩ : ∃ r, (SSet.chainComplexMap (TopCat.toSSet.map T.outerMap) R).f n ≫ r = 𝟙 _ :=
    have h := SSetPair.instIsSplitMonoFNatChainComplexMapHomSSet_tauCeti R
      (TopPair.toSSetPair.obj (outerPair.obj T)) n
    ⟨h.exists_splitMono.some.retraction, h.exists_splitMono.some.id⟩
  have hπA : Epi (((innerPair.obj T).singularChainComplexπ R).f n) := inferInstanceAs (Epi
    (((TopPair.toSSetPair.obj (innerPair.obj T)).chainComplexπ R).f n))
  refine IsSplitMono.mk' ⟨S.s ≫ rA ≫ ((innerPair.obj T).singularChainComplexπ R).f n,
    (cancel_epi (((innerPair.obj T).singularChainComplexπ R).f n)).1 ?_⟩
  -- On a chain `c` of `A`, the lift of the class of `c` to `X` differs from `c` by a chain of `B`,
  -- which the retraction carries back into `B` and the quotient map kills.
  have h₁ : ((innerPair.obj T).singularChainComplexπ R).f n ≫
      (TopPair.singularChainComplexMap (innerToTotal.app T) R).f n =
        (SSet.chainComplexMap (TopCat.toSSet.map T.outerMap) R).f n ≫
          ((totalPair.obj T).singularChainComplexπ R).f n :=
    (HomologicalComplex.comp_f _ _ n).symm.trans
      ((congrArg (fun φ ↦ φ.f n) (T.singularChainComplexπ_comp_innerToTotal R)).trans
        (HomologicalComplex.comp_f _ _ n))
  have h₂ : ((totalPair.obj T).singularChainComplexπ R).f n ≫ S.s =
      𝟙 _ - S.r ≫ (SSet.chainComplexMap (TopCat.toSSet.map T.totalMap) R).f n :=
    eq_sub_of_add_eq' S.id
  have h₃ : (SSet.chainComplexMap (TopCat.toSSet.map T.totalMap) R).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map T.innerMap) R).f n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map T.outerMap) R).f n := by
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp,
      T.innerMap_comp_outerMap]
  have h₄ : (SSet.chainComplexMap (TopCat.toSSet.map T.innerMap) R).f n ≫
      ((innerPair.obj T).singularChainComplexπ R).f n = 0 :=
    (HomologicalComplex.comp_f _ _ n).symm.trans ((congrArg (fun φ ↦ φ.f n)
      (TopPair.chainComplexMap_comp_singularChainComplexπ (innerPair.obj T) R)).trans
        (HomologicalComplex.zero_f_apply _))
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₁).trans <|
    (Category.assoc _ _ _).trans <| (comp_comp_comp_comp_eq_of_splitting h₂ h₃ hrA h₄).trans
      (Category.comp_id _).symm

variable (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The relative singular cochain sequence `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple
`(X, A, B)`: the image under `Hom(-, M)` of its relative singular chain sequence. Its first map is
induced by the map of pairs `(X, B) ⟶ (X, A)` and its second by the map of pairs
`(A, B) ⟶ (X, B)`. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  (T.singularChainComplexShortComplex R).op.map (TauCeti.ChainComplex.linearYonedaFunctor k M)

/-- The first map of the cochain sequence of a triple `(X, A, B)` is induced by the map of pairs
`(X, B) ⟶ (X, A)`. -/
lemma singularCochainComplexShortComplex_f :
    (T.singularCochainComplexShortComplex R k M).f =
      TopPair.singularCochainComplexMap (totalToOuter.app T) := (rfl)

/-- The second map of the cochain sequence of a triple `(X, A, B)` is induced by the map of pairs
`(A, B) ⟶ (X, B)`. -/
lemma singularCochainComplexShortComplex_g :
    (T.singularCochainComplexShortComplex R k M).g =
      TopPair.singularCochainComplexMap (innerToTotal.app T) := (rfl)

/-- **The relative singular cochain sequence of a triple is short exact**:
`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`. -/
lemma shortExact_singularCochainComplexShortComplex :
    (T.singularCochainComplexShortComplex R k M).ShortExact :=
  TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

end TopTriple

end TauCeti
