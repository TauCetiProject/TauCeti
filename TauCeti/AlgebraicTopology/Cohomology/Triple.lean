/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The cochain sequence of a triple

For a triple `B ⊆ A ⊆ X` of topological spaces, applying `Hom(-, M)` to the short exact sequence
of relative singular chains `0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0` gives the sequence of relative
singular cochains

`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`

(`TauCeti.TopTriple.singularCochainComplexShortComplex`). It is short exact
(`TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`), because the chain sequence
is split in each degree (`TauCeti.TopTriple.isSplitMono_singularChainComplexMap_innerToTotal_f`):
a cochain on `A` vanishing on `B` extends by zero to a cochain on `X` vanishing on `B`. Its first
map includes the cochains vanishing on `A` among those vanishing on `B`, and composed with the
inclusion of the latter into all cochains of `X` it is the inclusion of the former
(`TauCeti.TopTriple.singularCochainComplexMap_totalToOuter_comp_f`).

This identifies the quotient of two stages of the filtration of the singular cochains of a space
by vanishing on an increasing family of subspaces, from which the cohomological spectral sequence
of a filtered space is built.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (T : TopTriple.{w}) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- In each degree the relative singular chain sequence `0 ⟶ Cₙ(A, B) ⟶ Cₙ(X, B) ⟶ Cₙ(X, A) ⟶ 0`
of a triple is split: a section of the quotient map `Cₙ(X) ⟶ Cₙ(X, A)`, followed by the quotient
map `Cₙ(X) ⟶ Cₙ(X, B)`, is a section of `Cₙ(X, B) ⟶ Cₙ(X, A)`. So its first map is a split
monomorphism. -/
instance isSplitMono_singularChainComplexMap_innerToTotal_f (n : ℕ) :
    IsSplitMono ((TopPair.singularChainComplexMap (innerToTotal.app T) R).f n) := by
  have hS := (T.shortExact_singularChainComplexShortComplex R).map_of_exact
    (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
  let s := SSetPair.chainComplexXSplitting R (TopPair.toSSetPair.obj (outerPair.obj T)) n
  exact (ShortComplex.Splitting.ofExactOfSection _ hS.exact
    (s.s ≫ ((totalPair.obj T).singularChainComplexπ R).f n)
    (by
      have h := congrArg (fun f ↦ f.f n) (T.singularChainComplexπ_comp_totalToOuter R)
      dsimp only at h
      rw [HomologicalComplex.comp_f] at h
      exact (Category.assoc _ _ _).trans ((congrArg (s.s ≫ ·) h).trans s.s_g))
    hS.mono_f).isSplitMono_f

/-- The relative singular cochain sequence `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple
`(X, A, B)`: the image under `Hom(-, M)` of the relative singular chain sequence. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  (T.singularChainComplexShortComplex R).op.map (TauCeti.ChainComplex.linearYonedaFunctor k M)

/-- The first map of the cochain sequence of a triple is induced by the map of pairs
`(X, B) ⟶ (X, A)`. -/
lemma singularCochainComplexShortComplex_f :
    (T.singularCochainComplexShortComplex R k M).f =
      TopPair.singularCochainComplexMap (totalToOuter.app T) := (rfl)

/-- The second map of the cochain sequence of a triple is induced by the map of pairs
`(A, B) ⟶ (X, B)`. -/
lemma singularCochainComplexShortComplex_g :
    (T.singularCochainComplexShortComplex R k M).g =
      TopPair.singularCochainComplexMap (innerToTotal.app T) := (rfl)

/-- The relative singular cochain sequence `0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0` of a triple
is short exact. -/
lemma shortExact_singularCochainComplexShortComplex :
    (T.singularCochainComplexShortComplex R k M).ShortExact :=
  TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

/-- The inclusion of the cochains vanishing on `A` among those vanishing on `B`, followed by the
inclusion of the latter into the cochains of `X`, is the inclusion of the former. -/
@[reassoc (attr := simp)]
lemma singularCochainComplexMap_totalToOuter_comp_f :
    TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (totalToOuter.app T) ≫
        ((totalPair.obj T).singularCochainComplexShortComplex R k M).f =
      ((outerPair.obj T).singularCochainComplexShortComplex R k M).f := by
  -- `Hom(-, M)` reverses the composite of chain maps `C(X) ⟶ C(X, B) ⟶ C(X, A)`.
  exact ((TauCeti.ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    (congrArg (fun f ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map f.op)
      (T.singularChainComplexπ_comp_totalToOuter R))

end TopTriple

end TauCeti
