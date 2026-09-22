/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Relative singular chains and homology with local coefficients

Let `(X, A)` be a topological pair and let `L` be a local coefficient system on `X`.  Restricting
`L` along the inclusion of `A` twists the singular chains of `A`, and because the singular
simplices of `A` inject into those of `X` the resulting map into the twisted chains of `X` is a
monomorphism in every degree.  Its cokernel is the relative twisted chain complex of the pair,
whose homology is relative singular homology with coefficients in `L`.

This file constructs that complex, records the short exact sequence of chain complexes it sits
in, and derives from it the long exact sequence relating the twisted homology of `A`, of `X`, and
of the pair.  For a constant system the relative complex is the ordinary relative singular chain
complex, compatibly with the quotient maps from the chains of the ambient space, and the same
comparison in homology identifies relative twisted homology with ordinary relative homology.

Relative homology with local coefficients is the form in which cap products against the
orientation system express manifold duality, which is what makes the relative theory, and not
only the absolute one of `TauCeti.AlgebraicTopology.Singular.Twisted.Basic`, necessary.

## Main declarations

* `TopPair.twistedChainComplex`: the relative twisted singular chain complex of a pair, presented
  as a cokernel by `TopPair.isColimitCokernelCoforkTwistedChainComplex`.
* `TopPair.shortExact_twistedChainComplexShortComplex`: the twisted chains of the subspace, of the
  ambient space and of the pair form a short exact sequence of chain complexes.
* `TopPair.twistedHomology`, `TopPair.twistedHomologyπ` and `TopPair.twistedHomologyδ`, with the
  three exactness statements `TopPair.twistedHomology_exact_subspace`,
  `TopPair.twistedHomology_exact_space` and `TopPair.twistedHomology_exact_relative`.
* `TopPair.twistedHomologyConstantIso`: for a constant system, relative twisted homology is
  ordinary relative singular homology.

The cokernel presentation, the short exact sequence and the shape of the three exactness
statements follow Mathlib's relative simplicial homology
(`Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative`, by Joël Riou and Andrew Yang), of
which this is the twisted analogue; `TauCeti.AlgebraicTopology.Singular.Relative` is its untwisted
topological specialization.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapters VII--VIII.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- The restriction to the subspace of a topological pair of a local coefficient system on its
ambient space, that is, the pullback of the system along the inclusion. -/
abbrev subspaceSystem : LocalCoefficientSystem.{u, v, max v w} R P.snd :=
  (LocalCoefficientSystem.pullback P.map.hom).obj L

/-- The relative twisted singular chain complex of a topological pair `(X, A)` with coefficients
in a local coefficient system `L` on `X`: the quotient of the twisted chains of `X` by the
twisted chains of `A`. -/
def twistedChainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  cokernel (LocalCoefficientSystem.twistedChainComplexMap P.map L)

/-- The quotient map from the twisted chains of the ambient space onto the relative twisted
chains of the pair. -/
def twistedChainComplexπ :
    L.twistedChainComplex ⟶ P.twistedChainComplex L :=
  cokernel.π _

instance : Epi (P.twistedChainComplexπ L) := coequalizer.π_epi

@[reassoc (attr := simp)]
lemma twistedChainComplexMap_comp_twistedChainComplexπ :
    LocalCoefficientSystem.twistedChainComplexMap P.map L ≫ P.twistedChainComplexπ L = 0 :=
  cokernel.condition _

@[reassoc (attr := simp)]
lemma twistedChainComplexMap_f_comp_twistedChainComplexπ_f (k : ℕ) :
    (LocalCoefficientSystem.twistedChainComplexMap P.map L).f k ≫
      (P.twistedChainComplexπ L).f k = 0 := by
  simp [← HomologicalComplex.comp_f]

/-- The cokernel cofork presenting the relative twisted chain complex of a pair as the quotient
of the ambient twisted chains by the twisted chains of the subspace. -/
def cokernelCoforkTwistedChainComplex :
    CokernelCofork (LocalCoefficientSystem.twistedChainComplexMap P.map L) :=
  CokernelCofork.ofπ _ (P.twistedChainComplexMap_comp_twistedChainComplexπ L)

/-- The relative twisted chain complex of a pair is the cokernel of the inclusion of the twisted
chains of its subspace. -/
def isColimitCokernelCoforkTwistedChainComplex :
    IsColimit (P.cokernelCoforkTwistedChainComplex L) :=
  cokernelIsCokernel _

instance (k : ℕ) :
    PreservesColimit
      (parallelPair (LocalCoefficientSystem.twistedChainComplexMap P.map L) 0)
      (HomologicalComplex.eval (ModuleCat.{max v w} R) (ComplexShape.down ℕ) k) :=
  HomologicalComplex.eval_preservesColimit_of_hasCokernel_f ..

/-- The degreewise cokernel cofork presenting the relative twisted chains of a pair in degree `k`
as the quotient of the twisted `k`-chains of the ambient space. -/
def cokernelCoforkTwistedChainComplexX (k : ℕ) :
    CokernelCofork ((LocalCoefficientSystem.twistedChainComplexMap P.map L).f k) :=
  CokernelCofork.ofπ _ (P.twistedChainComplexMap_f_comp_twistedChainComplexπ_f L k)

/-- In each degree, the relative twisted chains of a pair are the cokernel of the inclusion of
the twisted chains of its subspace. -/
def isColimitCokernelCoforkTwistedChainComplexX (k : ℕ) :
    IsColimit (P.cokernelCoforkTwistedChainComplexX L k) :=
  CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkTwistedChainComplex L)
    (HomologicalComplex.eval _ _ k)

instance (k : ℕ) : Epi ((P.twistedChainComplexπ L).f k) :=
  Cofork.IsColimit.epi (P.isColimitCokernelCoforkTwistedChainComplexX L k)

/-- The twisted chain sequence of a topological pair: the twisted chains of the subspace, of the
ambient space, and of the pair. -/
abbrev twistedChainComplexShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{max v w} R) ℕ) :=
  ShortComplex.mk _ _ (P.twistedChainComplexMap_comp_twistedChainComplexπ L)

/-- The twisted chain sequence of a topological pair is short exact. -/
lemma shortExact_twistedChainComplexShortComplex :
    (P.twistedChainComplexShortComplex L).ShortExact where
  exact :=
    ShortComplex.exact_of_g_is_cokernel _ (P.isColimitCokernelCoforkTwistedChainComplex L)

section Homology

/-- The relative singular homology of a topological pair in degree `k`, with coefficients in a
local coefficient system on the ambient space. -/
abbrev twistedHomology (k : ℕ) : ModuleCat.{max v w} R := (P.twistedChainComplex L).homology k

/-- The map from the twisted homology of the ambient space of a pair to the relative twisted
homology of the pair. -/
abbrev twistedHomologyπ (k : ℕ) : L.twistedHomology k ⟶ P.twistedHomology L k :=
  HomologicalComplex.homologyMap (P.twistedChainComplexπ L) k

@[reassoc (attr := simp)]
lemma twistedHomologyMap_comp_twistedHomologyπ (k : ℕ) :
    LocalCoefficientSystem.twistedHomologyMap P.map L k ≫ P.twistedHomologyπ L k = 0 := by
  simp [← HomologicalComplex.homologyMap_comp]

/-- The map from ambient twisted homology to relative twisted homology is an epimorphism in
degree zero. -/
instance : Epi (P.twistedHomologyπ L 0) :=
  HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)

/-- The connecting morphism from the relative twisted homology of a pair in degree `n` to the
twisted homology of its subspace in degree `m`, where `m + 1 = n`. -/
def twistedHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomology L n ⟶ (P.subspaceSystem L).twistedHomology m :=
  (P.shortExact_twistedChainComplexShortComplex L).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma twistedHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomologyδ L n m h ≫ LocalCoefficientSystem.twistedHomologyMap P.map L m = 0 :=
  (P.shortExact_twistedChainComplexShortComplex L).δ_comp n m (by simpa)

@[reassoc (attr := simp)]
lemma twistedHomologyπ_comp_twistedHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomologyπ L n ≫ P.twistedHomologyδ L n m h = 0 :=
  (P.shortExact_twistedChainComplexShortComplex L).comp_δ n m (by simpa)

/-- Exactness at the twisted homology of the subspace in the long exact sequence of a pair. -/
lemma twistedHomology_exact_subspace (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.twistedHomologyδ_comp L n m h)).Exact :=
  (P.shortExact_twistedChainComplexShortComplex L).homology_exact₁ n m (by simpa)

/-- Exactness at the twisted homology of the ambient space in the long exact sequence of a
pair. -/
lemma twistedHomology_exact_space (k : ℕ) :
    (ShortComplex.mk _ _ (P.twistedHomologyMap_comp_twistedHomologyπ L k)).Exact :=
  (P.shortExact_twistedChainComplexShortComplex L).homology_exact₂ k

/-- Exactness at the relative twisted homology in the long exact sequence of a pair. -/
lemma twistedHomology_exact_relative (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.twistedHomologyπ_comp_twistedHomologyδ L n m h)).Exact :=
  (P.shortExact_twistedChainComplexShortComplex L).homology_exact₃ n m (by simpa)

end Homology

section Constant

variable (M : ModuleCat.{max v w} R)

/-- For a constant local coefficient system, the relative twisted chain complex of a pair is the
ordinary relative singular chain complex with the same coefficient module: both are the cokernel
of the same inclusion of subspace chains, once the restriction of a constant system is identified
with the constant system. -/
def twistedChainComplexConstantIso :
    P.twistedChainComplex ((LocalCoefficientSystem.constantFunctor P.fst).obj M) ≅
      P.singularChainComplex M :=
  IsColimit.coconePointsIsoOfNatIso
    (P.isColimitCokernelCoforkTwistedChainComplex _)
    (P.isColimitCokernelCoforkSingularChainComplex M)
    (parallelPair.ext
      (LocalCoefficientSystem.twistedChainComplexCoefficientIso
          (LocalCoefficientSystem.pullbackConstantIso P.map.hom M) ≪≫
        LocalCoefficientSystem.twistedChainComplexConstantIso P.snd M)
      (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M)
      -- The commutation condition for `left` is stated through `(parallelPair _ _).map`, whose
      -- reduction to the map itself is definitional but is not visible to `rw`.  It is therefore
      -- proved below in its reduced form, which leaves exactly two definitional identifications
      -- for the final `exact`s: the `parallelPair` reduction itself, and the identification of
      -- `((AlgebraicTopology.singularChainComplexFunctor _).obj M).map P.map` with
      -- `SSet.chainComplexMap (toSSetPair.obj P).hom M`, the singular chain complex functor being
      -- the simplicial one precomposed with `TopCat.toSSet`.
      (by
        have h : LocalCoefficientSystem.twistedChainComplexMap P.map
                ((LocalCoefficientSystem.constantFunctor P.fst).obj M) ≫
              (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M).hom =
            (LocalCoefficientSystem.twistedChainComplexCoefficientIso
                  (LocalCoefficientSystem.pullbackConstantIso P.map.hom M) ≪≫
                LocalCoefficientSystem.twistedChainComplexConstantIso P.snd M).hom ≫
              SSet.chainComplexMap (toSSetPair.obj P).hom M := by
          rw [Iso.trans_hom, LocalCoefficientSystem.twistedChainComplexCoefficientIso_hom]
          exact (LocalCoefficientSystem.twistedChainComplexConstantIso_hom_space_naturality
            P.map M).trans (Category.assoc _ _ _).symm
        exact h)
      -- Both composites are with the zero map of the `parallelPair`, hence zero.
      (zero_comp.trans comp_zero.symm))

/-- The comparison of relative twisted chains with ordinary relative singular chains is
compatible with the quotient maps from the chains of the ambient space. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom :
    P.twistedChainComplexπ ((LocalCoefficientSystem.constantFunctor P.fst).obj M) ≫
        (P.twistedChainComplexConstantIso M).hom =
      (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M).hom ≫
        P.singularChainComplexπ M :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (P.isColimitCokernelCoforkTwistedChainComplex _)
    (P.isColimitCokernelCoforkSingularChainComplex M) _ WalkingParallelPair.one

/-- For a constant local coefficient system, relative twisted homology is ordinary relative
singular homology. -/
-- The body is exposed only so that the two component lemmas below can be stated as definitional
-- equalities; both of their right hand sides are already public.
@[expose]
def twistedHomologyConstantIso (k : ℕ) :
    P.twistedHomology ((LocalCoefficientSystem.constantFunctor P.fst).obj M) k ≅
      P.singularHomology M k :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (P.twistedChainComplexConstantIso M)

-- Not `simp` lemmas, as for the absolute comparison in
-- `TauCeti.AlgebraicTopology.Singular.Twisted.Basic`: the comparison isomorphism is the simp
-- normal form, so that `twistedHomologyπ_comp_twistedHomologyConstantIso_hom` below can be `simp`.
/-- The comparison of relative twisted homology with ordinary relative singular homology is the
map induced on homology by the comparison of the relative chain complexes. -/
lemma twistedHomologyConstantIso_hom (k : ℕ) :
    (P.twistedHomologyConstantIso M k).hom =
      HomologicalComplex.homologyMap (P.twistedChainComplexConstantIso M).hom k :=
  rfl

/-- The inverse of the comparison of relative twisted homology with ordinary relative singular
homology is the map induced on homology by the inverse comparison of the relative chain
complexes. -/
lemma twistedHomologyConstantIso_inv (k : ℕ) :
    (P.twistedHomologyConstantIso M k).inv =
      HomologicalComplex.homologyMap (P.twistedChainComplexConstantIso M).inv k :=
  rfl

/-- The comparison of relative twisted homology with ordinary relative singular homology is
compatible with the maps from the homology of the ambient space. -/
@[reassoc (attr := simp)]
lemma twistedHomologyπ_comp_twistedHomologyConstantIso_hom (k : ℕ) :
    P.twistedHomologyπ ((LocalCoefficientSystem.constantFunctor P.fst).obj M) k ≫
        (P.twistedHomologyConstantIso M k).hom =
      (LocalCoefficientSystem.twistedHomologyConstantIso P.fst M k).hom ≫
        P.singularHomologyπ M k := by
  rw [twistedHomologyConstantIso_hom, LocalCoefficientSystem.twistedHomologyConstantIso_hom,
    ← HomologicalComplex.homologyMap_comp,
    P.twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom M]
  -- `P.singularHomologyπ M k` is `HomologicalComplex.homologyMap (P.singularChainComplexπ M) k`,
  -- but only after unfolding the relative singular homology abbreviations, so the last step is
  -- an `exact` rather than a further rewrite.
  exact HomologicalComplex.homologyMap_comp _ _ k

end Constant

end TopPair
