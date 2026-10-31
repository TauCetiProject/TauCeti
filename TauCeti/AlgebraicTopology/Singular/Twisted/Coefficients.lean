/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import TauCeti.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# The coefficient long exact sequence in twisted singular homology

A short exact sequence of local coefficient systems on a space induces a short exact sequence
of twisted singular chain complexes. In each degree the chain module is a coproduct of fibres,
and coproducts of modules are exact. There is no flatness hypothesis on the fibres.

`TauCeti.LocalCoefficientSystem.twistedChainComplexFunctor` preserves finite limits and finite
colimits. Applying the homology sequence to its image gives
`CategoryTheory.ShortComplex.ShortExact.twistedHomologyδ`, the coefficient connecting morphism
`Hₙ(X; L₃) ⟶ Hₘ(X; L₁)` for `m + 1 = n`. The three exactness statements and naturality use the
existing maps `TauCeti.LocalCoefficientSystem.twistedHomologyCoefficientMap`. In degree zero,
the map `H₀(X; L₂) ⟶ H₀(X; L₃)` is an epimorphism.

These are sequences varying the coefficients on one space. They supply the geometric connecting
maps needed to compare local-coefficient homology with algebraic homology theories, in particular
group homology for a classifying space.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients).
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Section III.1 (coefficient sequences).

The exactness argument uses Mathlib's AB4 instance for modules and its homology-sequence API.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u v

namespace TauCeti.LocalCoefficientSystem

variable (R : Type u) [Ring R] (X : TopCat.{v})

/-- Twisted singular chain complexes as a functor of the local coefficient system.
The abbreviation keeps its objects and maps definitionally identified with the existing
chain complexes and coefficient maps in homology-sequence statements. -/
abbrev twistedChainComplexFunctor :
    LocalCoefficientSystem.{u, v, v} R X ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj := twistedChainComplex
  map := twistedChainComplexCoefficientMap
  map_id := twistedChainComplexCoefficientMap_id
  map_comp := twistedChainComplexCoefficientMap_comp

/-- The twisted chain functor sends a local system to its twisted chain complex. -/
@[simp]
lemma twistedChainComplexFunctor_obj (L : LocalCoefficientSystem.{u, v, v} R X) :
    (twistedChainComplexFunctor R X).obj L = twistedChainComplex L :=
  (rfl)

/-- The twisted chain functor acts by the existing coefficient chain map. -/
@[simp]
lemma twistedChainComplexFunctor_map {L K : LocalCoefficientSystem.{u, v, v} R X} (f : L ⟶ K) :
    (twistedChainComplexFunctor R X).map f = twistedChainComplexCoefficientMap f :=
  (rfl)

variable {R X}

-- Evaluation in a chain degree is restriction to the initial vertices of singular simplices,
-- followed by the coproduct functor. The discrete-diagram comparison accounts for the two
-- presentations of the same coproduct without unfolding the twisted chain construction.
private def twistedChainComplexFunctorEvalIso (n : ℕ) :
    twistedChainComplexFunctor R X ⋙
        HomologicalComplex.eval (ModuleCat.{v} R) (.down ℕ) n ≅
      (Functor.whiskeringLeft (Discrete ((TopCat.toSSet.obj X) _⦋n⦌))
        (FundamentalGroupoid X) (ModuleCat.{v} R)).obj
        (Discrete.functor (fun σ ↦ initialVertex σ)) ⋙ colim := by
  refine NatIso.ofComponents (fun L ↦ eqToIso (twistedChainComplex_X L n) ≪≫
    (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F :=
      Discrete.functor (fun σ : (TopCat.toSSet.obj X) _⦋n⦌ ↦ initialVertex σ) ⋙ L))).symm) ?_
  intro L K f
  dsimp only [twistedChainComplexFunctor, Functor.comp_obj, Functor.comp_map,
    HomologicalComplex.eval]
  apply twistedChainComplex_hom_ext L
  intro σ
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc]
  simp

/-- Twisted chains preserve finite limits of local coefficient systems. In particular a
coefficient monomorphism stays injective on chains, without any flatness assumption. -/
instance : PreservesFiniteLimits (twistedChainComplexFunctor R X) where
  preservesFiniteLimits J _ _ :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦ by
      have : PreservesFiniteLimits (twistedChainComplexFunctor R X ⋙
          HomologicalComplex.eval (ModuleCat.{v} R) (.down ℕ) n) :=
        preservesFiniteLimits_of_natIso (twistedChainComplexFunctorEvalIso n).symm
      infer_instance

/-- Twisted chains preserve finite colimits of local coefficient systems. -/
instance : PreservesFiniteColimits (twistedChainComplexFunctor R X) where
  preservesFiniteColimits J _ _ :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦ by
      have : PreservesFiniteColimits (twistedChainComplexFunctor R X ⋙
          HomologicalComplex.eval (ModuleCat.{v} R) (.down ℕ) n) :=
        preservesFiniteColimits_of_natIso (twistedChainComplexFunctorEvalIso n).symm
      infer_instance

end TauCeti.LocalCoefficientSystem

namespace CategoryTheory.ShortComplex.ShortExact

open TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  {S T : ShortComplex (TauCeti.LocalCoefficientSystem.{u, v, v} R X)} (hS : S.ShortExact)

include hS

/-- The coefficient connecting morphism in twisted singular homology associated to a short exact
sequence `0 ⟶ L₁ ⟶ L₂ ⟶ L₃ ⟶ 0` of local systems on one space. -/
def twistedHomologyδ (n m : ℕ) (h : m + 1 = n) :
    twistedHomology S.X₃ n ⟶ twistedHomology S.X₁ m :=
  (hS.map_of_exact (twistedChainComplexFunctor R X)).δ n m h

/-- The coefficient connecting map is the homology connecting map of the induced short exact
sequence of twisted chain complexes. -/
lemma twistedHomologyδ_eq_δ (n m : ℕ) (h : m + 1 = n) :
    hS.twistedHomologyδ n m h =
      (hS.map_of_exact (twistedChainComplexFunctor R X)).δ n m h :=
  (rfl)

/-- The coefficient connecting map followed by the map induced by `L₁ ⟶ L₂` is zero. -/
@[reassoc (attr := simp)]
lemma twistedHomologyδ_comp (n m : ℕ) (h : m + 1 = n) :
    hS.twistedHomologyδ n m h ≫ twistedHomologyCoefficientMap S.f m = 0 :=
  (hS.map_of_exact (twistedChainComplexFunctor R X)).δ_comp n m h

/-- The map induced by `L₂ ⟶ L₃` followed by the coefficient connecting map is zero. -/
@[reassoc (attr := simp)]
lemma comp_twistedHomologyδ (n m : ℕ) (h : m + 1 = n) :
    twistedHomologyCoefficientMap S.g n ≫ hS.twistedHomologyδ n m h = 0 :=
  (hS.map_of_exact (twistedChainComplexFunctor R X)).comp_δ n m h

/-- Exactness at `Hₘ(X; L₁)` in the coefficient long exact sequence. -/
lemma twistedHomology_exact₁ (n m : ℕ) (h : m + 1 = n) :
    (ShortComplex.mk _ _ (hS.twistedHomologyδ_comp n m h)).Exact :=
  (hS.map_of_exact (twistedChainComplexFunctor R X)).homology_exact₁ n m h

/-- Exactness at `Hₙ(X; L₂)` in the coefficient long exact sequence. -/
lemma twistedHomology_exact₂ (n : ℕ) :
    ((S.map (twistedChainComplexFunctor R X)).map
      (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (hS.map_of_exact (twistedChainComplexFunctor R X)).homology_exact₂ n

/-- Exactness at `Hₙ(X; L₃)` in the coefficient long exact sequence. -/
lemma twistedHomology_exact₃ (n m : ℕ) (h : m + 1 = n) :
    (ShortComplex.mk _ _ (hS.comp_twistedHomologyδ n m h)).Exact :=
  (hS.map_of_exact (twistedChainComplexFunctor R X)).homology_exact₃ n m h

/-- A morphism of short exact coefficient sequences commutes with their connecting maps. -/
@[reassoc]
lemma twistedHomologyδ_naturality (hT : T.ShortExact) (φ : S ⟶ T)
    (n m : ℕ) (h : m + 1 = n) :
    hS.twistedHomologyδ n m h ≫ twistedHomologyCoefficientMap φ.τ₁ m =
      twistedHomologyCoefficientMap φ.τ₃ n ≫ hT.twistedHomologyδ n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((twistedChainComplexFunctor R X).mapShortComplex.map φ)
    (hS.map_of_exact _) (hT.map_of_exact _) n m h

/-- The coefficient long exact sequence ends with a surjection
`H₀(X; L₂) ⟶ H₀(X; L₃) ⟶ 0`. -/
lemma epi_twistedHomologyCoefficientMap_zero : Epi (twistedHomologyCoefficientMap S.g 0) := by
  have : Epi (twistedChainComplexCoefficientMap S.g) :=
    (hS.map_of_exact (twistedChainComplexFunctor R X)).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (twistedChainComplexCoefficientMap S.g) 0 (by simp)

end CategoryTheory.ShortComplex.ShortExact
