/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality

/-!
# The constant-system comparison for relative singular homology

The comparison of relative twisted chains with ordinary relative singular chains commutes
with maps of pairs and changes of the coefficient module. It identifies the short exact
sequences of chains, and hence the connecting maps in the long exact sequences, with no
change of sign. These identities allow calculations with ordinary relative homology to be
used in the local-coefficient theory.

The restriction and pullback of a constant system are identified with the constant system
by `LocalCoefficientSystem.pullbackConstantIso`. In particular, the pair-map square retains
the coefficient comparison on its source rather than treating pullback as a strict equality.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] {P Q : TopPair.{v}}
  (M : ModuleCat.{max v w} R)

/-- The constant-system comparison on relative chains is natural in maps of pairs, after
identifying the pullback of the target constant system with the source constant system. -/
@[reassoc]
lemma twistedChainComplexConstantIso_hom_pair_naturality (f : P ⟶ Q) :
    twistedChainComplexMap f ((LocalCoefficientSystem.constantFunctor Q.fst).obj M) ≫
        (Q.twistedChainComplexConstantIso M).hom =
      P.twistedChainComplexCoefficientMap
          (LocalCoefficientSystem.pullbackConstantIso (Hom.fst f).hom M).hom ≫
        (P.twistedChainComplexConstantIso M).hom ≫ singularChainComplexMap f M := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj
      ((LocalCoefficientSystem.constantFunctor Q.fst).obj M)))).1
  simp only [twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom_assoc]
  -- Reassociate the absolute comparison before composing it with the ordinary quotient map;
  -- its codomain is expressed via the absolute singular functor rather than the pair functor.
  calc
    _ = (LocalCoefficientSystem.twistedChainComplexCoefficientMap
          (LocalCoefficientSystem.pullbackConstantIso (Hom.fst f).hom M).hom ≫
        (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M).hom ≫
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj M).map
          (Hom.fst f) ≫ Q.singularChainComplexπ M)) :=
      LocalCoefficientSystem.twistedChainComplexConstantIso_hom_space_naturality_assoc
        (Hom.fst f) M (Q.singularChainComplexπ M)
    _ = _ := by
      erw [TauCeti.singularChainComplexFunctor_obj_map, singularChainComplexπ_pair_naturality]
      erw [Category.assoc]
      rfl

/-- The constant-system comparison on relative homology is natural in maps of pairs. -/
@[reassoc]
lemma twistedHomologyConstantIso_hom_pair_naturality (f : P ⟶ Q) (n : ℕ) :
    twistedHomologyMap f ((LocalCoefficientSystem.constantFunctor Q.fst).obj M) n ≫
        (Q.twistedHomologyConstantIso M n).hom =
      P.twistedHomologyCoefficientMap
          (LocalCoefficientSystem.pullbackConstantIso (Hom.fst f).hom M).hom n ≫
        (P.twistedHomologyConstantIso M n).hom ≫ P.singularHomologyMap f M n := by
  have h := congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
    (twistedChainComplexConstantIso_hom_pair_naturality M f)
  simpa only [HomologicalComplex.homologyMap_comp, twistedHomologyConstantIso_hom,
    twistedHomologyMap, twistedHomologyCoefficientMap] using h

variable (P)

/-- The constant-system comparison on relative chains is natural in the coefficient module. -/
@[reassoc]
lemma twistedChainComplexConstantIso_hom_naturality
    {M N : ModuleCat.{max v w} R} (φ : M ⟶ N) :
    P.twistedChainComplexCoefficientMap ((LocalCoefficientSystem.constantFunctor P.fst).map φ) ≫
        (P.twistedChainComplexConstantIso N).hom =
      (P.twistedChainComplexConstantIso M).hom ≫
        ((SSetPair.chainComplexFunctor (ModuleCat.{max v w} R)).map φ).app (toSSetPair.obj P) := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.constantFunctor P.fst).obj M))).1
  simp only [twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom,
    twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom_assoc]
  -- As in the pair-map square, use the absolute comparison before the quotient map.
  calc
    _ = (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).map φ).app
          P.fst ≫ P.singularChainComplexπ N :=
      LocalCoefficientSystem.twistedChainComplexConstantIso_hom_naturality_assoc
        P.fst φ (P.singularChainComplexπ N)
    _ = _ := by
      rw [singularChainComplexπ_coefficient_naturality]
      erw [Category.assoc]
      rfl

/-- The constant-system comparison on relative homology is natural in the coefficient module.
The ordinary coefficient map is induced by the relative singular chain bifunctor. -/
@[reassoc]
lemma twistedHomologyConstantIso_hom_naturality
    {M N : ModuleCat.{max v w} R} (φ : M ⟶ N) (n : ℕ) :
    P.twistedHomologyCoefficientMap ((LocalCoefficientSystem.constantFunctor P.fst).map φ) n ≫
        (P.twistedHomologyConstantIso N n).hom =
      (P.twistedHomologyConstantIso M n).hom ≫
        HomologicalComplex.homologyMap
          (((SSetPair.chainComplexFunctor (ModuleCat.{max v w} R)).map φ).app
            (toSSetPair.obj P)) n := by
  have h := congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
    (P.twistedChainComplexConstantIso_hom_naturality φ)
  simpa only [HomologicalComplex.homologyMap_comp, twistedHomologyConstantIso_hom,
    twistedHomologyCoefficientMap] using h

/-- The constant-system comparison identifies the entire short exact chain sequence of a pair
with its ordinary singular chain sequence. On subspace chains it first identifies the
restriction of the ambient constant system with the constant system on the subspace. -/
def twistedChainComplexShortComplexConstantIso :
    P.twistedChainComplexShortComplex ((LocalCoefficientSystem.constantFunctor P.fst).obj M) ≅
      P.singularChainComplexShortComplex M :=
  ShortComplex.isoMk
    (LocalCoefficientSystem.twistedChainComplexCoefficientIso
        (LocalCoefficientSystem.pullbackConstantIso P.map.hom M) ≪≫
      LocalCoefficientSystem.twistedChainComplexConstantIso P.snd M)
    (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M)
    (P.twistedChainComplexConstantIso M)
    (by
      -- State the square with its explicit components before identifying the short-complex
      -- projections, whose chain objects use the simplicial rather than singular functor.
      erw [Iso.trans_hom, LocalCoefficientSystem.twistedChainComplexCoefficientIso_hom]
      exact ((LocalCoefficientSystem.twistedChainComplexConstantIso_hom_space_naturality
        P.map M).trans (Category.assoc _ _ _).symm).symm)
    (P.twistedChainComplexπ_comp_twistedChainComplexConstantIso_hom M).symm

@[simp]
lemma twistedChainComplexShortComplexConstantIso_hom_τ₁ :
    (P.twistedChainComplexShortComplexConstantIso M).hom.τ₁ =
      LocalCoefficientSystem.twistedChainComplexCoefficientMap
          (LocalCoefficientSystem.pullbackConstantIso P.map.hom M).hom ≫
        (LocalCoefficientSystem.twistedChainComplexConstantIso P.snd M).hom := by
  -- The short-complex projection has chain objects expressed through two different functors.
  -- `erw` matches the component formula through those object identifications.
  dsimp only [twistedChainComplexShortComplexConstantIso, ShortComplex.isoMk]
  erw [Iso.trans_hom, LocalCoefficientSystem.twistedChainComplexCoefficientIso_hom]
  rfl

@[simp]
lemma twistedChainComplexShortComplexConstantIso_hom_τ₂ :
    (P.twistedChainComplexShortComplexConstantIso M).hom.τ₂ =
      (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M).hom :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexConstantIso_hom_τ₃ :
    (P.twistedChainComplexShortComplexConstantIso M).hom.τ₃ =
      (P.twistedChainComplexConstantIso M).hom :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexConstantIso_inv_τ₁ :
    (P.twistedChainComplexShortComplexConstantIso M).inv.τ₁ =
      (LocalCoefficientSystem.twistedChainComplexConstantIso P.snd M).inv ≫
        LocalCoefficientSystem.twistedChainComplexCoefficientMap
          (LocalCoefficientSystem.pullbackConstantIso P.map.hom M).inv := by
  dsimp only [twistedChainComplexShortComplexConstantIso, ShortComplex.isoMk,
    ShortComplex.homMk]
  erw [Iso.trans_inv, LocalCoefficientSystem.twistedChainComplexCoefficientIso_inv]
  rfl

@[simp]
lemma twistedChainComplexShortComplexConstantIso_inv_τ₂ :
    (P.twistedChainComplexShortComplexConstantIso M).inv.τ₂ =
      (LocalCoefficientSystem.twistedChainComplexConstantIso P.fst M).inv :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexConstantIso_inv_τ₃ :
    (P.twistedChainComplexShortComplexConstantIso M).inv.τ₃ =
      (P.twistedChainComplexConstantIso M).inv :=
  (rfl)

/-- The constant-system comparison preserves the connecting morphism of relative homology.
The boundary convention is the same on the twisted and ordinary sides. -/
@[reassoc (attr := simp)]
lemma twistedHomologyδ_comp_twistedHomologyConstantIso_hom
    (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomologyδ ((LocalCoefficientSystem.constantFunctor P.fst).obj M) n m h ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
          (LocalCoefficientSystem.pullbackConstantIso P.map.hom M).hom m ≫
        (LocalCoefficientSystem.twistedHomologyConstantIso P.snd M m).hom =
      (P.twistedHomologyConstantIso M n).hom ≫ P.singularHomologyδ M n m h := by
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (P.twistedChainComplexShortComplexConstantIso M).hom
    (P.shortExact_twistedChainComplexShortComplex _)
    (P.shortExact_singularChainComplexShortComplex M) n m (by simpa)
  rw [twistedChainComplexShortComplexConstantIso_hom_τ₁,
    twistedChainComplexShortComplexConstantIso_hom_τ₃] at hδ
  -- The restricted constant system and the constant system have different chain-object
  -- expressions; match homology of their composite through that identification.
  erw [HomologicalComplex.homologyMap_comp] at hδ
  simp only [twistedHomologyConstantIso_hom,
    LocalCoefficientSystem.twistedHomologyConstantIso_hom]
  exact hδ

end TopPair
