/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality

/-!
# Relative singular cohomology with local coefficients

Let `(X, A)` be a topological pair and let `L` be a local coefficient system of `R`-modules on `X`.
Applying `Hom(-, M)` to the relative twisted chains of the pair gives its relative twisted cochain
complex, whose cohomology is the relative singular cohomology of `(X, A)` with coefficients in `L`
and values in `M`.

The twisted chains of `A` sit inside those of `X` as the summands indexed by the singular simplices
of `A`, so that inclusion is split in each degree.  Applying `Hom(-, M)` to the short exact
sequence `0 ⟶ C(A; L) ⟶ C(X; L) ⟶ C(X, A; L) ⟶ 0` therefore again gives a short exact sequence

`0 ⟶ C*(X, A; L) ⟶ C*(X; L) ⟶ C*(A; L) ⟶ 0`,

and its long exact cohomology sequence is the long exact sequence of the pair with local
coefficients.  This is the sequence in which the cap product with the orientation system expresses
Poincaré--Lefschetz duality, so the twisted theory, and not only the untwisted one of
`TauCeti.AlgebraicTopology.Cohomology.Relative`, is needed.

## Main declarations

* `TopPair.twistedCochainComplex` and `TopPair.twistedCohomology`: the relative twisted cochain
  complex of a pair and its cohomology.
* `TopPair.twistedCochainComplexCoefficientMap` and `TopPair.twistedCohomologyCoefficientMap`:
  change of local coefficient system.
* `TopPair.twistedCochainComplexMap` and `TopPair.twistedCohomologyMap`: the maps induced by a map
  of topological pairs.
* `TopPair.shortExact_twistedCochainComplexShortComplex`: the twisted cochain sequence of a pair is
  short exact.
* `TopPair.twistedCohomologyδ`: the connecting morphism `Hⁿ(A; L) ⟶ Hᵐ(X, A; L)` for `n + 1 = m`,
  with the exactness statements `TopPair.twistedCohomology_exact_relative`,
  `TopPair.twistedCohomology_exact_space` and `TopPair.twistedCohomology_exact_subspace`, and its
  naturality `TopPair.twistedCohomologyδ_naturality` in maps of pairs and
  `TopPair.twistedCohomologyδ_naturality_coefficient` in morphisms of local coefficient systems.
* `TopPair.twistedCohomologyConstantIso`: for a constant system, relative twisted cohomology is
  ordinary relative singular cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapters VII--VIII.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti

universe u v w

namespace TopPair

variable {R : Type u} [Ring R]

section Pair

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)

/-- The relative singular cochain complex of a topological pair with coefficients in a local
coefficient system `L` on its ambient space and values in `M`: in degree `n`, the `k`-module of
morphisms from the relative twisted `n`-chains to `M`. -/
abbrev twistedCochainComplex : CochainComplex (ModuleCat.{max v w} k) ℕ :=
  (P.twistedChainComplex L).linearYonedaObj k M

/-- The relative singular cohomology of a topological pair in degree `n`, with coefficients in a
local coefficient system on its ambient space and values in `M`. -/
abbrev twistedCohomology (n : ℕ) : ModuleCat.{max v w} k :=
  (P.twistedCochainComplex L k M).homology n

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R P.fst}

/-- The cochain map on relative twisted cochains induced by a morphism of local coefficient
systems. -/
abbrev twistedCochainComplexCoefficientMap (η : L ⟶ K) :
    P.twistedCochainComplex K k M ⟶ P.twistedCochainComplex L k M :=
  (ChainComplex.linearYonedaFunctor k M).map (P.twistedChainComplexCoefficientMap η).op

@[simp]
lemma twistedCochainComplexCoefficientMap_id
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) :
    P.twistedCochainComplexCoefficientMap k M (𝟙 L) = 𝟙 _ :=
  (congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (P.twistedChainComplexCoefficientMap_id L)).trans (CategoryTheory.Functor.map_id _ _)

@[reassoc]
lemma twistedCochainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    P.twistedCochainComplexCoefficientMap k M (η ≫ θ) =
      P.twistedCochainComplexCoefficientMap k M θ ≫
        P.twistedCochainComplexCoefficientMap k M η :=
  (congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (P.twistedChainComplexCoefficientMap_comp η θ)).trans
    (CategoryTheory.Functor.map_comp _ _ _)

/-- The degree-`n` component of the relative cochain map induced by a morphism of local
coefficient systems acts by precomposition. -/
@[simp]
lemma twistedCochainComplexCoefficientMap_f_apply (η : L ⟶ K) (n : ℕ)
    (g : (P.twistedCochainComplex K k M).X n) :
    (P.twistedCochainComplexCoefficientMap k M η).f n g =
      (P.twistedChainComplexCoefficientMap η).f n ≫ g := (rfl)

/-- The map on relative twisted cohomology induced by a morphism of local coefficient systems. -/
abbrev twistedCohomologyCoefficientMap (η : L ⟶ K) (n : ℕ) :
    P.twistedCohomology K k M n ⟶ P.twistedCohomology L k M n :=
  HomologicalComplex.homologyMap (P.twistedCochainComplexCoefficientMap k M η) n

@[simp]
lemma twistedCohomologyCoefficientMap_id
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (n : ℕ) :
    P.twistedCohomologyCoefficientMap k M (𝟙 L) n = 𝟙 _ :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
      (P.twistedCochainComplexCoefficientMap_id k M L)).trans
    (CategoryTheory.Functor.map_id _ _)

@[reassoc]
lemma twistedCohomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (n : ℕ) :
    P.twistedCohomologyCoefficientMap k M (η ≫ θ) n =
      P.twistedCohomologyCoefficientMap k M θ n ≫ P.twistedCohomologyCoefficientMap k M η n :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
      (P.twistedCochainComplexCoefficientMap_comp k M η θ)).trans
    (CategoryTheory.Functor.map_comp _ _ _)

end Coefficients

section LongExactSequence

/-- The twisted cochain sequence `C*(X, A; L) ⟶ C*(X; L) ⟶ C*(A; L)` of a topological pair
`(X, A)`: the image under `Hom(-, M)` of the twisted chain sequence of the pair. -/
abbrev twistedCochainComplexShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{max v w} k) ℕ) :=
  (P.twistedChainComplexShortComplex L).op.map (ChainComplex.linearYonedaFunctor k M)

/-- The first map of the twisted cochain sequence of a pair is the image under `Hom(-, M)` of the
quotient map from ambient to relative twisted chains. -/
lemma twistedCochainComplexShortComplex_f_eq :
    (P.twistedCochainComplexShortComplex L k M).f =
      (ChainComplex.linearYonedaFunctor k M).map (P.twistedChainComplexπ L).op := (rfl)

/-- The second map of the twisted cochain sequence of a pair is restriction from the ambient space
to the subspace. -/
lemma twistedCochainComplexShortComplex_g_eq :
    (P.twistedCochainComplexShortComplex L k M).g =
      LocalCoefficientSystem.twistedCochainComplexMap k M P.map L := (rfl)

/-- The twisted cochain sequence `0 ⟶ C*(X, A; L) ⟶ C*(X; L) ⟶ C*(A; L) ⟶ 0` of a topological
pair is short exact. -/
lemma shortExact_twistedCochainComplexShortComplex :
    (P.twistedCochainComplexShortComplex L k M).ShortExact :=
  ChainComplex.shortExact_map_linearYonedaFunctor k M
    (P.shortExact_twistedChainComplexShortComplex L)

/-- The map `Hⁿ(X, A; L) ⟶ Hⁿ(X; L)` from relative to absolute twisted cohomology. -/
abbrev twistedCohomologyπ (n : ℕ) :
    P.twistedCohomology L k M n ⟶ L.twistedCohomology k M n :=
  HomologicalComplex.homologyMap (P.twistedCochainComplexShortComplex L k M).f n

/-- The connecting morphism `Hⁿ(A; L) ⟶ Hᵐ(X, A; L)` of the long exact sequence of a topological
pair, where `n + 1 = m`. -/
abbrev twistedCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (P.subspaceSystem L).twistedCohomology k M n ⟶ P.twistedCohomology L k M m :=
  (P.shortExact_twistedCochainComplexShortComplex L k M).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma twistedCohomologyπ_comp_twistedCohomologyMap (n : ℕ) :
    P.twistedCohomologyπ L k M n ≫
        LocalCoefficientSystem.twistedCohomologyMap k M P.map L n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
        (P.twistedCochainComplexShortComplex L k M).zero).trans
      (HomologicalComplex.homologyMap_zero _ _ n)

@[reassoc (attr := simp)]
lemma twistedCohomologyMap_comp_twistedCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    LocalCoefficientSystem.twistedCohomologyMap k M P.map L n ≫
        P.twistedCohomologyδ L k M n m h = 0 :=
  (P.shortExact_twistedCochainComplexShortComplex L k M).comp_δ n m (by simpa)

/-- Exactness at relative cohomology: `Hⁿ(A; L) ⟶ Hᵐ(X, A; L) ⟶ Hᵐ(X; L)` is exact for
`n + 1 = m`. -/
lemma twistedCohomology_exact_relative (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      ((P.shortExact_twistedCochainComplexShortComplex L k M).δ_comp n m (by simpa))).Exact :=
  (P.shortExact_twistedCochainComplexShortComplex L k M).homology_exact₁ n m (by simpa)

/-- Exactness at ambient cohomology: `Hⁿ(X, A; L) ⟶ Hⁿ(X; L) ⟶ Hⁿ(A; L)` is exact. -/
lemma twistedCohomology_exact_space (n : ℕ) :
    (ShortComplex.mk _ _ (P.twistedCohomologyπ_comp_twistedCohomologyMap L k M n)).Exact :=
  (P.shortExact_twistedCochainComplexShortComplex L k M).homology_exact₂ n

/-- Exactness at subspace cohomology: `Hⁿ(X; L) ⟶ Hⁿ(A; L) ⟶ Hᵐ(X, A; L)` is exact for
`n + 1 = m`. -/
lemma twistedCohomology_exact_subspace (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (P.twistedCohomologyMap_comp_twistedCohomologyδ L k M n m h)).Exact :=
  (P.shortExact_twistedCochainComplexShortComplex L k M).homology_exact₃ n m (by simpa)

/-- The map from relative to absolute twisted cohomology is a monomorphism in degree zero. -/
instance : Mono (P.twistedCohomologyπ L k M 0) := by
  let _ : Mono (P.twistedCochainComplexShortComplex L k M).f :=
    (P.shortExact_twistedCochainComplexShortComplex L k M).mono_f
  let _ : Mono ((P.twistedCochainComplexShortComplex L k M).f.f 0) :=
    Functor.map_mono (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) 0)
      (P.twistedCochainComplexShortComplex L k M).f
  exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (P.twistedCochainComplexShortComplex L k M).f 0 fun i h ↦ by
      rw [ComplexShape.up_Rel] at h
      omega

section Coefficients

variable {L K : LocalCoefficientSystem.{u, v, max v w} R P.fst}

/-- The morphism between the twisted cochain sequences of a pair induced by a morphism of local
coefficient systems. -/
def twistedCochainComplexShortComplexCoefficientMap (η : L ⟶ K) :
    P.twistedCochainComplexShortComplex K k M ⟶
      P.twistedCochainComplexShortComplex L k M where
  τ₁ := P.twistedCochainComplexCoefficientMap k M η
  τ₂ := LocalCoefficientSystem.twistedCochainComplexCoefficientMap k M η
  τ₃ := LocalCoefficientSystem.twistedCochainComplexCoefficientMap k M
    ((LocalCoefficientSystem.pullback P.map.hom).map η)
  comm₁₂ := ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)).trans
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))
  comm₂₃ := ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (LocalCoefficientSystem.twistedChainComplexMap_naturality P.map η)).trans
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))

@[simp]
lemma twistedCochainComplexShortComplexCoefficientMap_τ₁ (η : L ⟶ K) :
    (P.twistedCochainComplexShortComplexCoefficientMap k M η).τ₁ =
      P.twistedCochainComplexCoefficientMap k M η := (rfl)

@[simp]
lemma twistedCochainComplexShortComplexCoefficientMap_τ₂ (η : L ⟶ K) :
    (P.twistedCochainComplexShortComplexCoefficientMap k M η).τ₂ =
      LocalCoefficientSystem.twistedCochainComplexCoefficientMap k M η := (rfl)

@[simp]
lemma twistedCochainComplexShortComplexCoefficientMap_τ₃ (η : L ⟶ K) :
    (P.twistedCochainComplexShortComplexCoefficientMap k M η).τ₃ =
      LocalCoefficientSystem.twistedCochainComplexCoefficientMap k M
        ((LocalCoefficientSystem.pullback P.map.hom).map η) := (rfl)

/-- The map from relative to absolute twisted cohomology commutes with a change of local
coefficient system. -/
@[reassoc]
lemma twistedCohomologyπ_naturality_coefficient (η : L ⟶ K) (n : ℕ) :
    P.twistedCohomologyπ K k M n ≫
        LocalCoefficientSystem.twistedCohomologyCoefficientMap k M η n =
      P.twistedCohomologyCoefficientMap k M η n ≫ P.twistedCohomologyπ L k M n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (P.twistedCochainComplexShortComplexCoefficientMap k M η).comm₁₂.symm).trans
        (HomologicalComplex.homologyMap_comp _ _ n)

/-- The connecting morphism of the long exact sequence in relative twisted cohomology commutes
with a change of local coefficient system. -/
@[reassoc]
lemma twistedCohomologyδ_naturality_coefficient (η : L ⟶ K) (n m : ℕ) (h : n + 1 = m := by lia) :
    P.twistedCohomologyδ K k M n m h ≫ P.twistedCohomologyCoefficientMap k M η m =
      LocalCoefficientSystem.twistedCohomologyCoefficientMap k M
          ((LocalCoefficientSystem.pullback P.map.hom).map η) n ≫
        P.twistedCohomologyδ L k M n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (P.twistedCochainComplexShortComplexCoefficientMap k M η)
    (P.shortExact_twistedCochainComplexShortComplex K k M)
    (P.shortExact_twistedCochainComplexShortComplex L k M) n m (by simpa)

end Coefficients

end LongExactSequence

end Pair

section Functoriality

variable (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)
  {P Q : TopPair.{v}} (f : P ⟶ Q) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)

/-- The cochain map on relative twisted cochains induced by a map of topological pairs. -/
abbrev twistedCochainComplexMap :
    Q.twistedCochainComplex L k M ⟶
      P.twistedCochainComplex ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k M :=
  (ChainComplex.linearYonedaFunctor k M).map (twistedChainComplexMap f L).op

/-- The degree-`n` component of the relative cochain map induced by a map of pairs acts by
precomposition with the induced morphism of relative twisted chains. -/
@[simp]
lemma twistedCochainComplexMap_f_apply (n : ℕ) (g : (Q.twistedCochainComplex L k M).X n) :
    (twistedCochainComplexMap k M f L).f n g = (twistedChainComplexMap f L).f n ≫ g := (rfl)

/-- The map on relative twisted cohomology induced by a map of topological pairs. -/
abbrev twistedCohomologyMap (n : ℕ) :
    Q.twistedCohomology L k M n ⟶
      P.twistedCohomology ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k M n :=
  HomologicalComplex.homologyMap (twistedCochainComplexMap k M f L) n

/-- The relative cochain map induced by a map of pairs commutes with a change of coefficients on
the target pair. -/
@[reassoc]
lemma twistedCochainComplexMap_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R Q.fst} (η : L ⟶ K) :
    Q.twistedCochainComplexCoefficientMap k M η ≫ twistedCochainComplexMap k M f L =
      twistedCochainComplexMap k M f K ≫
        P.twistedCochainComplexCoefficientMap k M
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) :=
  ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (twistedChainComplexMap_naturality f L η)).trans
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))

/-- The cohomology form of `TopPair.twistedCochainComplexMap_naturality`. -/
@[reassoc]
lemma twistedCohomologyMap_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R Q.fst} (η : L ⟶ K) (n : ℕ) :
    Q.twistedCohomologyCoefficientMap k M η n ≫ twistedCohomologyMap k M f L n =
      twistedCohomologyMap k M f K n ≫
        P.twistedCohomologyCoefficientMap k M
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) n :=
  ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
      (twistedCochainComplexMap_naturality k M f L η)).trans
      ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _))

/-- The identity map of a pair induces on relative twisted cochains the coefficient-change map
coming from the canonical identification of a system with its pullback along the identity. -/
@[simp]
lemma twistedCochainComplexMap_id (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) :
    twistedCochainComplexMap k M (𝟙 P) L =
      P.twistedCochainComplexCoefficientMap k M (fstPullbackIdIso P L).hom :=
  congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
    (twistedChainComplexMap_id L)

/-- The cohomology form of `TopPair.twistedCochainComplexMap_id`. -/
@[simp]
lemma twistedCohomologyMap_id (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (n : ℕ) :
    twistedCohomologyMap k M (𝟙 P) L n =
      P.twistedCohomologyCoefficientMap k M (fstPullbackIdIso P L).hom n :=
  congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
    (twistedCochainComplexMap_id k M P L)

variable {S : TopPair.{v}} (g : Q ⟶ S) (K : LocalCoefficientSystem.{u, v, max v w} R S.fst)

/-- Maps of relative twisted cochain complexes respect composition of maps of pairs, after the
canonical comparison between pullback along a composite and iterated pullback. -/
@[simp, reassoc]
lemma twistedCochainComplexMap_comp :
    twistedCochainComplexMap k M (f ≫ g) K =
      twistedCochainComplexMap k M g K ≫
        twistedCochainComplexMap k M f
            ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) ≫
          P.twistedCochainComplexCoefficientMap k M (fstPullbackCompIso f g K).hom := by
  simp only [twistedCochainComplexMap, twistedChainComplexMap_comp, op_comp,
    twistedCochainComplexCoefficientMap, Category.assoc]
  exact ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).trans
    (congrArg ((ChainComplex.linearYonedaFunctor k M).map _ ≫ ·)
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))

/-- The cohomology form of `TopPair.twistedCochainComplexMap_comp`. -/
@[simp, reassoc]
lemma twistedCohomologyMap_comp (n : ℕ) :
    twistedCohomologyMap k M (f ≫ g) K n =
      twistedCohomologyMap k M g K n ≫
        twistedCohomologyMap k M f
            ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) n ≫
          P.twistedCohomologyCoefficientMap k M (fstPullbackCompIso f g K).hom n := by
  rw [twistedCohomologyMap, twistedCochainComplexMap_comp]
  exact ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _).trans
    (congrArg ((HomologicalComplex.homologyFunctor _ _ n).map _ ≫ ·)
      ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _))

end Functoriality

section Naturality

variable (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)
  {P Q : TopPair.{v}} (f : P ⟶ Q) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)

/-- The cochain map on subspace twisted cochains induced by a map of pairs: restriction along the
subspace component, after the canonical comparison of the pulled-back coefficient systems. -/
abbrev twistedSubspaceCochainComplexMap :
    (Q.subspaceSystem L).twistedCochainComplex k M ⟶
      (P.subspaceSystem
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)).twistedCochainComplex k M :=
  (ChainComplex.linearYonedaFunctor k M).map (twistedSubspaceChainComplexMap f L).op

/-- The morphism between the twisted cochain sequences of two pairs induced by a map of pairs. -/
def twistedCochainComplexShortComplexMap :
    Q.twistedCochainComplexShortComplex L k M ⟶
      P.twistedCochainComplexShortComplex
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k M where
  τ₁ := twistedCochainComplexMap k M f L
  τ₂ := LocalCoefficientSystem.twistedCochainComplexMap k M (Hom.fst f) L
  τ₃ := twistedSubspaceCochainComplexMap k M f L
  comm₁₂ := ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (twistedChainComplexπ_comp_twistedChainComplexMap f L)).trans
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))
  comm₂₃ := ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (twistedChainComplexMap_naturality_pair f L)).trans
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))

@[simp]
lemma twistedCochainComplexShortComplexMap_τ₁ :
    (twistedCochainComplexShortComplexMap k M f L).τ₁ =
      twistedCochainComplexMap k M f L := (rfl)

@[simp]
lemma twistedCochainComplexShortComplexMap_τ₂ :
    (twistedCochainComplexShortComplexMap k M f L).τ₂ =
      LocalCoefficientSystem.twistedCochainComplexMap k M (Hom.fst f) L := (rfl)

@[simp]
lemma twistedCochainComplexShortComplexMap_τ₃ :
    (twistedCochainComplexShortComplexMap k M f L).τ₃ =
      twistedSubspaceCochainComplexMap k M f L := (rfl)

/-- The map from relative to absolute twisted cohomology is natural in the pair. -/
@[reassoc]
lemma twistedCohomologyπ_naturality (n : ℕ) :
    Q.twistedCohomologyπ L k M n ≫
        LocalCoefficientSystem.twistedCohomologyMap k M (Hom.fst f) L n =
      twistedCohomologyMap k M f L n ≫
        P.twistedCohomologyπ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k M n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (twistedCochainComplexShortComplexMap k M f L).comm₁₂.symm).trans
        (HomologicalComplex.homologyMap_comp _ _ n)

/-- The connecting morphism of the long exact sequence in relative twisted cohomology is natural
in maps of topological pairs. -/
@[reassoc]
lemma twistedCohomologyδ_naturality (n m : ℕ) (h : n + 1 = m := by lia) :
    Q.twistedCohomologyδ L k M n m h ≫ twistedCohomologyMap k M f L m =
      HomologicalComplex.homologyMap (twistedSubspaceCochainComplexMap k M f L) n ≫
        P.twistedCohomologyδ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k M n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (twistedCochainComplexShortComplexMap k M f L)
    (Q.shortExact_twistedCochainComplexShortComplex L k M)
    (P.shortExact_twistedCochainComplexShortComplex _ k M) n m (by simpa)

end Naturality

section Constant

variable (P : TopPair.{v}) (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  (M N : ModuleCat.{max v w} R)

/-- For a constant local coefficient system, the relative twisted cochain complex of a pair is the
ordinary relative singular cochain complex with the same coefficient module. -/
def twistedCochainComplexConstantIso :
    P.twistedCochainComplex ((LocalCoefficientSystem.constantFunctor P.fst).obj N) k M ≅
      P.singularCochainComplex N k M :=
  ((ChainComplex.linearYonedaFunctor k M).mapIso (P.twistedChainComplexConstantIso N).op).symm

@[simp]
lemma twistedCochainComplexConstantIso_hom :
    (P.twistedCochainComplexConstantIso k M N).hom =
      (ChainComplex.linearYonedaFunctor k M).map
        (P.twistedChainComplexConstantIso N).inv.op := (rfl)

@[simp]
lemma twistedCochainComplexConstantIso_inv :
    (P.twistedCochainComplexConstantIso k M N).inv =
      (ChainComplex.linearYonedaFunctor k M).map
        (P.twistedChainComplexConstantIso N).hom.op := (rfl)

/-- For a constant local coefficient system, relative twisted cohomology is ordinary relative
singular cohomology. -/
def twistedCohomologyConstantIso (n : ℕ) :
    P.twistedCohomology ((LocalCoefficientSystem.constantFunctor P.fst).obj N) k M n ≅
      P.singularCohomology N k M n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (P.twistedCochainComplexConstantIso k M N)

@[simp]
lemma twistedCohomologyConstantIso_hom (n : ℕ) :
    (P.twistedCohomologyConstantIso k M N n).hom =
      HomologicalComplex.homologyMap (P.twistedCochainComplexConstantIso k M N).hom n := (rfl)

@[simp]
lemma twistedCohomologyConstantIso_inv (n : ℕ) :
    (P.twistedCohomologyConstantIso k M N n).inv =
      HomologicalComplex.homologyMap (P.twistedCochainComplexConstantIso k M N).inv n := (rfl)

end Constant

end TopPair
