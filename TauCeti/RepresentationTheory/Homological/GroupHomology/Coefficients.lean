/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.CoinvariantsTensor
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Resolution
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Naturality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Coefficient connecting maps computed by a projective resolution

For a complex `P` of projective representations, tensor coinvariants `(A ⊗ P)_G` are exact in
the coefficient representation `A`. Consequently a short exact coefficient sequence has a long
exact homology sequence when computed using any projective resolution of the trivial
representation. The isomorphism `groupHomologyIso` intertwines its connecting maps with
Mathlib's `groupHomology.δ`. Thus geometric resolutions compute the coefficient long exact
sequence, not just its individual groups and same-degree maps.

The chain comparison is Mathlib's inhomogeneous-to-bar identification followed by the comparison
map from the bar resolution to the chosen resolution. Its coefficient naturality makes it a
morphism of short exact sequences, so naturality of the homology connecting map applies.

## References

* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I.7 and III.1.

The tensor coinvariants and inhomogeneous chain comparison are Mathlib's constructions by
Amelia Livingston. We use the comparison-map description in
`Rep.groupHomologyIso_hom_eq_homologyMap`.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ProjectiveResolution

open Rep

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  (P : ProjectiveResolution (Rep.trivial k G k))
  {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)

/-- Computing group homology with a projective resolution carries Mathlib's coefficient
connecting map to the connecting map of the tensor-coinvariant coefficient sequence. -/
@[reassoc]
theorem groupHomology_δ_comp_groupHomologyIso_hom (i j : ℕ) (hij : j + 1 = i) :
    groupHomology.δ hS i j hij ≫ (groupHomologyIso S.X₁ j P).hom =
      (groupHomologyIso S.X₃ i P).hom ≫
        (P.complex.shortExact_map_coinvariantsTensorFunctor hS).δ i j hij := by
  let β : Rep.barComplex k G ⟶ P.complex :=
    ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P
  have hβ := (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k G) P).trans
    (Category.comp_id _)
  let ψ (A : Rep.{u} k G) : groupHomology.inhomogeneousChains A ⟶
      P.complex.coinvariantsTensorObj A :=
    (groupHomology.inhomogeneousChainsIso A).hom ≫
      (((coinvariantsTensor k G).obj A).mapHomologicalComplex _).map β
  have hψ {A B : Rep.{u} k G} (f : A ⟶ B) :
      groupHomology.chainsMap (MonoidHom.id G) f ≫ ψ B =
        ψ A ≫ (P.complex.coinvariantsTensorFunctor).map f := by
    dsimp only [ψ]
    rw [← Category.assoc, TauCeti.groupHomology.inhomogeneousChainsIso_hom_naturality,
      Category.assoc]
    rw [← (NatTrans.mapHomologicalComplex ((coinvariantsTensor k G).map f) _).naturality β,
      ← Category.assoc]
  let Φ : S.map (groupHomology.chainsFunctor k G) ⟶
      S.map P.complex.coinvariantsTensorFunctor :=
    { τ₁ := ψ S.X₁
      τ₂ := ψ S.X₂
      τ₃ := ψ S.X₃
      comm₁₂ := (hψ S.f).symm
      comm₂₃ := (hψ S.g).symm }
  rw [groupHomologyIso_hom_eq_homologyMap S.X₁ P β hβ,
    groupHomologyIso_hom_eq_homologyMap S.X₃ P β hβ]
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (groupHomology.map_chainsFunctor_shortExact hS)
    (P.complex.shortExact_map_coinvariantsTensorFunctor hS) i j hij

/-- The inverse projective-resolution comparison also intertwines coefficient connecting maps.
Together with coefficient naturality, this identifies the entire coefficient long exact sequence.
-/
@[reassoc]
theorem δ_comp_groupHomologyIso_inv (i j : ℕ) (hij : j + 1 = i) :
    (P.complex.shortExact_map_coinvariantsTensorFunctor hS).δ i j hij ≫
        (groupHomologyIso S.X₁ j P).inv =
      (groupHomologyIso S.X₃ i P).inv ≫ groupHomology.δ hS i j hij := by
  have h : CommSq (groupHomology.δ hS i j hij)
      (groupHomologyIso S.X₃ i P).hom (groupHomologyIso S.X₁ j P).hom
      ((P.complex.shortExact_map_coinvariantsTensorFunctor hS).δ i j hij) :=
    ⟨P.groupHomology_δ_comp_groupHomologyIso_hom hS i j hij⟩
  exact h.vert_inv.w

end CategoryTheory.ProjectiveResolution
