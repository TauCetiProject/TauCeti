/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalCoefficients
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.EquivariantMap

/-!
# Group naturality of classifying-space cohomology with dual local coefficients

A homomorphism `φ : G →* H` and a compatible coefficient map `ξ : A ⟶ Rep.res φ D` induce
pullback from the cohomology of `BH` with coefficients in `Homₖ(L_D, N)` to that of `BG` with
coefficients in `Homₖ(L_A, N)`. This is defined geometrically, by precomposing cochains with the
map of twisted chains induced by the strictly functorial map of Milnor's classifying spaces.

Under `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`, it is Mathlib's
`groupCohomology.map φ`, with coefficient map given by precomposition with `ξ`. These geometric
maps respect identities and reverse composition. No finiteness or projectivity hypothesis on
`A`, `D` or the module of values `N` is needed.

Twisted cohomology here is the cohomology of maps from twisted chains into `N`. In particular,
the result concerns dual local systems and does not identify `L_A` with its double dual.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.8.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace MonoidHom

variable {G H K : Type u} [Group G] [Group H] [Group K]
  (φ : G →* H) (k : Type u) [CommRing k]
  {A : Rep.{u} k G} {D : Rep.{u} k H}
  (N : Type u) [AddCommGroup N] [Module k N]

/-- Pullback in cohomology with dual local coefficients, induced by the map of classifying
spaces and a compatible coefficient map. On cochains it is precomposition with coefficient
change followed by pushforward of twisted chains. -/
def classifyingSpaceTwistedCohomologyMap (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    (classifyingSpaceLocalSystem k D).twistedCohomology k (ModuleCat.of k N) n ⟶
      (classifyingSpaceLocalSystem k A).twistedCohomology k (ModuleCat.of k N) n :=
  HomologicalComplex.homologyMap
    ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
      (twistedChainComplexCoefficientMap (φ.classifyingSpaceLocalSystemMapOver k ξ) ≫
        twistedChainComplexMap (TopCat.ofHom φ.classifyingSpaceMap)
          (classifyingSpaceLocalSystem k D)).op) n

/-- The geometric pullback is induced by precomposition with the map of twisted chains. -/
theorem classifyingSpaceTwistedCohomologyMap_def (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    φ.classifyingSpaceTwistedCohomologyMap k N ξ n =
      HomologicalComplex.homologyMap
        ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
          (twistedChainComplexCoefficientMap (φ.classifyingSpaceLocalSystemMapOver k ξ) ≫
            twistedChainComplexMap (TopCat.ofHom φ.classifyingSpaceMap)
              (classifyingSpaceLocalSystem k D)).op) n :=
  (rfl)

/-- The comparison with group cohomology is natural in the group and compatible coefficient
maps. The coefficient map on internal homs is precomposition, so the geometric map is
contravariant. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    φ.classifyingSpaceTwistedCohomologyMap k N ξ n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k D N n).hom ≫
        groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n := by
  have h := IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_over
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G)
    (isQuotientCoveringMap_classifyingSpaceProj H) k (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ N n
  rw [IsQuotientCoveringMap.associatedTwistedChainMap_def] at h
  rw [classifyingSpaceTwistedCohomologyMap_def,
    classifyingSpaceTwistedCohomologyIsoGroupCohomology_eq,
    classifyingSpaceTwistedCohomologyIsoGroupCohomology_eq]
  -- After exposing the chain maps, the remaining abbreviations specialize those of the
  -- quotient cover of Milnor's join; no instance search through bundled covers is needed.
  exact h

/-- The inverse comparison with group cohomology is also natural in the group. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_inv_naturality
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).inv =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k D N n).inv ≫
        φ.classifyingSpaceTwistedCohomologyMap k N ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality, Iso.inv_hom_id_assoc]

variable {k}

/-- Along the identity homomorphism the geometric pullback is the existing map induced by a
morphism of coefficient systems. -/
@[simp]
theorem classifyingSpaceTwistedCohomologyMap_id_hom {A' : Rep.{u} k G}
    (f : A ⟶ A') (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceTwistedCohomologyMap k N f n =
      twistedCohomologyCoefficientMap k (ModuleCat.of k N)
        (classifyingSpaceLocalSystemMap f) n := by
  apply (cancel_mono (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom).1
  rw [classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality,
    TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left]
  have h : (MonoidHom.id G).ihomTrivialPrecomp N f =
      (MonoidalClosed.pre f).app (Rep.trivial k G N) :=
    Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      LinearMap.ext fun ℓ ↦ LinearMap.ext fun a ↦
        (MonoidHom.id G).ihomTrivialPrecomp_hom_apply N f ℓ a
  exact congrArg (fun t ↦
    (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A' N n).hom ≫
      groupCohomology.map (MonoidHom.id G) t n) h

/-- Identity group and coefficient maps induce the identity on dual-local-system cohomology. -/
-- Match before the general identity-homomorphism rule reduces to coefficient change.
@[simp↓]
theorem classifyingSpaceTwistedCohomologyMap_id (A : Rep.{u} k G) (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceTwistedCohomologyMap k N (𝟙 A) n = 𝟙 _ := by
  apply (cancel_mono (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom).1
  rw [classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality,
    ihomTrivialPrecomp_id, groupCohomology.map_id, Category.comp_id, Category.id_comp]

/-- Pullback on dual-local-system cohomology reverses composites, including restriction of the
second coefficient map. -/
-- Match before simplification changes the restriction of the coefficient morphism.
@[simp↓, reassoc]
theorem classifyingSpaceTwistedCohomologyMap_comp (ψ : H →* K) {V : Rep.{u} k K}
    (ξ : A ⟶ Rep.res φ D) (ζ : D ⟶ Rep.res ψ V) (n : ℕ) :
    (ψ.comp φ).classifyingSpaceTwistedCohomologyMap k N (ξ ≫ (Rep.resFunctor φ).map ζ) n =
      ψ.classifyingSpaceTwistedCohomologyMap k N ζ n ≫
        φ.classifyingSpaceTwistedCohomologyMap k N ξ n := by
  apply (cancel_mono (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom).1
  have hs := (CommSq.mk
    (ψ.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality k N ζ n)).horiz_comp
      (CommSq.mk (φ.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality k N ξ n))
  rw [classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality,
    ihomTrivialPrecomp_comp, groupCohomology.map_comp]
  exact hs.w.symm

end MonoidHom
