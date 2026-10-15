/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Normalized

/-!
# The normalized cubical chain complex with local coefficients

The normalized cubical chains with coefficients in a local system `L`, with their boundary, form
a chain complex of modules `L.normalizedTwistedCubicalChainComplex`. Morphisms of local systems
and continuous maps (from the complex of the pulled back system) induce chain maps. This packages
`TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Normalized` in the form in which it
is compared with the singular chains with local coefficients `twistedChainComplex`, as
`TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex` does for constant coefficients.

The chain maps induced by continuous maps compare two complexes in one category of modules, so
here the spaces live in a common universe; the underlying linear maps of
`TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.map` have no such restriction.

## Main definitions

* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplex L`: the normalized cubical
  chain complex with coefficients in `L`.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexCoefficientMap η`,
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap f L`: the induced chain
  maps.

## Main results

* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap_id`,
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap_comp`,
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap_naturality`:
  functoriality.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and XIV.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y Z : TopCat.{v}}

open NormalizedTwistedCubicalChain

-- Exposed, like `TauCeti.normalizedCubicalChainComplex`, so that the term `X n` is definitionally
-- `ModuleCat.of R (L.NormalizedTwistedCubicalChain n)`: the chain maps to and from
-- `twistedChainComplex` in the comparison are built from linear maps on the normalized chains.
/-- The **normalized cubical chain complex with coefficients in a local system** `L`. -/
@[expose] def normalizedTwistedCubicalChainComplex (L : LocalCoefficientSystem.{u, v, w} R X) :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (L.NormalizedTwistedCubicalChain n))
    (fun n ↦ ModuleCat.ofHom (boundary L n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, boundary_boundary]
      rfl

/-- The terms of the normalized cubical chain complex are the normalized chains. -/
@[simp]
theorem normalizedTwistedCubicalChainComplex_X (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    L.normalizedTwistedCubicalChainComplex.X n =
      ModuleCat.of R (L.NormalizedTwistedCubicalChain n) :=
  (rfl)

/-- The differential of the normalized cubical chain complex is the boundary. -/
@[simp]
theorem normalizedTwistedCubicalChainComplex_d_apply (L : LocalCoefficientSystem.{u, v, w} R X)
    (n : ℕ)
    (x : L.NormalizedTwistedCubicalChain (n + 1)) :
    L.normalizedTwistedCubicalChainComplex.d (n + 1) n x = boundary L n x := by
  simp only [normalizedTwistedCubicalChainComplex, ChainComplex.of_d]
  rfl

/-- The chain map of normalized cubical chain complexes induced by a morphism of local
systems. -/
def normalizedTwistedCubicalChainComplexCoefficientMap {L K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) : L.normalizedTwistedCubicalChainComplex ⟶ K.normalizedTwistedCubicalChainComplex :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (coefficientMap η n)) fun n ↦ by
    simp only [normalizedTwistedCubicalChainComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp,
      coefficientMap_boundary]

/-- The components of the chain map induced by a morphism of local systems. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexCoefficientMap_f
    {L K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K) (n : ℕ) :
    (normalizedTwistedCubicalChainComplexCoefficientMap η).f n =
      ModuleCat.ofHom (coefficientMap η n) := by
  unfold normalizedTwistedCubicalChainComplexCoefficientMap
  rfl

/-- The chain map of normalized cubical chain complexes induced by a continuous map `f`, from the
complex with coefficients in `f⁎L` to the complex with coefficients in `L`. -/
def normalizedTwistedCubicalChainComplexMap (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v, w} R Y) :
    ((pullback f).obj L).normalizedTwistedCubicalChainComplex ⟶
      L.normalizedTwistedCubicalChainComplex :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (map f L n)) fun n ↦ by
    simp only [normalizedTwistedCubicalChainComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp,
      map_boundary]

/-- The components of the chain map induced by a continuous map. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexMap_f (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v, w} R Y) (n : ℕ) :
    (normalizedTwistedCubicalChainComplexMap f L).f n = ModuleCat.ofHom (map f L n) := by
  unfold normalizedTwistedCubicalChainComplexMap
  rfl

/-- The identity of a local system induces the identity chain map. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexCoefficientMap_id
    (L : LocalCoefficientSystem.{u, v, w} R X) :
    normalizedTwistedCubicalChainComplexCoefficientMap (𝟙 L) = 𝟙 _ := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexCoefficientMap_f, coefficientMap_id,
    HomologicalComplex.id_f]
  rfl

/-- A composite of morphisms of local systems induces the composite chain map. -/
theorem normalizedTwistedCubicalChainComplexCoefficientMap_comp
    {L K J : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K) (θ : K ⟶ J) :
    normalizedTwistedCubicalChainComplexCoefficientMap (η ≫ θ) =
      normalizedTwistedCubicalChainComplexCoefficientMap η ≫
        normalizedTwistedCubicalChainComplexCoefficientMap θ := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexCoefficientMap_f, HomologicalComplex.comp_f,
    coefficientMap_comp, ModuleCat.ofHom_comp]
  rfl

/-- The identity map induces on the normalized cubical chain complex the chain map coming from
the identification of a system with its pullback along the identity. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexMap_id (L : LocalCoefficientSystem.{u, v, w} R X) :
    normalizedTwistedCubicalChainComplexMap (ContinuousMap.id X) L =
      normalizedTwistedCubicalChainComplexCoefficientMap ((pullbackIdIso X).hom.app L) := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    NormalizedTwistedCubicalChain.map_id]
  rfl

/-- A composite of continuous maps induces on normalized cubical chain complexes the composite of
the two induced chain maps, after the identification of the pullback along the composite with
the iterated pullback. -/
theorem normalizedTwistedCubicalChainComplexMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (L : LocalCoefficientSystem.{u, v, w} R Z) :
    normalizedTwistedCubicalChainComplexMap (g.comp f) L =
      normalizedTwistedCubicalChainComplexCoefficientMap ((pullbackCompIso f g).hom.app L) ≫
        normalizedTwistedCubicalChainComplexMap f ((pullback g).obj L) ≫
          normalizedTwistedCubicalChainComplexMap g L := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    HomologicalComplex.comp_f, NormalizedTwistedCubicalChain.map_comp, ModuleCat.ofHom_comp]
  rfl

/-- The chain map induced by a continuous map is natural in the coefficient system. -/
theorem normalizedTwistedCubicalChainComplexMap_naturality (f : C(X, Y))
    {L K : LocalCoefficientSystem.{u, v, w} R Y} (η : L ⟶ K) :
    normalizedTwistedCubicalChainComplexMap f L ≫
        normalizedTwistedCubicalChainComplexCoefficientMap η =
      normalizedTwistedCubicalChainComplexCoefficientMap ((pullback f).map η) ≫
        normalizedTwistedCubicalChainComplexMap f K := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    HomologicalComplex.comp_f]
  exact congrArg ModuleCat.ofHom (NormalizedTwistedCubicalChain.coefficientMap_map η n)

end LocalCoefficientSystem

end TauCeti
