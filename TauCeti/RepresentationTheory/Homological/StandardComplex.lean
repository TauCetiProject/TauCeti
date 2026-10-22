/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# The standard complex along a homomorphism

A homomorphism `φ : G →* H` induces a chain map from the standard complex for `G` to
the restriction of the standard complex for `H`. In every degree it applies `φ` to every
entry of a tuple. The map commutes with the alternating boundaries and preserves the
augmentation. No injectivity or preservation of projective objects by restriction is needed.

The complexes are Amelia Livingston's standard complexes from
`Mathlib.RepresentationTheory.Homological.Resolution`; the maps use Mathlib's
`MonoidAlgebra.mapDomainLinearMap`.

## References

* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
-/

public section

noncomputable section

open CategoryTheory

namespace MonoidHom

universe u

variable {k G H : Type u} [Monoid G] [Monoid H]

section Ring

variable [Ring k]

/-- Apply a homomorphism to every entry of a standard generator, as a morphism to the
restricted permutation representation. -/
def standardComplexHom (φ : G →* H) (n : ℕ) :
    Rep.ofMulAction k G (Fin (n + 1) → G) ⟶
      Rep.res φ (Rep.ofMulAction k H (Fin (n + 1) → H)) :=
  Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k (fun x => φ ∘ x)
      isIntertwining' g := by
        apply MonoidAlgebra.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        simp [Representation.ofMulAction_single, Pi.smul_def, smul_eq_mul,
          Function.comp_def] }

/-- On a basis vector the degreewise map applies the homomorphism to the tuple. -/
@[simp]
theorem standardComplexHom_single (φ : G →* H) {n : ℕ} (x : Fin (n + 1) → G) (r : k) :
    (dsimp% only ((φ.standardComplexHom (k := k) n).hom (MonoidAlgebra.single x r))) =
      MonoidAlgebra.single (φ ∘ x) r := by
  simp [standardComplexHom]

end Ring

variable [CommRing k]

/-- The standard complex is functorial under a homomorphism, with its target action restricted
along that homomorphism. -/
def standardComplexMap (φ : G →* H) :
    Rep.standardComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj (Rep.standardComplex k H) where
  -- Mathlib presents each term as the corresponding permutation representation.
  f n := φ.standardComplexHom n
  comm' i j h := by
    subst i
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    -- Restriction leaves the linear maps unchanged; express composition on those maps
    -- before rewriting the categorical standard differentials.
    change ((Rep.standardComplex k H).d (j + 1) j).hom.toLinearMap ∘ₗ
        (φ.standardComplexHom (j + 1)).hom.toLinearMap =
      (φ.standardComplexHom j).hom.toLinearMap ∘ₗ
        ((Rep.standardComplex k G).d (j + 1) j).hom.toLinearMap
    rw [Rep.standardComplex.d_eq, Rep.standardComplex.d_eq]
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    -- The remaining morphisms are the defining tuple relabelling maps.
    change Rep.standardComplex.d k H (j + 1)
        (MonoidAlgebra.mapDomainLinearMap k k (fun x => φ ∘ x) (MonoidAlgebra.single x 1)) =
      MonoidAlgebra.mapDomainLinearMap k k (fun x => φ ∘ x)
        (Rep.standardComplex.d k G (j + 1) (MonoidAlgebra.single x 1))
    simp [Rep.standardComplex.d_of, Function.comp_def]

/-- The components of the induced standard-complex map in permutation coordinates. -/
@[simp]
theorem standardComplexMap_f (φ : G →* H) (n : ℕ) :
    (φ.standardComplexMap (k := k)).f n =
      φ.standardComplexHom n :=
  (rfl)

/-- The identity homomorphism induces the identity standard-complex map. -/
@[simp]
theorem standardComplexMap_id :
    (MonoidHom.id G).standardComplexMap (k := k) = 𝟙 (Rep.standardComplex k G) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  -- Generators of the standard complex are tuples in its simplicial G-set.
  change Fin (n + 1) → G at x
  apply LinearMap.ext_ring
  -- Restriction along the identity and the identity chain morphism act identically
  -- on the underlying permutation modules.
  change ((MonoidHom.id G).standardComplexHom n).hom (MonoidAlgebra.single x 1) =
    MonoidAlgebra.single x 1
  simp

/-- Standard-complex maps respect composition, restricting the second map along the first
homomorphism. -/
@[simp]
theorem standardComplexMap_comp {K : Type u} [Monoid K] (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).standardComplexMap (k := k) =
      φ.standardComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map ψ.standardComplexMap := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  -- Generators of the standard complex are tuples in its simplicial G-set.
  change Fin (n + 1) → G at x
  apply LinearMap.ext_ring
  -- Iterated restriction is restriction along the composite on underlying modules.
  change ((ψ.comp φ).standardComplexHom n).hom (MonoidAlgebra.single x 1) =
    (ψ.standardComplexHom n).hom ((φ.standardComplexHom n).hom (MonoidAlgebra.single x 1))
  simp [Function.comp_def]

/-- The standard-complex map preserves the degree-zero augmentation. -/
@[reassoc (attr := simp)]
theorem standardComplexHom_comp_ε (φ : G →* H) :
    φ.standardComplexHom (k := k) 0 ≫ (Rep.resFunctor φ).map (Rep.standardComplex.ε k H) =
      Rep.standardComplex.ε k G := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  -- The augmentation is the coefficient sum; restriction does not change its linear map.
  change (Rep.standardComplex.ε k H).hom
      ((φ.standardComplexHom 0).hom (MonoidAlgebra.single x 1)) =
    (Rep.standardComplex.ε k G).hom (MonoidAlgebra.single x 1)
  rw [standardComplexHom_single]
  dsimp [Rep.standardComplex.ε]
  simp

end MonoidHom
