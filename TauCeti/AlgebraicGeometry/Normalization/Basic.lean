/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Functoriality of the relative normalization

For quasi-compact quasi-separated morphisms `f : Y ⟶ J` and `g : Y' ⟶ J`, a morphism
`φ : Y ⟶ Y'` over `J` induces a morphism
`f.normalizationMap g φ hφ : f.normalization ⟶ g.normalization` of relative normalizations over
`J`, compatible with the canonical morphisms from `Y` and `Y'`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.normalizationMap`: the morphism of relative normalizations
  induced by a morphism of sources over a common target.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalizationMap_fromNormalization`: the induced morphism lies
  over `J`.
* `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationMap`: the induced morphism is
  compatible with the canonical morphisms from the sources.
* `AlgebraicGeometry.Scheme.Hom.normalizationMap_id` and
  `AlgebraicGeometry.Scheme.Hom.normalizationMap_comp`: the construction preserves identities and
  composition.
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

universe u

variable {Y Y' J : Scheme.{u}} (f : Y ⟶ J) [QuasiCompact f] [QuasiSeparated f]
  (g : Y' ⟶ J) [QuasiCompact g] [QuasiSeparated g]

/-- A morphism `φ : Y ⟶ Y'` over `J` induces a morphism `f.normalization ⟶ g.normalization` of
relative normalizations over `J`. -/
@[stacks 035J "existence, over a common base"]
noncomputable def normalizationMap (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.normalization ⟶ g.normalization :=
  f.normalizationDesc (φ ≫ g.toNormalization) g.fromNormalization (by simp [hφ])
  deriving IsIntegralHom

/-- The morphism of relative normalizations induced by `φ` lies over `J`. -/
@[reassoc (attr := simp)]
theorem normalizationMap_fromNormalization (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.normalizationMap g φ hφ ≫ g.fromNormalization = f.fromNormalization := by
  simp [normalizationMap]

/-- The morphism of relative normalizations induced by `φ` is compatible with the canonical
morphisms from `Y` and `Y'`. -/
@[reassoc (attr := simp)]
theorem toNormalization_normalizationMap (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.toNormalization ≫ f.normalizationMap g φ hφ = φ ≫ g.toNormalization := by
  simp [normalizationMap]

/-- The identity of `Y` induces the identity of `f.normalization`. -/
@[simp]
theorem normalizationMap_id : f.normalizationMap f (𝟙 Y) (Category.id_comp f) = 𝟙 _ :=
  normalization.hom_ext f _ _ f.fromNormalization (by simp) (by simp) (by simp)

/-- The morphisms of relative normalizations induced by `φ` and then `ψ` compose to the one
induced by `φ ≫ ψ`. -/
@[reassoc (attr := simp)]
theorem normalizationMap_comp {Y'' : Scheme.{u}} (h : Y'' ⟶ J) [QuasiCompact h] [QuasiSeparated h]
    (φ : Y ⟶ Y') (hφ : φ ≫ g = f) (ψ : Y' ⟶ Y'') (hψ : ψ ≫ h = g) :
    f.normalizationMap g φ hφ ≫ g.normalizationMap h ψ hψ =
      f.normalizationMap h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) :=
  normalization.hom_ext f _ _ h.fromNormalization (by simp) (by simp) (by simp)

end AlgebraicGeometry.Scheme.Hom
