/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Inverse images of ideal sheaves along scheme-theoretically dominant morphisms

For a commutative square `φ' ≫ g = p ≫ φ` whose side `p` is scheme-theoretically dominant,
factorization through a closed subscheme can be checked after precomposition with `p`
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_le_ker_iff_of_isSchemeTheoreticallyDominant`). In
particular an ideal sheaf vanishes exactly when its inverse image along a scheme-theoretically
dominant morphism does
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_bot_iff_of_isSchemeTheoreticallyDominant`).

If moreover every base change of `g` is scheme-theoretically dominant, then taking inverse images
along `g` reflects inclusion of ideal sheaves
(`comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant` in the namespace
`AlgebraicGeometry.Scheme.IdealSheafData`), so it is injective
(`comap_injective_of_universally_isSchemeTheoreticallyDominant`).
This is how equalities of closed subschemes descend along flat surjective morphisms, see
`TauCeti.AlgebraicGeometry.IdealSheaf.FaithfullyFlat`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_le_ker_iff_of_isSchemeTheoreticallyDominant`:
  factorization through a closed subscheme descends along scheme-theoretically dominant morphisms.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_bot_iff_of_isSchemeTheoreticallyDominant`: an
  ideal sheaf vanishes exactly when its inverse image along a scheme-theoretically dominant
  morphism does.
* `comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant` and
  `comap_injective_of_universally_isSchemeTheoreticallyDominant`, in the namespace
  `AlgebraicGeometry.Scheme.IdealSheafData`: inverse images along a universally
  scheme-theoretically dominant morphism reflect inclusion and are injective.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- **Factorization through a closed subscheme descends along scheme-theoretically dominant
morphisms.** For a commutative square `φ' ≫ g = p ≫ φ` with `p` scheme-theoretically dominant,
`φ'` factors through the inverse image of `V(D)` along `g` exactly when `φ` factors through
`V(D)`. -/
theorem comap_le_ker_iff_of_isSchemeTheoreticallyDominant
    {X' Y' : Scheme.{u}} (D : Y.IdealSheafData) {g : Y' ⟶ Y} (p : X' ⟶ X)
    [IsSchemeTheoreticallyDominant p] {φ' : X' ⟶ Y'} {φ : X ⟶ Y} (w : φ' ≫ g = p ≫ φ) :
    D.comap g ≤ φ'.ker ↔ D ≤ φ.ker := by
  rw [← le_map_iff_comap_le, map_ker, w, p.ker_comp_of_isSchemeTheoreticallyDominant]

/-- **A closed subscheme is everything as soon as its inverse image along a scheme-theoretically
dominant morphism is.** For `g` scheme-theoretically dominant, `I.comap g = ⊥` exactly when
`I = ⊥`. -/
@[simp]
theorem comap_eq_bot_iff_of_isSchemeTheoreticallyDominant (g : X ⟶ Y)
    [IsSchemeTheoreticallyDominant g] {I : Y.IdealSheafData} : I.comap g = ⊥ ↔ I = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ comap_bot g⟩
  rw [← le_bot_iff, ← g.ker_eq_bot, ← map_bot, le_map_iff_comap_le, h]

/-- **Inverse images along a universally scheme-theoretically dominant morphism reflect
inclusion.** If every base change of `g : X ⟶ Y` is scheme-theoretically dominant, then
`I.comap g ≤ J.comap g` exactly when `I ≤ J`. -/
theorem comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant
    (g : X ⟶ Y) (hg : MorphismProperty.universally @IsSchemeTheoreticallyDominant g)
    {I J : Y.IdealSheafData} : I.comap g ≤ J.comap g ↔ I ≤ J := by
  refine ⟨fun h ↦ ?_, fun h ↦ comap_mono g h⟩
  -- The projection to `V(J)` is scheme-theoretically dominant. The projection to `X` factors
  -- through `V(J.comap g)`, hence through `V(I.comap g)`.
  have hJ := IsPullback.of_hasPullback g J.subschemeι
  have : IsSchemeTheoreticallyDominant (pullback.snd g J.subschemeι) := hg _ _ _ hJ.flip
  have := (comap_le_ker_iff_of_isSchemeTheoreticallyDominant I _ pullback.condition).mp
    (by rwa [ker_eq_comap_of_isPullback J.subschemeι hJ, ker_subschemeι])
  rwa [ker_subschemeι] at this

/-- **Inverse images along a universally scheme-theoretically dominant morphism are injective.**
If every base change of `g` is scheme-theoretically dominant, then two ideal sheaves with the same
inverse image along `g` are equal. -/
theorem comap_injective_of_universally_isSchemeTheoreticallyDominant
    (g : X ⟶ Y) (hg : MorphismProperty.universally @IsSchemeTheoreticallyDominant g) :
    Function.Injective (comap · g) := fun _ _ h ↦
  le_antisymm ((comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant g hg).mp h.le)
    ((comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant g hg).mp h.ge)

end AlgebraicGeometry.Scheme.IdealSheafData
