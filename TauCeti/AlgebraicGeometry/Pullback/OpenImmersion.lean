/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pullback pasting along an open immersion into a fibre product

For an open immersion `i : V ⟶ X ×_S U` and a morphism `ψ : U' ⟶ U`, the pullback of `V → U`
along `ψ` is open in `X ×_S U'`, by pasting the two pullback squares.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.exists_isOpenImmersion_pullback_of_isOpenImmersion`: the open
  immersion of `V ×_U U'` into `X ×_S U'`, compatible with both projections.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Pullback pasting for an open immersion `i : V → pullback f φ`: the pullback of `V → U` along
`ψ : U' → U` is an open immersion `j` into `pullback f (ψ ≫ φ)`, compatible with both
projections. -/
theorem Scheme.Pullback.exists_isOpenImmersion_pullback_of_isOpenImmersion
    {X S U U' V : Scheme.{u}} (f : X ⟶ S) (φ : U ⟶ S) (i : V ⟶ pullback f φ)
    [IsOpenImmersion i] (ψ : U' ⟶ U) :
    ∃ j : pullback (i ≫ pullback.snd f φ) ψ ⟶ pullback f (ψ ≫ φ), IsOpenImmersion j ∧
      j ≫ pullback.fst f (ψ ≫ φ) =
        pullback.fst (i ≫ pullback.snd f φ) ψ ≫ i ≫ pullback.fst f φ ∧
      j ≫ pullback.snd f (ψ ≫ φ) = pullback.snd (i ≫ pullback.snd f φ) ψ := by
  let g := i ≫ pullback.snd f φ
  let a := pullback.map g ψ (pullback.snd f φ) ψ i (𝟙 U') (𝟙 U)
    (by simp [g]) (by simp)
  have : IsOpenImmersion a := Scheme.pullback_map_isOpenImmersion ..
  refine ⟨a ≫ (pullbackLeftPullbackSndIso f φ ψ).hom, inferInstance, ?_, ?_⟩
  · simp [a, g]
  · simp [a, g]

end AlgebraicGeometry
