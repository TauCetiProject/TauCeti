/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Pullback pasting along an open of a fibre product

For an open `V` of `X ×_S U` and a morphism `ψ : U' ⟶ U`, the pullback of `V → U` along `ψ`
is an open of `X ×_S U'`, by pasting the two pullback squares.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.exists_isOpenImmersion_pullback_opens`: the open immersion
  of `V ×_U U'` into `X ×_S U'`, compatible with both projections.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Pullback pasting for an open `V` of `pullback f φ`: the pullback of `V → U` along `ψ : U' → U`
is an open immersion `j` into `pullback f (ψ ≫ φ)`, compatible with both projections. -/
theorem Scheme.Pullback.exists_isOpenImmersion_pullback_opens {X S U U' : Scheme.{u}}
    (f : X ⟶ S) (φ : U ⟶ S) (V : (pullback f φ).Opens) (ψ : U' ⟶ U) :
    ∃ j : pullback (V.ι ≫ pullback.snd f φ) ψ ⟶ pullback f (ψ ≫ φ), IsOpenImmersion j ∧
      j ≫ pullback.fst f (ψ ≫ φ) =
        pullback.fst (V.ι ≫ pullback.snd f φ) ψ ≫ V.ι ≫ pullback.fst f φ ∧
      j ≫ pullback.snd f (ψ ≫ φ) = pullback.snd (V.ι ≫ pullback.snd f φ) ψ := by
  let g := V.ι ≫ pullback.snd f φ
  let a := pullback.map g ψ (pullback.snd f φ) ψ V.ι (𝟙 U') (𝟙 U)
    (by simp [g]) (by simp)
  have : IsOpenImmersion a := Scheme.pullback_map_isOpenImmersion ..
  refine ⟨a ≫ (pullbackLeftPullbackSndIso f φ ψ).hom, inferInstance, ?_, ?_⟩
  · simp [a, g]
  · simp [a, g]

end AlgebraicGeometry
