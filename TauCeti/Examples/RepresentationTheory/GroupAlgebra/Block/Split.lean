/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter.Split

/-!
# `𝔽₂` does not split `C₃`

If `𝔽₂` split `C₃`, every block of `𝔽₂[C₃]` would stay a block over every extension field
(`TauCeti.IsBlockIdempotent.centerMapRingHom_of_scalarSchur`). Over a field of characteristic `2`
containing a root of `X² + X + 1`, such as the algebraic closure of `𝔽₂`, the block `r + r²`
splits into two blocks
(`TauCeti.GroupAlgebraBlockExamples.not_isBlockIdempotent_centerMapRingHom_r_add_r_sq`). So some
simple `𝔽₂[C₃]`-module has endomorphisms beyond the scalars: the two-dimensional one, on which
`r` acts with the eigenvalues of `𝔽₄ ∖ 𝔽₂`.
-/

public section

open CategoryTheory

namespace TauCeti.GroupAlgebraBlockExamples

/-- **`𝔽₂` does not split `C₃`**: some simple finite-dimensional representation of `C₃` over
`𝔽₂` has an endomorphism space of dimension other than `1`. -/
theorem not_scalarSchur_zmod_two_c₃ :
    ¬ ∀ V : FDRep (ZMod 2) C₃, Simple V → Module.finrank (ZMod 2) (V ⟶ V) = 1 := by
  intro hk
  let K := AlgebraicClosure (ZMod 2)
  have : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (k := K)
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K) (by
      rw [show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).degree = 2 by
        compute_degree!]
      decide)
  have hα' : α ^ 2 + α + 1 = 0 := by simpa using hα
  exact not_isBlockIdempotent_centerMapRingHom_r_add_r_sq hα'
    (isBlockIdempotent_r_add_r_sq.centerMapRingHom_of_scalarSchur hk (ZMod.castHom (dvd_refl 2) K))

end TauCeti.GroupAlgebraBlockExamples
