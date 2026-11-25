/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal
import Mathlib.Algebra.CharP.Invertible

/-!
# Examples of principal blocks

The Checks of the principal block (`TauCeti.principalBlockIdempotent`).

* **`𝔽₂[S₃]`**: the augmentation of `1 + ρ + ρ²` is `3 = 1` and that of `ρ + ρ²` is `2 = 0`, so
  `1 + ρ + ρ²` is the principal block and `ρ + ρ²` is not.
* **`𝔽₂[C₃]` and `𝔽₄[C₃]`**: over every field of characteristic `2`, the principal block of
  `k[C₃]` is `1 + r + r²`, the averaging idempotent, since `3 = 1`.
* **`G = 1`**: the principal block is `1`.
-/

public section

namespace TauCeti.PrincipalBlockExamples

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples

/-! ### `𝔽₂[S₃]` -/

/-- The augmentation of `1 + ρ + ρ²` in `𝔽₂[S₃]` is `3 = 1`. -/
theorem augmentation_blockOneS₃ :
    augmentation (ZMod 2) S₃ (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) = 1 := by
  simp only [coe_blockOneS₃, of_apply, map_add, map_one, augmentation_single]
  decide

/-- The augmentation of `ρ + ρ²` in `𝔽₂[S₃]` is `2 = 0`. -/
theorem augmentation_blockTwoS₃ :
    augmentation (ZMod 2) S₃ (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 := by
  simp only [coe_blockTwoS₃, of_apply, map_add, augmentation_single]
  decide

/-- `1 + ρ + ρ²` is the principal block of `𝔽₂[S₃]`. -/
theorem blockOneS₃_eq_principalBlockIdempotent :
    blockOneS₃ = principalBlockIdempotent (ZMod 2) S₃ :=
  isBlockIdempotent_blockOneS₃.eq_principalBlockIdempotent_iff.2 <| by
    rw [centerAugmentation_apply, augmentation_blockOneS₃]
    exact one_ne_zero

/-- `ρ + ρ²` is not the principal block of `𝔽₂[S₃]`. -/
theorem blockTwoS₃_ne_principalBlockIdempotent :
    blockTwoS₃ ≠ principalBlockIdempotent (ZMod 2) S₃ := fun h =>
  (isBlockIdempotent_blockTwoS₃.eq_principalBlockIdempotent_iff.1 h) <| by
    rw [centerAugmentation_apply, augmentation_blockTwoS₃]

/-! ### `k[C₃]` in characteristic `2` -/

section C₃

variable (K : Type*) [Field K] [CharP K 2]

/-- **The principal block of `k[C₃]` in characteristic `2` is `1 + r + r²`**, for instance over
`𝔽₂` and over `𝔽₄`. -/
theorem coe_principalBlockIdempotent_c₃ :
    (principalBlockIdempotent K C₃ : MonoidAlgebra K C₃) =
      1 + of K C₃ r + of K C₃ (r ^ 2) := by
  have h₃ : Fintype.card C₃ = 3 := by rw [Fintype.card_multiplicative, ZMod.card]
  let := invertibleOfCharPNotDvd (K := K) (p := 2) (t := Fintype.card C₃) (by rw [h₃]; decide)
  have h : (3 : K) = 1 := by
    simpa using CharP.cast_eq_mod K 2 3
  simp [coe_principalBlockIdempotent_eq_average, GroupAlgebra.average, invOf_eq_inv, h, sum_c₃,
    one_def]

/-- Over `𝔽₂`, `1 + r + r²` is the principal block of `𝔽₂[C₃]`. -/
example : toCenter (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) =
    principalBlockIdempotent (ZMod 2) C₃ :=
  Subtype.ext ((coe_toCenter _).trans (coe_principalBlockIdempotent_c₃ (ZMod 2)).symm)

/-- Over `𝔽₄ = GaloisField 2 2`, the principal block of `𝔽₄[C₃]` is `1 + r + r²`. -/
example :
    (principalBlockIdempotent (GaloisField 2 2) C₃ : MonoidAlgebra (GaloisField 2 2) C₃) =
      1 + of _ C₃ r + of _ C₃ (r ^ 2) :=
  coe_principalBlockIdempotent_c₃ _

end C₃

/-! ### The trivial group -/

/-- The principal block of `k[1]` is `1`. -/
example (k : Type*) [Field k] : principalBlockIdempotent k Unit = 1 :=
  principalBlockIdempotent_eq_one_of_subsingleton

end TauCeti.PrincipalBlockExamples
