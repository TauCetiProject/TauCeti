/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Trichotomy
import Mathlib.Tactic.NormNum

/-!
# The three shapes of finite quadratic algebras

Over the field with five elements, the algebra with generator square `-1` splits by evaluation
at `2` and `3`. Its coordinate type equivalence is different from that algebra equivalence.
Over the field with three elements, the nonsquare `-1` gives the field with nine elements,
whereas the zero radicand gives the dual numbers. In characteristic two, the square radicand
`1` still gives a nonzero square-zero element, excluding a product of fields.
-/

public noncomputable section

open QuadraticAlgebra DualNumber

namespace TauCeti.QuadraticAlgebraExamples

/-- Five is prime, so its residue ring is the field used by the split examples. -/
local instance instPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Two is invertible modulo five, as required by the splitting equivalence. -/
local instance instInvertibleTwoModFive : Invertible (2 : ZMod 5) :=
  invertibleOfNonzero (by decide : (2 : ZMod 5) ≠ 0)

/-- The split algebra over `ZMod 5` evaluates its generator at the two roots `2` and `3`. -/
example :
    let u := Units.mk0 (2 : ZMod 5) (by decide)
    let e := algEquivProdOfSq u (a := -1) (by decide)
    e ω = (2, 3) := by
  have hneg : (-2 : ZMod 5) = 3 := by decide
  norm_num [algEquivProdOfSq_apply]
  exact hneg

/-- In the same splitting, `1+ω` maps to `(3,4)`. -/
private theorem split_one_add_generator_image :
    let u := Units.mk0 (2 : ZMod 5) (by decide)
    let e := algEquivProdOfSq u (a := -1) (by decide)
    e (1 + ω) = (3, 4) := by
  have hneg : (-1 : ZMod 5) = 4 := by decide
  norm_num [algEquivProdOfSq_apply]
  exact hneg

/-- The inverse splitting recovers `1+ω` from the pair `(3,4)`. -/
example :
    let u := Units.mk0 (2 : ZMod 5) (by decide)
    let e := algEquivProdOfSq u (a := -1) (by decide)
    e.symm (3, 4) = 1 + ω := by
  dsimp only
  rw [AlgEquiv.symm_apply_eq]
  exact split_one_add_generator_image.symm

/-- The norm is the product of the split coordinates, which is `3·4 = 2` modulo five. -/
example :
    let u := Units.mk0 (2 : ZMod 5) (by decide)
    let e := algEquivProdOfSq u (a := -1) (by decide)
    norm (1 + ω : QuadraticAlgebra (ZMod 5) (-1) 0) = (e (1 + ω)).1 * (e (1 + ω)).2 ∧
      norm (1 + ω : QuadraticAlgebra (ZMod 5) (-1) 0) = 2 := by
  exact ⟨norm_eq_fst_mul_snd_algEquivProdOfSq _ _ _, by norm_num [norm_def]⟩

/-- The trace is the sum of the split coordinates, which is `3+4 = 2` modulo five. -/
example :
    let u := Units.mk0 (2 : ZMod 5) (by decide)
    let e := algEquivProdOfSq u (a := -1) (by decide)
    trace (1 + ω : QuadraticAlgebra (ZMod 5) (-1) 0) = (e (1 + ω)).1 + (e (1 + ω)).2 ∧
      trace (1 + ω : QuadraticAlgebra (ZMod 5) (-1) 0) = 2 := by
  exact ⟨trace_eq_fst_add_snd_algEquivProdOfSq _ _ _, by norm_num [trace_def]⟩

/-- The quadratic involution exchanges `(3,4)` and `(4,3)` in the split algebra. -/
example :
    let u := Units.mk0 (2 : ZMod 5) (by decide)
    let e := algEquivProdOfSq u (a := -1) (by decide)
    e (star (1 + ω)) = (4, 3) := by
  dsimp only
  rw [algEquivProdOfSq_star]
  rw [split_one_add_generator_image]
  rfl

/-- The coordinate type equivalence fails to preserve multiplication, already at `ω²`. -/
example :
    equivProd (-1 : ZMod 5) 0 ω = (0, 1) ∧
      equivProd (-1 : ZMod 5) 0 ((ω : QuadraticAlgebra (ZMod 5) (-1) 0) ^ 2) = (4, 0) ∧
      equivProd (-1 : ZMod 5) 0 ((ω : QuadraticAlgebra (ZMod 5) (-1) 0) ^ 2) ≠
        (equivProd (-1 : ZMod 5) 0 ω) ^ 2 := by
  decide

/-- The nonsquare radicand `-1` gives an actual field with nine elements over `ZMod 3`. -/
example :
    IsField (QuadraticAlgebra (ZMod 3) (-1) 0) ∧
      Nat.card (QuadraticAlgebra (ZMod 3) (-1) 0) = 9 := by
  let : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩
  refine ⟨Field.toIsField _, ?_⟩
  norm_num [QuadraticAlgebra.natCard_eq]

/-- For radicand `3 = 0` over `ZMod 3`, the dual-number equivalence sends the generator to `ε`. -/
example :
    algEquivDualNumber (ω : QuadraticAlgebra (ZMod 3) 0 0) = ε :=
  algEquivDualNumber_omega

/-- The generator of the zero-radicand algebra is nonzero and has square zero. -/
example :
    (ω : QuadraticAlgebra (ZMod 3) 0 0) ≠ 0 ∧
      (ω : QuadraticAlgebra (ZMod 3) 0 0) ^ 2 = 0 := by
  decide

/-- On the repeated-root algebra, `1+ω` has norm one and trace two. -/
example :
    norm (1 + ω : QuadraticAlgebra (ZMod 3) 0 0) = 1 ∧
      trace (1 + ω : QuadraticAlgebra (ZMod 3) 0 0) = 2 := by
  rw [norm_eq_sq_of_double_root (0 : ZMod 3) (by simp) (by simp), trace_eq_two_mul_re]
  norm_num

/-- In characteristic two, even the nonzero square radicand `1` gives a nonzero nilpotent. -/
example :
    (ω + 1 : QuadraticAlgebra (ZMod 2) 1 0) ≠ 0 ∧
      (ω + 1 : QuadraticAlgebra (ZMod 2) 1 0) ^ 2 = 0 := by
  decide

/-- The characteristic-two example is a dual-number algebra. -/
example :
    Nonempty (QuadraticAlgebra (ZMod 2) 1 0 ≃ₐ[ZMod 2] (ZMod 2)[ε]) := by
  exact nonempty_algEquiv_dualNumber_of_isSquare_of_char_two (by decide)

/-- The same algebra cannot split as the product of two copies of `ZMod 2`. -/
example :
    IsEmpty (QuadraticAlgebra (ZMod 2) 1 0 ≃ₐ[ZMod 2] ZMod 2 × ZMod 2) :=
  isEmpty_algEquiv_prod_of_char_two 1

end TauCeti.QuadraticAlgebraExamples
