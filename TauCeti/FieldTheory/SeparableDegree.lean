/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Separable and inseparable degrees under a surjective base change

In a tower `K → E → L` of fields whose lower map `algebraMap K E` is onto, `E` carries no more
information over `K` than `K` itself does, so the degree of `L` is the same whichever of the two
it is measured over. This file records that for the separable and inseparable degrees; for
`Module.finrank` it is the special case of `Algebra.finrank_eq_of_equiv_equiv` along the ring
isomorphism `K ≃+* E` and the identity of `L`.

The hypothesis is surjectivity rather than bijectivity because a map of fields is automatically
injective; and it is stated for an arbitrary tower rather than for a specific construction, so
that a caller with any surjectively-presented intermediate field can use it.

## Main results

* `Field.finSepDegree_eq_of_surjective`: `[L : E]_s = [L : K]_s`.
* `Field.finInsepDegree_eq_of_surjective`: `[L : E]_i = [L : K]_i`.
-/

public section

variable {K L : Type*} [Field K] [Field L]

/-- **The separable degree is unchanged by a surjective base change.** Use this to move a
separable degree between an intermediate field and a field presented as mapping onto it. -/
theorem Field.finSepDegree_eq_of_surjective {E : Type*} [Field E] [Algebra K L] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] (hsurj : Function.Surjective (algebraMap K E)) :
    Field.finSepDegree E L = Field.finSepDegree K L := by
  -- an `L`-embedding is `E`-linear exactly when it is `K`-linear, so the embedding sets agree
  unfold Field.finSepDegree
  exact Nat.card_congr (AlgHom.extendScalarsOfSurjective hsurj).symm

/-- **The inseparable degree is unchanged by a surjective base change.** The inseparable
counterpart of `Field.finSepDegree_eq_of_surjective`, for the same tower. -/
theorem Field.finInsepDegree_eq_of_surjective {E : Type*} [Field E] [Algebra K L] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] (hsurj : Function.Surjective (algebraMap K E)) :
    Field.finInsepDegree E L = Field.finInsepDegree K L := by
  -- `K → E` is an isomorphism, so the lower step has inseparable degree one and the tower law
  -- leaves the upper step alone
  have := Algebra.isIntegral_of_surjective hsurj
  rw [← Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K E L,
    ← Field.finInsepDegree_eq_of_equiv K K E
      (.ofBijective (Algebra.ofId K E) ⟨(algebraMap K E).injective, hsurj⟩),
    Field.finInsepDegree_self, one_mul]
