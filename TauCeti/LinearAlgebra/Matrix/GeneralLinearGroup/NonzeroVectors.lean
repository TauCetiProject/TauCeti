/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Module (Matrix n n R) (n → R)` through `Matrix.mulVec` is the action restricted below.
public import Mathlib.LinearAlgebra.Matrix.Action
-- `GL` occurs in every statement below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `SubMulAction` carries the action on the nonzero vectors.
public import Mathlib.GroupTheory.GroupAction.SubMulAction
-- `Nat.card` occurs in the count below.
public import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: `Set.ncard_compl` removes the zero vector, inside the count only.
import Mathlib.Data.Set.Card
-- Non-public: extending an isomorphism of lines to the whole space, inside the transitivity proof.
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
-- Non-public: a faithful action stays faithful on a spanning invariant subset, inside the
-- faithfulness proof.
import TauCeti.GroupTheory.GroupAction.SubMulAction
-- Non-public: a right-linear map of coordinate vectors is a matrix, inside the transitivity proof.
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# The general linear group permuting the nonzero vectors

An invertible matrix carries a nonzero vector to a nonzero vector, because it has an inverse; so
`GL n R` acts on the nonzero vectors of `n → R`. The underlying `GL n R`-set is
`TauCeti.nonzeroVectors`, a `SubMulAction` of the `Matrix.mulVec` action of
`Mathlib.LinearAlgebra.Matrix.Action`, and the permutation representation it carries is Mathlib's
`MulAction.toPermHom`.

That representation is faithful: a matrix commutes with right scalar multiplication, so it is
determined by its values on any set spanning `n → R` as a right `R`-module, and the nonzero
vectors span (over the trivial semiring there are none, but then `n → R` is zero). Over a finite
semiring the set being permuted has `|R| ^ |n| - 1` elements, which can make the representation
surjective in small cases; the two-dimensional worked case, `GL₂(𝔽₂) ≅ S₃`, is in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/FieldCardTwo.lean`.

## Main definitions

* `TauCeti.nonzeroVectors`: the nonzero vectors of `n → R` as a `GL n R`-set.
* `TauCeti.nonzeroVectorsEquivFinThree`: a numbering of the three nonzero vectors in dimension two
  over a semiring with two elements.

## Main results

* `TauCeti.faithfulSMulNonzeroVectors`: the action on the nonzero vectors is faithful.
* `TauCeti.natCard_nonzeroVectors`: there are `|R| ^ |n| - 1` nonzero vectors.
* `TauCeti.natCard_nonzeroVectors_fin_two_of_card_eq_two`: in dimension two over a semiring with
  two elements, there are three nonzero vectors.
* `TauCeti.exists_smul_eq_of_ne_zero` and `TauCeti.isPretransitive_nonzeroVectors`: over a
  division ring the action on the nonzero vectors is transitive.
-/

public section

open Matrix

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]

/-- **The nonzero vectors of `n → R` as a `GL n R`-set.** An invertible matrix has an inverse, so
it cannot send a nonzero vector to zero; the action is the `Matrix.mulVec` action of
`Mathlib.LinearAlgebra.Matrix.Action` read through the unit group. -/
def nonzeroVectors (n R : Type*) [Fintype n] [DecidableEq n] [Semiring R] :
    SubMulAction (GL n R) (n → R) where
  carrier := {v | v ≠ 0}
  smul_mem' g _ hv := (smul_ne_zero_iff_ne g).2 hv

@[simp]
theorem mem_nonzeroVectors {v : n → R} : v ∈ nonzeroVectors n R ↔ v ≠ 0 := Iff.rfl

/-- **The action of `GL n R` on the nonzero vectors of `n → R` is faithful.** Over the trivial
semiring there are no nonzero vectors, but then `GL n R` is trivial as well. -/
instance faithfulSMulNonzeroVectors : FaithfulSMul (GL n R) (nonzeroVectors n R) :=
  -- Matrices act faithfully on `n → R`, commuting with right scalars, and the nonzero vectors
  -- span `n → R` over `Rᵐᵒᵖ`.
  have : FaithfulSMul (Matrix n n R) (n → R) := ⟨Matrix.ext_iff_smul.2⟩
  SubMulAction.faithfulSMul_of_span_eq_top (R := Rᵐᵒᵖ) _ <| Submodule.eq_top_iff'.2 fun v ↦ by
    by_cases hv : v = 0
    · exact hv ▸ zero_mem _
    · exact Submodule.subset_span hv

/-- **The number of nonzero vectors** is `|R| ^ |n| - 1`. Over an infinite semiring both sides are
`0`: `Nat.card R = 0`, and `nonzeroVectors n R` is empty (when `n` is empty) or infinite. -/
theorem natCard_nonzeroVectors :
    Nat.card (nonzeroVectors n R) = Nat.card R ^ Nat.card n - 1 := by
  rw [← Nat.card_fun, ← Set.ncard_singleton (0 : n → R), ← Set.ncard_compl {0}]
  have h : (nonzeroVectors n R : Set (n → R)) = {0}ᶜ := by
    ext v
    simp [mem_nonzeroVectors]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq]

/-- **A plane over a semiring with two elements has three nonzero vectors.** -/
theorem natCard_nonzeroVectors_fin_two_of_card_eq_two (hR : Nat.card R = 2) :
    Nat.card (nonzeroVectors (Fin 2) R) = 3 := by
  rw [natCard_nonzeroVectors, hR, Nat.card_fin]
  decide

/-- **A numbering of the three nonzero vectors of a plane over a semiring with two elements.**
The numbering is an arbitrary choice. -/
noncomputable def nonzeroVectorsEquivFinThree (hR : Nat.card R = 2) :
    nonzeroVectors (Fin 2) R ≃ Fin 3 := by
  have : Finite R := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.equivFinOfCardEq (natCard_nonzeroVectors_fin_two_of_card_eq_two hR)

section DivisionRing

variable {D : Type*} [DivisionRing D]

/-- **Invertible matrices act transitively on the nonzero vectors** over a division ring: any
nonzero vector of `n → D` is carried to any other by some element of `GL n D`. -/
theorem exists_smul_eq_of_ne_zero {v w : n → D} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : GL n D, g • v = w := by
  -- `Matrix.mulVec` commutes with the right scalar action of `D`, so we work over `Dᵐᵒᵖ`. Extend
  -- the `Dᵐᵒᵖ`-linear isomorphism of the right lines through `v` and `w` sending `v` to `w` to an
  -- automorphism `f` of `n → D`, as in `Projectivization.linearEquiv_is_two_pretransitive` of
  -- `Mathlib.LinearAlgebra.Projectivization.Action`, and take the matrices of `f` and `f.symm`.
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton Dᵐᵒᵖ _ v hv).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton Dᵐᵒᵖ _ w hw))
  have hfv : f v = w := by
    have h1 : (LinearEquiv.toSpanNonzeroSingleton Dᵐᵒᵖ _ v hv).symm _ = 1 :=
      LinearEquiv.coord_self Dᵐᵒᵖ _ v hv
    simpa [h1] using (hf ⟨v, Submodule.mem_span_singleton_self v⟩).symm
  -- A `Dᵐᵒᵖ`-linear automorphism `e` of `n → D` is `Matrix.mulVec` by the matrix whose `j`-th
  -- column is `e eⱼ`.
  have key (e : (n → D) ≃ₗ[Dᵐᵒᵖ] n → D) (x : n → D) :
      Matrix.of (fun i j ↦ e (Pi.single j 1) i) *ᵥ x = e x :=
    e.toLinearMap.of_apply_single_mulVec x
  refine ⟨⟨.of fun i j ↦ f (Pi.single j 1) i, .of fun i j ↦ f.symm (Pi.single j 1) i,
    Matrix.ext_of_mulVec_single fun j ↦ ?_, Matrix.ext_of_mulVec_single fun j ↦ ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, key, key, f.apply_symm_apply, Matrix.one_mulVec]
  · rw [← Matrix.mulVec_mulVec, key, key, f.symm_apply_apply, Matrix.one_mulVec]
  · rw [Units.smul_def, Units.val_mk, Matrix.smul_eq_mulVec, key, hfv]

/-- The action of `GL n D` on the nonzero vectors of `n → D` is transitive. -/
instance isPretransitive_nonzeroVectors : MulAction.IsPretransitive (GL n D) (nonzeroVectors n D) :=
  ⟨fun v w ↦ (exists_smul_eq_of_ne_zero v.property w.property).imp fun _ hg ↦ Subtype.ext hg⟩

end DivisionRing

end TauCeti
