/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Bimodule
public import Mathlib.FieldTheory.IsAlgClosed.Basic
-- Non-public: the tower law, finiteness transfer and Schur's lemma for division algebras are used
-- only inside proofs.
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.RingTheory.Semisimple.Schur

/-!
# The valuation of a space of irreducible morphisms

Let `X` and `Y` be objects with local endomorphism rings in a `k`-linear category with binary
biproducts. The space `Irr(X, Y) = rad(X, Y) / rad²(X, Y)` of irreducible morphisms is a bimodule
over the residue division rings `F_Y = End Y / rad(End Y)` and `F_X = End X / rad(End X)`
(`TauCeti/CategoryTheory/Preadditive/Radical/Bimodule.lean`; the source acts through the opposite
ring, the action being antimultiplicative). The pair of its dimensions over these two division
rings is the **valuation** `(a, b)` of the arrow `X → Y` of the valued Auslander-Reiten quiver:
`a` is the dimension over the residue ring `F_Y` of the target and `b` the dimension over the
residue ring `F_X` of the source (`TauCeti.irreducibleMorphismValuation`).

This file makes the valuation usable. Over a commutative base ring `k`, both residue actions are
compatible with the scalars of `k` (`TauCeti.instIsScalarTowerResiduePostcomp` and
`TauCeti.instIsScalarTowerResiduePrecomp`), so `k → F_Y → Irr(X, Y)` and `k → F_X → Irr(X, Y)` are
scalar towers. Consequently:

* **finiteness**: when `Irr(X, Y)` is finitely generated over `k` it is finite-dimensional over
  both residue division rings. This is the case for finitely generated modules over an Artin
  algebra, whose morphism spaces are finitely generated over the commutative Artinian base, and
  `Irr(X, Y)` inherits that by the Noetherian instance of
  `TauCeti/CategoryTheory/Preadditive/Radical/Quotient.lean`;
* **positivity**: in that case both entries of the valuation are positive exactly when an
  irreducible morphism `X ⟶ Y` exists, so a nonzero `Irr(X, Y)` is valued by a pair of positive
  integers;
* **the tower law over a field**: `dim_k Irr(X, Y) = dim_k F_Y · a = dim_k F_X · b`. The two residue
  division rings need not have the same `k`-dimension, which is how asymmetric valuations arise;
* **algebraically closed fields**: when `k` is algebraically closed and the endomorphism algebras
  are finite-dimensional, both residue division rings are `k` itself, and the valuation is
  `(n, n)` with `n = dim_k Irr(X, Y)`.

## Main definitions

* `TauCeti.irreducibleMorphismValuation k X Y`: the pair of dimensions of `Irr(X, Y)` over the
  residue division rings of the target and of the source.

## Main results

* `TauCeti.instFiniteResiduePostcomp` and `TauCeti.instFiniteResiduePrecomp`: finiteness over the
  base gives finiteness over each residue division ring.
* `TauCeti.irreducibleMorphismValuation_fst_pos_iff` and
  `TauCeti.irreducibleMorphismValuation_snd_pos_iff`: the entries of the valuation are positive
  exactly when an irreducible morphism exists.
* `TauCeti.finrank_residue_mul_irreducibleMorphismValuation_fst` and
  `TauCeti.finrank_residueOp_mul_irreducibleMorphismValuation_snd`: **the tower law**
  `dim_k F_Y · a = dim_k Irr(X, Y) = dim_k F_X · b` over a field.
* `TauCeti.irreducibleMorphismValuation_eq_of_isAlgClosed`: over an algebraically closed field
  the valuation is `(dim_k Irr(X, Y), dim_k Irr(X, Y))`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section VII.1, for the valuation of an arrow of the Auslander-Reiten
  quiver by the two dimensions of `Irr(X, Y)` over the residue division rings.
-/

public section

namespace TauCeti

open CategoryTheory Module

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### Finiteness over the residue rings -/

section Finite

variable (k : Type*) [CommRing k] [Linear k C] (X Y : C)

/-- **Finiteness over the residue ring of the target**: a space of irreducible morphisms that is
finitely generated over the base ring is finitely generated over the residue ring of the target. -/
instance instFiniteResiduePostcomp [Module.Finite k (irreducibleMorphismSpace k X Y)] :
    Module.Finite (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y) :=
  .of_restrictScalars_finite k _ _

/-- **Finiteness over the residue ring of the source**: a space of irreducible morphisms that is
finitely generated over the base ring is finitely generated over the residue ring of the source. -/
instance instFiniteResiduePrecomp [Module.Finite k (irreducibleMorphismSpace k X Y)] :
    Module.Finite ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (irreducibleMorphismSpace k X Y) :=
  .of_restrictScalars_finite k _ _

end Finite

/-! ### The valuation -/

section Valuation

variable (k : Type*) [Ring k] [Linear k C] (X Y : C)

/-- **The valuation of the space of irreducible morphisms** `X ⟶ Y`: its dimension over the
residue ring `End Y / rad(End Y)` of the target, and its dimension over the residue ring
`End X / rad(End X)` of the source (acting through the opposite ring). Between objects with local
endomorphism rings both residue rings are division rings, and when the space is nonzero and finite
over the base ring this is the pair of positive integers labelling the arrow `X → Y` of the valued
Auslander-Reiten quiver. -/
noncomputable def irreducibleMorphismValuation : ℕ × ℕ :=
  (finrank (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y),
    finrank ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (irreducibleMorphismSpace k X Y))

/-- The first entry of the valuation is the dimension over the residue ring of the target. -/
@[simp]
theorem irreducibleMorphismValuation_fst :
    (irreducibleMorphismValuation k X Y).1 =
      finrank (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y) :=
  (rfl)

/-- The second entry of the valuation is the dimension over the residue ring of the source. -/
@[simp]
theorem irreducibleMorphismValuation_snd :
    (irreducibleMorphismValuation k X Y).2 =
      finrank ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (irreducibleMorphismSpace k X Y) :=
  (rfl)

variable [Limits.HasBinaryBiproducts C] [IsLocalRing (End X)] [IsLocalRing (End Y)]

/-- **The first entry of the valuation is positive exactly when an irreducible morphism exists**,
for a space of irreducible morphisms that is finitely generated over the residue ring of the
target. -/
theorem irreducibleMorphismValuation_fst_pos_iff
    [Module.Finite (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y)] :
    0 < (irreducibleMorphismValuation k X Y).1 ↔ ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  rw [irreducibleMorphismValuation_fst, finrank_pos_iff_of_free,
    nontrivial_irreducibleMorphismSpace_iff]

/-- **The second entry of the valuation is positive exactly when an irreducible morphism exists**,
for a space of irreducible morphisms that is finitely generated over the residue ring of the
source. -/
theorem irreducibleMorphismValuation_snd_pos_iff
    [Module.Finite ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (irreducibleMorphismSpace k X Y)] :
    0 < (irreducibleMorphismValuation k X Y).2 ↔ ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  rw [irreducibleMorphismValuation_snd, finrank_pos_iff_of_free,
    nontrivial_irreducibleMorphismSpace_iff]

end Valuation

/-! ### Over a field -/

section Field

variable (k : Type*) [Field k] [Linear k C] (X Y : C)

/-- **The tower law for the target**: over a field `k`, the `k`-dimension of the space of
irreducible morphisms is the `k`-dimension of the residue division ring of the target times the
first entry of the valuation. -/
theorem finrank_residue_mul_irreducibleMorphismValuation_fst [IsLocalRing (End Y)] :
    finrank k (End Y ⧸ Ring.jacobson (End Y)) * (irreducibleMorphismValuation k X Y).1 =
      finrank k (irreducibleMorphismSpace k X Y) :=
  finrank_mul_finrank _ _ _

/-- **The tower law for the source**: over a field `k`, the `k`-dimension of the space of
irreducible morphisms is the `k`-dimension of the residue division ring of the source times the
second entry of the valuation. -/
theorem finrank_residueOp_mul_irreducibleMorphismValuation_snd [IsLocalRing (End X)] :
    finrank k ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) * (irreducibleMorphismValuation k X Y).2 =
      finrank k (irreducibleMorphismSpace k X Y) :=
  finrank_mul_finrank _ _ _

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the first entry of the valuation is the `k`-dimension of
the space of irreducible morphisms, when the endomorphism algebra of the target is local and
finite-dimensional. -/
theorem irreducibleMorphismValuation_fst_of_isAlgClosed [IsLocalRing (End Y)]
    [FiniteDimensional k (End Y)] :
    (irreducibleMorphismValuation k X Y).1 = finrank k (irreducibleMorphismSpace k X Y) := by
  obtain ⟨e⟩ := nonempty_algEquiv_self_of_finiteDimensional_divisionRing (k := k)
    (D := End Y ⧸ Ring.jacobson (End Y))
  rw [← finrank_residue_mul_irreducibleMorphismValuation_fst, e.toLinearEquiv.finrank_eq,
    finrank_self, one_mul]

/-- Over an algebraically closed field, the second entry of the valuation is the `k`-dimension of
the space of irreducible morphisms, when the endomorphism algebra of the source is local and
finite-dimensional. -/
theorem irreducibleMorphismValuation_snd_of_isAlgClosed [IsLocalRing (End X)]
    [FiniteDimensional k (End X)] :
    (irreducibleMorphismValuation k X Y).2 = finrank k (irreducibleMorphismSpace k X Y) := by
  obtain ⟨e⟩ := nonempty_algEquiv_self_of_finiteDimensional_divisionRing (k := k)
    (D := (End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
  rw [← finrank_residueOp_mul_irreducibleMorphismValuation_snd, e.toLinearEquiv.finrank_eq,
    finrank_self, one_mul]

/-- **Over an algebraically closed field the valuation is symmetric**: between objects with local
finite-dimensional endomorphism algebras, the valuation of the space of irreducible morphisms is
`(n, n)` with `n` its `k`-dimension. -/
theorem irreducibleMorphismValuation_eq_of_isAlgClosed [IsLocalRing (End X)]
    [IsLocalRing (End Y)] [FiniteDimensional k (End X)] [FiniteDimensional k (End Y)] :
    irreducibleMorphismValuation k X Y =
      (finrank k (irreducibleMorphismSpace k X Y), finrank k (irreducibleMorphismSpace k X Y)) :=
  Prod.ext (irreducibleMorphismValuation_fst_of_isAlgClosed k X Y)
    (irreducibleMorphismValuation_snd_of_isAlgClosed k X Y)

end Field

end TauCeti
