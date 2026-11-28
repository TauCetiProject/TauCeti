/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.ValuedQuiver

/-!
# The mesh of the Auslander–Reiten quiver of a finite-dimensional algebra

Let `A` be a finite-dimensional algebra over a field `k`, and consider the quiver of irreducible
morphisms of its finitely generated modules, with the partial Auslander–Reiten translation
`ModuleCat.arTranslation` on its vertices. For a non-projective vertex `[M]`, with translate
`[τ M]`, there are equally many arrows `[X] ⟶ [M]` and `[τ M] ⟶ [X]` for every vertex `[X]`
(`ModuleCat.card_arrows_eq_card_arrows_of_translate_eq_some`). This follows from the
valued mesh relation `ModuleCat.irreducibleMorphismValuation_eq_swap_of_translate_eq_some`.

The counts are dimensions over `k`. Write `D_X` for the residue division ring of `End X` and `μ`
for the multiplicity of `X` as a summand of the middle term `E`. The finer, valued mesh relation
says that `irr(X, M)` and `irr(τ M, X)` both have dimension `μ` over `D_X`; the relation proved here
is its `k`-dimensional form, obtained by multiplying by `dim_k D_X`. Over an algebraically closed
field `D_X = k`, so the counts are the numbers of arrows of the Auslander–Reiten quiver. Over
other fields they are not the valuations of the valued (species) Auslander–Reiten quiver, which
need the `D_X`-module structure of `irr`. No algebraic closedness is assumed.

## Main results

* `ModuleCat.card_arrows_eq_card_arrows_of_translate_eq_some`: the mesh relation
  `#([X] ⟶ [M]) = #([τ M] ⟶ [X])`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.4.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

variable (k A)

/-- **The mesh of the Auslander–Reiten quiver** of a finite-dimensional algebra: if the
Auslander–Reiten translation sends the vertex `m` to `t`, then for every vertex `x` there are
equally many arrows `x ⟶ m` and `t ⟶ x`. Both counts are the shared residue dimension at `x`
multiplied by the dimension of its residue division ring over `k`. -/
theorem card_arrows_eq_card_arrows_of_translate_eq_some
    {m t : IrreducibleMorphismQuiver k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M}
    (h : (arTranslation.{u, v, w} k A k (length_quotient_linearMap_self_eq_one k)).translate m =
      some t)
    (x : IrreducibleMorphismQuiver k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M) :
    Nat.card (x ⟶ m) = Nat.card (t ⟶ x) := by
  have hx := congrArg Prod.fst (irreducibleMorphismValuation_eq_swap_of_translate_eq_some h x)
  rw [IrreducibleMorphismQuiver.card_arrows, IrreducibleMorphismQuiver.card_arrows,
    ← finrank_residueOp_mul_irreducibleMorphismValuation_snd,
    ← finrank_residue_mul_irreducibleMorphismValuation_fst,
    Ring.finrank_quotient_jacobson_mulOpposite, hx, Prod.fst_swap]

end ModuleCat
