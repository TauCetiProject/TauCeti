/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Reorder

/-!
# The characteristic polynomial of a Coxeter element does not depend on the ordering

The two word moves of `TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Reorder` preserve the
characteristic polynomial of the matrix by which a word acts on the simple roots: a commutation
move does not change the Weyl-group element, hence not its matrix
(`RootPairing.Base.ActsBy.unique`), and a cyclic shift replaces `S W` by `W S`, which has the same
characteristic polynomial.

## Main results

* `RootPairing.Base.charpoly_prod_reflMatrix_eq_of_isOneDegenerateOrder`: for a base whose Dynkin
  diagram has a one-degenerate order, the matrices of all Coxeter elements on the simple roots have
  the same characteristic polynomial.
-/

public section

open Matrix TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]

/-- **All Coxeter elements have the same characteristic polynomial** (of their matrices on the
simple roots) when the Dynkin diagram of the base has a one-degenerate order. -/
theorem charpoly_prod_reflMatrix_eq_of_isOneDegenerateOrder [DecidableEq ι] (b : P.Base)
    {S : List b.support} (hnd : S.Nodup)
    (hel : List.IsOneDegenerateOrder (fun x y => b.cartanMatrix x y ≠ 0) S)
    {l l' : List b.support}
    (hl : l.Perm S) (hl' : l'.Perm S) :
    ((l.map (reflMatrix b.cartanMatrix)).prod).charpoly =
      ((l'.map (reflMatrix b.cartanMatrix)).prod).charpoly :=
  List.eq_of_isOneDegenerateOrder
    (fun _ _ h h' => h (b.cartanMatrix_apply_eq_zero_iff_symm.2 h')) hnd hel
    (fun l => ((l.map (reflMatrix b.cartanMatrix)).prod).charpoly)
    (fun l l' _ hce => by
      have hw : wordProd P b l = wordProd P b l' := wordProd_eq_of_commEquiv b hce
      have hl' : ActsBy b (wordProd P b l) ((l'.map (reflMatrix b.cartanMatrix)).prod) := by
        rw [hw]; exact actsBy_wordProd b l'
      rw [(actsBy_wordProd b l).unique hl'])
    (fun a t _ => by
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one]
      exact charpoly_mul_comm _ _)
    hl hl'

end RootPairing.Base

end
