/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Torus.Quotient

/-!
# The unipotent radical of a solvable group over a perfect field

Let `G` be a smooth geometrically connected affine group of finite type over a perfect field `k`
whose geometric points form a solvable group. This file proves that the formation of the
`k`-unipotent radical `R_u(G)` commutes with every field extension `K / k`, not only the separable
algebraic ones of
`TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`
(Milne, Theorem 16.33).

It combines two results from other files. The quotient `G ⧸ R_u(G)` is a torus by
`TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical_of_perfectField` in
`TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical.Basic`. Over any field, once
`G ⧸ R_u(G)` is a torus, the formation of `R_u(G)` commutes with field extension by
`TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus` in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Torus.Quotient`, which rests on the uniqueness
lemma `TauCeti.FiniteTypeCommHopfAlgCat.
unipotentRadicalDefiningIdeal_eq_of_multiplicativeType_coinvariants` there.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField`:
  over a perfect field, `R_u(G)` of a smooth connected solvable `G` commutes with every field
  extension.

The corresponding coordinate Hopf-algebra isomorphism and equality of closed subgroup schemes are
`TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIsoOfEq` and
`TauCeti.FiniteTypeCommHopfAlgCat.
mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal_of_eq` applied to this
equality.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33, pp. 335–336.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

variable [PerfectField k]

/-- **The unipotent radical of a smooth connected solvable group over a perfect field commutes
with every field extension** `K / k` (Milne, Theorem 16.33). For separable algebraic extensions
this holds for every finite-type group,
`TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField
    {K : Type u} [Field K] [Algebra k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal G) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) G) :=
  baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus G
    (torus_coinvariants_unipotentRadical_of_perfectField G hconnected hsolv)

end FiniteTypeCommHopfAlgCat

end

end TauCeti
