/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.TorusQuotient

/-!
# The unipotent radical of a solvable group over a perfect field

Let `G` be a smooth geometrically connected affine group of finite type over a perfect field `k`
whose geometric points form a solvable group. This file proves the perfect-field part of the
structure theorem for `G` (Milne, Theorem 16.33(a)–(c)):

* the affine quotient `G ⧸ R_u(G)` by the `k`-unipotent radical is a torus;
* `R_u(G)` is the only connected normal smooth unipotent subgroup with torus quotient;
* the formation of `R_u(G)` commutes with every field extension `K / k`, not only the separable
  algebraic ones of
  `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`.

Over a perfect field the quotient `G ⧸ R_u(G)` is reductive
(`TauCeti.FiniteTypeCommHopfAlgCat.reductive_coinvariants_unipotentRadical`) with solvable
geometric points, so it is a torus by
`TauCeti.reductiveCommHopfAlgProperty.torus_of_geometricallySolvable`.

The base-change statement holds over any field once `G ⧸ R_u(G)` is a torus. A torus stays a torus
after extension of scalars, and the points of a torus are semisimple; the image in a group with
semisimple geometric points of the smooth unipotent radical of `G_K` is trivial. Hence the
base change of `R_u(G)`, which is the kernel of `G_K → (G ⧸ R_u(G))_K`, is the unipotent radical
of `G_K` by `TauCeti.FiniteTypeCommHopfAlgCat.
unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple`.

The field-independent steps are in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.TorusQuotient`, and the torus theorem
`TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical_of_perfectField` is in
`TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical.Basic`.

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

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33(a)–(c), pp. 335–336.
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
