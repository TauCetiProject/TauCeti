/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
import TauCeti.Algebra.Order.Ring.Ordering.Semireal
import TauCeti.Algebra.Ring.Semireal
import TauCeti.FieldTheory.RealClosure.ArtinSchreier

/-!
# Elements of finite order in absolute Galois groups

By the Artin–Schreier theorem, a nontrivial element `g` of finite order of the absolute Galois group
of a field `k` has order two, and its fixed field in the algebraic closure is real closed. Since `k`
lies in that fixed field, `k` is formally real.

So the absolute Galois group of a field that is not formally real, for instance of a field of
positive characteristic or of a field in which `-1` is a square, has no nontrivial element of
finite order; in particular it has no element of prime order. This is what allows Serre's theorem
on the cohomological dimension of open subgroups of profinite groups without elements of order `ℓ`
to be applied to absolute Galois groups.

## Main results

* `Field.absoluteGaloisGroup.orderOf_eq_two_of_isOfFinOrder`: a nontrivial element of finite order
  has order two.
* `Field.absoluteGaloisGroup.isFormallyReal_of_isOfFinOrder`: if there is one, the field is
  formally real.

## References

* E. Artin and O. Schreier, *Eine Kennzeichnung der reell abgeschlossenen Körper*, Abh. Math.
  Sem. Univ. Hamburg 5 (1927), 225–231.
* M. Artin, A. Grothendieck and J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas
  (SGA 4), tome 3*, Lecture Notes in Mathematics 305, Exposé X, proof of Théorème 2.1.
-/

public section

open IntermediateField

namespace Field.absoluteGaloisGroup

variable {k : Type*} [Field k]

/-- **Artin–Schreier.** A nontrivial element of finite order of the absolute Galois group of a field
has order two. -/
theorem orderOf_eq_two_of_isOfFinOrder (g : absoluteGaloisGroup k) (hg : IsOfFinOrder g)
    (h1 : g ≠ 1) : orderOf g = 2 :=
  -- `absoluteGaloisGroup k` is by definition the group of `k`-automorphisms of
  -- `AlgebraicClosure k`, with the same multiplication.
  TauCeti.RealClosure.orderOf_eq_two_of_isOfFinOrder (C := AlgebraicClosure k) hg h1

/-- **Artin–Schreier.** If the absolute Galois group of a field `k` has a nontrivial element of
finite order, then `k` is formally real. -/
theorem isFormallyReal_of_isOfFinOrder (g : absoluteGaloisGroup k) (hg : IsOfFinOrder g)
    (h1 : g ≠ 1) : IsFormallyReal k := by
  -- `absoluteGaloisGroup k` is by definition the group of `k`-automorphisms of
  -- `AlgebraicClosure k`, with the same multiplication.
  let σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := g
  -- `k` embeds in the real closed field fixed by `σ`.
  have := TauCeti.RealClosure.isRealClosed_fixedField_zpowers (σ := σ) hg h1
  have : IsSemireal k := .of_ringHom (algebraMap k (fixedField (Subgroup.zpowers σ)))
  infer_instance

end Field.absoluteGaloisGroup
