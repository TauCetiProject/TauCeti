/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.RingTheory.Localization.Normal

/-!
# Geometrically normal algebras

A ring `R` is *normal* when its localization at every prime is an integrally closed domain
(Stacks, Definition 10.37.11 (00GV)); this is the condition
`∀ p [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`,
which `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff_forall_localization` identifies with the
normality of `Spec R`.

An algebra `A` over a field `k` is *geometrically normal* when `K ⊗[k] A` is normal for every
field extension `K / k` (Stacks, Definition 10.165.2 (0380), condition (1) of Lemma 10.165.1
(037Z)). The ring `K ⊗[k] A` need not be a domain: for `k = ℚ` and `A = K = ℚ(i)` it is
`ℚ(i) × ℚ(i)`, which is normal. Geometric normality is stronger than geometric reducedness:
over `k = 𝔽_p(t)` with `p > 2`, the domain `k[x, y] / (x ^ p + y ^ 2 + t)` stays a domain after
every field extension, but is not normal after adjoining `t ^ (1 / p)`.

## Main definitions

* `Algebra.IsGeometricallyNormal k A`: `K ⊗[k] A` is normal for every field extension `K / k` in
  the universe of `k`.

## Main results

* `Ideal.isDomain_and_isIntegrallyClosed_atPrime_of_isGeometricallyNormal`: a geometrically
  normal algebra is a normal ring.

## References

* [Stacks Project, Lemma 10.165.1](https://stacks.math.columbia.edu/tag/037Z) and
  [Definition 10.165.2](https://stacks.math.columbia.edu/tag/0380).
-/

public section

open TensorProduct

universe u v

namespace Algebra

/-- An algebra `A` over a field `k` is **geometrically normal** when `K ⊗[k] A` is a normal ring
for every field extension `K / k`: its localization at every prime is an integrally closed domain.
The fields `K` range over the universe of `k`. Stacks, Definition 10.165.2 (0380). -/
@[stacks 0380]
class IsGeometricallyNormal (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] :
    Prop where
  /-- For every field extension `K / k`, every localization of `K ⊗[k] A` at a prime is an
  integrally closed domain. -/
  forall_isDomain_and_isIntegrallyClosed (K : Type u) [Field K] [Algebra k K]
    (P : Ideal (K ⊗[k] A)) [P.IsPrime] :
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)

namespace IsGeometricallyNormal

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- **A geometrically normal algebra is a normal ring**: taking `K = k`, the ring
`k ⊗[k] A ≅ A` is normal. -/
theorem _root_.Ideal.isDomain_and_isIntegrallyClosed_atPrime_of_isGeometricallyNormal
    [IsGeometricallyNormal k A] (q : Ideal A)
    [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  (TensorProduct.lid k A).toRingEquiv.forall_isDomain_and_isIntegrallyClosed
    (fun P _ ↦ forall_isDomain_and_isIntegrallyClosed (A := A) k P) q

end IsGeometricallyNormal

end Algebra
