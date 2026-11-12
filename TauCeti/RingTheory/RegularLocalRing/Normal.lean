/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import TauCeti.RingTheory.SerreCondition.Normal

/-!
# Regular rings are normal

A regular ring is integrally closed (Stacks, Lemma 10.157.5 (0567), whose "normal" means that every
localization at a prime is an integrally closed domain). Consequently every localization of a
regular ring at a prime is an integrally closed domain. This is the ring-level step of the
statement that regular schemes are normal.

## Proof

As in Stacks, this is an instance of Serre's criterion `(R₁) + (S₂)`. A regular ring satisfies
`(R_n)` for every `n` (`IsRegularRing.satisfiesSerreR`), and its local rings are regular, hence
Cohen–Macaulay, so it satisfies `(S_n)` for every `n` (`IsRegularRing.satisfiesSerreS`).
`TauCeti.isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two` then shows that it is
integrally closed in its total ring of fractions.

## Main results

* `TauCeti.IsRegularRing.isIntegrallyClosed`: a regular ring is integrally closed. It is a
  low-priority instance, so with `TauCeti.IsRegularRing.isRegularRing_localization` and
  `TauCeti.IsRegularLocalRing.isDomain` every localization of a regular ring at a prime is found to
  be an integrally closed domain.

## References

* [Stacks Project, Lemma 10.157.5](https://stacks.math.columbia.edu/tag/0567).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Common/RegularNormal.lean`: `IsRegularRing.isIntegrallyClosed` is its
  `Pcf.Stacks.isIntegrallyClosed_of_isRegularRing`. Its associated-prime argument now lives, with
  depth at least two in place of regularity, in `TauCeti.RingTheory.SerreCondition.Normal`.
-/

public section

namespace TauCeti

namespace IsRegularRing

variable (R : Type*) [CommRing R] [IsRegularRing R]

/-- **A regular ring is integrally closed** (Stacks, Lemma 10.157.5 (0567)): it satisfies `(R_1)`
and `(S_2)`, so Serre's criterion applies. -/
@[stacks 0567 "in the form `IsIntegrallyClosed`"]
instance (priority := low) isIntegrallyClosed : IsIntegrallyClosed R :=
  isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two
    (_root_.IsRegularRing.satisfiesSerreR 1) (_root_.IsRegularRing.satisfiesSerreS 2)

/-- Every localization of a regular ring at a prime is an integrally closed domain, so a regular
ring is normal in the sense of Stacks, Definition 10.37.11 (00GV). -/
example (p : Ideal R) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
  ⟨inferInstance, inferInstance⟩

end IsRegularRing

end TauCeti
