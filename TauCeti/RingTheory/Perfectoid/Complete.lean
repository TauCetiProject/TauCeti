/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Principal
public import TauCeti.RingTheory.Perfectoid.Basic

/-!
# The power-bounded ring of a perfectoid Tate ring is `p`-adically complete

The power-bounded subring `R°` of a perfectoid Tate ring is complete for a pseudouniformiser
`ϖ`, and `ϖ` divides `p` in `R°`. Completeness for a principal subideal therefore makes `R°`
`p`-adically complete and separated. This includes equal-characteristic rings, where `p = 0`,
and products of equal- and mixed-characteristic rings: `p` need not be a unit in `R`, or even
a nonzerodivisor. This is the completeness hypothesis needed to construct the integral sharp
map and Fontaine's map using Mathlib's `PreTilt` and `WittVector.fontaineTheta`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, §3.1.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

/-- The power-bounded ring of a perfectoid Tate ring is `p`-adically complete and separated,
including when `p` vanishes or is a zero divisor in the ambient ring. -/
instance IsPerfectoidTateRing.isAdicComplete_span_natCast (p : ℕ) [NeZero p]
    (R : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [IsTateRing R] [CompleteSpace R] [T2Space R] [IsPerfectoidTateRing p R] :
    IsAdicComplete (Ideal.span {(p : powerBoundedSubring R)}) (powerBoundedSubring R) := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  obtain ⟨ϖ, hϖ, hdvd, -, -⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  have := IsUniform.isAdicComplete_span_singleton ϖ hϖ
  exact IsAdicComplete.span_singleton_of_dvd ((dvd_pow_self ϖ (NeZero.ne p)).trans hdvd)

end TauCeti.Perfectoid
