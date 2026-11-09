/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Projective cotangent modules of formally smooth extensions

For an extension `P → S` of `R`-algebras with `P` and `S` formally smooth over `R`, the
cotangent module `I / I²` of its kernel is projective over `S`
(`Algebra.Extension.projective_cotangent_of_formallySmooth`): Mathlib's splitting criterion
for formal smoothness exhibits it as a direct summand of the projective module
`S ⊗[P] Ω[P⁄R]`.

## References

* The Stacks Project, Tags 00TH and 031I (cotangent sequence and formal smoothness).
-/

public section

namespace Algebra.Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The cotangent module of an extension of formally smooth algebras is projective: it is a
direct summand of `S ⊗[P] Ω[P⁄R]` via the cotangent complex. -/
theorem projective_cotangent_of_formallySmooth (P : Extension R S)
    [FormallySmooth R P.Ring] [FormallySmooth R S] : Module.Projective S P.Cotangent :=
  have ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp ‹_›
  .of_split P.cotangentComplex l hl

end Algebra.Extension
