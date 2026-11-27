/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.Defs
-- Proof-only: `IsLocalization.isDedekindDomain`.
import Mathlib.RingTheory.DedekindDomain.Dvr
import TauCeti.RingTheory.Localization.Defs

/-!
# Nontrivial localizations of Dedekind domains

A localization `B` of a domain `A` at a submonoid `M` is either the zero ring (when `0 ∈ M`) or
inverts only non-zero-divisors (`TauCeti.IsLocalization.le_nonZeroDivisors_of_nontrivial`). In
the second case, if `A` is a Dedekind domain then so is `B` (Mathlib's
`IsLocalization.isDedekindDomain`, which takes the condition `M ≤ A⁰` and the domain `B`). The
statement here takes `Nontrivial B` instead.

## Main results

* `TauCeti.IsLocalization.isDedekindDomain_of_nontrivial`: a nontrivial localization of a
  Dedekind domain is a Dedekind domain.
-/

public section

namespace TauCeti.IsLocalization

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (M : Submonoid A) (B : Type*) [CommRing B]
  [Nontrivial B] [Algebra A B] [IsLocalization M B]

include M in
/-- A nontrivial localization of a Dedekind domain is a Dedekind domain. The zero ring, the
localization at a submonoid containing `0`, is not. -/
theorem isDedekindDomain_of_nontrivial : IsDedekindDomain B :=
  have hM := le_nonZeroDivisors_of_nontrivial M B
  have := _root_.IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  _root_.IsLocalization.isDedekindDomain A hM B

end TauCeti.IsLocalization
