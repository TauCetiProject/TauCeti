/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Algebraic.Basic

import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.RingTheory.Valuation.Discrete.Henselian

/-!
# Automatic valuation compatibility over nonarchimedean local fields

The integer ring `𝒪[K]` of a nonarchimedean local field `K` (of mixed or equal characteristic) is a
Henselian local ring (`TauCeti.henselianLocalRing_integer`) for a nontrivial rank-one valuation.
Specializing `ValuativeExtension.of_henselianLocalRing` to `K` shows that every algebraic
`K`-algebra `L` carrying a nontrivial rank-one discrete `ValuativeRel` (in particular, every
algebraic extension of nonarchimedean local fields) is automatically a `ValuativeExtension K L`,
with no valuation or topological compatibility assumption on `algebraMap K L`.

`ValuativeExtension.of_isAlgebraic` is intentionally stated as a theorem rather than a global
instance because `TopologicalSpace K` does not appear in `ValuativeExtension K L`.

## Main results

* `ValuativeExtension.of_isAlgebraic`: an algebraic algebra `L / K` from a nonarchimedean local
  field `K` into a ring `L` carrying a nontrivial rank-one discrete `ValuativeRel` is automatically
  a `ValuativeExtension K L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4, and
  [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2 (for unique prolongation of complete
  valuations along algebraic extensions, where compatibility with the base valuation is assumed).
-/

public section

open ValuativeRel

/-- **Every algebraic algebra over a nonarchimedean local field carrying a nontrivial rank-one
discrete valuation is automatically a `ValuativeExtension`.** In particular, any algebraic algebra
between nonarchimedean local fields is compatible with their valuations without assuming continuity
of `algebraMap K L`. -/
theorem ValuativeExtension.of_isAlgebraic (K L : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Ring L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    [Algebra K L] [Algebra.IsAlgebraic K L] :
    ValuativeExtension K L :=
  .of_henselianLocalRing K L
