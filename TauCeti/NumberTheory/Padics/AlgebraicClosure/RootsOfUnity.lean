/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CharP.LocalRing
public import TauCeti.NumberTheory.Padics.AlgebraicClosure.ResidueField
public import TauCeti.Topology.Algebra.Valued.RootsOfUnity

/-!
# Roots of unity of prime-to-`p` order in the algebraic closure of `ℚ_p`

Let `O = 𝒪[PadicAlgCl p]` be the valuation ring of the algebraic closure `PadicAlgCl p` of `ℚ_p`
and `κ = 𝓀[PadicAlgCl p]` its residue field. For `m` prime to `p`, reduction modulo the maximal
ideal identifies the `m`-th roots of unity of `PadicAlgCl p` with those of `κ`:

`μ_m(PadicAlgCl p) ≃* μ_m(κ)`.

This is the general `Valued.rootsOfUnityResidueEquiv`: `O` is henselian
(`PadicAlgCl.instHenselianLocalRingInteger`), and `m` is a unit of `O` because `κ` has
characteristic `p` (`IsLocalRing.isUnit_natCast_iff_not_dvd`).

## Main definitions

* `TauCeti.PadicAlgCl.rootsOfUnityResidueEquiv`: reduction `μ_m(PadicAlgCl p) ≃* μ_m(κ)` for `m`
  prime to `p`.
-/

public section

noncomputable section

open IsLocalRing Valued

namespace TauCeti.PadicAlgCl

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

/-- **Roots of unity of prime-to-`p` order reduce isomorphically**: for `m` prime to `p`,
reduction modulo the maximal ideal of `𝒪[PadicAlgCl p]` is an isomorphism from the `m`-th roots of
unity of `PadicAlgCl p` onto those of its residue field. It unfolds to
`Valued.rootsOfUnityResidueEquiv`, whose evaluation lemmas apply to it. -/
abbrev rootsOfUnityResidueEquiv (hm : ¬ p ∣ m) :
    rootsOfUnity m (PadicAlgCl p) ≃* rootsOfUnity m 𝓀[PadicAlgCl p] :=
  Valued.rootsOfUnityResidueEquiv
    (isUnit_natCast_iff_not_dvd.mpr (by rwa [ringChar.eq 𝓀[PadicAlgCl p] p]))

end TauCeti.PadicAlgCl
