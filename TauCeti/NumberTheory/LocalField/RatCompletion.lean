/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.Valuation.ValuativeRel.Henselian

/-!
# The completions of `ℚ` at its finite places are `p`-adic fields

Let `v` be a finite place of `ℚ`, a height-one prime of `𝓞 ℚ`, and let `p` be its rational prime
`Rat.HeightOneSpectrum.natGenerator v`. Mathlib identifies the completion `ℚ_v` with `ℚ_p` by a
continuous `ℚ`-algebra isomorphism (`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`). Through
its inverse, `ℚ_v` becomes a `ℚ_p`-algebra of degree one, so a finite extension of `ℚ_p` in the
sense of `TauCeti.FinitePadicExtension`. The valuative relation of `ℚ_v`, induced by its adic
valuation, needs no separate comparison: every integral extension of nonarchimedean local fields
is a valuative extension (`ValuativeExtension.of_isIntegral`).

This makes the results stated over an abstract finite extension of `ℚ_p` apply at the finite places
of `ℚ`, for instance local Tate duality, Tate's local Euler characteristic formula and the
finiteness of local Galois cohomology with finite coefficients.

## Main definitions

* `Rat.HeightOneSpectrum.instFinitePadicExtensionAdicCompletion`: the completion `ℚ_v` as a finite
  extension of `ℚ_p`, for `p` the rational prime of `v`.
-/

public section

noncomputable section

open IsDedekindDomain NumberField TauCeti

namespace Rat.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- **The completion of `ℚ` at a finite place `v` is a finite extension of `ℚ_p`**, for `p` the
rational prime of `v`. The `ℚ_p`-algebra structure is the inverse of Mathlib's isomorphism
`ℚ_v ≃ ℚ_p`, so the extension has degree one. -/
instance instFinitePadicExtensionAdicCompletion :
    FinitePadicExtension (v.adicCompletion ℚ) (natGenerator v) :=
  -- Pin the `ℚ`-algebra structure of `ℚ_v` to the one in the type of `padicEquiv`.
  letI : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion _ ℚ v
  let e : v.adicCompletion ℚ ≃+* ℚ_[natGenerator v] := (adicCompletion.padicEquiv v).toRingEquiv
  letI : Algebra ℚ_[natGenerator v] (v.adicCompletion ℚ) := e.symm.toRingHom.toAlgebra
  haveI : Module.Finite ℚ_[natGenerator v] (v.adicCompletion ℚ) :=
    Module.Finite.of_surjective (Algebra.linearMap ℚ_[natGenerator v] (v.adicCompletion ℚ))
      e.symm.surjective
  haveI : Nontrivial ℚ_[natGenerator v] := DivisionRing.toNontrivial
  { algebra := inferInstance
    toValuativeExtension := ValuativeExtension.of_isIntegral _ _ }

end Rat.HeightOneSpectrum
