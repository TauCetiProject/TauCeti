/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Basic

/-!
# The `ℤ`-linear extension of the twisted slash sum

`HeckeSlash/Nebentypus/Basic.lean` attaches a `ℂ`-linear endomorphism `twistedHeckeSlashSumEnd` of
`ℍ → ℂ` to a single double coset of `Γ₀(N)`, weighting each summand by the nebentypus character
of its own representative. This file extends that assignment `ℤ`-linearly over the basis of the
Hecke ring `𝕋 Δ₀(N) Γ₀(N) ℤ`, exactly as `HeckeSlash/Ring.lean` does for the untwisted `Γ₁(N)`
sum: the extension is `Finsupp.linearCombination` at the coefficient ring `ℤ`, so linearity in the
ring element is inherited rather than reproved — `map_zero` and `map_add` apply directly, and the
one lemma proved here is the value on a basis element.

## This is not yet a ring action, and not yet an operator on the character space

Two things are deliberately absent. Multiplicativity of the extension is Shimura §3.4 and is not
proved here, so what is delivered is the `ℤ`-linear assignment only. And the twisted sum is *not*
shown here to preserve the `χ`-invariant functions `TauCeti.functionCharSpace`
(`ModularForms/DiamondOperators.lean`) — that is the pay-off of the weighting, proved in
`HeckeSlash/Nebentypus/Invariance.lean`; here the extension lands in `Module.End ℂ (ℍ → ℂ)`,
endomorphisms of *all* functions.

## Main definitions

* `HeckeRing.GL2.twistedHeckeSlashRingLinearMap`: the `ℤ`-linear extension of
  `twistedHeckeSlashSumEnd` to the Hecke ring.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashRingLinearMap_single`: the value on a basis element is the
  scaled twisted sum of that double coset. With `map_zero`/`map_add` this determines the map.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 (the action of the Hecke ring on automorphic forms).

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), whose
`twistedHeckeSlashExtGen` this realizes. The source extends by a hand-rolled `Finsupp.sum` and
proves additivity separately; here the extension is a bundled `Finsupp.linearCombination`, so that
additivity is `map_add`.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset TauCeti
  HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

namespace HeckeRing.GL2

-- `twistedHeckeSlashSumEnd` needs `[NeZero N]` to know its index type is finite.
variable [NeZero N]

/-- The `ℤ`-linear extension of `twistedHeckeSlashSumEnd` to formal `ℤ`-combinations of double
cosets of `Γ₀(N)`: `ℤ`-linear in the ring element, but not known to be multiplicative, so this is
not yet a ring action.

`𝕋 Δ H ℤ` unfolds to `HeckeCoset Δ H H →₀ ℤ` carrying the transported module structure, which is
why `Finsupp.linearCombination` applies at this type. -/
noncomputable def twistedHeckeSlashRingLinearMap :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (ℍ → ℂ) :=
  -- Eta-expanded on purpose: `Nebentypus.lean` introduces `[NeZero N]` *after* the double
  -- coset in its `variable` block, so the partial application `twistedHeckeSlashSumEnd k χ`
  -- still expects the instance and does not have the function type `linearCombination` wants.
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashSumEnd k χ D

/-- The value on a basis element is the scaled twisted slash sum of that double coset. -/
@[simp] lemma twistedHeckeSlashRingLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
    (c : ℤ) :
    twistedHeckeSlashRingLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashSumEnd k χ D :=
  -- Mirrors `heckeSlashGamma1RingModularFormLinearMap_single`: `Finsupp.linearCombination_single`
  -- does not apply, since `HeckeCosetModule.single` is a separate, non-exposed `def`.
  (Finsupp.linearCombination_apply (R := ℤ) (v := fun D ↦ twistedHeckeSlashSumEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

end HeckeRing.GL2

end
