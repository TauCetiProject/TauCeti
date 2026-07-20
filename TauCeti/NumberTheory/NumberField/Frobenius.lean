/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.LegendreSymbol.Frobenius
public import TauCeti.NumberTheory.NumberField.IntegralSqrt
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Frobenius elements of a Galois number field and their action on square roots

For a Galois number field `K/ℚ` and a prime `Q` of `𝓞 K` over the rational prime `p`, an
arithmetic Frobenius at `Q` is a `σ ∈ Gal(K/ℚ)` with `σ x ≡ x ^ #(ℤ ⧸ Q ∩ ℤ) (mod Q)` for all
`x : 𝓞 K` — the exponent is the cardinality of the *base* residue ring `ℤ ⧸ Q ∩ ℤ`, which is
`p` for `Q` over `(p)`, distinguishing the arithmetic Frobenius from the absolute one (whose
exponent would be the residue-field norm `p^f`). This file provides the two number-field
services on top of Mathlib's `RingTheory/Frobenius.lean`:

* **existence** — a Frobenius exists at every prime over `p`
  (`IsArithFrobAt.exists_of_isInvariant` with the number-field instances discharged: the
  residue field of a nonzero prime is finite, and the Galois action on `𝓞 K` has invariants
  `ℤ`); and
* **the square-root action** — for `p` odd and `x ∈ K` with `x² = d ∈ ℤ`, `p ∤ d`, a
  Frobenius at `Q` satisfies `σ x = legendreSym p d • x`, transporting the `𝓞 K`-level
  computation `TauCeti.AlgHom.IsArithFrobAt.apply_sqrt` along the Galois action on the ring
  of integers.

`TauCeti.NumberTheory.Multiquadratic.Frobenius` combines the two to describe the Frobenius of
a multiquadratic field on all its generators at once (Layer 1 of the multiquadratic roadmap).

## Main results

* `TauCeti.NumberField.exists_isArithFrobAt`: a Frobenius exists at every prime of `𝓞 K`
  lying over a rational prime.
* `TauCeti.NumberField.isArithFrobAt_apply_sqrt`: a Frobenius at `Q ∣ p` sends a square root
  of `d` to `legendreSym p d` times it.
-/

public section

open Ideal

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/-- **Frobenius elements exist.** For a Galois number field `K/ℚ` and a prime `Q` of `𝓞 K`
lying over the rational prime `p`, some `σ ∈ Gal(K/ℚ)` is an arithmetic Frobenius at `Q`.
This is Mathlib's `IsArithFrobAt.exists_of_isInvariant` with the number-field side conditions
discharged. -/
theorem exists_isArithFrobAt [IsGalois ℚ K] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  -- `Q` is nonzero since it contains the image of `p`, hence maximal with finite residue field.
  have hQ : Q ≠ ⊥ := by
    intro h0
    have hp : algebraMap ℤ (𝓞 K) p ∈ Q :=
      (algebraMap_int_mem_iff_dvd_of_liesOver Q (p : ℤ)).mpr dvd_rfl
    rw [h0, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by
      exact_mod_cast FaithfulSMul.algebraMap_injective ℤ (𝓞 K) (hp.trans (map_zero _).symm))
  haveI : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ ‹Q.IsPrime›
  exact IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q

/-- **A Frobenius acts on square roots by the Legendre symbol.** Let `K` be a number field,
`p` an odd prime, and `σ ∈ Gal(K/ℚ)` an arithmetic Frobenius at a prime `Q` of `𝓞 K` above
`p`. If `x ∈ K` satisfies `x² = d` for an integer `d` with `p ∤ d`, then

`σ x = legendreSym p d • x`:

the Frobenius fixes `√d` when `d` is a quadratic residue mod `p` and negates it otherwise. -/
theorem isArithFrobAt_apply_sqrt (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = legendreSym p d • x := by
  -- The Galois action on `𝓞 K` is the restriction of the action on `K`: it agrees with
  -- `galRestrict ℤ ℚ K (𝓞 K) σ` (both restrict `σ`, pinned by injectivity of the algebra
  -- map), so compatibility is `algebraMap_galRestrict_apply`.
  have hact : ∀ y : 𝓞 K, algebraMap (𝓞 K) K (σ • y) = σ (algebraMap (𝓞 K) K y) := by
    intro y
    have hgal : galRestrict ℤ ℚ K (𝓞 K) σ y = σ • y := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [algebraMap_galRestrict_apply (A := ℤ) σ y]
      exact (integralClosure.coe_smul σ y).symm
    rw [← hgal, algebraMap_galRestrict_apply (A := ℤ) σ y]
  -- Apply the `𝓞 K`-level computation to the packaged square root.
  have hsmul : σ • integralSqrt hx = legendreSym p d • integralSqrt hx :=
    TauCeti.IsArithFrobAt.smul_sqrt hσ hodd hd (integralSqrt_sq hx)
  -- Push the identity from `𝓞 K` down to `K` along the coercion.
  have hcoe := congrArg (algebraMap (𝓞 K) K) hsmul
  rw [map_zsmul, algebraMap_integralSqrt, hact] at hcoe
  rwa [algebraMap_integralSqrt] at hcoe

end TauCeti.NumberField
