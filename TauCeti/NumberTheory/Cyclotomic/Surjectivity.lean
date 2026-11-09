/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Surjectivity of finite cyclotomic characters

In a normal extension containing all `n`-th roots of unity, irreducibility of the `n`-th
cyclotomic polynomial makes the finite cyclotomic character surjective. A primitive root and
any of its coprime powers have the same minimal polynomial; normality realizes this conjugacy
by an automorphism of the ambient field. This supplies the finite-level input to surjectivity
of cyclotomic characters on absolute Galois groups.

The central formal input is `IsPrimitiveRoot.exists_algEquiv_apply_eq_pow_of_coprime`.

## References

* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.7.4.
-/

public section

namespace TauCeti

open Polynomial

/-- If `Φ_n` is irreducible over `K`, the action of a normal extension's Galois group on
its `n`-th roots of unity realizes every unit modulo `n`. -/
theorem modularCyclotomicCharacter_surjective_of_irreducible
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    {n : ℕ} [NeZero n] (hn : Nat.card (rootsOfUnity n L) = n)
    (hirr : Irreducible (cyclotomic n K)) :
    Function.Surjective (fun σ : Gal(L/K) ↦
      modularCyclotomicCharacter L hn σ.toRingEquiv) := by
  obtain ⟨ζ, hζ⟩ := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hn
  intro u
  obtain ⟨σ, hpow⟩ := hζ.exists_algEquiv_apply_eq_pow_of_coprime
    (ZMod.val_coe_unit_coprime u).symm hirr
  refine ⟨σ, ?_⟩
  have hAut : hζ.autToPow K σ = u := by
    exact Units.ext (by simpa only [ZMod.natCast_zmod_val] using
      hζ.coe_autToPow_eq_natCast hpow)
  exact (IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter n K hζ σ).symm.trans hAut

end TauCeti
