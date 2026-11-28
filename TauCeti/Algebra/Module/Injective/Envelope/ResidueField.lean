/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Envelope.Basic
public import TauCeti.Algebra.Module.Torsion.ResidueField

/-!
# Injective envelopes of the residue field of a local ring

Over a commutative Noetherian local ring `R` with maximal ideal `𝔪` and residue field `κ`, every
element of an injective envelope `E` of `κ` is annihilated by a power of `𝔪`
(`TauCeti.IsInjectiveEnvelope.mem_primaryComponent`).

## References

* The Stacks Project, Lemma 47.7.3, Tag 08Z4.
-/

public section

namespace TauCeti.IsInjectiveEnvelope

open IsLocalRing Submodule

variable {R E : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [AddCommGroup E] [Module R E] {ι : ResidueField R →ₗ[R] E}

/-- Every element of an injective envelope of the residue field is killed by a power of `𝔪`. -/
theorem mem_primaryComponent (hι : IsInjectiveEnvelope ι) (x : E) :
    x ∈ (maximalIdeal R).primaryComponent E :=
  hι.isEssential_range.primaryComponent_maximalIdeal_eq_top ▸ mem_top

end TauCeti.IsInjectiveEnvelope
