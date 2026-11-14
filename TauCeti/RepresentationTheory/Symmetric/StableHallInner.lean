/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.HallInner

/-!
# The orthogonality of the power sums in the symmetric functions

The power-sum products `p_μ` of the partitions `μ` of `n` are orthogonal for the Hall inner product
`TauCeti.stableHallInner R n` on the symmetric functions of degree `n`: `⟨p_μ, p_ν⟩ = z_μ δ_(μν)`,
where `z_μ` is the order of the centralizer of a permutation of cycle type `μ` (`TauCeti.zPart`).
In `n` variables this is `TauCeti.hallInner_psumPart`, which rests on the character table of the
symmetric group; it passes to the symmetric functions because projection to an alphabet of `n`
letters is an isometry (`TauCeti.hallInner_stableSymmetricProj`).

## Main results

* `TauCeti.stableHallInner_stablePsumPart`: **the power sums are orthogonal**,
  `⟨p_μ, p_ν⟩ = z_μ δ_(μν)`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 4, (4.7): the orthogonality of the power sums.
-/

public section

namespace TauCeti

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The power sums are orthogonal for the Hall inner product**: `⟨p_μ, p_ν⟩ = z_μ δ_(μν)` for
the power-sum products of partitions of `n`, where `z_μ = ∏ᵢ i^(mᵢ) mᵢ!` is the order of the
centralizer of a permutation of cycle type `μ` (`TauCeti.zPart`). This holds over every commutative
ring. -/
@[simp]
theorem stableHallInner_stablePsumPart (μ ν : n.Partition) :
    stableHallInner R n (stablePsumPart R μ) (stablePsumPart R ν) =
      if μ = ν then (zPart μ : R) else 0 := by
  have h (ρ : n.Partition) : stableSymmetricProj R n n (stablePsumPart R ρ) =
      ⟨psumPart (Fin n) R ρ, psumPart_mem_symmetricHomogeneousSubmodule R ρ⟩ :=
    Subtype.ext (coe_stableSymmetricProj_stablePsumPart R ρ n)
  rw [← hallInner_stableSymmetricProj le_rfl, h, h, hallInner_psumPart (by simp)]

end TauCeti
