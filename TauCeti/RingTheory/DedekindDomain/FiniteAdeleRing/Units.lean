/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import TauCeti.Topology.Algebra.RestrictedProduct.Units
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

/-!
# The finite ideles as a restricted product

Let `R` be a Dedekind domain with fraction field `K`. The *finite ideles* are the units
`𝔸ᶠ[R, K]ˣ` of the finite adele ring, with the units topology induced by `x ↦ (x, x⁻¹)`. Placewise,
a finite idele is a family of units `x_v ∈ K_vˣ` that are units of the local integers `𝒪_v` for all
but finitely many `v`, so Mathlib's `RestrictedProduct.unitsEquiv` identifies the finite ideles,
as a group, with the restricted product of the local unit groups `K_vˣ` with respect to the local
integral units `𝒪_vˣ`.

This file shows that this identification is also topological: the units topology of the finite
ideles is the restricted-product topology of the groups `K_vˣ`. The local integer rings are open in
the completions, so this is a case of `ContinuousMulEquiv.restrictedProductUnits`. In particular,
a map into the finite ideles is continuous as soon as it is continuous into the restricted product
of the local unit groups, and the finite ideles carry the usual idelic topology. This topology is
finer than the subspace topology from the finite adeles, and strictly finer as soon as `R` has
infinitely many height-one primes (for instance for the ring of integers of a number field):
uniformizers placed at single places tend to `1` in the finite adeles, while their inverses stay
outside the open set of integral finite adeles.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.unitsContinuousMulEquiv`: the isomorphism of topological groups
  between the finite ideles and the restricted product of the `K_vˣ` with respect to the `𝒪_vˣ`.
* `IsDedekindDomain.FiniteAdeleRing.not_isEmbedding_val`: for infinitely many height-one primes,
  the inclusion of the finite ideles into the finite adeles is not an embedding.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* A. Weil, *Basic Number Theory*, Chapter IV, §3.
-/

public section

open scoped RestrictedProduct

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **The finite ideles are the restricted product of the local unit groups**: the units of the
finite adele ring, with the units topology, are isomorphic as topological groups to the restricted
product of the unit groups `K_vˣ` of the completions with respect to the local integral units
`𝒪_vˣ`. The underlying group isomorphism is Mathlib's `RestrictedProduct.unitsEquiv`. -/
noncomputable def unitsContinuousMulEquiv :
    𝔸ᶠ[R, K]ˣ ≃ₜ* Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  ContinuousMulEquiv.restrictedProductUnits fun _ ↦ Valued.isOpen_valuationSubring _

variable {R K}

/-- The underlying group isomorphism of `FiniteAdeleRing.unitsContinuousMulEquiv` is Mathlib's
`RestrictedProduct.unitsEquiv`. -/
theorem unitsContinuousMulEquiv_apply (x : 𝔸ᶠ[R, K]ˣ) :
    unitsContinuousMulEquiv R K x = RestrictedProduct.unitsEquiv _ x :=
  ContinuousMulEquiv.restrictedProductUnits_apply _ x

/-- The local unit at `v` attached to a finite idele by `FiniteAdeleRing.unitsContinuousMulEquiv`
is its coordinate at `v`. -/
@[simp]
theorem coe_unitsContinuousMulEquiv_apply (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    (unitsContinuousMulEquiv R K x v : v.adicCompletion K) = (x : 𝔸ᶠ[R, K]) v :=
  ContinuousMulEquiv.coe_restrictedProductUnits_apply _ x v

/-- The finite idele attached to a restricted family of local units has these units as its
coordinates. -/
@[simp]
theorem unitsContinuousMulEquiv_symm_apply_apply
    (y : Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units])
    (v : HeightOneSpectrum R) :
    ((unitsContinuousMulEquiv R K).symm y : 𝔸ᶠ[R, K]) v = y v :=
  ContinuousMulEquiv.restrictedProductUnits_symm_apply_apply _ y v

/-! ### The units topology is strictly finer than the subspace topology -/

section Embedding

open Filter Topology

variable (R K) in
/-- **The finite ideles do not carry the subspace topology** when `R` has infinitely many
height-one primes: the inclusion of the units of the finite adele ring, with the units topology,
is not an embedding. -/
theorem not_isEmbedding_val [Infinite (HeightOneSpectrum R)] :
    ¬IsEmbedding (Units.val : 𝔸ᶠ[R, K]ˣ → 𝔸ᶠ[R, K]) := by
  intro h
  -- uniformizers placed at single places tend to `1`, while their inverses never enter the
  -- open set of integral finite adeles
  choose x hx hxinv using fun v : HeightOneSpectrum R ↦
    v.exists_mem_adicCompletionIntegers_inv_notMem K
  let u : HeightOneSpectrum R → 𝔸ᶠ[R, K]ˣ := fun v ↦ Units.map (ofAdicCompletion K v) (x v)
  have hu : Tendsto u cofinite (𝓝 1) := by
    rw [h.isInducing.tendsto_nhds_iff, Units.val_one]
    exact tendsto_ofAdicCompletion_cofinite hx
  have hmem := ((Units.continuous_coe_inv.tendsto 1).comp hu).eventually
    ((isOpen_integralAdeles R K).mem_nhds (by simp))
  obtain ⟨v, hv⟩ := hmem.exists
  have hinv : (((u v)⁻¹ : 𝔸ᶠ[R, K]ˣ) : 𝔸ᶠ[R, K]) v = ((x v)⁻¹ : (v.adicCompletion K)ˣ) := by
    rw [Units.coe_map_inv, ofAdicCompletion_apply_self]
  exact hxinv v (hinv ▸ mem_integralAdeles.1 hv v)

end Embedding

end IsDedekindDomain.FiniteAdeleRing
