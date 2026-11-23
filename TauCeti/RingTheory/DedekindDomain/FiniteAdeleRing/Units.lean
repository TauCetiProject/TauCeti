/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import TauCeti.Topology.Algebra.RestrictedProduct.Units

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
* `IsDedekindDomain.FiniteAdeleRing.tendsto_ofAdicCompletion_cofinite`: local integers placed at
  single places tend to `1` in the finite adeles.
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

variable (K) in
/-- The finite adele `ofAdicCompletion K v x` has `v`-component `x`. -/
theorem ofAdicCompletion_apply_self (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    ofAdicCompletion K v x v = x := by
  classical
  exact RestrictedProduct.mulSingle_eq_same _ v x

variable (K) in
/-- The finite adele `ofAdicCompletion K v x` is `1` at every place other than `v`. -/
theorem ofAdicCompletion_apply_of_ne {v w : HeightOneSpectrum R} (h : w ≠ v)
    (x : v.adicCompletion K) : ofAdicCompletion K v x w = 1 := by
  classical
  exact RestrictedProduct.mulSingle_eq_of_ne _ x h

/-- For local integers `x v ∈ 𝒪_v`, the finite adeles `ofAdicCompletion K v (x v)`, equal to `x v`
at `v` and to `1` at every other place, tend to `1` as `v` leaves every finite set of places. -/
theorem tendsto_ofAdicCompletion_cofinite {x : ∀ v : HeightOneSpectrum R, v.adicCompletion K}
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers K) :
    Tendsto (fun v ↦ ofAdicCompletion K v (x v)) cofinite (𝓝 1) := by
  classical
  let y : HeightOneSpectrum R → ∀ w : HeightOneSpectrum R, w.adicCompletionIntegers K :=
    fun v ↦ Pi.mulSingle v ⟨x v, hx v⟩
  have hy : Tendsto y cofinite (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun w ↦ tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_cofinite_ne w] with v hv
    exact Pi.mulSingle_eq_of_ne' hv _
  have hc := (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum R ↦
    v.adicCompletion K) (A := fun v ↦ (v.adicCompletionIntegers K : Set _))
    (𝓕 := cofinite)).continuous
  refine ((hc.tendsto 1).comp hy).congr fun v ↦ FiniteAdeleRing.ext K fun w ↦ ?_
  rcases eq_or_ne w v with rfl | hw
  · rw [ofAdicCompletion_apply_self]
    change ((y w w : w.adicCompletionIntegers K) : w.adicCompletion K) = x w
    simp [y]
  · rw [ofAdicCompletion_apply_of_ne K hw]
    change ((y v w : w.adicCompletionIntegers K) : w.adicCompletion K) = 1
    simp [y, Pi.mulSingle_eq_of_ne hw]

variable (K) in
/-- The completion `K_v` has a unit `x ∈ 𝒪_v` whose inverse is not in `𝒪_v`: the image of an
element of `K` of `v`-adic valuation `exp (-1)`. -/
theorem _root_.IsDedekindDomain.HeightOneSpectrum.exists_mem_adicCompletionIntegers_inv_notMem
    (v : HeightOneSpectrum R) :
    ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∉ v.adicCompletionIntegers K := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1) := by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have h0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨Units.mk0 _ h0, ?_, ?_⟩
  · rw [mem_adicCompletionIntegers, Units.val_mk0, hv]
    exact WithZero.exp_le_one_iff.2 (by norm_num)
  · rw [mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hv,
      ← WithZero.exp_neg, neg_neg, not_le]
    exact WithZero.one_lt_exp_iff.2 one_pos

variable (R K) in
/-- **The finite ideles do not carry the subspace topology** when `R` has infinitely many
height-one primes: the inclusion of the units of the finite adele ring, with the units topology,
is not an embedding. Uniformizers `π_v` placed at single places tend to `1` in `𝔸ᶠ[R, K]`, while
their inverses never enter the open set of integral finite adeles. -/
theorem not_isEmbedding_val [Infinite (HeightOneSpectrum R)] :
    ¬IsEmbedding (Units.val : 𝔸ᶠ[R, K]ˣ → 𝔸ᶠ[R, K]) := by
  intro h
  choose x hx hxinv using fun v : HeightOneSpectrum R ↦
    v.exists_mem_adicCompletionIntegers_inv_notMem K
  let u : HeightOneSpectrum R → 𝔸ᶠ[R, K]ˣ := fun v ↦ Units.map (ofAdicCompletion K v) (x v)
  have hu : Tendsto u cofinite (𝓝 1) := by
    rw [h.isInducing.tendsto_nhds_iff, Units.val_one]
    exact tendsto_ofAdicCompletion_cofinite hx
  have hopen : IsOpen {a : 𝔸ᶠ[R, K] | ∀ w, a w ∈ w.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem fun w ↦ Valued.isOpen_valuationSubring _
  have hmem := ((Units.continuous_coe_inv.tendsto 1).comp hu).eventually
    (hopen.mem_nhds fun w ↦ by
      rw [inv_one, Units.val_one]
      exact one_mem _)
  obtain ⟨v, hv⟩ := hmem.exists
  refine hxinv v ?_
  simpa [u, ← map_inv, ofAdicCompletion_apply_self] using hv v

end Embedding

end IsDedekindDomain.FiniteAdeleRing
