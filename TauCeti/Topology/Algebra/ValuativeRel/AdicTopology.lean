/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The valuation topology of a discretely valued field is adic

Let `K` be a field whose topology is induced by its valuative relation, and whose ring of
integers `𝒪[K]` is a discrete valuation ring; a nonarchimedean local field is the motivating
example. This file proves that the subspace topology of `𝒪[K]` is its `𝓂[K]`-adic topology, and
reads the consequence back in `K`: the powers `𝓂[K] ^ n` form a neighbourhood basis of `0` in
`K` consisting of open additive subgroups, which are moreover compact when `𝒪[K]` is.

So near `0` the topology of `K` is described by the ideals of `𝒪[K]` alone, with no reference to
the value group. For a local field this is the additive counterpart of the statement that the
unit filtration `U(K,n)` is a neighbourhood basis of `1` in `Kˣ`
(`TauCeti.hasBasis_nhds_one_unitFiltration`).

## Main results

* `Irreducible.exists_valuation_pow_lt`: the valuations of the powers of a uniformizer eventually
  drop below any nonzero value.
* `TauCeti.isAdic_maximalIdeal`: the topology of `𝒪[K]` is the `𝓂[K]`-adic topology.
* `TauCeti.hasBasis_nhds_zero_maximalIdeal_pow`: the images in `K` of the powers `𝓂[K] ^ n` form
  a neighbourhood basis of `0` in `K`.
* `TauCeti.isOpen_image_maximalIdeal_pow` and `TauCeti.isCompact_image_maximalIdeal_pow`: each of
  these images is open in `K`, and compact when `𝒪[K]` is.

For a nonarchimedean local field the remaining point-set facts are Mathlib's: `𝒪[K]` is open
(`Valuation.isOpen_integer`) and compact (`CompactSpace 𝒪[K]`), it is `𝓂[K]`-adically complete
(`IsAdicComplete 𝓂[K] 𝒪[K]`), and `Kˣ` is locally compact.

The proof outline for `isAdic_maximalIdeal` follows
`IsDedekindDomain.HeightOneSpectrum.isAdic_maximalIdeal_adicCompletionIntegers`, adapted from
the `Valued` setting of an adic completion to the `ValuativeRel` setting of `K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§4–5.
-/

public section

open Filter Topology ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

/-- For a uniformizer `π`, an element of `𝒪[K]` lies in `𝓂[K] ^ n` exactly when its valuation is
at most that of `π ^ n`. -/
private theorem mem_maximalIdeal_pow_iff_valuation_le {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)
    (x : 𝒪[K]) : x ∈ 𝓂[K] ^ n ↔ valuation K (x : K) ≤ valuation K (π : K) ^ n :=
  Set.ext_iff.mp (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) n) x

/-- The valuations of the powers of a uniformizer `π` of `K` eventually drop below any nonzero
value of the valuation. -/
theorem _root_.Irreducible.exists_valuation_pow_lt {π : 𝒪[K]} (hπ : Irreducible π)
    (γ : (ValueGroupWithZero K)ˣ) : ∃ n : ℕ, valuation K (π : K) ^ n < γ := by
  have hπ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
  rw [← hc]
  by_cases hcO : valuation K c ≤ 1
  · -- An integral `c ≠ 0` is `u π ^ m` for a unit `u` of `𝒪[K]`, so `v(π ^ (m + 1)) < v(c)`.
    have hc0 : (⟨c, hcO⟩ : 𝒪[K]) ≠ 0 := by
      rintro h
      have : c = 0 := congrArg Subtype.val h
      exact γ.ne_zero (by simpa [this] using hc.symm)
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hπ
    have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    have hcu : valuation K c = valuation K (π : K) ^ m := by
      have := congrArg (fun x : 𝒪[K] ↦ valuation K (x : K)) hu
      simpa [hu1] using this
    refine ⟨m + 1, ?_⟩
    rw [hcu, pow_succ]
    exact mul_lt_of_lt_one_right
      (pow_pos (zero_lt_iff.mpr (by simpa using hπ.ne_zero)) m) hπ1
  · -- A non-integral `c` has `v(π) < 1 < v(c)`.
    exact ⟨1, (pow_one (valuation K (π : K))).symm ▸ hπ1.trans (not_le.mp hcO)⟩

variable (K) [TopologicalSpace K] [IsValuativeTopology K]

/-- **The topology of `𝒪[K]` is the `𝓂[K]`-adic topology**: the powers `𝓂[K] ^ n` are open, and
every neighbourhood of `0` in `𝒪[K]` contains one of them. -/
theorem isAdic_maximalIdeal : IsAdic 𝓂[K] := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ0 : valuation K (π : K) ≠ 0 := by simpa using hπ.ne_zero
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · -- `𝓂[K] ^ n` contains the preimage of the open ball of radius `v(π) ^ n`.
    refine (𝓂[K] ^ n).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    have hball : {x : K | valuation K x < valuation K (π : K) ^ n} ∈ 𝓝 (0 : K) :=
      (IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem (i := Units.mk0 _ hπ0 ^ n) trivial
    refine mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hball)
      fun x hx ↦ ?_
    exact (mem_maximalIdeal_pow_iff_valuation_le hπ n x).mpr (le_of_lt hx)
  · -- `s` contains the trace of a ball of some radius `γ`, and `v(π) ^ n < γ` for large `n`.
    obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).mp hs
    obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp ht
    obtain ⟨n, hn⟩ := hπ.exists_valuation_pow_lt γ
    exact ⟨n, fun x hx ↦ hts <| hγ <|
      ((mem_maximalIdeal_pow_iff_valuation_le hπ n x).mp hx).trans_lt hn⟩

/-- **The powers of the maximal ideal form a neighbourhood basis of `0` in `K`**: a subset of `K`
is a neighbourhood of `0` exactly when it contains `𝓂[K] ^ n` for some `n`. -/
theorem hasBasis_nhds_zero_maximalIdeal_pow :
    (𝓝 (0 : K)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((↑) : 𝒪[K] → K) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  have h := ((isAdic_maximalIdeal K).hasBasis_nhds_zero).map ((↑) : 𝒪[K] → K)
  rwa [map_nhds_subtype_val, ZeroMemClass.coe_zero,
    nhdsWithin_eq_nhds.mpr (((valuation K).isOpen_integer).mem_nhds (zero_mem _))] at h

/-- Each power `𝓂[K] ^ n` of the maximal ideal is open in `K`. -/
theorem isOpen_image_maximalIdeal_pow (n : ℕ) :
    IsOpen (((↑) : 𝒪[K] → K) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) :=
  ((valuation K).isOpen_integer).isOpenMap_subtype_val _ ((isAdic_maximalIdeal K).isOpen_pow n)

/-- If `𝒪[K]` is compact, as for a nonarchimedean local field, then each power `𝓂[K] ^ n` of the
maximal ideal is compact in `K`. -/
theorem isCompact_image_maximalIdeal_pow [CompactSpace 𝒪[K]] (n : ℕ) :
    IsCompact (((↑) : 𝒪[K] → K) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) :=
  ((isAdic_maximalIdeal K).isClosed_pow n).isCompact.image continuous_subtype_val

end TauCeti
