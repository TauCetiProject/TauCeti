/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Renaming the variables of `A⟨X⟩_T`

An embedding `e : Fin k ↪ Fin m` of variables renames power series in `k` variables to power
series in `m` variables, `Xᵢ ↦ X_{e i}`. Renaming preserves weighted restrictedness as soon as each
weight `T i` lies in the weight `S (e i)` of the variable it is sent to, and so induces a
continuous ring homomorphism `A⟨X⟩_T → A⟨X⟩_S`.

At the trivial weight these include the two maps `A⟨ζ⟩ → A⟨X, Y⟩`, `ζ ↦ X` and `ζ ↦ Y`, that
compare the pieces of a two-piece Laurent cover with their overlap in Wedhorn's Lemma 8.33.

## Main definitions

* `TauCeti.Huber.weightedRename`: the ring homomorphism `A⟨X⟩_T → A⟨X⟩_S` induced by an embedding
  of the variables; `TauCeti.Huber.coe_weightedRename` says it is `MvPowerSeries.rename`.

## Main results

* `TauCeti.Huber.IsWeightedRestricted.rename`: renaming along an embedding carries `T`-restricted
  series to `S`-restricted ones.
* `TauCeti.Huber.weightedRename_weightedC` and `TauCeti.Huber.weightedRename_weightedX`: the
  induced homomorphism fixes the constants and sends `Xᵢ` to `X_{e i}`.
* `TauCeti.Huber.continuous_weightedRename`: it is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48, and
  the proof of Lemma 8.33. This serves §4.1 step 5 of `TauCetiRoadmap/AdicSpaces/README.md`.

## Provenance

The renaming is Mathlib's `MvPowerSeries.rename`. AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0) at commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/TateAlgebra.lean`, has the two
trivial-weight maps from its `TateAlgebra A` into `TateAlgebra₂ A` as `posIncl` and `negIncl`,
built on its own `varInclHom`, with `posIncl_algebraMap` and `posIncl_X` and their `negIncl`
counterparts. They were consulted; nothing was copied, and the construction here is for an
arbitrary embedding of variables and arbitrary weights.
-/

public section

open Filter Finsupp

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] {k m : ℕ}

omit [TopologicalSpace A] in
private theorem coeff_rename_eq_zero_of_notMem_range_embDomain {σ τ : Type*} (e : σ ↪ τ)
    (p : MvPowerSeries σ A) {ν : τ →₀ ℕ} (h : ν ∉ Set.range (embDomain e)) :
    MvPowerSeries.coeff ν (MvPowerSeries.rename e p) = 0 :=
  MvPowerSeries.coeff_rename_eq_zero _ _ (by rwa [← funext (embDomain_eq_mapDomain e)])

open Pointwise in
omit [TopologicalSpace A] in
private theorem weightPow_subset_weightPow_embDomain (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} (hTS : ∀ i, T i ⊆ S (e i)) (s : Fin k →₀ ℕ) :
    weightPow T s ⊆ weightPow S (embDomain e s) := by
  refine (weightPow_mono hTS s).trans_eq ?_
  -- reindex the product over `Fin m` along `e`: off its image the exponents vanish
  rw [weightPow_def, weightPow_def]
  exact Fintype.prod_of_injective e e.injective _ _
    (fun j hj ↦ by rw [embDomain_of_notMem_range _ _ _ hj, pow_zero]) (by simp)

omit [TopologicalSpace A] in
private theorem weightMul_le_weightMul_embDomain (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} (hTS : ∀ i, T i ⊆ S (e i)) (s : Fin k →₀ ℕ) (U : AddSubgroup A) :
    weightMul T s U ≤ weightMul S (embDomain e s) U :=
  weightMul_le.mpr fun _ ht _ hu ↦
    mul_mem_weightMul S _ U (weightPow_subset_weightPow_embDomain e hTS s ht) hu

/-- **Renaming preserves weighted restrictedness**: along an embedding `e` of the variables with
each `T i ⊆ S (e i)`, a `T`-restricted series renames to an `S`-restricted one. The weights of the
variables outside the image of `e` are arbitrary. This renames the variables, where
`TauCeti.Huber.IsWeightedRestricted.map` changes the coefficient ring. -/
theorem IsWeightedRestricted.rename (e : Fin k ↪ Fin m) {T : Fin k → Set A} {S : Fin m → Set A}
    (hTS : ∀ i, T i ⊆ S (e i)) {f : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f) :
    IsWeightedRestricted S (MvPowerSeries.rename e f) := by
  refine isWeightedRestricted_iff.mpr fun U ↦ eventually_cofinite.mpr <|
    ((hf.finite_coeff_notMem U).image (embDomain e)).subset fun ν hν ↦ ?_
  -- off the image of `embDomain e` the renamed coefficients vanish, so `ν` lies in that image
  obtain ⟨s, rfl⟩ : ν ∈ Set.range (embDomain e) :=
    by_contra fun h ↦ hν (coeff_rename_eq_zero_of_notMem_range_embDomain e f h ▸ zero_mem _)
  exact ⟨s, fun hs ↦ hν <| by simpa using weightMul_le_weightMul_embDomain e hTS s _ hs, rfl⟩

/-- **The homomorphism `A⟨X⟩_T → A⟨X⟩_S` induced by an embedding `e` of the variables**, sending
`Xᵢ` to `X_{e i}`. Each weight `T i` must lie in the weight `S (e i)` of its image.

It moves the variables and keeps the coefficients, where `TauCeti.Huber.weightedMap` moves the
coefficients along a ring map and keeps the variables. Its values are computed by
`TauCeti.Huber.coe_weightedRename`. -/
noncomputable def weightedRename [NonarchimedeanRing A] (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} (hT : IsWeightFamily T) (hS : IsWeightFamily S) (hTS : ∀ i, T i ⊆ S (e i)) :
    weightedRestrictedSubring T hT →+* weightedRestrictedSubring S hS :=
  (MvPowerSeries.rename e).toRingHom.restrict _ _ fun _ hf ↦
    mem_weightedRestrictedSubring.mpr <| (mem_weightedRestrictedSubring.mp hf).rename e hTS

/-- `weightedRename` is `MvPowerSeries.rename` with its domain and codomain cut down. -/
@[simp]
theorem coe_weightedRename [NonarchimedeanRing A] (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} {hT : IsWeightFamily T} {hS : IsWeightFamily S} (hTS : ∀ i, T i ⊆ S (e i))
    (f : weightedRestrictedSubring T hT) :
    (weightedRename e hT hS hTS f : MvPowerSeries (Fin m) A) =
      MvPowerSeries.rename e (f : MvPowerSeries (Fin k) A) := (rfl)

/-- `weightedRename` fixes the constant series. -/
@[simp]
theorem weightedRename_weightedC [NonarchimedeanRing A] (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} {hT : IsWeightFamily T} {hS : IsWeightFamily S} (hTS : ∀ i, T i ⊆ S (e i))
    (a : A) : weightedRename e hT hS hTS (weightedC T hT a) = weightedC S hS a :=
  Subtype.ext (by simp)

/-- `weightedRename` sends the variable `Xᵢ` to `X_{e i}`. -/
@[simp]
theorem weightedRename_weightedX [NonarchimedeanRing A] (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} {hT : IsWeightFamily T} {hS : IsWeightFamily S} (hTS : ∀ i, T i ⊆ S (e i))
    (i : Fin k) : weightedRename e hT hS hTS (weightedX T hT i) = weightedX S hS (e i) :=
  Subtype.ext (by simp)

/-- **`weightedRename` is continuous** for the weighted topologies, so it is a morphism of
topological rings. -/
theorem continuous_weightedRename [NonarchimedeanRing A] (e : Fin k ↪ Fin m) {T : Fin k → Set A}
    {S : Fin m → Set A} (hT : IsWeightFamily T) (hS : IsWeightFamily S) (hTS : ∀ i, T i ⊆ S (e i)) :
    Continuous (weightedRename e hT hS hTS) := by
  -- the basic neighbourhood `V⟨X⟩` of the source lands in `V⟨X⟩` of the target
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_weightedTopology hT).tendsto_iff
    (hasBasis_nhds_zero_weightedTopology hS)]
  refine fun V _ ↦ ⟨V, trivial, fun f hf ↦ mem_weightedNhd.mpr fun ν ↦ ?_⟩
  obtain ⟨s, rfl⟩ | h := em (ν ∈ Set.range (embDomain e))
  · simpa using weightMul_le_weightMul_embDomain e hTS s _ (mem_weightedNhd.mp hf s)
  · simp [coeff_rename_eq_zero_of_notMem_range_embDomain e _ h]

end TauCeti.Huber
