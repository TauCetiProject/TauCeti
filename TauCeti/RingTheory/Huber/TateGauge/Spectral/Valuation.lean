/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TateGauge.Spectral.Topology
public import TauCeti.RingTheory.Valuation.Continuous.Basic
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.RingTheory.Valuation.LtAddSubgroup

/-!
# Continuous valuations for the spectral topology

Let `A` be a Tate ring and `A_sp = SpectralTop A` the ring `A` with its spectral topology, which
is coarser than the topology of `A`. This file shows that the two topologies cannot be told
apart by valuations: a valuation is continuous for the topology of `A` exactly when it is
continuous for the spectral topology.

One direction is continuity of the identity `A → A_sp`. Conversely, if `v` is continuous on `A`
and `v(b) ≠ 0`, pick a pseudouniformiser `ϖ` and `n` with `v(ϖ)ⁿ < v(b)`; since `v` is below `1`
on the topologically nilpotent elements `A°°`, the spectral neighbourhood `ϖⁿ • A°°` of zero lies
in the additive subgroup `{x | v(x) < v(b)}`, which is therefore open for the spectral topology.

## Main results

* `TauCeti.Huber.SpectralTop.valuation_isContinuous_iff`: a valuation on `A_sp` is continuous
  exactly when its pullback to `A` is.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.4.3 and Definition 2.8.13.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7.
-/

public section

open Topology

namespace TauCeti.Huber.SpectralTop

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **Valuations do not see the spectral topology.** A valuation on `SpectralTop A` is continuous
exactly when its pullback to `A` is continuous for the topology of `A`. -/
theorem valuation_isContinuous_iff {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {v : Valuation (SpectralTop A) Γ₀} :
    v.IsContinuous ↔ (v.comap (toSpectralTop A : A →+* SpectralTop A)).IsContinuous := by
  refine ⟨fun hv ↦ hv.comap continuous_toSpectralTop, fun hv ↦ ?_⟩
  set w := v.comap (toSpectralTop A : A →+* SpectralTop A)
  have hw (x : A) : w x = v (toSpectralTop A x) := by simp [w]
  rw [Valuation.isContinuous_def]
  intro b
  rcases eq_or_ne (v b) 0 with hb | hb
  · simp [hb]
  have : Nontrivial Γ₀ := ⟨⟨_, _, hb⟩⟩
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  -- Some power of `ϖ` has value below `v b`.
  have hball : {x : A | w x < v b} ∈ 𝓝 0 := by
    have hopen := Valuation.isContinuous_def.mp hv ((toSpectralTop A).symm b)
    rw [hw, RingEquiv.apply_symm_apply] at hopen
    exact hopen.mem_nhds (by simpa [hw] using pos_iff_ne_zero.mpr hb)
  obtain ⟨n, hn⟩ := Valuation.exists_pow_lt_of_isTopologicallyNilpotent hball
    hϖ.isTopologicallyNilpotent
  -- The spectral neighbourhood `ϖ ^ n • A°°` of zero lies in the subgroup `{x | v x < v b}`,
  -- since `v < 1` on `A°°`.
  have hmem : ((v.ltAddSubgroupOfNeZero hb : AddSubgroup (SpectralTop A)) : Set (SpectralTop A)) ∈
      𝓝 0 := by
    refine Filter.mem_of_superset ((hasBasis_nhds_zero hϖ).mem_of_mem (i := n) trivial) ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Valuation.mem_ltAddSubgroupOfNeZero, ← hw]
    beta_reduce
    rw [smul_eq_mul, map_mul, map_pow]
    calc w ϖ ^ n * w a ≤ w ϖ ^ n * 1 := by
          gcongr
          exact (hv.lt_one_of_isTopologicallyNilpotent ha).le
      _ < v b := by rwa [mul_one]
  simpa using (v.ltAddSubgroupOfNeZero hb).isOpen_of_mem_nhds hmem

end TauCeti.Huber.SpectralTop
