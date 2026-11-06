/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Away
public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.RingTheory.Huber.Pair.Complete
public import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Checks for the Tate ring `A₀[1/π]`

* Compatibility: for every ring of integral elements `A⁺` of `ℚ_p`, the `p`-adic topology on
  `A⁺[1/p] = ℚ_p` is the topology of `ℚ_p`, so the general results recover that `ℚ_p` is a
  complete Hausdorff Tate ring.
* Computation: in `ℤ[1/2]`, the neighbourhood `2² ℤ` contains `4` but not `2`, and `π⁰ ℤ = ℤ`
  does not contain `1/2`.
* Degenerate case: for `π = 1` every neighbourhood `πⁿ A₀` is the whole ring, so the topology is
  indiscrete.
-/

public section

open Topology

namespace TauCeti.Huber.AwayChecks

section Padic

variable (p : ℕ) [Fact p.Prime] {Aplus : Subring ℚ_[p]} (h : IsRingOfIntegralElements Aplus)
include h

/-- `ℚ_p` is a localisation of any of its rings of integral elements away from `p`. -/
theorem isLocalizationAway : IsLocalization.Away (p : Aplus) ℚ_[p] :=
  Aplus.isLocalizationAway_of_isOpen h.isOpen _
    (by simpa using (Padic.isPseudoUniformizer_p (p := p)).isTopologicallyNilpotent)
    (by simpa using (Padic.isPseudoUniformizer_p (p := p)).isUnit)

/-- The neighbourhoods of zero of `ℚ_p` have basis `pⁿ A⁺`. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : ℚ_[p])).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (awayNhd (p : Aplus) ℚ_[p] n : Set ℚ_[p]) := by
  have hp : IsPseudoUniformizer (p : ℚ_[p]) := Padic.isPseudoUniformizer_p
  have hmem : (p : ℚ_[p]) ∈ Aplus := natCast_mem Aplus p
  refine (hp.hasBasis_nhds_zero
    (PairOfDefinition.ofIsPseudoUniformizer Aplus h.isOpen h.isBounded hp hmem)).congr
    (fun _ ↦ Iff.rfl) fun n _ ↦ ?_
  ext x
  simp only [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition, SetLike.mem_coe,
    mem_awayNhd, Set.mem_smul_set, smul_eq_mul, Subtype.exists, map_mul, map_pow, map_natCast]
  exact ⟨fun ⟨y, hy, e⟩ ↦ ⟨y, hy, e⟩, fun ⟨a, b, e⟩ ↦ ⟨a, b, e⟩⟩

/-- **Compatibility**: the `p`-adic topology on `A⁺[1/p]` is the topology of `ℚ_p`. -/
example :
    have := isLocalizationAway p h
    awayTopology (p : Aplus) ℚ_[p] = (inferInstance : TopologicalSpace ℚ_[p]) := by
  have := isLocalizationAway p h
  exact IsTopologicalAddGroup.ext
    (@IsTopologicalRing.isTopologicalAddGroup _ _ (awayTopology (p : Aplus) ℚ_[p])
      isTopologicalRing_awayTopology) inferInstance
    (hasBasis_nhds_zero_awayTopology.eq_of_same_basis (hasBasis_nhds_zero p h))

/-- The general results recover that `ℚ_p` is a Tate ring with pseudouniformiser `p`. -/
example : IsTateRing ℚ_[p] ∧ IsPseudoUniformizer (p : ℚ_[p]) := by
  have := isLocalizationAway p h
  exact ⟨isTateRing_of_hasBasis (hasBasis_nhds_zero p h),
    by simpa using isPseudoUniformizer_algebraMap_of_hasBasis (hasBasis_nhds_zero p h)⟩

/-- The general results recover that `ℚ_p` is Hausdorff and complete, from the `p`-adic
completeness of every ring of integral elements. -/
example : T2Space ℚ_[p] ∧ CompleteSpace ℚ_[p] := by
  have := isLocalizationAway p h
  have hp : IsPseudoUniformizer ((p : Aplus) : ℚ_[p]) := by simpa using Padic.isPseudoUniformizer_p
  have : IsAdicComplete (Ideal.span {(p : Aplus)}) Aplus := h.isAdicComplete_span_singleton _ hp
  have hreg : (p : Aplus) ∈ (nonZeroDivisors Aplus) :=
    mem_nonZeroDivisors_of_ne_zero (fun h0 ↦ by simpa [h0] using hp.isUnit)
  exact ⟨t2Space_of_hasBasis (hasBasis_nhds_zero p h) hreg,
    completeSpace_of_hasBasis (hasBasis_nhds_zero p h) hreg⟩

end Padic

section Dyadic

/-- `ℤ → ℤ[1/2]` is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap ℤ (Localization.Away (2 : ℤ))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)

/-- **Computation**: `4 ∈ 2² ℤ` in `ℤ[1/2]`. -/
example :
    algebraMap ℤ (Localization.Away (2 : ℤ)) 4 ∈ awayNhd (2 : ℤ) (Localization.Away (2 : ℤ)) 2 :=
  mem_awayNhd.mpr ⟨1, by norm_num⟩

/-- **Computation**: `2 ∉ 2² ℤ` in `ℤ[1/2]`. -/
example :
    algebraMap ℤ (Localization.Away (2 : ℤ)) 2 ∉ awayNhd (2 : ℤ) (Localization.Away (2 : ℤ)) 2 := by
  rintro hmem
  obtain ⟨a, ha⟩ := mem_awayNhd.mp hmem
  have := algebraMap_injective ha
  omega

/-- **Non-example**: `1/2` is not in the image `π⁰ ℤ` of `ℤ` in `ℤ[1/2]`, so `awayNhd` is not the
whole localisation. -/
example :
    IsLocalization.Away.invSelf (2 : ℤ) ∉ awayNhd (2 : ℤ) (Localization.Away (2 : ℤ)) 0 := by
  rintro hmem
  obtain ⟨a, ha⟩ := mem_awayNhd.mp hmem
  rw [pow_zero, one_mul] at ha
  have h1 : algebraMap ℤ (Localization.Away (2 : ℤ)) (2 * a) =
      algebraMap ℤ (Localization.Away (2 : ℤ)) 1 := by
    rw [map_mul, ha, IsLocalization.Away.mul_invSelf, map_one]
  have := algebraMap_injective h1
  omega

end Dyadic

section Degenerate

variable {R : Type*} [CommRing R]

/-- **Degenerate case**: for `π = 1` every neighbourhood `πⁿ A₀` is all of `A₀`. -/
example (n : ℕ) : awayNhd (1 : R) R n = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_awayNhd.mpr ⟨x, by simp⟩

/-- `R` is its own localisation away from `1`. -/
theorem isLocalizationAway_one : IsLocalization.Away (1 : R) R :=
  IsLocalization.self (Submonoid.powers_le.mpr ((IsUnit.mem_submonoid_iff 1).mpr isUnit_one))

/-- For `π = 1` the topology is indiscrete: the only neighbourhood of zero is the whole ring. -/
example :
    have := isLocalizationAway_one (R := R)
    @nhds R (awayTopology (1 : R) R) 0 = ⊤ := by
  have := isLocalizationAway_one (R := R)
  refine eq_top_iff.mpr fun s hs ↦ Filter.mem_top.mpr ?_
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_awayTopology.mem_iff.mp hs
  exact Set.eq_univ_of_forall fun x ↦ hn (mem_awayNhd.mpr ⟨x, by simp⟩)

end Degenerate

end TauCeti.Huber.AwayChecks
