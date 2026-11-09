/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.AdicRing.Basic

/-!
# Complete rank-one valuation bases

Formal models over a complete nonarchimedean field `K` with a nontrivial rank-one absolute value
live over its valuation ring `O = K°`, equipped with a pseudouniformiser `ϖ` (an element with
`0 < |ϖ| < 1`) and the `ϖ`-adic topology. This file bundles that standing data, independently of
the field, as the class `TauCeti.Huber.IsCompleteRankOneBase O ϖ`: the ring `O` has Krull
dimension one, `ϖ` is nonzero and not a unit, the topology of `O` is the `ϖ`-adic one, and `O` is
`ϖ`-adically separated and complete. That `O` is a valuation ring and a domain is assumed
separately where it is used. `O` need not be noetherian: it is noetherian exactly when `K` is
discretely valued, and `𝒪_{ℂ_p}` is the standard example where it is not.

The class does not mention the maximal ideal `m_O` of `O`. The `ϖ`-adic topology is the valuation
topology, while the `m_O`-adic topology can differ from it: for `𝒪_{ℂ_p}` one has `m_O = m_O²`, so
the `m_O`-adic topology has `m_O` as its smallest neighbourhood of zero and is not separated.

Separatedness is what makes `ϖ` behave like a uniformiser for divisibility: in a `ϖ`-adically
separated valuation ring every nonzero element divides a power of `ϖ`
(`TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff`). Consequently a module on which `ϖ` acts
injectively has no torsion at all (`IsSMulRegular.of_isHausdorff`), which is what identifies
flatness over `O` with the absence of `ϖ`-torsion for the admissible algebras of
Bosch–Lütkebohmert.

## Main definitions

* `TauCeti.Huber.IsCompleteRankOneBase`: the standing data on a complete rank-one valuation base.

## Main results

* `TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff`: in a valuation ring that is separated
  for the `ϖ`-adic topology, every nonzero element divides a power of `ϖ`.
* `IsSMulRegular.of_isHausdorff`: over such a ring, a module on which `ϖ` is regular is
  torsion-free.
* `TauCeti.Huber.IsCompleteRankOneBase.isAdicRing`: the base is an adic ring of finite ideal type,
  with ideal of definition `(ϖ)`.

## References

* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*, Math. Ann. 295
  (1993), §1.
* B. Conrad, *Several approaches to non-archimedean geometry*, in *p-adic Geometry* (Arizona
  Winter School 2007), §3.3.
-/

public section

/-- In a valuation ring that is separated for the `ϖ`-adic topology, every nonzero element
divides some power of `ϖ`: otherwise it would lie in every `ϖⁿ R`. -/
theorem TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff {R : Type*} [CommRing R]
    [PreValuationRing R] {ϖ : R} [IsHausdorff (Ideal.span {ϖ}) R] {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, a ∣ ϖ ^ n := by
  by_contra! h
  refine ha (IsHausdorff.haus (I := Ideal.span {ϖ}) inferInstance a fun n ↦ ?_)
  rcases ValuationRing.dvd_total a (ϖ ^ n) with hdvd | hdvd
  · exact absurd hdvd (h n)
  · rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr hdvd

/-- Over a valuation ring that is separated for the `ϖ`-adic topology, a module on which `ϖ`
acts injectively has no torsion: multiplication by every nonzero scalar is injective. -/
theorem IsSMulRegular.of_isHausdorff {R M : Type*} [CommRing R] [PreValuationRing R]
    [AddCommGroup M] [Module R M] {ϖ : R} [IsHausdorff (Ideal.span {ϖ}) R]
    (hϖ : IsSMulRegular M ϖ) {a : R} (ha : a ≠ 0) : IsSMulRegular M a := by
  obtain ⟨n, b, hb⟩ := TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff (ϖ := ϖ) ha
  have h := hϖ.pow n
  rw [hb, mul_comm] at h
  exact h.of_mul

namespace TauCeti.Huber

/-- The standing data on a **complete rank-one valuation base** `O` with pseudouniformiser `ϖ`:
`O` has Krull dimension one, `ϖ` is nonzero and not a unit, the topology of `O` is the
`ϖ`-adic topology, and `O` is `ϖ`-adically separated and complete. That `O` is a valuation ring
and a domain is assumed separately where it is used. -/
class IsCompleteRankOneBase (O : Type*) [CommRing O] [TopologicalSpace O] (ϖ : O) : Prop where
  /-- The base has Krull dimension one. -/
  ringKrullDim_eq_one : ringKrullDim O = 1
  /-- The pseudouniformiser is nonzero. -/
  ne_zero : ϖ ≠ 0
  /-- The pseudouniformiser is not a unit. -/
  not_isUnit : ¬ IsUnit ϖ
  /-- The topology of the base is the `ϖ`-adic topology. -/
  isAdic : IsAdic (Ideal.span {ϖ})
  /-- The base is `ϖ`-adically separated and complete. -/
  isAdicComplete : IsAdicComplete (Ideal.span {ϖ}) O

namespace IsCompleteRankOneBase

variable {O : Type*} [CommRing O] [TopologicalSpace O] (ϖ : O) [IsCompleteRankOneBase O ϖ]

-- A complete rank-one valuation base is `ϖ`-adically separated and complete; registering this
-- lets lemmas stated with `[IsHausdorff (Ideal.span {ϖ}) O]` apply to such a base directly.
attribute [instance] IsCompleteRankOneBase.isAdicComplete

include ϖ

/-- A complete rank-one valuation base is an adic ring of finite ideal type, with ideal of
definition `(ϖ)`. -/
theorem isAdicRing [IsTopologicalRing O] : IsAdicRing O :=
  ⟨Ideal.span {ϖ}, ⟨{ϖ}, by simp⟩, isAdic, isAdicComplete⟩

end IsCompleteRankOneBase

end TauCeti.Huber
