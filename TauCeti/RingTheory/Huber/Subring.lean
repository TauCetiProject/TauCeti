/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair

/-!
# Subrings of Huber rings

A subring `S` of a topological ring `R` carries the subspace topology. This file compares the
Huber-theoretic notions of `S` with those of `R`.

A subring of a Tate ring is Tate as soon as it contains a pseudouniformiser and its inverse.
No closedness assumption is needed: intersecting a ring of definition with the subring supplies
an open bounded subring. Closedness is needed only when one also wants completeness.

Boundedness for the subspace topology is in general weaker than boundedness in `R`: the
neighbourhoods of zero of `S` only test against elements of `S`. Once `S` contains a
pseudouniformiser of its own, the two notions agree, because a power of the pseudouniformiser
multiplies a bounded subset of `S` into a ring of definition of `R`. Consequently `S° = R° ∩ S`
for a Tate subring `S` of a Huber ring `R`. Finally, the trace `A⁺ ∩ S` of a ring of integral
elements of `R` is a ring of integral elements of `S`, with no hypothesis on `S` beyond being
nonarchimedean.

These are the comparisons needed for the fixed subring of a finite group acting continuously on
a Tate ring (`TauCeti/RingTheory/Huber/Pair/Invariant.lean`).

## Main results

* `Subring.isTateRing_of_isPseudoUniformizer`: a subring containing a pseudouniformiser and its
  inverse is Tate.
* `Subring.isPowerBounded_of_isPowerBounded_coe`: power-boundedness descends to a subring.
* `Subring.isBounded_image_val_iff`: in a subring with a pseudouniformiser of its own, a subset
  is bounded exactly when its image in the ambient Huber ring is.
* `Subring.comap_powerBoundedSubring`: `R° ∩ S = S°` for a Tate subring `S`.
* `TauCeti.Huber.IsRingOfIntegralElements.comap_subtype`: `A⁺ ∩ S` is a ring of integral
  elements of `S`.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace Subring

section Tate

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]

/-- A subring containing a pseudouniformiser as a unit is a Tate ring in its subspace topology.
The unit hypothesis says that the inverse also lies in the subring. -/
theorem isTateRing_of_isPseudoUniformizer (S : Subring R) (u : Rˣ)
    (hu : IsPseudoUniformizer u.val) (hmem : u.val ∈ S) (hinv : (u⁻¹).val ∈ S) :
    IsTateRing S := by
  let v : Sˣ := Units.mkOfMulEqOne ⟨u.val, hmem⟩ ⟨(u⁻¹).val, hinv⟩ (Subtype.ext u.val_inv)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  exact IsTateRing.of_isOpen_isBounded (P.ringOfDefinition.comap S.subtype)
    (P.isOpen_ringOfDefinition.preimage continuous_subtype_val)
    (S.isBounded_preimage_subtype P.isBounded_ringOfDefinition)
    (isPseudoUniformizer_iff.mpr ⟨v.isUnit,
      isTopologicallyNilpotent_mk hmem hu.isTopologicallyNilpotent⟩)

end Tate

section Bounded

/-- Power-boundedness descends to a subring, which carries the subspace topology. -/
theorem isPowerBounded_of_isPowerBounded_coe {R : Type*} [Ring R] [TopologicalSpace R]
    (S : Subring R) {x : S} (hx : IsPowerBounded (x : R)) : IsPowerBounded x := by
  rw [isPowerBounded_iff] at hx ⊢
  refine (S.isBounded_preimage_subtype hx).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, (SubmonoidClass.coe_pow x n).symm⟩

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]

/-- **Boundedness in a subring with a pseudouniformiser.** If the subring `S` of a Huber ring
contains a pseudouniformiser `v` for its subspace topology, a subset of `S` is bounded in `S`
exactly when its image is bounded in the ambient ring. -/
theorem isBounded_image_val_iff (S : Subring R) {v : S} (hv : IsPseudoUniformizer v)
    {s : Set S} : IsBounded (Subtype.val '' s) ↔ IsBounded s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [Set.preimage_image_eq _ Subtype.val_injective] using S.isBounded_preimage_subtype h
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  obtain ⟨n, hn⟩ := h.exists_pow_mul_subset hv.isTopologicallyNilpotent
    ((P.isOpen_ringOfDefinition.preimage continuous_subtype_val).mem_nhds
      P.ringOfDefinition.zero_mem)
  obtain ⟨w, rfl⟩ := hv.isUnit
  -- `w ^ n` multiplies `s` into the ring of definition `A₀`, so `s ⊆ w⁻ⁿ A₀`.
  refine ((isBounded_singleton (((w⁻¹ ^ n : Sˣ) : S) : R)).mul
    P.isBounded_ringOfDefinition).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, rfl, (((w : S) ^ n * x : S) : R), hn (Set.mul_mem_mul rfl hx), ?_⟩
  have hx' : ((w⁻¹ ^ n : Sˣ) : S) * ((w : S) ^ n * x) = x := by
    rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel,
      one_pow, Units.val_one, one_mul]
  exact (MulMemClass.coe_mul S _ _).symm.trans congr(Subtype.val $hx')

/-- In a subring of a Huber ring containing a pseudouniformiser for its subspace topology, an
element is power-bounded exactly when it is power-bounded in the ambient ring. -/
theorem isPowerBounded_coe_iff (S : Subring R) {v : S} (hv : IsPseudoUniformizer v) {x : S} :
    IsPowerBounded (x : R) ↔ IsPowerBounded x := by
  have hpow : (fun n : ℕ ↦ (x : R) ^ n) = Subtype.val ∘ (x ^ · : ℕ → S) :=
    funext fun n ↦ (SubmonoidClass.coe_pow x n).symm
  rw [isPowerBounded_iff, isPowerBounded_iff, ← S.isBounded_image_val_iff hv, ← Set.range_comp,
    hpow]

/-- **`S° = R° ∩ S`** for a subring `S` of a Huber ring that is Tate in its subspace topology. -/
theorem comap_powerBoundedSubring (S : Subring R) [IsTateRing S] :
    (powerBoundedSubring R).comap S.subtype = powerBoundedSubring S := by
  obtain ⟨v, hv⟩ := IsTateRing.exists_isPseudoUniformizer (A := S)
  ext
  rw [Subring.mem_comap, mem_powerBoundedSubring, mem_powerBoundedSubring]
  exact S.isPowerBounded_coe_iff hv

end Bounded

end Subring

namespace TauCeti.Huber

variable {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]

/-- **The trace of a ring of integral elements on a subring.** For a subring `S` of a
nonarchimedean ring, `A⁺ ∩ S` is a ring of integral elements of `S`: it is open in the subspace
topology, integrally closed in `S` because `A⁺` is integrally closed in `R`, and power-bounded in
`S` because power-boundedness descends to subrings. -/
theorem IsRingOfIntegralElements.comap_subtype {Aplus : Subring R}
    (h : IsRingOfIntegralElements Aplus) (S : Subring R) [NonarchimedeanRing S] :
    IsRingOfIntegralElements (Aplus.comap S.subtype) where
  isOpen := h.isOpen.preimage continuous_subtype_val
  isIntegrallyClosedIn := Subring.isIntegrallyClosedIn_iff.mpr fun _ hx ↦
    -- An element of `S` integral over `A⁺ ∩ S` is integral over `A⁺`.
    Subring.isIntegrallyClosedIn_iff.mp h.isIntegrallyClosedIn
      (hx.map_of_comp_eq (S.subtype.restrict _ Aplus fun _ hy ↦ hy) S.subtype
        (RingHom.ext fun _ ↦ rfl))
  le_powerBoundedSubring _ hx := mem_powerBoundedSubring.mpr
    (S.isPowerBounded_of_isPowerBounded_coe (h.isPowerBounded_of_mem hx))

end TauCeti.Huber
