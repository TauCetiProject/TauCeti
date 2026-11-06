/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Admissibility
public import TauCeti.LowDimTopology.Heegaard.MaslovIndex
import Mathlib.Tactic.Linarith

/-!
# Weak admissibility for a fixed spin^c structure

Weak admissibility of a pointed Heegaard diagram (`TauCeti.HeegaardRegionSystem.WeaklyAdmissible`)
asks every nonzero periodic domain to have coefficients of both signs. Ozsváth and Szabó only
need this for the periodic domains `P` that pair to zero with the first Chern class of the spin^c
structure `s` under consideration: the diagram is *weakly admissible for `s`* when every nonzero
periodic domain `P` with `⟨c₁(s), H(P)⟩ = 0` has both positive and negative coefficients.

For a generator `x` with `s_z(x) = s`, the pairing `⟨c₁(s), H(P)⟩` is the Maslov index of `P`
at `x` (Ozsváth–Szabó, Theorem 4.9), which on the incidence data `TauCeti.HeegaardRegionSystem`
is the combinatorial Maslov index `TauCeti.HeegaardRegionSystem.maslovIndex` with region Euler
characteristics `χ`. So we define weak admissibility at a generator `x`,
`TauCeti.HeegaardRegionSystem.WeaklyAdmissibleAt`, by the condition on periodic domains of
Maslov index zero at `x`; it depends only on the class of `x` under the relation of being joined
by a domain, as the spin^c structure does. The identification of the Maslov index of a periodic
domain with the Chern class pairing is geometric and is not formalized here.

Weak admissibility implies weak admissibility at every generator, and so does strong
admissibility at that generator (`TauCeti.HeegaardRegionSystem.StronglyAdmissible`, in
`TauCeti.LowDimTopology.Heegaard.StrongAdmissibility`). When every periodic domain has Maslov
index zero at `x`, as for a torsion spin^c structure, the two weak conditions agree. In general
they do not: the genus-one diagram of `S¹ × S²` with its basepoint in a bigon is weakly
admissible at both of its generators, although it is not weakly admissible
(`TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_circleTimesSphere_one`).

Weak admissibility at `y` is exactly what makes the set of nonnegative domains from any `x` to
`y` with prescribed basepoint multiplicities and prescribed Maslov index finite; this is the
finiteness behind the hat differential of a single spin^c summand. It is also the existence of
strictly positive region areas for which every periodic domain of Maslov index zero has signed
area zero, and for such areas all domains from `x` to `y` with the same basepoint multiplicities
and the same Maslov index have the same area: the energy bound for holomorphic disks once their
energy is identified with the area of their domain.

## Main definitions

* `TauCeti.HeegaardRegionSystem.WeaklyAdmissibleAt`: every nonzero periodic domain of Maslov
  index zero at a generator has both positive and negative coefficients.

## Main results

* `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_iff`: equivalently, the only nonnegative
  periodic domain of Maslov index zero is zero.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_iff_of_isDomainBetween`: the condition is
  the same at generators joined by a domain.
* `TauCeti.HeegaardRegionSystem.WeaklyAdmissible.weaklyAdmissibleAt` and
  `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_iff_weaklyAdmissible`: weak admissibility
  implies weak admissibility at every generator, with equality when the periodic domains have
  Maslov index zero.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_iff_exists_pos_forall_sum_mul_eq_zero`: the
  area form characterization.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.sum_mul_eq_of_maslovIndex_eq`: domains with the
  same basepoint multiplicities and Maslov index have the same area.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_iff_forall_finite`: weak admissibility at `y`
  is the finiteness of the nonnegative domains ending at `y` with prescribed basepoint
  multiplicities and Maslov index.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.2: Definition 4.10 and
  Remark 4.11 (admissibility for a fixed spin^c structure), Theorem 4.9 (the Maslov index of a
  periodic class) and Lemmas 4.13–4.14 (finiteness and the area bound).
-/

public section

open Finset

namespace TauCeti

namespace HeegaardRegionSystem

variable {n : ℕ} {Point Region Basepoint : Type*}
  {H : HeegaardRegionSystem n Point Region Basepoint}
  [Fintype Point] [Fintype Region] [DecidableEq Region]

variable (H) in
/-- Weak admissibility at the generator `x`, for the region Euler characteristics `χ`: every
nonzero periodic domain of Maslov index zero at `x` has both positive and negative coefficients.
This is weak admissibility for the spin^c structure of `x`. -/
def WeaklyAdmissibleAt (χ : Region → ℤ) (x : H.Generator) : Prop :=
  ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0 → P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0

variable {χ : Region → ℤ} {x y : H.Generator}

/-- Weak admissibility at `x` means every nonzero periodic domain of Maslov index zero at `x` has
both positive and negative coefficients. -/
theorem weaklyAdmissibleAt_def :
    H.WeaklyAdmissibleAt χ x ↔
      ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0 → P ≠ 0 →
        (∃ r, 0 < P r) ∧ ∃ r, P r < 0 :=
  Iff.rfl

/-- A diagram is weakly admissible at `x` exactly when its only nonnegative periodic domain of
Maslov index zero at `x` is zero. -/
theorem weaklyAdmissibleAt_iff :
    H.WeaklyAdmissibleAt χ x ↔
      ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0 → 0 ≤ P → P = 0 := by
  constructor
  · intro h P hP hμ hnonneg
    by_contra hne
    obtain ⟨r, hr⟩ := (h P hP hμ hne).2
    exact (hnonneg r).not_gt hr
  · intro h P hP hμ hne
    refine ⟨?_, ?_⟩
    · by_contra hpos
      push Not at hpos
      refine hne (neg_eq_zero.mp (h (-P) (neg_mem hP) (by rw [map_neg, hμ, neg_zero])
        fun r => ?_))
      simpa using hpos r
    · by_contra hneg
      push Not at hneg
      exact hne (h P hP hμ hneg)

/-- Weak admissibility at a generator is the same at generators joined by a domain: a periodic
domain has the same Maslov index at both. -/
theorem weaklyAdmissibleAt_iff_of_isDomainBetween {D : Region → ℤ}
    (hD : H.IsDomainBetween x y D) :
    H.WeaklyAdmissibleAt χ x ↔ H.WeaklyAdmissibleAt χ y := by
  have hμ : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = H.maslovIndex χ y y P :=
    fun P hP => hD.maslovIndex_self_eq χ (isDomainBetween_self_iff.mpr hP).1
  refine ⟨fun h P hP hP₀ => ?_, fun h P hP hP₀ => ?_⟩
  · exact h P hP ((hμ P hP).trans hP₀)
  · exact h P hP ((hμ P hP).symm.trans hP₀)

/-- A weakly admissible diagram is weakly admissible at every generator. -/
theorem WeaklyAdmissible.weaklyAdmissibleAt (hH : H.WeaklyAdmissible) (χ : Region → ℤ)
    (x : H.Generator) : H.WeaklyAdmissibleAt χ x :=
  weaklyAdmissibleAt_iff.mpr fun P hP _ hP₀ => weaklyAdmissible_iff.mp hH P hP hP₀

/-- If every periodic domain has Maslov index zero at `x`, as for the generators of a torsion
spin^c structure, then weak admissibility at `x` is weak admissibility. -/
theorem weaklyAdmissibleAt_iff_weaklyAdmissible
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) :
    H.WeaklyAdmissibleAt χ x ↔ H.WeaklyAdmissible :=
  ⟨fun h => weaklyAdmissible_iff.mpr fun P hPmem hP₀ =>
    weaklyAdmissibleAt_iff.mp h P hPmem (hP P hPmem) hP₀, fun h => h.weaklyAdmissibleAt χ x⟩

variable (H) in
/-- A diagram is weakly admissible at `x` exactly when its regions carry strictly positive areas
`A` for which every periodic domain of Maslov index zero at `x` has signed area
`∑ r, A r * P r` equal to zero. -/
theorem weaklyAdmissibleAt_iff_exists_pos_forall_sum_mul_eq_zero :
    H.WeaklyAdmissibleAt χ x ↔
      ∃ A : Region → ℝ, (∀ r, 0 < A r) ∧
        ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0 → ∑ r, A r * P r = 0 := by
  have := exists_pos_forall_sum_mul_intCast_eq_zero_iff
    (P := H.periodicDomains ⊓ (H.maslovIndex χ x x).ker)
  simp only [AddSubgroup.mem_inf, AddMonoidHom.mem_ker, and_imp] at this
  rw [weaklyAdmissibleAt_iff, this]

/-- If an area form `A` vanishes on the periodic domains of Maslov index zero at `y`, then all
domains from `x` to `y` with the same basepoint multiplicities and the same Maslov index have the
same area. -/
theorem IsDomainBetween.sum_mul_eq_of_maslovIndex_eq {A : Region → ℝ}
    (hA : ∀ P ∈ H.periodicDomains, H.maslovIndex χ y y P = 0 → ∑ r, A r * P r = 0)
    {D D' : Region → ℤ} (hD : H.IsDomainBetween x y D) (hD' : H.IsDomainBetween x y D')
    (hz : ∀ z, D' (H.basepoint z) = D (H.basepoint z))
    (hμ : H.maslovIndex χ x y D' = H.maslovIndex χ x y D) :
    ∑ r, A r * D' r = ∑ r, A r * D r := by
  have hP : D' - D ∈ H.periodicDomains := hD.sub_mem_periodicDomains_iff.mpr ⟨hD', hz⟩
  have hsum := hD.maslovIndex_add χ (isDomainBetween_self_iff.mpr hP).1
  rw [add_sub_cancel, hμ, left_eq_add] at hsum
  simpa [mul_sub, sum_sub_distrib, sub_eq_zero] using hA _ hP hsum

/-- In a diagram weakly admissible at `y`, only finitely many nonnegative domains connect `x` to
`y` with prescribed basepoint multiplicities `k` and Maslov index `m`. -/
theorem WeaklyAdmissibleAt.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index
    (hH : H.WeaklyAdmissibleAt χ y) (x : H.Generator) (k : Basepoint → ℤ) (m : ℚ) :
    {D : Region → ℤ | H.IsDomainBetween x y D ∧
      (∀ z, D (H.basepoint z) = k z) ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  refine IsAntichain.finite_of_partiallyWellOrderedOn (r := (· ≤ ·)) ?_ ?_
  · -- Two comparable elements differ by a nonnegative periodic domain of Maslov index zero.
    rintro D ⟨hD, hDz, -, hDm⟩ D' ⟨hD', hD'z, -, hD'm⟩ hne hle
    have hP : D' - D ∈ H.periodicDomains :=
      hD.sub_mem_periodicDomains_iff.mpr ⟨hD', by simp [hDz, hD'z]⟩
    have hsum := hD.maslovIndex_add χ (isDomainBetween_self_iff.mpr hP).1
    rw [add_sub_cancel, hDm, hD'm, left_eq_add] at hsum
    exact hne (sub_eq_zero.mp
      (weaklyAdmissibleAt_iff.mp hH _ hP hsum (sub_nonneg.mpr hle))).symm
  · -- The set is partially well-ordered, being inside the image of `Region → ℕ` (Dickson).
    refine ((Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set (Region → ℕ))).image_of_monotone
      (f := fun a r => (a r : ℤ)) fun a b hab r => Int.ofNat_le.mpr (hab r)).mono ?_
    rintro D ⟨-, -, hD, -⟩
    exact ⟨fun r => (D r).toNat, trivial, funext fun r => Int.toNat_of_nonneg (hD r)⟩

/-- A diagram is weakly admissible at `y` exactly when, for every generator `x`, basepoint
multiplicities `k` and Maslov index `m`, only finitely many nonnegative domains connect `x` to
`y` with these basepoint multiplicities and this Maslov index. Without weak admissibility at
`y`, the multiples of a nonzero nonnegative periodic domain of Maslov index zero are infinitely
many such domains from `y` to itself. -/
theorem weaklyAdmissibleAt_iff_forall_finite :
    H.WeaklyAdmissibleAt χ y ↔ ∀ (x : H.Generator) (k : Basepoint → ℤ) (m : ℚ),
      {D : Region → ℤ | H.IsDomainBetween x y D ∧
        (∀ z, D (H.basepoint z) = k z) ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  refine ⟨fun hH => hH.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index,
    fun hfin => weaklyAdmissibleAt_iff.mpr fun P hP hμ hP₀ => ?_⟩
  by_contra hne
  have hinj : Function.Injective fun j : ℕ => j • P := fun a b h =>
    Nat.cast_injective (R := ℤ) (smul_left_injective ℤ hne (by simpa only [natCast_zsmul] using h))
  refine Set.infinite_of_injective_forall_mem hinj (fun j => ?_) (hfin y 0 0)
  have hjP := H.periodicDomains.nsmul_mem hP j
  obtain ⟨hdom, hz⟩ := isDomainBetween_self_iff.mpr hjP
  exact ⟨hdom, hz, nsmul_nonneg hP₀ j, by rw [map_nsmul, hμ, smul_zero]⟩

end HeegaardRegionSystem

end TauCeti
