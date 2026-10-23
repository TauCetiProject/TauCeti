/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.WellQuasiOrder
public import TauCeti.Analysis.Convex.Stiemke
public import TauCeti.LowDimTopology.Heegaard.Domain

/-!
# Weak admissibility: area forms and finiteness of positive domains

Weak admissibility of a pointed Heegaard diagram (`TauCeti.HeegaardRegionSystem.WeaklyAdmissible`:
every nonzero periodic domain has both positive and negative coefficients) is the hypothesis
under which the differential of `HF̂` is a finite sum. This file proves two domain-level
consequences of it, in terms of the region incidence data of `TauCeti.HeegaardRegionSystem`.

* **Area forms.** A diagram is weakly admissible exactly when the regions can be given strictly
  positive areas for which every periodic domain has signed area zero. For such an area form,
  all domains connecting `x` to `y` with prescribed basepoint multiplicities have the same area.
* **Finiteness.** In a weakly admissible diagram with finitely many regions, only finitely many
  nonnegative domains connect `x` to `y` with prescribed basepoint multiplicities. Conversely,
  the diagram is weakly admissible exactly when it has only finitely many nonnegative periodic
  domains.

These are statements about domains only. Once the energy of a holomorphic disk is identified with
the area of its domain, and its domain is known to be nonnegative (both analytic inputs not
formalized here), they give the energy bound replacing monotonicity and the finiteness of the
homotopy classes that can contribute to the `HF̂` differential.

## Main results

* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_iff_exists_pos_forall_sum_mul_eq_zero`: weak
  admissibility is the existence of a strictly positive area form vanishing on periodic domains.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.sum_mul_eq`: for such an area form, the area of
  a domain connecting `x` to `y` depends only on its basepoint multiplicities.
* `TauCeti.HeegaardRegionSystem.WeaklyAdmissible.finite_setOf_isDomainBetween_basepoint_eq_nonneg`:
  finitely many nonnegative domains connect `x` to `y` with prescribed basepoint multiplicities.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_iff_finite_setOf_mem_periodicDomains_nonneg`:
  weak admissibility is the finiteness of the set of nonnegative periodic domains.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.2 (admissibility, its
  reformulation by area forms, and the resulting finiteness of positive domains).
-/

public section

open Finset

namespace TauCeti

namespace HeegaardRegionSystem

variable {n : ℕ} {Point : Type*} {Region : Type*} {Basepoint : Type*}
  {H : HeegaardRegionSystem n Point Region Basepoint}

variable (H) in
/-- A diagram is weakly admissible exactly when its regions carry strictly positive areas `A`
for which every periodic domain has signed area `∑ r, A r * P r` equal to zero. -/
theorem weaklyAdmissible_iff_exists_pos_forall_sum_mul_eq_zero [Fintype Region] :
    H.WeaklyAdmissible ↔
      ∃ A : Region → ℝ, (∀ r, 0 < A r) ∧ ∀ P ∈ H.periodicDomains, ∑ r, A r * P r = 0 := by
  rw [weaklyAdmissible_iff, exists_pos_forall_sum_mul_intCast_eq_zero_iff]

/-- If an area form `A` vanishes on the periodic domains, then all domains connecting `x` to `y`
with the same basepoint multiplicities have the same area. -/
theorem IsDomainBetween.sum_mul_eq [Fintype Region] {A : Region → ℝ}
    (hA : ∀ P ∈ H.periodicDomains, ∑ r, A r * P r = 0) {x y : H.Generator}
    {D D' : Region → ℤ} (hD : H.IsDomainBetween x y D) (hD' : H.IsDomainBetween x y D')
    (hz : ∀ z, D' (H.basepoint z) = D (H.basepoint z)) :
    ∑ r, A r * D' r = ∑ r, A r * D r := by
  have := hA (D' - D) (hD.sub_mem_periodicDomains_iff.mpr ⟨hD', hz⟩)
  simpa [mul_sub, sum_sub_distrib, sub_eq_zero] using this

/-- In a weakly admissible diagram with finitely many regions, only finitely many nonnegative
domains connect `x` to `y` with prescribed basepoint multiplicities `k`. -/
theorem WeaklyAdmissible.finite_setOf_isDomainBetween_basepoint_eq_nonneg [Finite Region]
    (hH : H.WeaklyAdmissible) (x y : H.Generator) (k : Basepoint → ℤ) :
    {D : Region → ℤ |
      H.IsDomainBetween x y D ∧ (∀ z, D (H.basepoint z) = k z) ∧ 0 ≤ D}.Finite := by
  refine IsAntichain.finite_of_partiallyWellOrderedOn (r := (· ≤ ·)) ?_ ?_
  · -- Two comparable elements differ by a nonnegative periodic domain, which must vanish.
    rintro D ⟨hD, hDz, -⟩ D' ⟨hD', hD'z, -⟩ hne hle
    have hP : D' - D ∈ H.periodicDomains :=
      hD.sub_mem_periodicDomains_iff.mpr ⟨hD', by simp [hDz, hD'z]⟩
    exact hne (sub_eq_zero.mp (weaklyAdmissible_iff.mp hH _ hP (sub_nonneg.mpr hle))).symm
  · -- The set is partially well-ordered, being inside the image of `Region → ℕ` (Dickson).
    refine ((Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set (Region → ℕ))).image_of_monotone
      (f := fun m r => (m r : ℤ)) fun a b h r => Int.ofNat_le.mpr (h r)).mono ?_
    rintro D ⟨-, -, hD⟩
    exact ⟨fun r => (D r).toNat, trivial, funext fun r => Int.toNat_of_nonneg (hD r)⟩

variable (H) in
/-- A diagram is weakly admissible exactly when it has only finitely many nonnegative periodic
domains. -/
theorem weaklyAdmissible_iff_finite_setOf_mem_periodicDomains_nonneg :
    H.WeaklyAdmissible ↔ {P | P ∈ H.periodicDomains ∧ 0 ≤ P}.Finite := by
  refine ⟨fun hH => (Set.finite_singleton 0).subset fun P hP =>
    weaklyAdmissible_iff.mp hH P hP.1 hP.2, fun hfin => weaklyAdmissible_iff.mpr ?_⟩
  -- A nonzero nonnegative periodic domain `P` would give the infinitely many `m • P`.
  intro P hP hP₀
  by_contra hne
  have hinj : Function.Injective fun m : ℕ => m • P := fun a b h =>
    Nat.cast_injective (R := ℤ) (smul_left_injective ℤ hne (by simpa only [natCast_zsmul] using h))
  exact Set.infinite_of_injective_forall_mem (s := {P | P ∈ H.periodicDomains ∧ 0 ≤ P}) hinj
    (fun m => ⟨H.periodicDomains.nsmul_mem hP m, nsmul_nonneg hP₀ m⟩) hfin

end HeegaardRegionSystem

end TauCeti
