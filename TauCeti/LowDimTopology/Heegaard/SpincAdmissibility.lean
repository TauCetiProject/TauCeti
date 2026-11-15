/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Admissibility
public import TauCeti.LowDimTopology.Heegaard.MaslovIndex

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
On a genuine Heegaard diagram with its region Euler characteristics `χ`, this corresponds by
Ozsváth–Szabó Theorem 4.9 to weak admissibility for the spin^c structure `s_z(x)`; that
identification is not formalized. -/
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
  have := AddSubgroup.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero
    (H.periodicDomains ⊓ (H.maslovIndex χ x x).ker)
  simp only [AddSubgroup.mem_inf, AddMonoidHom.mem_ker, and_imp] at this
  exact this

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
  have := (H.periodicDomains ⊓ (H.maslovIndex χ x x).ker).exists_pos_sum_mul_intCast_eq_zero_iff
    (K := ℝ)
  simp only [AddSubgroup.mem_inf, AddMonoidHom.mem_ker, and_imp] at this
  rw [weaklyAdmissibleAt_iff, this]

/-- Two domains from `x` to `y` with the same basepoint multiplicities and the same Maslov index
differ by a periodic domain of Maslov index zero at `y`. -/
theorem IsDomainBetween.sub_mem_periodicDomains_inf_ker_maslovIndex {D D' : Region → ℤ}
    (hD : H.IsDomainBetween x y D) (hD' : H.IsDomainBetween x y D')
    (hz : ∀ z, D' (H.basepoint z) = D (H.basepoint z))
    (hμ : H.maslovIndex χ x y D' = H.maslovIndex χ x y D) :
    D' - D ∈ H.periodicDomains ⊓ (H.maslovIndex χ y y).ker := by
  have hP : D' - D ∈ H.periodicDomains := hD.sub_mem_periodicDomains_iff.mpr ⟨hD', hz⟩
  have hsum := hD.maslovIndex_add χ (isDomainBetween_self_iff.mpr hP).1
  rw [add_sub_cancel, hμ, left_eq_add] at hsum
  exact ⟨hP, hsum⟩

/-- If an area form `A` vanishes on the periodic domains of Maslov index zero at `y`, then all
domains from `x` to `y` with the same basepoint multiplicities and the same Maslov index have the
same area. -/
theorem IsDomainBetween.sum_mul_eq_of_maslovIndex_eq {A : Region → ℝ}
    (hA : ∀ P ∈ H.periodicDomains, H.maslovIndex χ y y P = 0 → ∑ r, A r * P r = 0)
    {D D' : Region → ℤ} (hD : H.IsDomainBetween x y D) (hD' : H.IsDomainBetween x y D')
    (hz : ∀ z, D' (H.basepoint z) = D (H.basepoint z))
    (hμ : H.maslovIndex χ x y D' = H.maslovIndex χ x y D) :
    ∑ r, A r * D' r = ∑ r, A r * D r :=
  sum_mul_intCast_eq_of_sub_mem (P := H.periodicDomains ⊓ (H.maslovIndex χ y y).ker)
    (fun P hP => hA P hP.1 hP.2) (hD.sub_mem_periodicDomains_inf_ker_maslovIndex hD' hz hμ)

/-- In a diagram weakly admissible at `y`, only finitely many nonnegative domains connect `x` to
`y` with prescribed basepoint multiplicities `k` and Maslov index `m`. -/
theorem WeaklyAdmissibleAt.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index
    (hH : H.WeaklyAdmissibleAt χ y) (x : H.Generator) (k : Basepoint → ℤ) (m : ℚ) :
    {D : Region → ℤ | H.IsDomainBetween x y D ∧
      (∀ z, D (H.basepoint z) = k z) ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite :=
  -- Any two of these domains differ by a periodic domain of Maslov index zero at `y`.
  AddSubgroup.finite_of_forall_sub_mem (P := H.periodicDomains ⊓ (H.maslovIndex χ y y).ker)
    (fun P hP => weaklyAdmissibleAt_iff.mp hH P hP.1 hP.2) (fun _ hD => hD.2.2.1)
    fun _ ⟨hD, hDz, _, hDm⟩ _ ⟨hD', hD'z, _, hD'm⟩ =>
      hD.sub_mem_periodicDomains_inf_ker_maslovIndex hD' (by simp [hDz, hD'z])
        (hD'm.trans hDm.symm)

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
    fun hfin => weaklyAdmissibleAt_iff.mpr fun P hP hμ hP₀ =>
      (H.periodicDomains ⊓ (H.maslovIndex χ y y).ker).finite_setOf_mem_nonneg_iff.mp
        ((hfin y 0 0).subset ?_) P ⟨hP, hμ⟩ hP₀⟩
  -- The nonnegative periodic domains of Maslov index zero are domains from `y` to itself.
  rintro Q ⟨⟨hQ, hQμ⟩, hQ₀⟩
  obtain ⟨hdom, hz⟩ := isDomainBetween_self_iff.mpr hQ
  exact ⟨hdom, hz, hQ₀, hQμ⟩

end HeegaardRegionSystem

end TauCeti
