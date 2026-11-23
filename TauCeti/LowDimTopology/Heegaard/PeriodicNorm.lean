/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.LatticeBound
public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility

/-!
# Admissibility from norms on periodic domains

Ozsváth and Szabó make a pointed Heegaard diagram admissible by winding its attaching curves
along auxiliary curves. The winding creates regions on which every nonzero periodic domain has
large positive and negative multiplicities, measured by a norm on the group of periodic domains,
and the winding amount is chosen large compared with the Maslov index. This file isolates the
part of that argument which takes place on the region incidence data
`TauCeti.HeegaardRegionSystem`: a norm detected by the multiplicities of periodic domains forces
weak admissibility, and strong admissibility once it dominates the Maslov index.

The norms are the sup norms `‖ν P‖` of an additive map `ν : (Region → ℤ) →+ (κ → ℤ)`, with `κ`
finite, injective on the periodic domains; in the winding argument `ν P` records the
multiplicities of the boundary of `P` on the attaching curves.

* **The Maslov index is bounded by the norm.** There is a constant `C` with
  `|μ_x(P)| ≤ C * ‖ν P‖` for every periodic domain `P` and every generator `x`
  (`TauCeti.HeegaardRegionSystem.exists_abs_maslovIndex_le_mul_norm`). For a genuine diagram the
  Maslov index of a periodic domain at `x` is the pairing of `c₁(s_z(x))` with its homology
  class, so this bounds the Chern class pairing by the norm.
* **Weak admissibility.** If, for some `D > 0`, every periodic domain `P` has a region of
  multiplicity at least `D * ‖ν P‖`, then the diagram is weakly admissible
  (`TauCeti.HeegaardRegionSystem.weaklyAdmissible_of_forall_exists_mul_norm_le`): applied to
  `-P`, the same hypothesis gives a region of multiplicity at most `-D * ‖ν P‖`, and both
  bounds are strict for `P ≠ 0` since `‖ν P‖ ≥ 1`.
* **Strong admissibility.** If moreover the Maslov index at `x` is at most `C * ‖ν P‖` on
  periodic domains, with `C < 2 * D`, then the diagram is strongly admissible at `x`
  (`TauCeti.HeegaardRegionSystem.stronglyAdmissible_of_forall_exists_mul_norm_le`). Combining
  the two, some `C` depending only on the region system, the Euler characteristics `χ` and `ν`
  makes every `D > C` force strong admissibility at all generators at once
  (`TauCeti.HeegaardRegionSystem.exists_forall_stronglyAdmissible_of_forall_exists_mul_norm_le`).

The winding estimate `AddMonoidHom.exists_forall_exists_le_add_mul_abs_and_sub_mul_abs_le`
supplies the hypothesis on the regions created by winding, with `D` growing linearly in the
winding amount. The construction of the wound diagram, and the identification of its periodic
domains and Maslov indices with those of the original diagram, are not part of this file.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.2, Definition 4.10 (weak and
  strong admissibility), and §5, Lemmas 5.4 and 5.6 (admissibility by winding).
-/

public section

open Finset

namespace TauCeti

namespace HeegaardRegionSystem

variable {n : ℕ} {Point Region Basepoint κ : Type*}
  {H : HeegaardRegionSystem n Point Region Basepoint} [Fintype κ]
  {ν : (Region → ℤ) →+ (κ → ℤ)}

/-- A nonzero periodic domain has norm at least `1`, for a norm `‖ν P‖` injective on periodic
domains. -/
private theorem one_le_norm_of_mem_periodicDomains
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) {P : Region → ℤ}
    (hP : P ∈ H.periodicDomains) (hne : P ≠ 0) : 1 ≤ ‖ν P‖ :=
  one_le_pi_norm_of_ne_zero fun h ↦ hne (hν P hP h)

/-- **Weak admissibility from a detected norm.** If `ν` is injective on periodic domains and, for
some `D > 0`, every periodic domain `P` has a region of multiplicity at least `D * ‖ν P‖`, the
diagram is weakly admissible. -/
theorem weaklyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) {D : ℝ} (hD₀ : 0 < D)
    (hD : ∀ P ∈ H.periodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) : H.WeaklyAdmissible := by
  refine weaklyAdmissible_iff.mpr fun P hP hP₀ ↦ by_contra fun hne ↦ ?_
  have hpos : 0 < D * ‖ν P‖ :=
    mul_pos hD₀ (zero_lt_one.trans_le (one_le_norm_of_mem_periodicDomains hν hP hne))
  obtain ⟨s, hs⟩ := hD (-P) (H.periodicDomains.neg_mem hP)
  rw [map_neg, norm_neg, Pi.neg_apply, Int.cast_neg] at hs
  have : (0 : ℝ) ≤ P s := by exact_mod_cast hP₀ s
  linarith

variable [Fintype Point] [Fintype Region] [DecidableEq Region]

/-- **The Maslov index is bounded by the norm.** If `ν` is injective on periodic domains, there is
a constant `C ≥ 0` such that `|μ_x(P)| ≤ C * ‖ν P‖` for every periodic domain `P` and every
generator `x`. -/
theorem exists_abs_maslovIndex_le_mul_norm
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) (χ : Region → ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ (x : H.Generator), ∀ P ∈ H.periodicDomains,
      |(H.maslovIndex χ x x P : ℝ)| ≤ C * ‖ν P‖ := by
  have hinj : Function.Injective (ν.comp H.periodicDomains.subtype) :=
    (injective_iff_map_eq_zero _).mpr fun P hP ↦ Subtype.ext (hν P P.property hP)
  have hC (x : H.Generator) : ∃ C, 0 ≤ C ∧ ∀ P : H.periodicDomains,
      ‖((Rat.castHom ℝ).toAddMonoidHom.comp
        ((H.maslovIndex χ x x).comp H.periodicDomains.subtype)) P‖ ≤
        C * ‖(ν.comp H.periodicDomains.subtype) P‖ :=
    AddMonoidHom.exists_norm_le_mul_norm_of_injective _ hinj
  choose C hC₀ hC using hC
  refine ⟨∑ x, C x, sum_nonneg fun x _ ↦ hC₀ x, fun x P hP ↦ ?_⟩
  refine ((Real.norm_eq_abs _).symm.trans_le (hC x ⟨P, hP⟩)).trans ?_
  exact mul_le_mul_of_nonneg_right
    (single_le_sum (fun x _ ↦ hC₀ x) (mem_univ x)) (norm_nonneg _)

/-- **Strong admissibility from a detected norm.** If `ν` is injective on periodic domains, the
Maslov index at `x` of every periodic domain `P` is at most `C * ‖ν P‖`, and every periodic domain
`P` has a region of multiplicity at least `D * ‖ν P‖` with `C < 2 * D`, the diagram is strongly
admissible at `x`. -/
theorem stronglyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) {χ : Region → ℤ} {x : H.Generator}
    {C D : ℝ} (hC : ∀ P ∈ H.periodicDomains, (H.maslovIndex χ x x P : ℝ) ≤ C * ‖ν P‖)
    (hD : ∀ P ∈ H.periodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) (hCD : C < 2 * D) :
    H.StronglyAdmissible χ x := by
  rw [stronglyAdmissible_iff]
  intro P hP hne _
  have hlt : C * ‖ν P‖ < 2 * D * ‖ν P‖ :=
    mul_lt_mul_of_pos_right hCD
      (zero_lt_one.trans_le (one_le_norm_of_mem_periodicDomains hν hP hne))
  obtain ⟨r, hr⟩ := hD P hP
  refine ⟨r, ?_⟩
  have h : ((H.maslovIndex χ x x P / 2 : ℚ) : ℝ) < ((P r : ℚ) : ℝ) := by
    push_cast
    linarith [hC P hP]
  exact_mod_cast h

/-- **Strong admissibility at every generator from a detected norm.** If `ν` is injective on
periodic domains, there is a constant `C ≥ 0` such that, whenever every periodic domain `P` has a
region of multiplicity at least `D * ‖ν P‖` for some `D > C`, the diagram is strongly admissible
at every generator. -/
theorem exists_forall_stronglyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) (χ : Region → ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ D, C < D → (∀ P ∈ H.periodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) →
      ∀ x, H.StronglyAdmissible χ x := by
  obtain ⟨C, hC₀, hC⟩ := exists_abs_maslovIndex_le_mul_norm hν χ
  refine ⟨C / 2, by positivity, fun D hCD hD x ↦
    stronglyAdmissible_of_forall_exists_mul_norm_le hν (C := C) (fun P hP ↦ ?_) hD
      (by linarith)⟩
  exact (le_abs_self _).trans (hC x P hP)

end HeegaardRegionSystem

end TauCeti
