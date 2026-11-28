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

Both criteria hold for any subgroup `S` of `Region → ℤ` on which `ν` is injective
(`TauCeti.forall_nonneg_eq_zero_of_forall_exists_mul_norm_le` and
`TauCeti.forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le`), as does strong admissibility
for finitely many additive functionals on `S` at once
(`TauCeti.exists_forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le`), which bounds them
all by the norm with `AddMonoidHom.exists_forall_abs_le_mul_norm_of_injective`, so the versions
for the sums of doubly periodic domains of Heegaard triples in
`TauCeti.LowDimTopology.Heegaard.Triple.PeriodicNorm` use them too.

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

namespace TauCeti

section Subgroup

variable {Region κ : Type*} [Fintype κ] {ν : (Region → ℤ) →+ (κ → ℤ)}
  {S : AddSubgroup (Region → ℤ)}

/-- A nonzero element of a subgroup `S` of domains has norm at least `1`, for a norm `‖ν P‖`
injective on `S`. -/
private theorem one_le_norm_of_mem (hν : ∀ P ∈ S, ν P = 0 → P = 0) {P : Region → ℤ}
    (hP : P ∈ S) (hne : P ≠ 0) : 1 ≤ ‖ν P‖ :=
  one_le_pi_norm_of_ne_zero fun h ↦ hne (hν P hP h)

/-- **Nonnegative domains vanish under a detected norm.** If `ν` is injective on a subgroup `S` of
domains and, for some `D > 0`, every `P ∈ S` has a region of multiplicity at least `D * ‖ν P‖`,
then the only nonnegative element of `S` is `0`. This is the weak admissibility of
`TauCeti.HeegaardRegionSystem.weaklyAdmissible_of_forall_exists_mul_norm_le` and of its version for
Heegaard triples, for `S` the periodic domains. -/
theorem forall_nonneg_eq_zero_of_forall_exists_mul_norm_le (hν : ∀ P ∈ S, ν P = 0 → P = 0)
    {D : ℝ} (hD₀ : 0 < D) (hD : ∀ P ∈ S, ∃ r, D * ‖ν P‖ ≤ P r) : ∀ P ∈ S, 0 ≤ P → P = 0 := by
  refine fun P hP hP₀ ↦ by_contra fun hne ↦ ?_
  have hpos : 0 < D * ‖ν P‖ :=
    mul_pos hD₀ (zero_lt_one.trans_le (one_le_norm_of_mem hν hP hne))
  -- Applied to `-P`, the hypothesis gives a region on which `P` is negative.
  obtain ⟨s, hs⟩ := hD (-P) (neg_mem hP)
  rw [map_neg, norm_neg, Pi.neg_apply, Int.cast_neg] at hs
  have : (0 : ℝ) ≤ P s := by exact_mod_cast hP₀ s
  linarith

/-- **Large coefficients under a detected norm.** If `ν` is injective on a subgroup `S` of domains,
`m P ≤ C * ‖ν P‖` for every `P ∈ S`, and every `P ∈ S` has a region of multiplicity at least
`D * ‖ν P‖` with `C < 2 * D`, then every nonzero `P ∈ S` has a coefficient larger than `m P / 2`.
This is the strong admissibility of
`TauCeti.HeegaardRegionSystem.stronglyAdmissible_of_forall_exists_mul_norm_le` and of its version
for Heegaard triples, for `m` the Maslov index. -/
theorem forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ S, ν P = 0 → P = 0) {m : (Region → ℤ) → ℚ} {C D : ℝ}
    (hC : ∀ P ∈ S, (m P : ℝ) ≤ C * ‖ν P‖) (hD : ∀ P ∈ S, ∃ r, D * ‖ν P‖ ≤ P r)
    (hCD : C < 2 * D) : ∀ P ∈ S, P ≠ 0 → ∃ r, m P / 2 < P r := by
  intro P hP hne
  have hlt : C * ‖ν P‖ < 2 * D * ‖ν P‖ :=
    mul_lt_mul_of_pos_right hCD (zero_lt_one.trans_le (one_le_norm_of_mem hν hP hne))
  obtain ⟨r, hr⟩ := hD P hP
  refine ⟨r, ?_⟩
  have h : ((m P / 2 : ℚ) : ℝ) < ((P r : ℚ) : ℝ) := by
    push_cast
    linarith [hC P hP]
  exact_mod_cast h

/-- **Large coefficients for finitely many functionals under a detected norm.** If `ν` is injective
on a subgroup `S` of domains, there is a constant `C ≥ 0` such that, whenever every `P ∈ S` has a
region of multiplicity at least `D * ‖ν P‖` for some `D > C`, every nonzero `P ∈ S` has a
coefficient larger than `m i P / 2`, for each of finitely many additive functionals `m i` on `S`.
This is the strong admissibility at every generator of
`TauCeti.HeegaardRegionSystem.exists_forall_stronglyAdmissible_of_forall_exists_mul_norm_le` and of
its version for Heegaard triples, for `m` the Maslov indices. -/
theorem exists_forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le {ι : Type*} [Finite ι]
    (hν : ∀ P ∈ S, ν P = 0 → P = 0) (m : ι → S →+ ℚ) :
    ∃ C, 0 ≤ C ∧ ∀ D, C < D → (∀ P ∈ S, ∃ r, D * ‖ν P‖ ≤ P r) →
      ∀ i, ∀ P : S, (P : Region → ℤ) ≠ 0 → ∃ r, m i P / 2 < (P : Region → ℤ) r := by
  classical
  obtain ⟨C, hC₀, hC⟩ := AddMonoidHom.exists_forall_abs_le_mul_norm_of_injective
    (fun i ↦ (Rat.castHom ℝ).toAddMonoidHom.comp (m i)) (n := ν.comp S.subtype)
    ((injective_iff_map_eq_zero _).mpr fun P hP ↦ Subtype.ext (hν P P.property hP))
  refine ⟨C / 2, by positivity, fun D hCD hD i P hne ↦ ?_⟩
  -- Extend `m i` by `0` off `S` to apply the criterion for a single functional.
  have h := forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le hν
    (m := fun Q ↦ if hQ : Q ∈ S then m i ⟨Q, hQ⟩ else 0) (C := C)
    (fun Q hQ ↦ by simpa [hQ] using (le_abs_self _).trans (hC i ⟨Q, hQ⟩)) hD
    (by linarith) P P.property hne
  simpa [P.property] using h

end Subgroup

namespace HeegaardRegionSystem

variable {n : ℕ} {Point Region Basepoint κ : Type*}
  {H : HeegaardRegionSystem n Point Region Basepoint} [Fintype κ]
  {ν : (Region → ℤ) →+ (κ → ℤ)}

/-- **Weak admissibility from a detected norm.** If `ν` is injective on periodic domains and, for
some `D > 0`, every periodic domain `P` has a region of multiplicity at least `D * ‖ν P‖`, the
diagram is weakly admissible. -/
theorem weaklyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) {D : ℝ} (hD₀ : 0 < D)
    (hD : ∀ P ∈ H.periodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) : H.WeaklyAdmissible :=
  weaklyAdmissible_iff.mpr (forall_nonneg_eq_zero_of_forall_exists_mul_norm_le hν hD₀ hD)

variable [Fintype Point] [Fintype Region] [DecidableEq Region]

/-- **The Maslov index is bounded by the norm.** If `ν` is injective on periodic domains, there is
a constant `C ≥ 0` such that `|μ_x(P)| ≤ C * ‖ν P‖` for every periodic domain `P` and every
generator `x`. -/
theorem exists_abs_maslovIndex_le_mul_norm
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) (χ : Region → ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ (x : H.Generator), ∀ P ∈ H.periodicDomains,
      |(H.maslovIndex χ x x P : ℝ)| ≤ C * ‖ν P‖ := by
  obtain ⟨C, hC₀, hC⟩ := AddMonoidHom.exists_forall_abs_le_mul_norm_of_injective
    (fun x : H.Generator ↦ (Rat.castHom ℝ).toAddMonoidHom.comp
      ((H.maslovIndex χ x x).comp H.periodicDomains.subtype))
    (n := ν.comp H.periodicDomains.subtype)
    ((injective_iff_map_eq_zero _).mpr fun P hP ↦ Subtype.ext (hν P P.property hP))
  exact ⟨C, hC₀, fun x P hP ↦ hC x ⟨P, hP⟩⟩

/-- **Strong admissibility from a detected norm.** If `ν` is injective on periodic domains, the
Maslov index at `x` of every periodic domain `P` is at most `C * ‖ν P‖`, and every periodic domain
`P` has a region of multiplicity at least `D * ‖ν P‖` with `C < 2 * D`, the diagram is strongly
admissible at `x`. -/
theorem stronglyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) {χ : Region → ℤ} {x : H.Generator}
    {C D : ℝ} (hC : ∀ P ∈ H.periodicDomains, (H.maslovIndex χ x x P : ℝ) ≤ C * ‖ν P‖)
    (hD : ∀ P ∈ H.periodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) (hCD : C < 2 * D) :
    H.StronglyAdmissible χ x :=
  stronglyAdmissible_iff.mpr fun P hP hne _ ↦
    forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le hν hC hD hCD P hP hne

/-- **Strong admissibility at every generator from a detected norm.** If `ν` is injective on
periodic domains, there is a constant `C ≥ 0` such that, whenever every periodic domain `P` has a
region of multiplicity at least `D * ‖ν P‖` for some `D > C`, the diagram is strongly admissible
at every generator. -/
theorem exists_forall_stronglyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ H.periodicDomains, ν P = 0 → P = 0) (χ : Region → ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ D, C < D → (∀ P ∈ H.periodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) →
      ∀ x, H.StronglyAdmissible χ x := by
  obtain ⟨C, hC₀, hC⟩ := exists_forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le hν
    fun x : H.Generator ↦ (H.maslovIndex χ x x).comp H.periodicDomains.subtype
  exact ⟨C, hC₀, fun D hCD hD x ↦
    stronglyAdmissible_iff.mpr fun P hP hne _ ↦ hC D hCD hD x ⟨P, hP⟩ hne⟩

end HeegaardRegionSystem

end TauCeti
