/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Admissibility
public import TauCeti.LowDimTopology.Heegaard.MaslovIndex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Strong admissibility and finiteness at a fixed Maslov index

Strong admissibility restricts periodic domains using the Maslov index of a chosen generator.
For a nonzero periodic domain of nonnegative index `2m`, some region must have multiplicity
greater than `m`. We use the rational half-index because the abstract region system accepts
an arbitrary Euler-characteristic function; on a geometric Heegaard diagram this is the usual
integer-valued condition. In particular, an index-zero periodic domain has both positive and
negative coefficients.

The latter observation makes nonnegative domains from `x` to `y` with fixed basepoint
multiplicities and fixed Maslov index finite. This is the finiteness input for an index-one
Heegaard Floer differential in a strongly admissible diagram.

## References

P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Ann. of Math. **159** (2004), §4.2.
-/

public section

namespace TauCeti.HeegaardRegionSystem

variable {n : ℕ} {Point Region Basepoint : Type*}
  {H : HeegaardRegionSystem n Point Region Basepoint}
  [Fintype Point] [Fintype Region] [DecidableEq Region]

variable (H) in
/-- Strong admissibility at a generator `x`: every nonzero periodic domain `P` of nonnegative
Maslov index has a coefficient strictly greater than half its index. The Euler characteristics
of the regions are supplied by `χ`. -/
def StronglyAdmissible (χ : Region → ℤ) (x : H.Generator) : Prop :=
  ∀ P ∈ H.periodicDomains, P ≠ 0 → 0 ≤ H.maslovIndex χ x x P →
    ∃ r, H.maslovIndex χ x x P / 2 < (P r : ℚ)

/-- Strong admissibility at `x` means every nonzero periodic domain of nonnegative Maslov
index has a coefficient strictly greater than half its index. -/
theorem stronglyAdmissible_iff {χ : Region → ℤ} {x : H.Generator} :
    H.StronglyAdmissible χ x ↔
      ∀ P ∈ H.periodicDomains, P ≠ 0 → 0 ≤ H.maslovIndex χ x x P →
        ∃ r, H.maslovIndex χ x x P / 2 < (P r : ℚ) := Iff.rfl

/-- Strong admissibility has the same value at generators joined by a domain: the Maslov
index of a periodic domain is independent of the generator within that class. -/
theorem stronglyAdmissible_iff_of_isDomainBetween {χ : Region → ℤ} {x y : H.Generator}
    {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    H.StronglyAdmissible χ x ↔ H.StronglyAdmissible χ y := by
  constructor
  · intro h P hP hne hidx
    have hμ := hD.maslovIndex_self_eq χ (H.isDomainBetween_self_iff.mpr hP).1
    rw [← hμ] at hidx ⊢
    exact h P hP hne hidx
  · intro h P hP hne hidx
    have hμ := hD.maslovIndex_self_eq χ (H.isDomainBetween_self_iff.mpr hP).1
    rw [hμ] at hidx ⊢
    exact h P hP hne hidx

/-- An index-zero periodic domain in a strongly admissible diagram has coefficients of both
signs, unless it is zero. -/
theorem StronglyAdmissible.signs_of_index_zero {χ : Region → ℤ} {x : H.Generator}
    (hH : H.StronglyAdmissible χ x) {P : Region → ℤ}
    (hP : P ∈ H.periodicDomains) (hindex : H.maslovIndex χ x x P = 0)
    (hne : P ≠ 0) : (∃ r, 0 < P r) ∧ ∃ r, P r < 0 := by
  obtain ⟨r, hr⟩ := hH P hP hne (by simp [hindex])
  have hnegindex : H.maslovIndex χ x x (-P) = 0 := by
    rw [map_neg, hindex]
    exact neg_zero
  obtain ⟨s, hs⟩ := hH (-P) (H.periodicDomains.neg_mem hP)
    (by simpa using hne) (hnegindex ▸ le_refl _)
  simp only [hindex, zero_div] at hr
  simp only [hnegindex, zero_div] at hs
  refine ⟨⟨r, by exact_mod_cast hr⟩, ⟨s, ?_⟩⟩
  have hsInt : (0 : ℤ) < -P s := by exact_mod_cast hs
  exact neg_pos.mp hsInt

/-- A nonnegative index-zero periodic domain in a strongly admissible diagram vanishes. -/
theorem StronglyAdmissible.eq_zero_of_nonneg_index_zero {χ : Region → ℤ} {x : H.Generator}
    (hH : H.StronglyAdmissible χ x) {P : Region → ℤ}
    (hP : P ∈ H.periodicDomains) (hindex : H.maslovIndex χ x x P = 0)
    (hPnonneg : 0 ≤ P) : P = 0 := by
  by_contra hne
  obtain ⟨r, hr⟩ := hH.signs_of_index_zero hP hindex hne |>.2
  exact (hPnonneg r).not_gt hr

/-- If every nonnegative periodic domain of Maslov index zero vanishes, then there are only
finitely many nonnegative domains from `x` to `y` with prescribed basepoint multiplicities and
Maslov index. -/
theorem finite_setOf_isDomainBetween_basepoint_eq_nonneg_index_of_eq_zero
    {χ : Region → ℤ} {y : H.Generator}
    (hzero : ∀ P ∈ H.periodicDomains, H.maslovIndex χ y y P = 0 → 0 ≤ P → P = 0)
    (x : H.Generator) (k : Basepoint → ℤ) (m : ℚ) :
    {D : Region → ℤ | H.IsDomainBetween x y D ∧
      (∀ z, D (H.basepoint z) = k z) ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  classical
  refine IsAntichain.finite_of_partiallyWellOrderedOn (r := (· ≤ ·)) ?_ ?_
  · rintro D ⟨hD, hDz, -, hDm⟩ D' ⟨hD', hD'z, -, hD'm⟩ hne hle
    have hP : D' - D ∈ H.periodicDomains :=
      hD.sub_mem_periodicDomains_iff.mpr ⟨hD', by simp [hDz, hD'z]⟩
    have hself : H.IsDomainBetween y y (D' - D) :=
      (H.isDomainBetween_self_iff.mpr hP).1
    have hsum := hD.maslovIndex_add χ hself
    have hindex : H.maslovIndex χ y y (D' - D) = 0 := by
      rw [add_comm D (D' - D), sub_add_cancel] at hsum
      rw [hDm, hD'm] at hsum
      linarith
    have hvanish := hzero (D' - D) hP hindex (sub_nonneg.mpr hle)
    exact hne (sub_eq_zero.mp hvanish).symm
  · refine ((Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set (Region → ℕ))).image_of_monotone
      (f := fun a r => (a r : ℤ)) fun a b hab r => Int.ofNat_le.mpr (hab r)).mono ?_
    rintro D ⟨-, -, hD, -⟩
    exact ⟨fun r => (D r).toNat, trivial, funext fun r => Int.toNat_of_nonneg (hD r)⟩

/-- In a strongly admissible diagram with finitely many regions, there are only finitely many
nonnegative domains from `x` to `y` with prescribed basepoint multiplicities and Maslov index.
The strong condition is needed only at the terminal generator `y`. -/
theorem StronglyAdmissible.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index
    {χ : Region → ℤ} {y : H.Generator} (hH : H.StronglyAdmissible χ y)
    (x : H.Generator) (k : Basepoint → ℤ) (m : ℚ) :
    {D : Region → ℤ | H.IsDomainBetween x y D ∧
      (∀ z, D (H.basepoint z) = k z) ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  exact finite_setOf_isDomainBetween_basepoint_eq_nonneg_index_of_eq_zero
    (fun P hP hindex hnonneg => hH.eq_zero_of_nonneg_index_zero hP hindex hnonneg)
    x k m

end TauCeti.HeegaardRegionSystem
