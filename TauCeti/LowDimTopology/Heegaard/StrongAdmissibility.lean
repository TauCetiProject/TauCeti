/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.SpincAdmissibility

/-!
# Strong admissibility

Strong admissibility restricts periodic domains using the Maslov index of a chosen generator.
For a nonzero periodic domain of nonnegative index `2m`, some region must have multiplicity
greater than `m`. We use the rational half-index because the abstract region system accepts
an arbitrary Euler-characteristic function; on a geometric Heegaard diagram this is the usual
integer-valued condition. In particular, an index-zero periodic domain has both positive and
negative coefficients, so strong admissibility at `x` implies weak admissibility at `x`
(`TauCeti.HeegaardRegionSystem.WeaklyAdmissibleAt`).

Through weak admissibility at the terminal generator `y`, this makes nonnegative domains from
`x` to `y` with fixed basepoint multiplicities and fixed Maslov index finite
(`HeegaardRegionSystem.WeaklyAdmissibleAt.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index`).
This is the finiteness input for an index-one Heegaard Floer differential in a strongly
admissible diagram.

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

/-- A strongly admissible diagram at `x` is weakly admissible at `x`: an index-zero periodic
domain `P` must have a coefficient greater than zero, and so must `-P`. -/
theorem StronglyAdmissible.weaklyAdmissibleAt {χ : Region → ℤ} {x : H.Generator}
    (hH : H.StronglyAdmissible χ x) : H.WeaklyAdmissibleAt χ x := by
  refine weaklyAdmissibleAt_def.mpr fun P hP hindex hne => ?_
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

end TauCeti.HeegaardRegionSystem
