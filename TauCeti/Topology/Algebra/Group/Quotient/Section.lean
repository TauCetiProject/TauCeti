/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous right-coset factorizations

A continuous section of `G → G ⧸ H` gives continuous maps `w : G → H` and `r : G → G`
with `g = w g * r g`, where `w` is `H`-equivariant and `r` is constant on right cosets.
For an open subgroup the quotient is discrete, so `Quotient.out` supplies such a section.

## Main results

* `Subgroup.exists_continuous_rightCosetFactorization_of_section`: factorization from any
  continuous section of the quotient map.
* `Subgroup.exists_continuous_rightCosetFactorization_of_isOpen`: factorization for an open
  subgroup of any topological group.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The right-coset factorization attached to a continuous section `s` of `G → G ⧸ H`:
`w g = g * s ⟦g⁻¹⟧ ∈ H` and `r g = (s ⟦g⁻¹⟧)⁻¹`, with `w 1 = s ⟦1⟧`. Inverting exchanges left and
right cosets, so `r g` lies in `H * g` and depends only on that right coset. -/
theorem _root_.Subgroup.exists_continuous_rightCosetFactorization_of_section (H : Subgroup G)
    (s : G ⧸ H → G) (hs_cont : Continuous s)
    (hs_sec : ∀ x : G ⧸ H, (QuotientGroup.mk (s x) : G ⧸ H) = x) :
    ∃ (w : G → H) (r : G → G), Continuous w ∧ Continuous r ∧
      (∀ g : G, (w g : G) * r g = g) ∧
      (∀ (h : H) (g : G), w ((h : G) * g) = h * w g) ∧
      (∀ (h : H) (g : G), r ((h : G) * g) = r g) ∧ (w 1 : G) = s (QuotientGroup.mk 1) := by
  have hcoset : ∀ (h : H) (g : G),
      (QuotientGroup.mk (((h : G) * g)⁻¹) : G ⧸ H) = QuotientGroup.mk g⁻¹ := by
    intro h g
    rw [QuotientGroup.eq]
    simp [mul_assoc, h.2]
  have hmem : ∀ g : G, g * s (QuotientGroup.mk g⁻¹) ∈ H := by
    intro g
    have h := hs_sec (QuotientGroup.mk g⁻¹)
    rw [QuotientGroup.eq] at h
    simpa using H.inv_mem h
  refine ⟨fun g => ⟨g * s (QuotientGroup.mk g⁻¹), hmem g⟩,
    fun g => (s (QuotientGroup.mk g⁻¹))⁻¹, ?_, ?_, fun g => by simp, fun h g => ?_, fun h g => ?_,
    by simp⟩
  · exact continuous_induced_rng.2 (continuous_id.mul
      (hs_cont.comp (QuotientGroup.continuous_mk.comp continuous_inv)))
  · exact (hs_cont.comp (QuotientGroup.continuous_mk.comp continuous_inv)).inv
  · exact Subtype.ext (by simp only [hcoset, mul_assoc, Subgroup.coe_mul])
  · simp only [hcoset]

/-- **The right-coset factorization for an open subgroup.** For an open subgroup `H` of a
topological group `G`, every `g : G` factors as `g = w g * r g` with `w g ∈ H`, where `r g` depends
only on the right coset `H * g`, and both `w` and `r` are continuous. No compactness is needed: the
coset space `G ⧸ H` is discrete, so the choice of representatives `Quotient.out` is already a
continuous section. The factorization need not be normalized at `1`. -/
theorem _root_.Subgroup.exists_continuous_rightCosetFactorization_of_isOpen (H : Subgroup G)
    (hH : IsOpen (H : Set G)) :
    ∃ (w : G → H) (r : G → G), Continuous w ∧ Continuous r ∧
      (∀ g : G, (w g : G) * r g = g) ∧
      (∀ (h : H) (g : G), w ((h : G) * g) = h * w g) ∧
      (∀ (h : H) (g : G), r ((h : G) * g) = r g) := by
  have := QuotientGroup.discreteTopology hH
  obtain ⟨w, r, hw, hr, hwr, hwh, hrh, -⟩ :=
    H.exists_continuous_rightCosetFactorization_of_section Quotient.out
      continuous_of_discreteTopology QuotientGroup.out_eq'
  exact ⟨w, r, hw, hr, hwr, hwh, hrh⟩

end TauCeti
