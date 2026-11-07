/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous right-coset factorizations

A continuous section of `G → G ⧸ H` can be normalized to send the identity coset to `1`. It
gives continuous maps `w : G → H` and `r : G → G` with `g = w g * r g`, where `w` is
`H`-equivariant, `r` is constant on right cosets, and `w 1 = 1`. For an open subgroup the quotient
is discrete, so `Quotient.out` supplies such a section.

## Main results

* `Subgroup.exists_continuous_section_one_eq_one_of_section`: a continuous section of the quotient
  map can be normalized at the identity coset.
* `Subgroup.exists_continuous_rightCosetFactorization_of_section`: factorization from any
  continuous section of the quotient map.
* `Subgroup.exists_continuous_rightCosetFactorization_of_isOpen`: factorization for an open
  subgroup of any topological group.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Normalizing a continuous section.** If `s` is a continuous section of `G → G ⧸ H`, then so is
`t x = s x * (s ⟦1⟧)⁻¹`, and `t ⟦1⟧ = 1`. -/
theorem _root_.Subgroup.exists_continuous_section_one_eq_one_of_section [ContinuousMul G]
    (H : Subgroup G) (s : G ⧸ H → G) (hs_cont : Continuous s)
    (hs_sec : ∀ x : G ⧸ H, (QuotientGroup.mk (s x) : G ⧸ H) = x) :
    ∃ t : G ⧸ H → G, Continuous t ∧ (∀ x : G ⧸ H, (QuotientGroup.mk (t x) : G ⧸ H) = x) ∧
      t (QuotientGroup.mk 1) = 1 := by
  have hs₁ : s (QuotientGroup.mk 1) ∈ H := by
    simpa using QuotientGroup.eq.mp (hs_sec (QuotientGroup.mk 1))
  exact ⟨fun x => s x * (s (QuotientGroup.mk 1))⁻¹, hs_cont.mul continuous_const,
    fun x => by rw [QuotientGroup.mk_mul_of_mem _ (H.inv_mem hs₁), hs_sec], mul_inv_cancel _⟩

variable [IsTopologicalGroup G]

/-- **The right-coset factorization from a continuous section.** If `s` is a continuous section of
`G → G ⧸ H`, then every `g : G` factors as `g = w g * r g` with `w g ∈ H`, where `w` is
`H`-equivariant, `r g` depends only on the right coset `H * g`, both `w` and `r` are continuous, and
the factorization is normalized: `w 1 = 1`. -/
theorem _root_.Subgroup.exists_continuous_rightCosetFactorization_of_section (H : Subgroup G)
    (s : G ⧸ H → G) (hs_cont : Continuous s)
    (hs_sec : ∀ x : G ⧸ H, (QuotientGroup.mk (s x) : G ⧸ H) = x) :
    ∃ (w : G → H) (r : G → G), Continuous w ∧ Continuous r ∧
      (∀ g : G, (w g : G) * r g = g) ∧
      (∀ (h : H) (g : G), w ((h : G) * g) = h * w g) ∧
      (∀ (h : H) (g : G), r ((h : G) * g) = r g) ∧ w 1 = 1 := by
  -- Normalize `s` to a section `t` with `t ⟦1⟧ = 1`, then take `w g = g * t ⟦g⁻¹⟧` and
  -- `r g = (t ⟦g⁻¹⟧)⁻¹`: inverting exchanges left and right cosets, so `r g` lies in `H * g` and
  -- depends only on that right coset.
  obtain ⟨t, ht_cont, ht_sec, ht_one⟩ :=
    H.exists_continuous_section_one_eq_one_of_section s hs_cont hs_sec
  have hmem (g : G) : g * t (QuotientGroup.mk g⁻¹) ∈ H := by
    simpa using QuotientGroup.eq.mp (ht_sec (QuotientGroup.mk g⁻¹)).symm
  have hcoset (h : H) (g : G) :
      (QuotientGroup.mk ((h : G) * g)⁻¹ : G ⧸ H) = QuotientGroup.mk g⁻¹ := by
    rw [mul_inv_rev, QuotientGroup.mk_mul_of_mem _ (H.inv_mem h.2)]
  have hcont : Continuous fun g : G => t (QuotientGroup.mk g⁻¹) :=
    ht_cont.comp (QuotientGroup.continuous_mk.comp continuous_inv)
  refine ⟨fun g => ⟨g * t (QuotientGroup.mk g⁻¹), hmem g⟩, fun g => (t (QuotientGroup.mk g⁻¹))⁻¹,
    continuous_induced_rng.2 (continuous_id.mul hcont), hcont.inv, fun g => by simp,
    fun h g => Subtype.ext ?_, fun h g => by simp only [hcoset], Subtype.ext (by simp [ht_one])⟩
  simp only [hcoset, mul_assoc, Subgroup.coe_mul]

/-- **The right-coset factorization for an open subgroup.** For an open subgroup `H` of a
topological group `G`, every `g : G` factors as `g = w g * r g` with `w g ∈ H`, where `w` is
`H`-equivariant, `r g` depends only on the right coset `H * g`, both `w` and `r` are continuous, and
`w 1 = 1`. No compactness is needed: the coset space `G ⧸ H` is discrete, so the choice of
representatives `Quotient.out` is already a continuous section. -/
theorem _root_.Subgroup.exists_continuous_rightCosetFactorization_of_isOpen (H : Subgroup G)
    (hH : IsOpen (H : Set G)) :
    ∃ (w : G → H) (r : G → G), Continuous w ∧ Continuous r ∧
      (∀ g : G, (w g : G) * r g = g) ∧
      (∀ (h : H) (g : G), w ((h : G) * g) = h * w g) ∧
      (∀ (h : H) (g : G), r ((h : G) * g) = r g) ∧ w 1 = 1 :=
  have := QuotientGroup.discreteTopology hH
  H.exists_continuous_rightCosetFactorization_of_section Quotient.out
    continuous_of_discreteTopology QuotientGroup.out_eq'

end TauCeti
