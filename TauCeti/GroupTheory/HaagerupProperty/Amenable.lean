/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HaagerupProperty.Basic
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.Analysis.PositiveDefinite.Function.Finset

/-!
# Amenable discrete groups have the Haagerup property

For a finite nonempty set `F`, the normalized overlap function
`g ↦ |F ∩ gF| / |F|` is positive definite, equals one at the identity, and is supported
on `FF⁻¹`. Its distance from one is `|F ∖ gF| / |F|`, bounded by the relative translation
boundary. Følner sets therefore give the approximations required for the Haagerup property.
No countability or finite generation assumption is needed.

The construction follows Cherix–Cowling–Jolissaint–Julg–Valette, *Groups with the Haagerup
property*, §1.1, and the Følner criterion in Bekka–de la Harpe–Valette,
*Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open Filter Topology Finset
open scoped Pointwise symmDiff ComplexOrder

namespace TauCeti

variable {G : Type*} [Group G]

/-- Groups with Følner sets have the Haagerup property. -/
theorem hasHaagerupProperty_of_hasFoelnerSets (hG : HasFoelnerSets G) :
    HasHaagerupProperty G := by
  classical
  rw [hasHaagerupProperty_iff]
  intro K ε hε
  obtain ⟨F, hF, hboundary⟩ := hasFoelnerSets_iff.mp hG K ε hε
  have hc : (0 : ℝ) < F.card := Nat.cast_pos.mpr hF.card_pos
  have hcC : (F.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hF.card_pos.ne'
  let φ (g : G) : ℂ := (F.convolution F⁻¹ g : ℂ) / F.card
  refine ⟨φ, ?_, ?_, ?_, fun g hg ↦ ?_⟩
  · convert (F.posSemidef_convolution_inv (𝕜 := ℂ)).smul (inv_nonneg.mpr hc.le) using 1
    ext g h
    simp [φ, Algebra.smul_def, div_eq_mul_inv, mul_comm]
  · simp [φ, ← Finset.card_inter_smul, hcC]
  · apply tendsto_const_nhds.congr'
    filter_upwards [(F * F⁻¹).eventually_cofinite_notMem] with g hg
    simp [φ, Finset.convolution_eq_zero.mpr hg]
  · have hcard : (#(F \ g • F) : ℂ) + #(F ∩ g • F) = F.card := by
      exact_mod_cast F.card_sdiff_add_card_inter (g • F)
    have herror : φ g - 1 = -((#(F \ g • F) : ℂ) / F.card) := by
      dsimp [φ]
      rw [← Finset.card_inter_smul]
      field_simp
      linear_combination hcard
    have hle : #(F \ g • F) ≤ #((g • F) ∆ F) := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simp [Finset.mem_symmDiff, hx.1, hx.2]
    rw [herror, norm_neg, norm_div, RCLike.norm_natCast, RCLike.norm_natCast]
    apply (div_lt_iff₀ hc).mpr
    exact (Nat.cast_le.mpr hle).trans_lt (hboundary g hg)

/-- Every amenable discrete group has the Haagerup property. -/
theorem hasHaagerupProperty_of_amenable [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [Amenable G] : HasHaagerupProperty G :=
  hasHaagerupProperty_of_hasFoelnerSets Amenable.hasFoelnerSets

end TauCeti
