/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HaagerupProperty.Basic
public import TauCeti.GroupTheory.PropertyT.KazhdanPair
public import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite

/-!
# Property (T) obstructs the Haagerup property

The Haagerup property and relative property (T) are opposing approximation properties: in a group
with the Haagerup property, every subgroup with relative property (T) is finite. Consequently an
infinite group with property (T) does not have the Haagerup property, and neither does a group
containing an infinite subgroup with relative property (T).

Given a Kazhdan pair `(F, δ)` for `Λ`, the Haagerup property supplies a positive-definite function
`φ` vanishing at infinity with `φ 1 = 1` and `φ` close to `1` on `F`. The GNS vector of `φ` is then
an `(F, δ)`-invariant unit vector, so the GNS representation has a nonzero `Λ`-invariant vector
`v`. Its coefficient `g ↦ ⟪v, π g v⟫` vanishes at infinity, because `φ` does, but equals `‖v‖ ^ 2`
on `Λ`; hence `Λ` is finite.

Relative property (T) is used with Hilbert spaces in the universe of the group, which contains
the GNS spaces of positive-definite functions on it.

## Main statements

* `TauCeti.HasHaagerupProperty.finite_of_relativePropertyT`: in a group with the Haagerup property,
  a subgroup with relative property (T) is finite.
* `TauCeti.not_hasHaagerupProperty_of_relativePropertyT_top`: an infinite group with property (T)
  does not have the Haagerup property.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §16.1.
* P.-A. Cherix, M. Cowling, P. Jolissaint, P. Julg and A. Valette, *Groups with the Haagerup
  property*, Progress in Mathematics 197, Birkhäuser (2001), §1.1.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Theorem 2.12.4.
-/

public section

open Filter Topology InnerProductSpace

namespace TauCeti

universe v

variable {Γ : Type v} [Group Γ]

/-- In a group with the Haagerup property, every subgroup with relative property (T) is finite. -/
theorem HasHaagerupProperty.finite_of_relativePropertyT (hΓ : HasHaagerupProperty Γ)
    {Λ : Subgroup Γ} (hΛ : Λ.RelativePropertyT.{v}) : Finite Λ := by
  obtain ⟨F, δ, hδ, hK⟩ := Λ.relativePropertyT_iff_exists_isKazhdanPair.{v, v}.mp hΛ
  obtain ⟨φ, hφ, hφ1, hφ0, hφF⟩ := hasHaagerupProperty_iff.mp hΓ F (δ ^ 2 / 2) (by positivity)
  set π := hφ.gnsRepresentation
  set ξ := hφ.gnsVector 1
  -- The GNS vector at the identity is an `(F, δ)`-invariant unit vector.
  have hξ : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ, hφ.inner_gnsVector, inv_mul_cancel, hφ1, RCLike.one_re]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ξ) two_ne_zero).mp h
  have hξF : ∀ g ∈ F, ‖π g ξ - ξ‖ < δ := by
    intro g hg
    have hsq := hφ.norm_gnsVector_sub_sq 1 g
    rw [inv_one, one_mul, hφ1, RCLike.one_re] at hsq
    have hre : 1 - RCLike.re (φ g) < δ ^ 2 / 2 := by
      have := hφF g hg
      rw [← norm_neg, neg_sub] at this
      linarith [RCLike.re_le_norm (1 - φ g), show RCLike.re (1 - φ g) = 1 - RCLike.re (φ g) by
        simp]
    rw [hφ.gnsRepresentation_gnsVector_one, norm_sub_rev]
    exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp (by linarith)
  obtain ⟨v, hv, hvΛ⟩ := (Λ.isKazhdanPair_def F δ).mp hK hφ.gnsSpace π
    hφ.isUnitary_gnsRepresentation ⟨ξ, hξ, hξF⟩
  have hvΛ' (g : Γ) (hg : g ∈ Λ) : π g v = v := by
    simpa using (ContRepresentation.mem_invariants v).mp hvΛ ⟨g, hg⟩
  -- The coefficient of `v` vanishes at infinity but has norm `‖v‖ ^ 2` on `Λ`.
  have hev : ∀ᶠ g in cofinite, ‖⟪v, π g v⟫_ℂ‖ < ‖v‖ ^ 2 :=
    (hφ.tendsto_inner_gnsRepresentation_cofinite hφ0 v v).norm.eventually
      (gt_mem_nhds (by rw [norm_zero]; positivity))
  refine Set.finite_coe_iff.mpr ((eventually_cofinite.mp hev).subset fun g hg ↦ ?_)
  simp [hvΛ' g hg]

/-- An infinite group with property (T) does not have the Haagerup property. -/
theorem not_hasHaagerupProperty_of_relativePropertyT_top [Infinite Γ]
    (hT : (⊤ : Subgroup Γ).RelativePropertyT.{v}) : ¬ HasHaagerupProperty Γ := fun hΓ ↦
  have := hΓ.finite_of_relativePropertyT hT
  have := Finite.of_equiv _ (Subgroup.topEquiv (G := Γ)).toEquiv
  not_finite Γ

end TauCeti
