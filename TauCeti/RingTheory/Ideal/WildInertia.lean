/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise

import Mathlib.Tactic.LinearCombination

/-!
# The wild inertia subgroup of an ideal

Let a group `G` act by ring automorphisms on a commutative ring `R`, and let `Q` be an ideal of `R`.
The **wild inertia subgroup** `Q.wildInertia G` consists of the `σ ∈ G` such that every `x ∈ R`
admits `s ∈ 1 + Q` and `q ∈ Q` with `s (σ x - x) = q x`. For a maximal ideal `Q` of a domain `R`
this says that for every nonzero `x ∈ R` the ratio `σ(x)/x` lies in the localization `R_Q` and is
`≡ 1` modulo its maximal ideal; the condition on the `x ∈ Q` is what separates wild inertia from
inertia. This is Serre's characterization of the first lower ramification group `G_1`
(*Corps locaux*, IV §2, Proposition 6 and its corollaries); unlike the definition through `G_1`, it
does not need the maximal ideal of `R_Q` to be finitely generated or its powers to separate points.
For a prime `Q` of a domain that is not maximal, membership still implies the ratio condition, but
the converse can fail, since a denominator outside `Q` need not be invertible modulo `Q`.

## Main definitions

* `Ideal.wildInertia G Q`: the wild inertia subgroup of `Q`.

## Main results

* `Ideal.wildInertia_le_inertia`: the wild inertia subgroup lies in Mathlib's inertia subgroup.
* `Ideal.wildInertia_smul`: `P_{τQ} = τ P_Q τ⁻¹`.
* `Ideal.subgroupOf_wildInertia`: the wild inertia subgroup of a subgroup `H` is the trace of the
  wild inertia subgroup of `G` on `H`.
* `Ideal.normal_wildInertia_stabilizer`: the wild inertia subgroup of `Q` for the action of the
  stabilizer of `Q` is normal, like Mathlib's instance for `Ideal.inertia`.

## References

* J.-P. Serre, *Corps locaux*, Chapter IV, §2.
-/

public section

open Pointwise

namespace Ideal

variable (G : Type*) [Group G] {R : Type*} [CommRing R] [MulSemiringAction G R] (Q : Ideal R)

/-- The **wild inertia subgroup** of an ideal `Q`: the `σ ∈ G` such that every `x` has `s ∈ 1 + Q`
and `q ∈ Q` with `s (σ x - x) = q x`. For a maximal ideal `Q` of a domain, these are the `σ` such
that for every nonzero `x` the ratio `σ(x)/x` lies in the localization at `Q` and is `≡ 1` modulo
its maximal ideal. -/
def wildInertia : Subgroup G where
  carrier := {σ | ∀ x, ∃ s q, s - 1 ∈ Q ∧ q ∈ Q ∧ s * (σ • x - x) = q * x}
  one_mem' x := ⟨1, 0, by simp, Q.zero_mem, by simp⟩
  mul_mem' {σ τ} hσ hτ x := by
    obtain ⟨s₁, q₁, hs₁, hq₁, h₁⟩ := hτ x
    obtain ⟨s₂, q₂, hs₂, hq₂, h₂⟩ := hσ (τ • x)
    refine ⟨s₁ * s₂, q₂ * (s₁ + q₁) + s₂ * q₁, ?_, ?_, ?_⟩
    · have : s₁ * s₂ - 1 = s₁ * (s₂ - 1) + (s₁ - 1) := by ring
      rw [this]
      exact Q.add_mem (Q.mul_mem_left _ hs₂) hs₁
    · exact Q.add_mem (Q.mul_mem_right _ hq₂) (Q.mul_mem_left _ hq₁)
    · rw [mul_smul]
      linear_combination s₁ * h₂ + (s₂ + q₂) * h₁
  inv_mem' {σ} hσ x := by
    obtain ⟨s, q, hs, hq, h⟩ := hσ (σ⁻¹ • x)
    refine ⟨s + q, -q, ?_, Q.neg_mem hq, ?_⟩
    · rw [add_sub_right_comm]
      exact Q.add_mem hs hq
    · rw [smul_inv_smul] at h
      linear_combination -h

variable {G Q}

/-- `σ` lies in the wild inertia subgroup of `Q` exactly when every `x` has `s ∈ 1 + Q` and
`q ∈ Q` with `s (σ x - x) = q x`. -/
theorem mem_wildInertia {σ : G} :
    σ ∈ Q.wildInertia G ↔ ∀ x, ∃ s q, s - 1 ∈ Q ∧ q ∈ Q ∧ s * (σ • x - x) = q * x :=
  Iff.rfl

variable (G Q)

/-- The wild inertia subgroup lies in the inertia subgroup. -/
theorem wildInertia_le_inertia : Q.wildInertia G ≤ Q.inertia G := by
  intro σ hσ x
  obtain ⟨s, q, hs, hq, h⟩ := mem_wildInertia.mp hσ x
  have : σ • x - x = q * x - (s - 1) * (σ • x - x) := by linear_combination h
  rw [this]
  exact Q.sub_mem (Q.mul_mem_right _ hq) (Q.mul_mem_right _ hs)

/-- If `τ⁻¹ σ τ` lies in the wild inertia subgroup of `Q`, then `σ` lies in that of `τ • Q`. -/
private theorem mem_wildInertia_smul_of_inv_mul_mul_mem {σ τ : G}
    (h : τ⁻¹ * σ * τ ∈ Q.wildInertia G) : σ ∈ (τ • Q).wildInertia G := by
  intro x
  obtain ⟨s, q, hs, hq, h⟩ := mem_wildInertia.mp h (τ⁻¹ • x)
  refine ⟨τ • s, τ • q, ?_, smul_mem_pointwise_smul τ q Q hq, ?_⟩
  · rw [← smul_one τ, ← smul_sub]
    exact smul_mem_pointwise_smul τ _ Q hs
  · have := congrArg (τ • ·) h
    simp only [smul_mul', smul_sub, mul_smul, smul_inv_smul] at this
    exact this

/-- **Conjugating the ideal conjugates the wild inertia subgroup**: `P_{τQ} = τ P_Q τ⁻¹`. -/
theorem wildInertia_smul (τ : G) :
    (τ • Q).wildInertia G = (Q.wildInertia G).map (MulAut.conj τ) := by
  ext σ
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap]
  refine ⟨fun h ↦ ?_, fun h ↦ mem_wildInertia_smul_of_inv_mul_mul_mem G Q
    (by simpa [mul_assoc] using h)⟩
  have := mem_wildInertia_smul_of_inv_mul_mul_mem G (τ • Q) (τ := τ⁻¹) (σ := τ⁻¹ * σ * τ)
    (by simpa [mul_assoc] using h)
  simpa [smul_smul] using this

/-- The wild inertia subgroup of `Q` for the action of a subgroup `H` is the trace on `H` of the
wild inertia subgroup for `G`. -/
@[simp]
theorem subgroupOf_wildInertia (H : Subgroup G) :
    (Q.wildInertia G).subgroupOf H = Q.wildInertia H := by
  ext σ
  exact Iff.rfl

/-- The wild inertia subgroup of `Q` is normal in the stabilizer of `Q`, stated like Mathlib's
instance for `Ideal.inertia`. -/
instance normal_wildInertia_stabilizer :
    (Q.wildInertia (MulAction.stabilizer G Q)).Normal := by
  simp_rw [Subgroup.normal_iff_map_conj_eq, ← wildInertia_smul]
  exact fun g ↦ congrArg (wildInertia _) g.property

end Ideal
