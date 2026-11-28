/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.FirstMinimum
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel

/-!
# Congruence separation in adelically framed hermitian spaces

Rational vectors congruent in the inverse finite frame modulo `a` differ by `a` times a
lattice vector. If they are distinct, their archimedean distance is bounded below by the
first minimum times any common lower bound on the archimedean absolute values of `a`.
In particular, this separates the last columns that occur at deep principal level in
unfolding periods of Poincaré series.

The application is the separation of nonidentity terms in `New.Exchange.norm_poincare_period_sub_le`
in `New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean` of [grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean
-/

public section

open IsDedekindDomain Matrix NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ}
  (V : FramedHermitianSpace E s)

/-- Finite-frame congruence modulo an algebraic integer is equivalent to the difference
being that integer times a vector of the rational lattice. The congruent vectors need
not themselves be integral in the frame. -/
theorem forall_finiteFrame_modEq_iff (a : 𝓞 E) (y z : ι → E) :
    (∀ i, FiniteAdeleRing.ModEq a
      (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)) i)
      (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ z)) i)) ↔
      ∃ t ∈ V.lattice, y - z = (a : E) • t := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [FiniteAdeleRing.modEq_zero_iff, map_zero, zero_smul, sub_eq_zero]
    refine ⟨fun h ↦ ⟨0, V.lattice.zero_mem, ?_⟩, fun ⟨_, _, h⟩ i ↦ by rw [h]⟩
    have he := mulVec_injective_of_isUnit V.frame.2⁻¹.isUnit (funext h)
    exact funext fun i ↦ FiniteAdeleRing.algebraMap_injective E (RingOfIntegers.not_isField E)
      (congrFun he i)
  have haE : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hcoords (c : E) :
      (↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ (c • (y - z))) =
      algebraMap E 𝔸ᶠ[E] c •
        (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)) -
          ((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ z))) := by
    rw [← mulVec_sub, ← mulVec_smul]
    congr 1
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_sub]
  have hdiv : (∀ i, FiniteAdeleRing.ModEq a
      (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)) i)
      (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ z)) i)) ↔
      (a : E)⁻¹ • (y - z) ∈ V.lattice := by
    simp only [V.mem_lattice_iff, hcoords, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      FiniteAdeleRing.modEq_iff_inv_mul_mem ha]
  rw [hdiv]
  constructor
  · intro h
    exact ⟨_, h, by rw [smul_smul, mul_inv_cancel₀ haE, one_smul]⟩
  · rintro ⟨t, ht, heq⟩
    rwa [heq, smul_smul, inv_mul_cancel₀ haE, one_smul]

/-- Distinct rational vectors congruent modulo `a` in the inverse finite frame have
archimedean distance at least `R` times the truncated first minimum, where `R` is a
common lower bound for the absolute values of `a` at infinity. -/
theorem mul_firstMinimum_le_vectorLength_sub_of_forall_modEq {a : 𝓞 E}
    {y z : ι → E} (hyz : y ≠ z) {R : ℝ} (hR : ∀ w : InfinitePlace E, R ≤ w (a : E))
    (hcongr : ∀ i, FiniteAdeleRing.ModEq a
      (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)) i)
      (((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ z)) i)) :
    R * V.firstMinimum ≤ V.vectorLength (y - z) := by
  by_cases hR₀ : 0 ≤ R
  · obtain ⟨t, ht, h⟩ := (V.forall_finiteFrame_modEq_iff a y z).mp hcongr
    have ht₀ : t ≠ 0 := fun ht₀ ↦ (sub_ne_zero.mpr hyz) (by simp [h, ht₀])
    rw [h]
    exact (mul_le_mul_of_nonneg_left (V.firstMinimum_le_vectorLength ht ht₀) hR₀).trans
      (V.mul_vectorLength_le_vectorLength_smul _ _ hR)
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hR₀) V.firstMinimum_pos.le).trans
      (V.vectorLength_nonneg _)

/-- Distinct rational vectors whose inverse finite-frame coordinates are the same column
of two matrices in the principal level `(a)` are separated at infinity by `R` times the
truncated first minimum, where each archimedean absolute value of `a` is at least `R`. -/
theorem mul_firstMinimum_le_vectorLength_sub_of_principalUnitaryLevel {a : 𝓞 E}
    {y z : ι → E} (hyz : y ≠ z) {R : ℝ} (hR : ∀ w : InfinitePlace E, R ≤ w (a : E))
    {g h : finiteAdelicUnitaryGroup E ι}
    (hg : g ∈ principalUnitaryLevel E ι (Ideal.span {a}))
    (hh : h ∈ principalUnitaryLevel E ι (Ideal.span {a})) (j : ι)
    (hy : (↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y) =
      (↑(g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ Pi.single j 1)
    (hz : (↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ z) =
      (↑(h : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ Pi.single j 1) :
    R * V.firstMinimum ≤ V.vectorLength (y - z) := by
  apply V.mul_firstMinimum_le_vectorLength_sub_of_forall_modEq hyz hR
  rw [hy, hz, mulVec_single_one, mulVec_single_one]
  exact fun i ↦ (modEq_apply_of_mem_principalUnitaryLevel hg i j).trans
    (modEq_apply_of_mem_principalUnitaryLevel hh i j).symm

end TauCeti.FramedHermitianSpace
