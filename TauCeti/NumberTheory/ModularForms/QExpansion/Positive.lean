/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Uniqueness from positive Fourier coefficients

At nonzero weight, a modular form whose group has finite-index intersection with the modular
group is determined by its positive Fourier coefficients. The omitted constant term cannot hide
a nonzero constant modular form:
a finite-index intersection with the modular group contains a lower unipotent matrix, whose
automorphy factor is nonconstant.

This allows coefficient identities at positive indices to imply identities of modular forms,
without imposing a spurious condition on the constant term of an Eisenstein series.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Proposition 5.8.5.
-/

public noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup ModularGroup Filter
open scoped MatrixGroups

namespace TauCeti.ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- At nonzero weight, vanishing of all positive Fourier coefficients forces a modular form
whose group has finite-index intersection with the modular group to vanish. -/
theorem eq_zero_of_forall_pos_qExpansion_coeff_eq_zero [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : k ≠ 0)
    {f : ModularForm Γ k} (hf : ∀ n : ℕ, 0 < n → (qExpansion h f).coeff n = 0) : f = 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hconst : ⇑f = Function.const ℍ ((qExpansion h f).coeff 0) := by
    funext z
    have hs := _root_.ModularForm.hasSum_qExpansion f hh hΓ z
    have heq : (fun n ↦ (qExpansion h f).coeff n * Function.Periodic.qParam h z ^ n) =
        fun n ↦ if n = 0 then (qExpansion h f).coeff 0 else 0 := by
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, hf n (Nat.pos_of_ne_zero hn)]
    rw [heq] at hs
    exact hs.unique (hasSum_ite_eq 0 _)
  have hc := eq_zero_of_eq_const hconst hk
  ext z
  rw [hconst, Function.const_apply, hc]
  simp

/-- At nonzero weight, equality of the positive Fourier coefficients determines a modular form.
The constant coefficient need not be supplied. -/
theorem eq_of_forall_pos_qExpansion_coeff_eq [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : k ≠ 0)
    {f g : ModularForm Γ k}
    (hfg : ∀ n : ℕ, 0 < n → (qExpansion h f).coeff n = (qExpansion h g).coeff n) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_pos_qExpansion_coeff_eq_zero hh hΓ hk
  intro n hn
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub hh hΓ f g, map_sub, hfg n hn, sub_self]

/-- A nonzero positive Fourier coefficient excludes weight zero when the group has
finite-index intersection with the modular group. -/
theorem weight_ne_zero_of_pos_qExpansion_coeff_ne_zero [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {f : ModularForm Γ k}
    {n : ℕ} (hn : 0 < n) (hc : (qExpansion h f).coeff n ≠ 0) : k ≠ 0 := by
  rintro rfl
  let : (Γ ⊓ 𝒮ℒ).IsArithmetic := ⟨⟨⟨by
    simpa only [Subgroup.inf_relIndex_right] using Γ.relIndex_ne_zero⟩,
    Subgroup.isFiniteRelIndex_of_le_right 𝒮ℒ inf_le_right⟩⟩
  obtain ⟨c, hconst⟩ := _root_.ModularForm.eq_const_of_weight_zero
    (_root_.ModularForm.ofLe (Γ' := Γ ⊓ 𝒮ℒ) inf_le_left f)
  rw [_root_.ModularForm.coe_ofLe] at hconst
  have hs (z : ℍ) :
      HasSum (fun m ↦ (if m = 0 then c else 0) • Function.Periodic.qParam h z ^ m) (f z) := by
    rw [hconst, Function.const_apply]
    convert (hasSum_ite_eq 0 c : HasSum (fun m : ℕ ↦ if m = 0 then c else 0) c) using 1
    funext m
    by_cases hm : m = 0 <;> simp [hm]
  have he := ModularFormClass.qExpansion_coeff_unique hh hΓ hs n
  simp only [ite_eq_right hn.ne'] at he
  exact hc he.symm

end TauCeti.ModularForm
