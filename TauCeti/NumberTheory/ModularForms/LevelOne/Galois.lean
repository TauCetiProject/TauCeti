/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.Hecke
public import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Galois action on level-one modular forms

Every automorphism of `ℂ` acts on level-one modular forms through their Fourier coefficients.
No continuity of the automorphism is required: existence follows by subtracting a multiple of
a rational Eisenstein series and dividing the resulting cusp form by `Δ`, inductively on the
weight. Uniqueness follows from the q-expansion principle. Thus the construction does not apply
an automorphism to an analytic limit or to a transformation law.

The action is semilinear, preserves cusp forms, and commutes with the arithmetic Hecke
operators. In particular it transports normalized simultaneous Hecke eigenvectors to normalized
simultaneous eigenvectors with conjugated eigenvalues.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §§3–5.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Chapter 3.

The weight induction follows Mathlib's proof of `ModularForm.evalE₄E₆_surjective`; rationality
of the Eisenstein series and the discriminant is supplied by
`TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion`.
-/

public noncomputable section

open UpperHalfPlane EisensteinSeries
open scoped MatrixGroups

namespace ModularForm

private theorem map_qExpansion_discriminant (σ : ℂ ≃+* ℂ) :
    (qExpansion 1 discriminant).map σ.toRingHom = qExpansion 1 discriminant := by
  ext n
  obtain ⟨m, hm⟩ := TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n
  simp [hm]

private theorem exists_map_fixed_coeff_zero_one {k : ℕ} (hk : Even k) (h2 : k ≠ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ m : ModularForm 𝒮ℒ k, (qExpansion 1 m).coeff 0 = 1 ∧
      (qExpansion 1 m).map σ.toRingHom = qExpansion 1 m := by
  rcases eq_or_ne k 0 with rfl | h0
  · refine ⟨mcast (by norm_num) (1 : ModularForm 𝒮ℒ 0), ?_, ?_⟩ <;>
      simp [coe_mcast, UpperHalfPlane.qExpansion_one]
  have hk3 : 3 ≤ k := by have := hk.two_dvd; omega
  refine ⟨E hk3, E_qExpansion_coeff_zero _ hk, ?_⟩
  obtain ⟨P, hP⟩ := TauCeti.ModularForm.qExpansion_E_mem_range_map (Rat.castHom ℂ) hk3 hk
  rw [← hP]
  ext n
  simp

/-- Applying any automorphism of `ℂ` coefficientwise to a level-one modular form's expansion
again gives the expansion of a modular form of the same weight. -/
theorem exists_qExpansion_eq_map (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) :
    ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = (qExpansion 1 f).map σ.toRingHom := by
  induction k using Int.strongRec (m := 0) with
  | lt k hk =>
    rw [rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f]
    exact ⟨0, by simp [UpperHalfPlane.qExpansion_zero]⟩
  | ge k hk ih =>
    lift k to ℕ using hk
    by_cases hodd : Odd k
    · rw [levelOne_odd_weight_eq_zero hodd.natCast f]
      exact ⟨0, by simp [UpperHalfPlane.qExpansion_zero]⟩
    obtain rfl | h2 := eq_or_ne k 2
    · rw [rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f]
      exact ⟨0, by simp [UpperHalfPlane.qExpansion_zero]⟩
    obtain ⟨m, hm0, hmσ⟩ := exists_map_fixed_coeff_zero_one (Nat.not_odd_iff_even.mp hodd) h2 σ
    obtain ⟨g, hg⟩ := sub_smul_isCuspForm f m hm0
    obtain ⟨h, hh⟩ := ih ((k : ℤ) - 12) (by omega) (CuspForm.discriminantEquiv g)
    refine ⟨mcast (by omega) ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).mul h) +
      σ ((qExpansion 1 f).coeff 0) • m, ?_⟩
    have hf : f = (g : ModularForm 𝒮ℒ k) + (qExpansion 1 f).coeff 0 • m := by
      rw [← CuspForm.toModularFormₗ_eq_coe, hg]
      abel
    have hgq : qExpansion 1 g = qExpansion 1 discriminant *
        qExpansion 1 (CuspForm.discriminantEquiv g) := by
      rw [← discriminant_mul_discriminantEquiv g]
      exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
        CuspForm.discriminant (CuspForm.discriminantEquiv g)
    have hgcoe : ⇑(g : ModularForm 𝒮ℒ k) = ⇑g :=
      funext (CuspForm.toModularFormₗ_apply g)
    have hqf : qExpansion 1 f = qExpansion 1 g +
        (qExpansion 1 f).coeff 0 • qExpansion 1 m := by
      simpa only [map_add, map_smul, TauCeti.ModularForm.qExpansionLinearMap_apply, hgcoe] using
        congrArg (TauCeti.ModularForm.qExpansionLinearMap one_pos one_mem_strictPeriods_SL k) hf
    conv_rhs => rw [hqf, hgq]
    rw [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos one_mem_strictPeriods_SL,
      map_add, map_smul]
    simp only [TauCeti.ModularForm.qExpansionLinearMap_apply, coe_mcast]
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hh, map_add, map_mul]
    have hΔ : qExpansion 1 (CuspForm.discriminant : ModularForm 𝒮ℒ 12) =
        qExpansion 1 discriminant := by
      rw [← CuspForm.toModularFormₗ_eq_coe]
      exact congrArg (qExpansion 1)
        ((funext (CuspForm.toModularFormₗ_apply CuspForm.discriminant)).trans
          CuspForm.coe_discriminant)
    rw [hΔ, map_qExpansion_discriminant]
    congr 1
    ext n
    simpa using
      congrArg (σ ((qExpansion 1 f).coeff 0) * ·) (congrArg (PowerSeries.coeff n) hmσ).symm

/-- The Galois conjugate of a level-one modular form: its Fourier coefficients are obtained by
applying `σ`, even when `σ` is discontinuous. -/
def galois (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) : ModularForm 𝒮ℒ k :=
  (f.exists_qExpansion_eq_map σ).choose

/-- The q-expansion characterizes Galois conjugation. -/
@[simp]
theorem qExpansion_galois (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) :
    qExpansion 1 (f.galois σ) = (qExpansion 1 f).map σ.toRingHom :=
  (f.exists_qExpansion_eq_map σ).choose_spec

/-- A Galois conjugate has the conjugated Fourier coefficients. -/
theorem qExpansion_galois_coeff (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) (n : ℕ) :
    (qExpansion 1 (f.galois σ)).coeff n = σ ((qExpansion 1 f).coeff n) := by
  simp

/-- Galois conjugation is additive. -/
@[simp]
theorem galois_add (f g : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) :
    (f + g).galois σ = f.galois σ + g.galois σ := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  simp only [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos one_mem_strictPeriods_SL,
    map_add]
  simp only [TauCeti.ModularForm.qExpansionLinearMap_apply, qExpansion_galois]
  simp only [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos one_mem_strictPeriods_SL,
    map_add]

/-- Galois conjugation is `σ`-semilinear. -/
@[simp]
theorem galois_smul (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) (c : ℂ) :
    (c • f).galois σ = σ c • f.galois σ := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  simp only [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos one_mem_strictPeriods_SL,
    map_smul]
  simp only [TauCeti.ModularForm.qExpansionLinearMap_apply, qExpansion_galois]
  rw [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos one_mem_strictPeriods_SL,
    map_smul]
  ext n
  simp

/-- The identity automorphism fixes each modular form. -/
@[simp]
theorem galois_refl (f : ModularForm 𝒮ℒ k) : f.galois (RingEquiv.refl ℂ) = f := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  ext n
  simp

/-- Successive conjugations compose in the order in which they act on coefficients. -/
@[simp]
theorem galois_galois (f : ModularForm 𝒮ℒ k) (σ τ : ℂ ≃+* ℂ) :
    (f.galois σ).galois τ = f.galois (σ.trans τ) := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  ext n
  simp

/-- Galois conjugation fixes the zero form. -/
@[simp]
theorem galois_zero (σ : ℂ ≃+* ℂ) : (0 : ModularForm 𝒮ℒ k).galois σ = 0 := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  simp [UpperHalfPlane.qExpansion_zero]

/-- Galois conjugation respects multiplication of forms of possibly different weights. -/
@[simp]
theorem galois_mul (f : ModularForm 𝒮ℒ k) (g : ModularForm 𝒮ℒ l) (σ : ℂ ≃+* ℂ) :
    (f.mul g).galois σ = (f.galois σ).mul (g.galois σ) := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  simp only [qExpansion_galois, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    map_mul]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Coefficientwise Galois conjugation as a semilinear equivalence of level-one modular forms. -/
def _root_.RingEquiv.modularFormLevelOneEquiv (σ : ℂ ≃+* ℂ) (k : ℤ) :
    ModularForm 𝒮ℒ k ≃ₛₗ[(σ : ℂ →+* ℂ)] ModularForm 𝒮ℒ k where
  toFun f := f.galois σ
  invFun f := f.galois σ.symm
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := galois_add f g σ
  map_smul' c f := galois_smul f σ c

@[simp]
theorem _root_.RingEquiv.modularFormLevelOneEquiv_apply (σ : ℂ ≃+* ℂ)
    (f : ModularForm 𝒮ℒ k) : σ.modularFormLevelOneEquiv k f = f.galois σ := (rfl)

/-- The inverse equivalence acts through the inverse field automorphism. -/
theorem _root_.RingEquiv.modularFormLevelOneEquiv_symm (σ : ℂ ≃+* ℂ) (k : ℤ) :
    (σ.modularFormLevelOneEquiv k).symm = σ.symm.modularFormLevelOneEquiv k := by
  ext f
  rfl

/-- Galois conjugation preserves cuspidality: at level one it is exactly vanishing of the
constant Fourier coefficient. -/
@[simp]
theorem isCuspForm_galois_iff (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) :
    IsCuspForm (f.galois σ) ↔ IsCuspForm f := by
  simp [isCuspForm_iff_coeffZero_eq_zero]

/-- Galois conjugation commutes with every arithmetic Hecke operator at level one. -/
@[simp]
theorem galois_heckeTLevelOne (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ) (n : ℕ) [NeZero n] :
    (TauCeti.heckeTLevelOne k n f).galois σ = TauCeti.heckeTLevelOne k n (f.galois σ) := by
  apply ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  ext m
  rw [qExpansion_galois_coeff, TauCeti.qExpansion_coeff_heckeTLevelOne,
    TauCeti.qExpansion_coeff_heckeTLevelOne]
  simp only [map_sum, map_mul, map_zpow₀, map_natCast, qExpansion_galois_coeff]

/-- A Hecke eigenrelation is transported to the conjugated eigenvalue. -/
theorem heckeTLevelOne_galois_eq_smul (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ)
    (n : ℕ) [NeZero n] {a : ℂ} (h : TauCeti.heckeTLevelOne k n f = a • f) :
    TauCeti.heckeTLevelOne k n (f.galois σ) = σ a • f.galois σ := by
  rw [← galois_heckeTLevelOne, h, galois_smul]

/-- The Galois conjugate of a normalized simultaneous eigenform is normalized and has
conjugated eigenvalues at every positive index. The form remains cuspidal if it was cuspidal. -/
theorem exists_normalized_eigenform_galois (f : ModularForm 𝒮ℒ k) (σ : ℂ ≃+* ℂ)
    (h1 : (qExpansion 1 f).coeff 1 = 1)
    (hT : ∀ n : ℕ+,
      TauCeti.heckeTLevelOne k n f = (qExpansion 1 f).coeff n • f) :
    ∃ g : ModularForm 𝒮ℒ k,
      qExpansion 1 g = (qExpansion 1 f).map σ.toRingHom ∧
      (qExpansion 1 g).coeff 1 = 1 ∧
      (IsCuspForm g ↔ IsCuspForm f) ∧
      ∀ n : ℕ+,
        TauCeti.heckeTLevelOne k n g = (qExpansion 1 g).coeff n • g := by
  refine ⟨f.galois σ, qExpansion_galois f σ, by simp [h1], isCuspForm_galois_iff f σ, ?_⟩
  intro n
  simpa using heckeTLevelOne_galois_eq_smul f σ n (hT n)

end ModularForm
