/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.DiamondOperators

import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Units
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Twisting modular forms by functions modulo `M`

For `Φ : ZMod M → ℂ` and a modular form `f` for `Γ₁(N)` with `q`-expansion `∑ aₙ qⁿ`, the
*twist* `f ⊗ Φ` is the modular form with `q`-expansion `∑ Φ(n) aₙ qⁿ`. It is the finite
combination of translates

`(f ⊗ Φ)(τ) = M⁻¹ ∑_{a mod M} 𝓕Φ(a) f(τ + a / M)`,

where `𝓕Φ` is the discrete Fourier transform of `Φ` on `ZMod M` (`ZMod.dft`): translating by
`a / M` multiplies the `n`-th coefficient by the root of unity `e(an / M)`, and Fourier inversion
on `ZMod M` turns the resulting combination of roots of unity back into `Φ(n)`.

Each translate `f(τ + a / M)` is a form for the conjugate of `Γ₁(N)` by `[1, a/M; 0, 1]`, and
that conjugate contains `Γ₁(L)` as soon as `N M ∣ L` and `M² ∣ L`. So `f ⊗ Φ` is a modular form
of level `Γ₁(L)`, and a cusp form when `f` is one; holomorphy and the conditions at the cusps come
from mathlib's `ModularForm.translate` and `CuspForm.translate`. The least such `L` is
`M · lcm(N, M)`. This is the level the matrix computation below produces, not the sharp level of
Atkin–Li.

When `Φ = ψ` is a Dirichlet character modulo `M` and `f ∈ M_k(Γ₁(N), χ)`, the twist lies in
`M_k(Γ₁(L), χψ²)`. Moving `[1, a/M; 0, 1]` past a matrix `γ ∈ Γ₀(L)` with lower-right entry `d`
gives a matrix of `Γ₀(N)` whose lower-right entry is still `d` modulo `N`, followed by the
translation by `a d² / M`. Reindexing `a ↦ a d²` then multiplies `𝓕ψ` by `ψ(d)²`. No primitivity
of `ψ` is needed. For primitive `ψ`, `𝓕ψ` is a Gauss-sum multiple of `ψ⁻¹`
(`DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`), and the formula above
becomes the classical expression of the twist through Gauss sums.

## Main definitions

* `ModularForm.twist`, `CuspForm.twist`: the twist `f ⊗ Φ`, from level `Γ₁(N)`
  to level `Γ₁(L)` for `N * M ∣ L` and `M * M ∣ L`, with their `ℂ`-linear packagings
  `twistₗ`.

## Main results

* `TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom`: moving the translation
  `[1, a/M; 0, 1]` past `γ ∈ SL(2, ℤ)` with `M² ∣ γ₁₀` yields `γ' [1, a'/M; 0, 1]` for an integral
  `γ'` and any `a' ≡ a d² (mod M)`.
* `TauCeti.Gamma1_map_le_conjAct_upperRightHom`: `Γ₁(L) ≤ [1, a/M; 0, 1]⁻¹ Γ₁(N) [1, a/M; 0, 1]`.
* `ModularForm.twist_apply`: `(f ⊗ Φ)(τ) = M⁻¹ ∑ₐ 𝓕Φ(a) f(τ + a / M)`.
* `ModularForm.qExpansion_twist_coeff`, `CuspForm.qExpansion_twist_coeff`:
  `aₙ(f ⊗ Φ) = Φ(n) aₙ(f)`.
* `ModularForm.twist_mem_modFormCharSpace`,
  `CuspForm.twist_mem_cuspFormCharSpace`: the twist of `f ∈ M_k(Γ₁(N), χ)` by a
  Dirichlet character `ψ` modulo `M` lies in `M_k(Γ₁(L), χψ²)`, and likewise for `S_k`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Proposition 3.64.
* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978), for the sharper level of the twist.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ZMod
open Matrix.GeneralLinearGroup (upperRightHom)

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {M N L : ℕ} {k : ℤ}

/-- **Moving a translation by `a / M` past a matrix of `Γ₀(M²)`.** Let `γ = [A, B; C, D]` be in
`SL(2, ℤ)` with `C = M² c`, and let `a' ≡ a D² (mod M)`. Then
`[1, a/M; 0, 1] γ = γ' [1, a'/M; 0, 1]` for some `γ' ∈ SL(2, ℤ)` with lower-left entry `C`,
upper-left entry `A + a M c` and lower-right entry `D - a' M c`.

The congruence on `a'` is what makes `γ'` integral: `A D ≡ 1 (mod M)`, so `a D ≡ a' A (mod M)`.
For `M = 0` both translations are the identity (`a / 0 = 0`) and `γ' = γ`. -/
theorem exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom (γ : SL(2, ℤ))
    {c a a' : ℤ} (hc : γ 1 0 = M * M * c) (ha : (a' : ZMod M) = a * (γ 1 1 : ZMod M) ^ 2) :
    ∃ γ' : SL(2, ℤ), γ' 0 0 = γ 0 0 + a * M * c ∧ γ' 1 0 = γ 1 0 ∧
      γ' 1 1 = γ 1 1 - a' * M * c ∧
      upperRightHom ((a : ℝ) / M) * mapGL ℝ γ = mapGL ℝ γ' * upperRightHom ((a' : ℝ) / M) := by
  rcases eq_or_ne M 0 with rfl | hM0
  · exact ⟨γ, by simp, rfl, by simp, by simp⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  -- `a D ≡ a' A (mod M)`, because `A D ≡ 1 (mod M)`
  obtain ⟨e, he⟩ : (M : ℤ) ∣ a * γ 1 1 - a' * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hAD : (γ 0 0 : ZMod M) * γ 1 1 = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod M) hdet
      push_cast [hc, ZMod.natCast_self] at this
      simpa using this
    push_cast
    rw [ha]
    linear_combination (-(a : ZMod M) * γ 1 1) * hAD
  let γ' : SL(2, ℤ) :=
    ⟨!![γ 0 0 + a * M * c, γ 0 1 + e - a * a' * c; γ 1 0, γ 1 1 - a' * M * c], by
      rw [Matrix.det_fin_two_of]
      linear_combination hdet + (M * c) * he + (a * a' * c - e) * hc⟩
  have hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0 + a * M * c, γ 0 1 + e - a * a' * c; γ 1 0, γ 1 1 - a' * M * c] := rfl
  refine ⟨γ', by simp [hγ'], by simp [hγ'], by simp [hγ'], ?_⟩
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM0
  have hcR : (γ 1 0 : ℝ) = M * M * c := by exact_mod_cast hc
  have heR : (a : ℝ) * γ 1 1 - a' * γ 0 0 = M * e := by exact_mod_cast he
  -- the `(0, 0)` and `(1, 0)` entries close by `simp`; the `(0, 1)` entry is `a D ≡ a' A`
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix, hγ', hcR] <;>
    field_simp
  · linear_combination heR
  · ring

/-- **The level of a translate by `a / M`.** For `N * M ∣ L` and `M * M ∣ L`, `Γ₁(L)` is contained
in the conjugate `[1, a/M; 0, 1]⁻¹ Γ₁(N) [1, a/M; 0, 1]`, so the translate `τ ↦ f(τ + a/M)` of a
form for `Γ₁(N)` is a form for `Γ₁(L)`. -/
theorem Gamma1_map_le_conjAct_upperRightHom (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (a : ℤ) : (Gamma1 L).map (mapGL ℝ) ≤
      ConjAct.toConjAct (upperRightHom ((a : ℝ) / M))⁻¹ • (Gamma1 N).map (mapGL ℝ) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  obtain ⟨hA, hD, hC⟩ := (Gamma1_mem L γ).mp hγ
  obtain ⟨c, hc, hNc⟩ := CongruenceSubgroup.exists_eq_mul_mul_of_mem_Gamma0 hNL hML
    (Gamma1_in_Gamma0 L hγ)
  have hDM : ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    simpa [map_one] using congrArg (ZMod.castHom (dvd_of_mul_left_dvd hML) (ZMod M)) hD
  obtain ⟨γ', hA', hC', hD', heq⟩ :=
    exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom γ (a := a) (a' := a) hc
      (by rw [hDM]; ring)
  refine ⟨γ', ?_, by rw [heq, mul_inv_cancel_right]⟩
  have hN : ((a * M * c : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by rw [mul_assoc]; exact hNc.mul_left a)
  have hNL' : N ∣ L := dvd_of_mul_right_dvd hNL
  rw [SetLike.mem_coe, Gamma1_mem, hA', hC', hD', Int.cast_add, Int.cast_sub, hN, add_zero,
    sub_zero]
  exact ⟨by simpa [map_one] using congrArg (ZMod.castHom hNL' (ZMod N)) hA,
    by simpa [map_one] using congrArg (ZMod.castHom hNL' (ZMod N)) hD,
    by simpa using congrArg (ZMod.castHom hNL' (ZMod N)) hC⟩

/-- **The twist of a modular form by a function modulo `M`.** For `Φ : ZMod M → ℂ` and a modular
form `f` for `Γ₁(N)`, the modular form `f ⊗ Φ` for `Γ₁(L)`, where `N * M ∣ L` and `M * M ∣ L`,
given by `(f ⊗ Φ)(τ) = M⁻¹ ∑_{a mod M} 𝓕Φ(a) f(τ + a / M)` (`twist_apply`). Its `q`-expansion is
`∑ Φ(n) aₙ(f) qⁿ` (`qExpansion_twist_coeff`). -/
def _root_.ModularForm.twist [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k :=
  (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a •
    _root_.ModularForm.restrict (Gamma1_map_le_conjAct_upperRightHom hNL hML (a.val : ℤ))
      (_root_.ModularForm.translate f (upperRightHom (((a.val : ℤ) : ℝ) / M)))

/-- The defining formula of the twist: `(f ⊗ Φ)(τ) = M⁻¹ ∑ₐ 𝓕Φ(a) f(τ + a / M)`. -/
@[simp]
lemma _root_.ModularForm.twist_apply [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L)
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    ModularForm.twist Φ hNL hML f τ =
      (M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * f (((a.val : ℝ) / M) +ᵥ τ) := by
  simp only [ModularForm.twist, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
    Finset.sum_apply,
    smul_eq_mul,
    _root_.ModularForm.coe_restrict, _root_.ModularForm.coe_translate,
    ModularForm.slash_upperRightHom_apply, Int.cast_natCast]

/-- The twist by `Φ`, as a `ℂ`-linear map `M_k(Γ₁(N)) → M_k(Γ₁(L))`. -/
def _root_.ModularForm.twistₗ [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L) :
    _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k where
  toFun := ModularForm.twist Φ hNL hML
  map_add' f g := by
    ext τ
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext τ
    simp [Finset.mul_sum, mul_left_comm]

@[simp]
lemma _root_.ModularForm.twistₗ_apply [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L)
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.twistₗ Φ hNL hML f = ModularForm.twist Φ hNL hML f := (rfl)

/-- The twist as a combination of slashes by the translation matrices `[1, a/M; 0, 1]`. This is
the form in which the transformation law of the twist is computed. -/
private lemma _root_.ModularForm.coe_twist_eq_sum_slash [NeZero M] (Φ : ZMod M → ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.twist Φ hNL hML f) =
      (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a • (⇑f ∣[k] upperRightHom ((a.val : ℝ) / M)) := by
  ext τ
  simp only [ModularForm.twist_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    ModularForm.slash_upperRightHom_apply]

/-- **The twist of a cusp form by a function modulo `M`.** For `Φ : ZMod M → ℂ` and a cusp form
`f` for `Γ₁(N)`, the cusp form `f ⊗ Φ` for `Γ₁(L)`, where `N * M ∣ L` and `M * M ∣ L`, given by
`(f ⊗ Φ)(τ) = M⁻¹ ∑_{a mod M} 𝓕Φ(a) f(τ + a / M)`. Its underlying function is that of the twist
of `f` as a modular form (`coe_twist`). -/
def _root_.CuspForm.twist [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.CuspForm ((Gamma1 L).map (mapGL ℝ)) k :=
  (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a •
    _root_.CuspForm.restrict (Gamma1_map_le_conjAct_upperRightHom hNL hML (a.val : ℤ))
      (_root_.CuspForm.translate f (upperRightHom (((a.val : ℤ) : ℝ) / M)))

/-- The defining formula of the twist of a cusp form: `(f ⊗ Φ)(τ) = M⁻¹ ∑ₐ 𝓕Φ(a) f(τ + a / M)`. -/
@[simp]
lemma _root_.CuspForm.twist_apply [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L)
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    CuspForm.twist Φ hNL hML f τ =
      (M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * f (((a.val : ℝ) / M) +ᵥ τ) := by
  simp only [CuspForm.twist, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
    Finset.sum_apply,
    smul_eq_mul, _root_.CuspForm.coe_restrict, _root_.CuspForm.coe_translate,
    ModularForm.slash_upperRightHom_apply, Int.cast_natCast]

/-- The twist by `Φ`, as a `ℂ`-linear map `S_k(Γ₁(N)) → S_k(Γ₁(L))`. -/
def _root_.CuspForm.twistₗ [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L) :
    _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      _root_.CuspForm ((Gamma1 L).map (mapGL ℝ)) k where
  toFun := CuspForm.twist Φ hNL hML
  map_add' f g := by
    ext τ
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext τ
    simp [Finset.mul_sum, mul_left_comm]

@[simp]
lemma _root_.CuspForm.twistₗ_apply [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L)
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.twistₗ Φ hNL hML f = CuspForm.twist Φ hNL hML f := (rfl)

/-- The twist of a cusp form has the same underlying function as the twist of `f` regarded as a
modular form. -/
@[simp]
lemma _root_.CuspForm.coe_twist [NeZero M] (Φ : ZMod M → ℂ) (hNL : N * M ∣ L)
    (hML : M * M ∣ L)
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.twist Φ hNL hML f) =
      ⇑(ModularForm.twist Φ hNL hML (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  ext τ
  simp

section QExpansion

/-- **The `q`-expansion of a twist.** `aₙ(f ⊗ Φ) = Φ(n) aₙ(f)` for every `n`. -/
@[simp]
theorem _root_.ModularForm.qExpansion_twist_coeff [NeZero M] (Φ : ZMod M → ℂ)
    (hNL : N * M ∣ L)
    (hML : M * M ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.twist Φ hNL hML f)).coeff n =
      Φ n * (qExpansion 1 f).coeff n := by
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma1_map N)⟩
  -- Fourier inversion on `ZMod M` expresses `Φ` through the additive characters
  have hinv (m : ZMod M) : Φ m = (M : ℂ)⁻¹ * ∑ a, 𝓕 Φ a * stdAddChar (a * m) := by
    conv_lhs => rw [← LinearEquiv.symm_apply_apply dft Φ]
    simp [ZMod.invDFT_apply, mul_comm]
  -- translating by `a / M` multiplies `q ^ m` by the root of unity `e(a m / M)`
  have hq (a : ZMod M) (m : ℕ) (τ : ℍ) :
      Function.Periodic.qParam 1 ((((a.val : ℝ) / M) +ᵥ τ : ℍ) : ℂ) ^ m =
        stdAddChar (a * (m : ZMod M)) * Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    have ham : a * (m : ZMod M) = ((a.val * m : ℕ) : ℤ) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
    rw [ham, ZMod.stdAddChar_coe, coe_vadd, Function.Periodic.qParam,
      Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have key : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (Φ m * (qExpansion 1 f).coeff m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.twist Φ hNL hML f τ) := by
    intro τ
    rw [ModularForm.twist_apply]
    refine ((hasSum_sum fun a _ ↦ (_root_.ModularForm.hasSum_qExpansion f one_pos
      (one_mem_strictPeriods_Gamma1_map N) (((a.val : ℝ) / M) +ᵥ τ)).mul_left (𝓕 Φ a)).mul_left
      (M : ℂ)⁻¹).congr_fun fun m ↦ ?_
    rw [hinv, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hq]
    ring
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma1_map L)
    key n).symm

/-- **The `q`-expansion of a twisted cusp form.** `aₙ(f ⊗ Φ) = Φ(n) aₙ(f)` for every `n`. -/
theorem _root_.CuspForm.qExpansion_twist_coeff [NeZero M] (Φ : ZMod M → ℂ)
    (hNL : N * M ∣ L)
    (hML : M * M ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.twist Φ hNL hML f)).coeff n =
      Φ n * (qExpansion 1 f).coeff n := by
  rw [CuspForm.coe_twist]
  exact ModularForm.qExpansion_twist_coeff Φ hNL hML _ n

end QExpansion

section Nebentypus

/-- One translate of a function with nebentypus `χ` at level `N`, slashed by `g ∈ Γ₀(L)` with
lower-right entry `d`: the result is `χ(d)` times the translate by `a d² / M`. -/
private lemma slash_upperRightHom_slash_mapGL [NeZero M] (hNL : N * M ∣ L) (hML : M * M ∣ L)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : ℍ → ℂ}
    (hf : ∀ g : Gamma0 N,
      f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (χ ((Gamma0Map N).toHomUnits g) : ℂ) • f)
    (g : Gamma0 L) (a : ZMod M) :
    (f ∣[k] upperRightHom ((a.val : ℝ) / M)) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (χ (unitsMap (dvd_of_mul_right_dvd hNL) ((Gamma0Map L).toHomUnits g)) : ℂ) •
        (f ∣[k] upperRightHom (((a * ((g : SL(2, ℤ)) 1 1 : ZMod M) ^ 2).val : ℝ) / M)) := by
  have hNL' : N ∣ L := dvd_of_mul_right_dvd hNL
  obtain ⟨c, hc, hNc⟩ := CongruenceSubgroup.exists_eq_mul_mul_of_mem_Gamma0 hNL hML g.2
  obtain ⟨γ', -, hC', hD', heq⟩ := exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom
    (g : SL(2, ℤ)) (a := a.val) (a' := (a * ((g : SL(2, ℤ)) 1 1 : ZMod M) ^ 2).val) hc
    (by simp)
  simp only [Int.cast_natCast] at heq
  have hγ' : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem, hC']
    simpa using congrArg (ZMod.castHom hNL' (ZMod N)) (Gamma0_mem.mp g.2)
  rw [← SlashAction.slash_mul, heq, SlashAction.slash_mul, hf ⟨γ', hγ'⟩]
  have hN : ((((a * ((g : SL(2, ℤ)) 1 1 : ZMod M) ^ 2).val : ℤ) * M * c : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by rw [mul_assoc]; exact hNc.mul_left _)
  have hχ : (Gamma0Map N).toHomUnits ⟨γ', hγ'⟩ = unitsMap hNL' ((Gamma0Map L).toHomUnits g) := by
    ext
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply, ZMod.unitsMap_val, MonoidHom.coe_toHomUnits,
      Gamma0Map_apply, hD', ZMod.cast_intCast hNL', Int.cast_sub, hN, sub_zero]
  ext τ
  simp [hχ]

/-- The transformation law of the twist, for a bare function `f` with nebentypus `χ` at level `N`:
the twisted function transforms under `Γ₀(L)` by `χψ²`. -/
private lemma sum_slash_upperRightHom_slash_mapGL [NeZero M] (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) {χ : (ZMod N)ˣ →* ℂˣ} {f : ℍ → ℂ}
    (hf : ∀ g : Gamma0 N,
      f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (χ ((Gamma0Map N).toHomUnits g) : ℂ) • f)
    (g : Gamma0 L) :
    ((M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 ψ a • (f ∣[k] upperRightHom ((a.val : ℝ) / M))) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      ((χ.comp (unitsMap (dvd_of_mul_right_dvd hNL)) *
          (ψ.toUnitHom.comp (unitsMap (dvd_of_mul_left_dvd hML))) ^ 2)
          ((Gamma0Map L).toHomUnits g) : ℂ) •
        ((M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 ψ a • (f ∣[k] upperRightHom ((a.val : ℝ) / M))) := by
  set u := unitsMap (dvd_of_mul_left_dvd hML) ((Gamma0Map L).toHomUnits g)
  have hsmul (c : ℂ) (F : ℍ → ℂ) :
      (c • F) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = c • F ∣[k] mapGL ℝ (g : SL(2, ℤ)) :=
    _root_.ModularForm.SL_smul_slash k g F c
  -- `𝓕 ψ (a) = ψ(u) ^ 2 * 𝓕 ψ (a u²)`: the Fourier transform of `ψ` is `ψ⁻¹`-equivariant
  have hF (a : ZMod M) : 𝓕 ψ a = ψ u ^ 2 * 𝓕 ψ (a * (u : ZMod M) ^ 2) := by
    have h := dft_comp_unitMul (⇑ψ) (u ^ 2) (↑(u ^ 2) * a)
    have hfun : (fun j ↦ ψ (↑(u ^ 2) * j)) = ψ ↑(u ^ 2) • ⇑ψ := by
      ext j
      simp
    rw [hfun, _root_.map_smul, Units.inv_mul_cancel_left, Pi.smul_apply, smul_eq_mul] at h
    rw [← h, mul_comm _ a]
    simp [Units.val_pow_eq_pow_val]
  -- reindexing `a ↦ a u²` pulls out `ψ(u) ^ 2`
  have hre (c : ℂ) (F : ZMod M → ℍ → ℂ) :
      ∑ a : ZMod M, 𝓕 ψ a • c • F (a * (u : ZMod M) ^ 2) = (c * ψ u ^ 2) • ∑ a, 𝓕 ψ a • F a := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Units.mulRight (u ^ 2)) _ _ fun a ↦ ?_
    simp only [Units.mulRight_apply, Units.val_pow_eq_pow_val]
    rw [hF a, smul_smul, smul_smul]
    congr 1
    ring
  have hval : ((χ.comp (unitsMap (dvd_of_mul_right_dvd hNL)) *
      (ψ.toUnitHom.comp (unitsMap (dvd_of_mul_left_dvd hML))) ^ 2)
        ((Gamma0Map L).toHomUnits g) : ℂ) =
      χ (unitsMap (dvd_of_mul_right_dvd hNL) ((Gamma0Map L).toHomUnits g)) * ψ u ^ 2 := by
    simp [u]
  have hu : (u : ZMod M) = ((g : SL(2, ℤ)) 1 1 : ZMod M) := by
    simp [u, ZMod.unitsMap_val, Gamma0Map_apply, ZMod.cast_intCast (dvd_of_mul_left_dvd hML)]
  rw [hsmul, SlashAction.sum_slash]
  simp_rw [hsmul, slash_upperRightHom_slash_mapGL hNL hML hf g, ← hu]
  rw [hre _ (fun b ↦ f ∣[k] upperRightHom ((b.val : ℝ) / M)), hval, smul_comm]

/-- **The nebentypus of a twist.** For a Dirichlet character `ψ` modulo `M` and
`f ∈ M_k(Γ₁(N), χ)`, the twist `f ⊗ ψ` lies in `M_k(Γ₁(L), χψ²)`, both characters read at level
`L` along the reduction maps. -/
theorem _root_.ModularForm.twist_mem_modFormCharSpace [NeZero M]
    (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    ModularForm.twist ψ hNL hML f ∈ modFormCharSpace k
      (χ.comp (unitsMap (dvd_of_mul_right_dvd hNL)) *
        (ψ.toUnitHom.comp (unitsMap (dvd_of_mul_left_dvd hML))) ^ 2) := by
  rw [mem_modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [ModularForm.coe_twist_eq_sum_slash]
  exact sum_slash_upperRightHom_slash_mapGL ψ hNL hML hf g

/-- **The nebentypus of a twisted cusp form.** For a Dirichlet character `ψ` modulo `M` and
`f ∈ S_k(Γ₁(N), χ)`, the twist `f ⊗ ψ` lies in `S_k(Γ₁(L), χψ²)`. -/
theorem _root_.CuspForm.twist_mem_cuspFormCharSpace [NeZero M] (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm.twist ψ hNL hML f ∈ cuspFormCharSpace k
      (χ.comp (unitsMap (dvd_of_mul_right_dvd hNL)) *
        (ψ.toUnitHom.comp (unitsMap (dvd_of_mul_left_dvd hML))) ^ 2) := by
  rw [mem_cuspFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [CuspForm.coe_twist, ModularForm.coe_twist_eq_sum_slash]
  exact sum_slash_upperRightHom_slash_mapGL ψ hNL hML hf g

end Nebentypus

end TauCeti
