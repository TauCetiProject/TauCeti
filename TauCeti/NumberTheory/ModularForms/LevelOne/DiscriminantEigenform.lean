/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# The discriminant as a full Hecke eigenform

The discriminant `Δ` is a normalized full Hecke eigenform of level one and weight twelve.
Its eigenvalues are its Fourier coefficients, which satisfy coprime multiplicativity and
the prime-power recurrence. In particular, the classical operator `T₂` acts by `-24`.

The bundled `discriminantEigenform` makes the general Hecke eigenform theory available for `Δ`.
The eigenvalue identity translates Hecke actions into Fourier coefficients, while multiplicativity
and the prime-power recurrence reduce coefficient calculations to prime indices. The uniqueness
results identify any level-one, weight-twelve cusp form with first Fourier coefficient `1` as `Δ`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.8, in particular Proposition 5.8.5.
* J.-P. Serre, *A Course in Arithmetic*, VII.4.
* Mathlib, `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`.
-/

public noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open HeckeRing.GL2
open scoped MatrixGroups ModularForm

namespace TauCeti

private def discriminantGamma1 : CuspForm ((Gamma1 1).map (mapGL ℝ)) 12 :=
  CuspForm.discriminant.copy discriminant rfl Gamma1_one_map_eq_SL

@[simp]
private theorem coe_discriminantGamma1 : (discriminantGamma1 : ℍ → ℂ) = discriminant :=
  (rfl)

private theorem discriminantGamma1_mem :
    discriminantGamma1 ∈ cuspFormCharSpace 12 (1 : (ZMod 1)ˣ →* ℂˣ) := by
  apply (mem_cuspFormCharSpace_one_iff _).mpr
  rintro γ ⟨g, _, rfl⟩
  exact CuspForm.discriminant.slash_action_eq' _ ⟨g, rfl⟩

private theorem exists_smul_discriminantGamma1
    (f : CuspForm ((Gamma1 1).map (mapGL ℝ)) 12) :
    ∃ c : ℂ, f = c • discriminantGamma1 := by
  let F : CuspForm 𝒮ℒ 12 := f.copy f rfl Gamma1_one_map_eq_SL.symm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve F
  refine ⟨c, ?_⟩
  ext z
  exact (congrArg (fun g : CuspForm 𝒮ℒ 12 ↦ g z) hc).symm

/-- The modular discriminant, bundled as a full Hecke eigenform of level one and weight twelve. -/
def discriminantEigenform : Eigenform 1 12 where
  toCuspForm := discriminantGamma1
  χ := 1
  mem_charSpace := discriminantGamma1_mem
  eigenvalue n := (qExpansion 1 discriminant).coeff n
  isEigen n := by
    let T := heckeRingHomCuspCharSpace 12 (1 : (ZMod 1)ˣ →* ℂˣ)
      (heckeTCompositeGamma0 1 n.val)
    let D : cuspFormCharSpace 12 (1 : (ZMod 1)ˣ →* ℂˣ) :=
      ⟨discriminantGamma1, discriminantGamma1_mem⟩
    obtain ⟨c, hc⟩ := exists_smul_discriminantGamma1 (T D).val
    have hT : T D = c • D := Subtype.ext hc
    have hcoeff :=
      qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime
        n.pos.ne' D (Nat.coprime_one_left n)
    rw [hT, Submodule.coe_smul, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map 1),
      PowerSeries.coeff_smul] at hcoeff
    have hc' : c = (qExpansion 1 discriminant).coeff n := by
      simpa [D, discriminant_qExpansion_coeff_one] using hcoeff
    simpa [T, D, hc'] using hT
  ne_zero := by
    intro h
    exact discriminant_ne_zero I (congrArg (fun f ↦ f I) h)

/-- The underlying function of the bundled eigenform is the modular discriminant. -/
@[simp]
theorem coe_discriminantEigenform :
    (discriminantEigenform.toCuspForm : ℍ → ℂ) = discriminant := (rfl)

/-- The discriminant has trivial nebentypus. -/
@[simp]
theorem discriminantEigenform_χ : discriminantEigenform.χ = 1 := (rfl)

/-- Every positive-index Hecke eigenvalue of `Δ` is its Fourier coefficient. -/
@[simp]
theorem discriminantEigenform_eigenvalue_eq_qExpansion_coeff (n : ℕ+) :
    discriminantEigenform.eigenvalue n = (qExpansion 1 discriminant).coeff n := (rfl)

/-- The discriminant is the unique normalized cusp form of level one and weight twelve. -/
theorem eq_discriminantEigenform_toCuspForm_of_coeff_one
    {f : CuspForm ((Gamma1 1).map (mapGL ℝ)) 12}
    (h₁ : (qExpansion 1 f).coeff 1 = 1) : f = discriminantEigenform.toCuspForm := by
  obtain ⟨c, hc⟩ := exists_smul_discriminantGamma1 f
  have hc' : c = 1 := by
    rw [hc, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map 1),
      PowerSeries.coeff_smul] at h₁
    simpa [discriminant_qExpansion_coeff_one] using h₁
  ext z
  simpa [hc'] using DFunLike.congr_fun hc z

/-- The discriminant is the unique normalized full eigenform of level one and weight twelve. -/
theorem eq_discriminantEigenform_of_coeff_one {f : Eigenform 1 12}
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) : f = discriminantEigenform :=
  Eigenform.ext (eq_discriminantEigenform_toCuspForm_of_coeff_one h₁)

namespace ModularForm

/-- The Fourier coefficients of `Δ` are multiplicative at coprime indices. -/
theorem discriminant_qExpansion_coeff_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    (qExpansion 1 discriminant).coeff (m * n) =
      (qExpansion 1 discriminant).coeff m * (qExpansion 1 discriminant).coeff n := by
  simpa using discriminantEigenform.qExpansion_coeff_mul
    (by simpa using discriminant_qExpansion_coeff_one) hmn

/-- The coefficients of `Δ` satisfy Ramanujan's prime-power recurrence. -/
theorem discriminant_qExpansion_coeff_prime_pow_add_two {p : ℕ} (hp : p.Prime) (r : ℕ) :
    (qExpansion 1 discriminant).coeff (p ^ (r + 2)) =
      (qExpansion 1 discriminant).coeff p *
        (qExpansion 1 discriminant).coeff (p ^ (r + 1)) -
      (p : ℂ) ^ 11 * (qExpansion 1 discriminant).coeff (p ^ r) := by
  simpa [Subsingleton.elim (p : ZMod 1) 1, zpow_ofNat] using
    discriminantEigenform.qExpansion_coeff_prime_pow_add_two
      (by simpa using discriminant_qExpansion_coeff_one) hp r

end ModularForm

/-- The classical operator `T₂` acts on the discriminant by `-24`. -/
theorem heckeTCuspNat_discriminant_two :
    heckeTCuspNat 12 2 discriminantEigenform.toCuspForm =
      (-24 : ℂ) • discriminantEigenform.toCuspForm := by
  simpa [ModularForm.discriminant_qExpansion_coeff_two] using
    discriminantEigenform.heckeTCuspNat_eq_eigenvalue_smul Nat.prime_two

end TauCeti
