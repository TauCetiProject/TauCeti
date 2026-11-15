/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Residue
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Count

/-!
# Constant terms at squarefree level

For squarefree `N`, a cusp of `Γ₀(N)` is determined by the gcd of its denominator with `N`.
Consequently `TauCeti.constantTermsAtDivisors`, recording the constant terms at the
representatives `1/d` for `d ∣ N`, detects cuspidality:
`TauCeti.ker_constantTermsAtDivisors_of_squarefree` identifies its kernel with the cusp space.
The map recording these constant terms has proper image in weight two, by the residue
relation. These facts allow boundary interpolation by corrected Eisenstein series.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.1 and 3.8.

The cusp classification uses `TauCeti.gamma0CuspLabel_eq_iff_exists_dvd`.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace TauCeti

open _root_.ModularForm TauCeti.ModularForm

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- At squarefree level, equal denominator gcds give equal cusp constant terms. -/
theorem constantTermAt_eq_of_gcd_eq_of_squarefree
    (hN : Squarefree N) (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k)
    {γ γ' : SL(2, ℤ)} (h : Int.gcd (γ 1 0) N = Int.gcd (γ' 1 0) N) :
    constantTermAt γ f = constantTermAt γ' f := by
  have hlabel := (gamma0CuspLabel_eq_iff_gcd_eq_of_squarefree hN γ γ').mpr h
  obtain ⟨j, hj⟩ := (TauCeti.gamma0CuspLabel_eq_iff_exists_dvd γ γ').mp hlabel
  let δ := γ * T ^ (-j) * γ'⁻¹
  have hδ : δ ∈ Gamma0 N := by
    rw [mem_Gamma0_iff_dvd]
    convert hj using 1
    simp [δ, Matrix.mul_apply, Fin.sum_univ_two, coe_T_zpow, adjugate_fin_two]
    ring
  have hγ : γ = δ * γ' * T ^ j := by simp [δ, mul_assoc]
  rw [hγ, constantTermAt_mul_T_zpow,
    constantTermAt_mul_left (Subgroup.mem_map_of_mem _ hδ)]

/-- At squarefree level, the divisor-indexed values recover every cusp constant term. -/
theorem constantTermAt_eq_constantTermsAtDivisors_of_squarefree
    (hN : Squarefree N) (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    constantTermAt γ f = constantTermsAtDivisors f
      ⟨Int.gcd (γ 1 0) N,
        Nat.mem_divisors.mpr ⟨Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..), NeZero.ne N⟩⟩ := by
  rw [constantTermsAtDivisors_apply]
  apply constantTermAt_eq_of_gcd_eq_of_squarefree hN f
  simp [Int.gcd_natCast_natCast, Nat.gcd_eq_left
    (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right (γ 1 0) N))]

/-- At squarefree level the kernel of the divisor-indexed constant terms is the cusp space. -/
@[simp]
theorem ker_constantTermsAtDivisors_of_squarefree (hN : Squarefree N) :
    LinearMap.ker (constantTermsAtDivisors (N := N) (k := k)) =
      cuspFormSubmodule ((Gamma0 N).map (mapGL ℝ)) k := by
  ext f
  rw [LinearMap.mem_ker, mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
  constructor
  · intro h γ
    rw [constantTermAt_eq_constantTermsAtDivisors_of_squarefree hN f γ, h]
    rfl
  · intro h
    ext d
    rw [constantTermsAtDivisors_apply]
    exact h _

/-- In weight two, not every divisor-indexed boundary vector occurs at squarefree level. -/
theorem weight_two_range_constantTermsAtDivisors_ne_top_of_squarefree (hN : Squarefree N) :
    LinearMap.range (constantTermsAtDivisors (N := N) (k := 2)) ≠ ⊤ := by
  classical
  intro htop
  obtain ⟨f, hf⟩ := LinearMap.range_eq_top.mp htop (1 : N.divisors → ℂ)
  have hall (γ : SL(2, ℤ)) : constantTermAt γ f = 1 := by
    rw [constantTermAt_eq_constantTermsAtDivisors_of_squarefree hN f γ, hf]
    rfl
  have horbit (c : TauCeti.ModularForm.CuspTranslationOrbit ((Gamma0 N).map (mapGL ℝ))) :
      TauCeti.ModularForm.constantTermAtCuspTranslationOrbit f c = 1 := by
    induction c using TauCeti.ModularForm.CuspTranslationOrbit.induction_on with
    | h γ =>
      rw [TauCeti.ModularForm.constantTermAtCuspTranslationOrbit_mk_mapGL]
      exact hall _
  have hsum :=
    weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero f
  simp only [horbit, mul_one] at hsum
  have hpos : 0 < ∑ c : TauCeti.ModularForm.CuspTranslationOrbit ((Gamma0 N).map (mapGL ℝ)),
      TauCeti.ModularForm.cuspTranslationOrbitWidth c :=
    Finset.sum_pos (fun c _ ↦ TauCeti.ModularForm.cuspTranslationOrbitWidth_pos c)
      Finset.univ_nonempty
  rw [← Nat.cast_sum, Nat.cast_eq_zero] at hsum
  omega

end TauCeti
