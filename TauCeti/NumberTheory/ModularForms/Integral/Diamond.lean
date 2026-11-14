/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diamond
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.Integral.BoundedDenominators


/-!
# Cusp forms whose diamond translates have integral expansions at `∞`

For a subring `R ⊆ ℂ`, the cusp forms `f` on `Γ₁(N)` such that every diamond translate `⟨d⟩ f`
has its `q`-expansion at `∞` in `R` form a `ℤ`-submodule `TauCeti.CuspForm.diamondIntegral R N k`
of `S_k(Γ₁(N))`. For `R = ℤ` these are the forms of Deligne–Serre's Proposition 2.7: once they
span `S_k(Γ₁(N))` over `ℂ` they form a Hecke-stable lattice, the integral structure that makes
the Hecke eigenvalues of a weight-one newform algebraic integers. The condition involves only
expansions at `∞`, so it applies to cusp forms with rational `q`-expansion without any
knowledge of their expansions at the other cusps.

The submodule is stable under the diamond operators by construction, and under `Tₚ` at every
prime `p` in weight `k ≥ 1`. The recurrence `aₘ(Tₚ f) = a_{pm}(f) + p^{k−1} a_{m/p}(⟨p⟩ f)`
(`HeckeRing.GL2.qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime`) reads
the expansion of `Tₚ f` off those of `f` and `⟨p⟩ f`, and `Tₚ` commutes with the diamond
operators. When `p ∣ N` the diamond term is absent, so this includes the operator `Uₚ`.

When `R` is a finitely generated abelian group, the submodule is finite and free over `ℤ`: by the
Sturm bound, a cusp form is determined by finitely many coefficients at `∞`. It contains the
cusp forms integral at every cusp (`TauCeti.ModularForm.integralAtCusps`).

Its complex span is governed by the rational forms: the `ℂ`-span of the forms with integral
diamond translates equals the `ℂ`-span of the forms with rational diamond translates
(`TauCeti.CuspForm.span_diamondIntegral_int_eq_span_diamondIntegral_rat`). This is the
bounded-denominator step of Deligne–Serre, Remarque 2.8: by
`CuspForm.exists_nsmul_qExpansion_coeff_eq_intCast`, each of the finitely many diamond translates
of a rational form has its denominators cleared by one integer.

## Main definitions

* `TauCeti.CuspForm.diamondIntegral R N k`: the cusp forms on `Γ₁(N)` all of whose diamond
  translates have `q`-expansion coefficients at `∞` in `R`.

## Main results

* `TauCeti.CuspForm.diamondOpCusp_mem_diamondIntegral`,
  `TauCeti.CuspForm.diamondOpCuspNat_mem_diamondIntegral`: stability under the diamond operators.
* `TauCeti.CuspForm.heckeTCuspNat_mem_diamondIntegral`: stability under `Tₚ` at every prime, in
  weight `k ≥ 1`.
* `TauCeti.CuspForm.instFiniteDiamondIntegral`, `TauCeti.CuspForm.instFreeDiamondIntegral`: when
  `R` is a finitely generated abelian group, a finite free `ℤ`-module.
* `TauCeti.CuspForm.mem_diamondIntegral_of_mem_integralAtCusps`: forms integral at every cusp
  lie in it.
* `TauCeti.CuspForm.span_diamondIntegral_int_eq_span_diamondIntegral_rat`: the forms with
  integral diamond translates and those with rational diamond translates have the same `ℂ`-span.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, Proposition 2.7 and Remarque 2.8.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm HeckeRing.GL2 UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.CuspForm

variable (R : Subring ℂ) (N : ℕ) (k : ℤ)

/-- The cusp forms on `Γ₁(N)` of weight `k` all of whose diamond translates `⟨d⟩ f` have their
`q`-expansion coefficients at `∞` in the subring `R` of `ℂ`, as a `ℤ`-submodule of
`S_k(Γ₁(N))`. -/
noncomputable def diamondIntegral : Submodule ℤ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | ∀ (d : (ZMod N)ˣ) (n : ℕ), (qExpansion 1 (diamondOpCusp k d f)).coeff n ∈ R}
  add_mem' {f g} hf hg d n := by
    have h := CuspForm.qExpansionCoeffₗ_apply (k := k) one_pos
      (one_mem_strictPeriods_Gamma1_map N) n
    rw [← h, map_add, map_add, h, h]
    exact R.add_mem (hf d n) (hg d n)
  zero_mem' d n := by
    rw [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), map_zero,
      map_zero]
    exact R.zero_mem
  smul_mem' c f hf d n := by
    rw [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), map_zsmul,
      map_zsmul, CuspForm.qExpansionCoeffₗ_apply]
    exact R.zsmul_mem (hf d n) c

variable {R N k}

/-- Membership in `diamondIntegral`: every coefficient at `∞` of every diamond translate lies
in `R`. -/
@[simp]
theorem mem_diamondIntegral_iff {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} :
    f ∈ diamondIntegral R N k ↔
      ∀ (d : (ZMod N)ˣ) (n : ℕ), (qExpansion 1 (diamondOpCusp k d f)).coeff n ∈ R :=
  Iff.rfl

/-- The coefficients at `∞` of a form in `diamondIntegral R N k` lie in `R`. -/
theorem qExpansion_coeff_mem_of_mem_diamondIntegral {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ diamondIntegral R N k) (n : ℕ) : (qExpansion 1 f).coeff n ∈ R := by
  simpa using hf 1 n

/-- `diamondIntegral` is monotone in the coefficient ring. -/
theorem diamondIntegral_mono {S : Subring ℂ} (h : R ≤ S) :
    diamondIntegral R N k ≤ diamondIntegral S N k :=
  fun _ hf d n ↦ h (hf d n)

/-- `diamondIntegral R N k` is stable under scaling by elements of `R`. -/
theorem smul_mem_diamondIntegral {r : ℂ} (hr : r ∈ R) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ diamondIntegral R N k) : r • f ∈ diamondIntegral R N k := fun d n ↦ by
  rw [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), map_smul,
    map_smul, CuspForm.qExpansionCoeffₗ_apply, smul_eq_mul]
  exact R.mul_mem hr (hf d n)

/-- **Diamond stability.** `diamondIntegral R N k` is stable under every diamond operator. -/
theorem diamondOpCusp_mem_diamondIntegral (e : (ZMod N)ˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ diamondIntegral R N k) :
    diamondOpCusp k e f ∈ diamondIntegral R N k := fun d n ↦ by
  simpa only [diamondOpCusp_mul, LinearMap.comp_apply] using hf (d * e) n

/-- The zero-extended diamond operator `⟨n⟩` preserves `diamondIntegral R N k`. -/
theorem diamondOpCuspNat_mem_diamondIntegral (m : ℕ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ diamondIntegral R N k) :
    diamondOpCuspNat k m f ∈ diamondIntegral R N k := by
  by_cases h : m.Coprime N
  · rw [diamondOpCuspNat_of_coprime k h]
    exact diamondOpCusp_mem_diamondIntegral _ hf
  · rw [diamondOpCuspNat_of_not_coprime k h, LinearMap.zero_apply]
    exact (diamondIntegral R N k).zero_mem

variable [NeZero N]

/-- **Hecke stability.** For a prime `p` and a weight `k ≥ 1`, the Hecke operator `Tₚ` maps
`diamondIntegral R N k` into itself. There is no condition on `p`: when `p ∣ N` the operator is
`Uₚ`. -/
theorem heckeTCuspNat_mem_diamondIntegral {p : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ diamondIntegral R N k) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f ∈ diamondIntegral R N k := fun d n ↦ by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hd := diamondOpCusp_mem_diamondIntegral d hf
  have hc : diamondOpCusp k d (heckeTCuspNat k p f) = heckeTCuspNat k p (diamondOpCusp k d f) := by
    simpa only [Module.End.mul_eq_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (commute_heckeTCuspNat_diamondOpCusp k p d).eq.symm f
  rw [hc, heckeTCuspNat_def,
    qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp]
  refine R.add_mem (qExpansion_coeff_mem_of_mem_diamondIntegral hd _) ?_
  split_ifs
  · -- `p ^ (k - 1)` is a natural number since `k ≥ 1`
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hk)
    rw [hj, zpow_natCast]
    exact R.mul_mem (R.pow_mem (natCast_mem R p) j) (qExpansion_coeff_mem_of_mem_diamondIntegral
      (diamondOpCuspNat_mem_diamondIntegral p hd) _)
  · exact R.zero_mem

/-- Forms on `Γ₁(N)` whose expansions at every cusp have coefficients in `R` lie in
`diamondIntegral R N k`: a diamond translate is a slash by an element of `SL₂(ℤ)`. -/
theorem mem_diamondIntegral_of_mem_integralAtCusps {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      ModularForm.integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ diamondIntegral R N k := fun d n ↦ by
  have h := ModularForm.qExpansion_coeff_mem_of_mem_integralAtCusps
    (ModularForm.diamondOp_mem_integralAtCusps d hf) n
  rwa [diamondOp_coe_cuspForm, strictWidthInfty_Gamma1, ModularFormClass.coe_modularForm] at h

section Finite

variable (R N k)

/-- The first `sturmLength` coefficients at `∞` of a form in `diamondIntegral R N k`, as
elements of `R`. -/
private noncomputable def truncCoeffs :
    diamondIntegral R N k →ₗ[ℤ] Fin (sturmLength ((Gamma1 N).map (mapGL ℝ)) k) → R where
  toFun f i := ⟨CuspForm.qExpansionCoeffₗ one_pos (one_mem_strictPeriods_Gamma1_map N) k i f,
    by simpa using qExpansion_coeff_mem_of_mem_diamondIntegral f.2 i⟩
  map_add' f g := by
    ext i
    simp only [Submodule.coe_add, map_add, Pi.add_apply, Subring.coe_add]
  map_smul' c f := by
    ext i
    simp

private theorem truncCoeffs_injective : Function.Injective (truncCoeffs R N k) := fun f g h ↦ by
  refine Subtype.ext <| CuspForm.toModularFormₗ_injective <| sturmCoeffsₗ_injective <|
    funext fun i ↦ ?_
  have hi := congrArg (fun F ↦ (F i : ℂ)) h
  simpa [truncCoeffs, strictWidthInfty_Gamma1, CuspForm.toModularFormₗ_eq_coe] using hi

/-- When `R` is a finitely generated abelian group, as is the ring of integers of a number field,
`diamondIntegral R N k` is a finitely generated `ℤ`-module: by the Sturm bound it embeds into
finitely many copies of `R`. -/
instance instFiniteDiamondIntegral [Module.Finite ℤ R] : Module.Finite ℤ (diamondIntegral R N k) :=
  Module.Finite.of_injective (truncCoeffs R N k) (truncCoeffs_injective R N k)

/-- When `R` is a finitely generated abelian group, `diamondIntegral R N k` is a free `ℤ`-module
of finite rank. -/
instance instFreeDiamondIntegral [Module.Finite ℤ R] : Module.Free ℤ (diamondIntegral R N k) :=
  haveI : Module.IsTorsionFree ℤ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    Module.IsTorsionFree.trans ℂ
  inferInstance

end Finite

/-- **Bounded denominators for the diamond translates.** The `ℂ`-span of the forms on `Γ₁(N)`
whose diamond translates have integer coefficients at `∞` equals the `ℂ`-span of those whose
diamond translates have rational coefficients there. A rational form has finitely many diamond
translates, each with bounded denominators, so one integer multiple of it is integral. -/
theorem span_diamondIntegral_int_eq_span_diamondIntegral_rat :
    Submodule.span ℂ (diamondIntegral (Int.castRingHom ℂ).range N k :
      Set (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      Submodule.span ℂ (diamondIntegral (Rat.castHom ℂ).range N k :
        Set (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  refine le_antisymm (Submodule.span_mono (diamondIntegral_mono ?_)) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, by simp⟩
  intro f hf
  -- a denominator for each diamond translate, and their product for all of them
  choose D hD hint using fun d : (ZMod N)ˣ ↦
    CuspForm.exists_nsmul_qExpansion_coeff_eq_intCast (diamondOpCusp k d f) fun n ↦ by
      obtain ⟨r, hr⟩ := hf d n
      exact ⟨r, by simpa using hr.symm⟩
  set E := ∏ d, D d
  have hE : (E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun d _ ↦ hD d)
  have hEf : (E : ℂ) • f ∈ diamondIntegral (Int.castRingHom ℂ).range N k := fun d n ↦ by
    obtain ⟨z, hz⟩ := hint d n
    refine ⟨(∏ e ∈ Finset.univ.erase d, D e : ℕ) * z, ?_⟩
    have hEd : E = D d * ∏ e ∈ Finset.univ.erase d, D e :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ d)).symm
    rw [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), map_smul,
      map_smul, CuspForm.qExpansionCoeffₗ_apply, smul_eq_mul, hEd]
    rw [nsmul_eq_mul] at hz
    rw [eq_intCast, Int.cast_mul, ← hz]
    push_cast
    ring
  have hf' : f = (E : ℂ)⁻¹ • ((E : ℂ) • f) := by rw [inv_smul_smul₀ hE]
  rw [SetLike.mem_coe, hf']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hEf)

end TauCeti.CuspForm
