/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.NumberTheory.ModularForms.SturmBound
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Modular forms with integral `q`-expansions at every cusp

For a subring `R ⊆ ℂ` and an arithmetic subgroup `Γ` of determinant one, the forms of weight `k`
whose `q`-expansions at *every* cusp have all their coefficients in `R` form a `ℤ`-submodule
`ModularForm.integralAtCusps R Γ k` of `M_k(Γ)`. The cusp expansions are those of the translates
`f ∣ γ` for `γ ∈ SL₂(ℤ)` (`ModularForm.qExpansionAt`), so no choice of cusp representatives is
involved.

This is the integral structure of Deligne–Serre's lattice argument for the algebraicity of the
Hecke eigenvalues, which works in every weight, including weight one, where no cohomological
lattice is available. Integrality is required at all cusps, and not only at `∞`, because the
operators of that argument move the cusps: a diamond operator turns the expansion at one cusp
into the expansion at another, and so preserves the submodule; in Deligne–Serre the expansion of
`Tₚ f` at a cusp is likewise assembled from expansions of `f` at other cusps.

## Main definitions

* `TauCeti.ModularForm.integralAtCusps R Γ k`: the forms in `M_k(Γ)` whose `q`-expansions at
  every cusp have coefficients in `R`.

## Main results

* `TauCeti.ModularForm.smul_mem_integralAtCusps`: the submodule is stable under scaling by `R`.
* `TauCeti.ModularForm.mul_mem_integralAtCusps`: products of integral forms are integral.
* `TauCeti.ModularForm.instFiniteIntegralAtCusps`, `TauCeti.ModularForm.instFreeIntegralAtCusps`:
  when `R` is a finitely generated abelian group, as is the ring of integers of a number field,
  the integral forms make up a finite free `ℤ`-module. Finiteness comes from the Sturm bound,
  which embeds them into finitely many copies of `R` through the first coefficients at `∞`.
* `TauCeti.ModularForm.diamondOp_mem_integralAtCusps`: on `Γ₁(N)` the integral forms are
  stable under the diamond operators.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, Proposition 2.7.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.ModularForm

variable (R : Subring ℂ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] [Γ.IsArithmetic] (k : ℤ)

/-- The modular forms of weight `k` on `Γ` whose `q`-expansions at every cusp have all their
coefficients in the subring `R` of `ℂ`, as a `ℤ`-submodule of `M_k(Γ)`. The expansion at the cusp
represented by `γ ∈ SL₂(ℤ)` is `ModularForm.qExpansionAt γ`. -/
noncomputable def integralAtCusps : Submodule ℤ (ModularForm Γ k) where
  carrier := {f | ∀ (γ : SL(2, ℤ)) (n : ℕ), (qExpansionAt γ f).coeff n ∈ R}
  add_mem' hf hg γ n := by simpa only [map_add] using R.add_mem (hf γ n) (hg γ n)
  zero_mem' γ n := by
    rw [map_zero, map_zero]
    exact R.zero_mem
  smul_mem' c f hf γ n := by
    rw [map_zsmul, map_zsmul]
    exact R.zsmul_mem (hf γ n) c

variable {R Γ k}

/-- Membership in the integral forms: every coefficient of every cusp expansion lies in `R`. -/
theorem mem_integralAtCusps_iff {f : ModularForm Γ k} :
    f ∈ integralAtCusps R Γ k ↔ ∀ (γ : SL(2, ℤ)) (n : ℕ), (qExpansionAt γ f).coeff n ∈ R :=
  Iff.rfl

/-- The coefficients at `∞` of an integral form lie in `R`. -/
theorem qExpansion_coeff_mem_of_mem_integralAtCusps {f : ModularForm Γ k}
    (hf : f ∈ integralAtCusps R Γ k) (n : ℕ) :
    (qExpansion Γ.strictWidthInfty f).coeff n ∈ R := by
  simpa only [qExpansionAt_one] using hf 1 n

/-- The integral forms are stable under scaling by elements of `R`. -/
theorem smul_mem_integralAtCusps {r : ℂ} (hr : r ∈ R) {f : ModularForm Γ k}
    (hf : f ∈ integralAtCusps R Γ k) : r • f ∈ integralAtCusps R Γ k := fun γ n ↦ by
  rw [map_smul, PowerSeries.coeff_smul, smul_eq_mul]
  exact R.mul_mem hr (hf γ n)

/-- The product of integral forms is integral. -/
theorem mul_mem_integralAtCusps {k₁ k₂ : ℤ} {f : ModularForm Γ k₁} {g : ModularForm Γ k₂}
    (hf : f ∈ integralAtCusps R Γ k₁) (hg : g ∈ integralAtCusps R Γ k₂) :
    f.mul g ∈ integralAtCusps R Γ (k₁ + k₂) := fun γ n ↦ by
  rw [qExpansionAt_mul, PowerSeries.coeff_mul]
  exact R.sum_mem fun x _ ↦ R.mul_mem (hf γ x.1) (hg γ x.2)

section Finite

variable (R Γ k)

/-- The number of coefficients at `∞` that determine a form of weight `k` on `Γ`, one more
than the Sturm bound. -/
private noncomputable def sturmLength : ℕ :=
  (k * Nat.card (𝒮ℒ ⧸ Γ.subgroupOf 𝒮ℒ)).toNat / 12 + 1

/-- The first `sturmLength Γ k` coefficients at `∞` of an integral form, as elements of `R`. -/
private noncomputable def truncCoeffs : integralAtCusps R Γ k →ₗ[ℤ] Fin (sturmLength Γ k) → R where
  toFun f i := ⟨(qExpansionAt 1 (f : ModularForm Γ k)).coeff i, f.2 1 i⟩
  map_add' f g := by
    ext i
    simp
  map_smul' c f := by
    ext i
    simp

private theorem truncCoeffs_injective : Function.Injective (truncCoeffs R Γ k) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ Subtype.ext ?_
  refine TauCeti.ModularForm.sturm_bound_finiteIndex (f : ModularForm Γ k)
    (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
      (PowerSeries.nat_le_order _ _ fun i hi ↦ ?_))
  have hcoeff := congrArg (fun F ↦ (F ⟨i, hi⟩ : ℂ)) hf
  simpa [truncCoeffs, qExpansionAt_one] using hcoeff

/-- When `R` is a finitely generated abelian group, the integral forms make up a finitely
generated `ℤ`-module: by the Sturm bound they embed into finitely many copies of `R`. -/
instance instFiniteIntegralAtCusps [Module.Finite ℤ R] : Module.Finite ℤ (integralAtCusps R Γ k) :=
  Module.Finite.of_injective (truncCoeffs R Γ k) (truncCoeffs_injective R Γ k)

/-- When `R` is a finitely generated abelian group, the integral forms make up a free
`ℤ`-module of finite rank. -/
instance instFreeIntegralAtCusps [Module.Finite ℤ R] : Module.Free ℤ (integralAtCusps R Γ k) :=
  haveI : Module.IsTorsionFree ℤ (ModularForm Γ k) := Module.IsTorsionFree.trans ℂ
  inferInstance

end Finite

/-- On `Γ₁(N)` the integral forms are stable under the diamond operators, which permute the
cusp expansions. -/
theorem diamondOp_mem_integralAtCusps {N : ℕ} [NeZero N] (d : (ZMod N)ˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp k d f ∈ integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k := fun γ n ↦ by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective d
  rw [qExpansionAt_diamondOp k d g hg]
  exact hf _ n

end TauCeti.ModularForm
