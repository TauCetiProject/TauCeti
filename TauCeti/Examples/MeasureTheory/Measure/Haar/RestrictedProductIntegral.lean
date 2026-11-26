/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.MeasureTheory.Measure.Count.Topology
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Integral

/-!
# Checks for integrals of factorizable functions on restricted products

Three instances of `TauCeti.integral_restrictedAddHaar_finprod`, which computes the integral of a
factorizable function `x ↦ ∏ᶠ i, f i (x i)` over a restricted product as the finitary product of
the local integrals, on copies of `C₂ = ZMod 2` with counting measure and reference subgroup `C₂`:

* with no factors, the empty product `1` has integral `1` over the one-point group
  (`TauCeti.RestrictedProductIntegralChecks.integral_finprod_empty`);
* on one copy, the constant function `2` has integral `4`
  (`TauCeti.RestrictedProductIntegralChecks.integral_finprod_unit`);
* on two copies, the constants `2` and `3` have product integral `4 · 6 = 24`
  (`TauCeti.RestrictedProductIntegralChecks.integral_finprod_two`).

Counting measure on `C₂` has total mass `2`; probability normalization would give `2` and `6` in
the last two cases.
-/

public section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct
open scoped RestrictedProduct

namespace TauCeti.RestrictedProductIntegralChecks

/-- The reference subgroups `C₂` of `ZMod 2` are open. -/
local instance factIsOpenTop (ι : Type) :
    Fact (∀ _ : ι, IsOpen ((⊤ : AddSubgroup (ZMod 2)) : Set (ZMod 2))) :=
  ⟨fun _ ↦ isOpen_univ⟩

/-- Over a finite index set the normalization hypothesis holds vacuously. -/
theorem eventually_count_top (ι : Type) [Finite ι] :
    ∀ᶠ _ : ι in cofinite, (count : Measure (ZMod 2)) (⊤ : AddSubgroup (ZMod 2)) = 1 := by
  simp [Filter.cofinite_eq_bot]

/-- A constant function on `C₂` has counting integral twice its value. -/
theorem integral_count_const (c : ℝ) : ∫ _ : ZMod 2, c ∂count = 2 * c := by
  rw [integral_const, smul_eq_mul, measureReal_def, count_univ]
  simp

/-- With no factors, the empty product `1` has integral `1` over the one-point group. -/
theorem integral_finprod_empty :
    ∫ x, ∏ᶠ i, (fun (_ : Empty) (_ : ZMod 2) ↦ (2 : ℝ)) i (x i)
      ∂restrictedAddHaar (fun _ : Empty ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count)
        (eventually_count_top Empty) = 1 := by
  have h := integral_restrictedAddHaar_finprod (𝕜 := ℝ)
    (fun _ : Empty ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count) (eventually_count_top Empty)
    (f := fun (_ : Empty) (_ : ZMod 2) ↦ (2 : ℝ)) (by simp [Filter.cofinite_eq_bot])
  exact h.trans (finprod_of_isEmpty _)

/-- On one copy of `C₂` with counting measure, the constant function `2` has integral `4`. -/
theorem integral_finprod_unit :
    ∫ x, ∏ᶠ i, (fun (_ : Unit) (_ : ZMod 2) ↦ (2 : ℝ)) i (x i)
      ∂restrictedAddHaar (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count)
        (eventually_count_top Unit) = 4 := by
  have h := integral_restrictedAddHaar_finprod (𝕜 := ℝ)
    (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count) (eventually_count_top Unit)
    (f := fun (_ : Unit) (_ : ZMod 2) ↦ (2 : ℝ)) (by simp [Filter.cofinite_eq_bot])
  refine h.trans ?_
  rw [finprod_unique, integral_count_const]
  norm_num

/-- On two copies of `C₂` with counting measure, the constants `2` and `3` have product integral
`4 · 6 = 24`. -/
theorem integral_finprod_two :
    ∫ x, ∏ᶠ i, (fun (i : Fin 2) (_ : ZMod 2) ↦ ![(2 : ℝ), 3] i) i (x i)
      ∂restrictedAddHaar (fun _ : Fin 2 ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count)
        (eventually_count_top (Fin 2)) = 24 := by
  have h := integral_restrictedAddHaar_finprod (𝕜 := ℝ)
    (fun _ : Fin 2 ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count) (eventually_count_top (Fin 2))
    (f := fun (i : Fin 2) (_ : ZMod 2) ↦ ![(2 : ℝ), 3] i) (by simp [Filter.cofinite_eq_bot])
  refine h.trans ?_
  rw [finprod_eq_prod_of_fintype, Fin.prod_univ_two, integral_count_const, integral_count_const]
  norm_num

end TauCeti.RestrictedProductIntegralChecks
