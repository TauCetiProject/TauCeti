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

/-- Over a finite index set, `integral_restrictedAddHaar_finprod` applies to copies of `C₂` with
counting measure and reference subgroup `C₂`. -/
private theorem integral_finprod_count (ι : Type) [Finite ι] (f : ι → ZMod 2 → ℝ)
    (h : ∀ᶠ _ : ι in cofinite, (count : Measure (ZMod 2)) (⊤ : AddSubgroup (ZMod 2)) = 1) :
    ∫ x, ∏ᶠ i, f i (x i)
      ∂restrictedAddHaar (fun _ : ι ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count) h =
      ∏ᶠ i, ∫ y, f i y ∂count :=
  integral_restrictedAddHaar_finprod _ _ h (by simp [Filter.cofinite_eq_bot])

/-- With no factors, the empty product `1` has integral `1` over the one-point group. -/
theorem integral_finprod_empty :
    ∫ x, ∏ᶠ i, (fun (_ : Empty) (_ : ZMod 2) ↦ (2 : ℝ)) i (x i)
      ∂restrictedAddHaar (fun _ : Empty ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count)
        (by simp [Filter.cofinite_eq_bot]) = 1 :=
  (integral_finprod_count Empty (fun _ _ ↦ 2) _).trans (finprod_of_isEmpty _)

/-- On one copy of `C₂` with counting measure, the constant function `2` has integral `4`. -/
theorem integral_finprod_unit :
    ∫ x, ∏ᶠ i, (fun (_ : Unit) (_ : ZMod 2) ↦ (2 : ℝ)) i (x i)
      ∂restrictedAddHaar (fun _ : Unit ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count)
        (by simp [Filter.cofinite_eq_bot]) = 4 := by
  refine (integral_finprod_count Unit (fun _ _ ↦ 2) _).trans ?_
  norm_num [finprod_unique]

/-- On two copies of `C₂` with counting measure, the constants `2` and `3` have product integral
`4 · 6 = 24`. -/
theorem integral_finprod_two :
    ∫ x, ∏ᶠ i, (fun (i : Fin 2) (_ : ZMod 2) ↦ ![(2 : ℝ), 3] i) i (x i)
      ∂restrictedAddHaar (fun _ : Fin 2 ↦ (⊤ : AddSubgroup (ZMod 2))) (fun _ ↦ count)
        (by simp [Filter.cofinite_eq_bot]) = 24 := by
  refine (integral_finprod_count (Fin 2) (fun i _ ↦ ![2, 3] i) _).trans ?_
  norm_num [finprod_eq_prod_of_fintype, Fin.prod_univ_two]

end TauCeti.RestrictedProductIntegralChecks
