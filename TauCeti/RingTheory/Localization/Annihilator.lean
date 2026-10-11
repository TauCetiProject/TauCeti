/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Annihilators of finite modules commute with localization

Let `M` be a finitely generated module over a commutative ring `R`, and let `M'` be its
localization at a submonoid `S`, a module over the localization `A` of `R` at `S`. Then

`Ann_A(M') = Ann_R(M) A`.

An element `r / s` annihilates `M'` exactly when every generator of `M` is killed by `r` after
multiplication by some element of `S`; the product of these finitely many elements of `S` then
multiplies `r` into `Ann_R(M)`. Without finite generation only the inclusion `⊇` holds.

This is the compatibility that lets the annihilators of the modules of sections of a
quasi-coherent module of finite type glue to an ideal sheaf.

## Main results

* `IsLocalizedModule.map_annihilator_le`: `Ann_R(M) A ≤ Ann_A(M')` for an arbitrary module `M`.
* `IsLocalizedModule.annihilator_eq_map`: `Ann_A(M') = Ann_R(M) A` for a finite module `M`.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 3.14.
-/

public section

open Submodule

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Module A M'] [IsScalarTower R A M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]

namespace IsLocalizedModule

omit [IsLocalization S A] in
include S f in
/-- The extension of the annihilator of `M` annihilates every localization of `M`. This holds
without any finiteness assumption on `M`, and for any `R`-algebra `A` acting compatibly on `M'`. -/
theorem map_annihilator_le :
    (Module.annihilator R M).map (algebraMap R A) ≤ Module.annihilator A M' := by
  refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Module.mem_annihilator.mpr fun m' ↦ ?_
  -- Write `m' = f m / s`; then `r • m' = f (r • m) / s = 0`.
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f m'
  simp [algebraMap_smul, ← IsLocalizedModule.mk'_smul, Module.mem_annihilator.mp hr]

include S f in
/-- **Annihilators of finite modules commute with localization.** If `M` is a finite `R`-module
and `f : M → M'` is the localization of `M` at a submonoid `S`, with `A` the localization of `R`
at `S`, then the annihilator of `M'` over `A` is the extension of the annihilator of `M`. -/
theorem annihilator_eq_map [Module.Finite R M] :
    Module.annihilator A M' = (Module.annihilator R M).map (algebraMap R A) := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (map_annihilator_le S A f)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj S x
  -- Each element `m` of `M` is killed by `r` after multiplication by some `t m ∈ S`.
  have hgen (m : M) : ∃ t : S, (t : R) • r • m = 0 := by
    have hfm : f (r • m) = 0 := calc
      f (r • m) = (x * algebraMap R A s) • f m := by rw [map_smul, hrs, algebraMap_smul]
      _ = 0 := by rw [mul_smul, Module.mem_annihilator.mp hx]
    simpa [Submonoid.smul_def] using (IsLocalizedModule.eq_zero_iff S f).mp hfm
  choose t ht using hgen
  -- The product `u` of the `t m` over the generators multiplies `r` into `Ann_R(M)`.
  let u : S := ∏ m ∈ T, t m
  have hu : (u : R) * r ∈ Module.annihilator R M := by
    rw [← Submodule.annihilator_top, ← hT, Submodule.mem_annihilator_span]
    rintro ⟨m, hm⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t hm
    have hcu : (u : R) * r = c * (t m * r) := by simp only [u, hc, Submonoid.coe_mul]; ring
    simp [hcu, mul_smul, ht m]
  -- `x = r / s = (u * r) / (u * s)`.
  have hx : x = algebraMap R A ((u : R) * r) * IsLocalization.mk' A (1 : R) (u * s) := by
    rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
    simp only [Submonoid.coe_mul, map_mul, ← hrs]
    ring
  rw [hx]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

end IsLocalizedModule
