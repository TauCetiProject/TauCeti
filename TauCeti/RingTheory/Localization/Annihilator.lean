/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Ideal

/-!
# Annihilators of finite modules commute with localization

Let `M` be a finitely generated module over a commutative semiring `R`, and let `M'` be its
localization at a submonoid `S`, a module over the localization `A` of `R` at `S`. Then

`Ann_A(M') = Ann_R(M) A`.

An element `r / s` annihilates `M'` exactly when every generator of `M` is killed by `r` after
multiplication by some element of `S`; the product of these finitely many elements of `S` then
multiplies `r` into `Ann_R(M)`. Without finite generation only the inclusion `⊇` holds.

This is the compatibility that lets the annihilators of the modules of sections of a
quasi-coherent module of finite type glue to an ideal sheaf.

## Main results

* `IsLocalizedModule.map_annihilator_le`: `Ann_R(M) A ≤ Ann_A(M')` for an arbitrary module `M`
  and an arbitrary `R`-algebra `A`.
* `IsLocalizedModule.annihilator_eq_map`: `Ann_A(M') = Ann_R(M) A` for a finite module `M`.
* `IsLocalization.map_annihilator_span_singleton`: the annihilator of an element `a` of `R`,
  extended to `A`, is the annihilator of the image of `a`.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 3.14.
-/

public section

open Submodule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*) {M M' : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')
  [IsLocalizedModule S f]

namespace IsLocalizedModule

include S f in
/-- The extension of the annihilator of `M` annihilates every localization of `M`. This holds
without any finiteness assumption on `M`, and for any `R`-algebra `A` acting compatibly on `M'`. -/
theorem map_annihilator_le [Semiring A] [Algebra R A] [Module A M'] [IsScalarTower R A M'] :
    (Module.annihilator R M).map (algebraMap R A) ≤ Module.annihilator A M' := by
  refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Module.mem_annihilator.mpr fun m' ↦ ?_
  -- Write `m' = f m / s`; then `r • m' = f (r • m) / s = 0`.
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f m'
  simp [algebraMap_smul, ← IsLocalizedModule.mk'_smul, Module.mem_annihilator.mp hr]

include f in
/-- **Annihilators of finite modules commute with localization.** If `M` is a finite `R`-module
and `f : M → M'` is the localization of `M` at a submonoid `S`, with `A` the localization of `R`
at `S`, then the annihilator of `M'` over `A` is the extension of the annihilator of `M`. -/
theorem annihilator_eq_map [CommSemiring A] [Algebra R A] [IsLocalization S A] [Module A M']
    [IsScalarTower R A M'] [Module.Finite R M] :
    Module.annihilator A M' = (Module.annihilator R M).map (algebraMap R A) := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (map_annihilator_le S A f)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  -- Each element `m` of `M` is killed by `r` after multiplication by some `t m ∈ S`.
  have hgen (m : M) : ∃ t : S, (t : R) • r • m = 0 := by
    have hfm : f (r • m) = 0 := calc
      f (r • m) = (IsLocalization.mk' A r s * algebraMap R A s) • f m := by
        rw [map_smul, IsLocalization.mk'_spec, algebraMap_smul]
      _ = 0 := by rw [mul_smul, Module.mem_annihilator.mp hx]
    simpa [Submonoid.smul_def] using (IsLocalizedModule.eq_zero_iff S f).mp hfm
  choose t ht using hgen
  -- The product `u` of the `t m` over the generators multiplies `r` into `Ann_R(M)`, so
  -- `r / s = (u * r) / (u * s)` lies in the extension of `Ann_R(M)`.
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  refine ⟨∏ m ∈ T, (t m : R), S.prod_mem fun m _ ↦ (t m).2, ?_⟩
  rw [← Submodule.annihilator_top, ← hT, Submodule.mem_annihilator_span]
  rintro ⟨m, hm⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun m ↦ (t m : R)) hm
  rw [hc, mul_comm _ c, mul_assoc, mul_smul, mul_smul, ht m, smul_zero]

end IsLocalizedModule

namespace IsLocalization

variable [CommSemiring A] [Algebra R A] [IsLocalization S A]

include S in
/-- **The annihilator of an element commutes with localization.** The ideal of elements of the
localization `A` killing the image of `a` is the extension of the ideal of elements of `R` killing
`a`. This is the cyclic case `M = R ∙ a` of `IsLocalizedModule.annihilator_eq_map`, stated for the
principal ideal `(a)` of `R` and its image in `A` rather than for an abstract localized module. -/
theorem map_annihilator_span_singleton (a : R) :
    (Ideal.span {a}).annihilator.map (algebraMap R A) =
      (Ideal.span {algebraMap R A a}).annihilator := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun y hy ↦ ?_
  · simp_all [Ideal.span, mem_annihilator_span_singleton, ← map_mul]
  · -- Write `y = x / s`; then `y * a = 0` means that `t * x * a = 0` for some `t ∈ S`.
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S y
    rw [Ideal.span, mem_annihilator_span_singleton, smul_eq_mul, mul_comm,
      IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨t, ht⟩ := hy
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨t, t.2, ?_⟩
    rw [Ideal.span, mem_annihilator_span_singleton, smul_eq_mul, mul_assoc, mul_comm x, ht]

end IsLocalization
