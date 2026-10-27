/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic

/-!
# Annihilators of `Ext` groups of modules

For modules `N` and `M` over a commutative ring `R`, the `R`-module `Ext N M n` is killed both by
the annihilator of `N` and by the annihilator of `M`, since multiplication by `r` on `Ext N M n`
is induced by multiplication by `r` on either argument. In particular `Ext N M n` vanishes when
these two annihilators are comaximal, for example `Ext (R ⧸ I) M n = 0` when `I M = M` for a
finite module `M`.

## Main results

* `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator_left` and
  `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator_right`: elements of the annihilator
  of either argument act by zero on `Ext N M n`.
* `CategoryTheory.Abelian.Ext.subsingleton_of_annihilator_sup_eq_top`: `Ext N M n` vanishes when
  the annihilators of `N` and `M` are comaximal.
-/

public section

universe v u

open CategoryTheory

namespace CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] {N M : ModuleCat.{v} R}

/-- An element of the annihilator of `N` acts by zero on `Ext N M n`. This restates
`Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` as a statement about the scalar action. -/
theorem Ext.smul_eq_zero_of_mem_annihilator_left {r : R} (hr : r ∈ Module.annihilator R N)
    {n : ℕ} (x : Ext N M n) : r • x = 0 := by
  simpa [Ext.mk₀_smul] using
    congrArg (fun f ↦ f.hom x) (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator (M := M) hr n)

/-- An element of the annihilator of `M` acts by zero on `Ext N M n`. -/
theorem Ext.smul_eq_zero_of_mem_annihilator_right {r : R} (hr : r ∈ Module.annihilator R M)
    {n : ℕ} (x : Ext N M n) : r • x = 0 := by
  have : r • 𝟙 M = 0 := by
    simp [← ModuleCat.lsmul_eq_smul_id, Module.mem_annihilator_iff_lsmul_eq_zero.mp hr]
  rw [← Ext.comp_mk₀_id x, ← Ext.comp_smul, ← Ext.mk₀_smul, this, Ext.mk₀_zero, Ext.comp_zero]

/-- `Ext N M n` vanishes when the annihilators of `N` and `M` are comaximal. -/
theorem Ext.subsingleton_of_annihilator_sup_eq_top
    (h : Module.annihilator R N ⊔ Module.annihilator R M = ⊤) (n : ℕ) :
    Subsingleton (Ext N M n) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h ▸ Submodule.mem_top : (1 : R) ∈ _)
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  rw [← one_smul R z, ← hab, add_smul, smul_eq_zero_of_mem_annihilator_left ha,
    smul_eq_zero_of_mem_annihilator_right hb, add_zero]

end CategoryTheory.Abelian
