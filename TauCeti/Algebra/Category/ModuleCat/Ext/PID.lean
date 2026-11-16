/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.Category.ModuleCat.Ext.Basic
import TauCeti.Algebra.Homology.Ext.Basic

/-!
# `Ext` groups of finitely generated modules over principal ideal domains

Over a principal ideal domain `R`, the torsion-free quotient `A ⧸ Submodule.torsion R A` of any
finitely generated `R`-module `A` is finite free, hence projective. In positive degree `n + 1`,
restriction along `Submodule.torsion R A → A` is therefore injective on `Ext`, and since
`Submodule.torsion R A` is finitely generated and torsion it is annihilated by a single nonzero
scalar, making `Ext A Y (n + 1)` a torsion `R`-module (`ModuleCat.isTorsion_ext_succ_of_finite`).
-/

public section

open CategoryTheory Abelian

universe v u

namespace ModuleCat

/-- Over a principal ideal domain, `Ext^{n + 1}(A, Y)` is a torsion `R`-module whenever `A` is
finitely generated. -/
theorem isTorsion_ext_succ_of_finite {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Small.{v} R] (A Y : ModuleCat.{v} R) [Module.Finite R A] (n : ℕ) :
    Module.IsTorsion R (Ext.{v} A Y (n + 1)) := by
  let T := Submodule.torsion R A
  let Q := A ⧸ T
  have : Module.Free R Q := Module.free_of_finite_type_torsion_free'
  have : Projective (ModuleCat.of R Q) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R Q)
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (ModuleCat.ofHom T.subtype) (ModuleCat.ofHom T.mkQ) (by ext; simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff _).2 fun x hx ↦
        ⟨⟨x, (Submodule.Quotient.mk_eq_zero T).1 hx⟩, rfl⟩
      mono_f := (ModuleCat.mono_iff_injective _).2 T.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).2 T.mkQ_surjective }
  obtain ⟨r, hr_ann, hr_mem⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := R) (M := A))
  have hrT : r ∈ Module.annihilator R (ModuleCat.of R T) :=
    Module.mem_annihilator.2 fun x ↦ Submodule.mem_annihilator.1 hr_ann x Submodule.mem_top
  intro e
  refine ⟨⟨r, hr_mem⟩, ?_⟩
  rw [Submonoid.smul_def]
  have hzero : Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add (n + 1)) (r • e) = 0 := by
    rw [map_smul, Ext.smul_eq_zero_of_mem_annihilator_left hrT]
  obtain ⟨q, hq⟩ := (TauCeti.exact_precompOfLinear R hS Y (n + 1) (r • e)).1 hzero
  rw [Ext.eq_zero_of_projective q, map_zero] at hq
  exact hq.symm

end ModuleCat
