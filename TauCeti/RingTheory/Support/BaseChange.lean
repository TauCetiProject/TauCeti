/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.FittingIdeal.Determinant

/-!
# Annihilators of finite modules after scalar extension

A finite module that vanishes after scalar extension has unit extended annihilator.
This detects vanishing after base change, and hence spanning of finite-module quotients,
through an ideal in the original coefficient ring. More generally, a unit extended quotient
annihilator forces the image of a semilinear map into any submodule containing the defining
submodule’s image.
-/

public section

open TensorProduct

namespace TauCeti.Module

/-- If the base change of a finite `A`-module `C` to an `A`-algebra `B` vanishes, then the
annihilator of `C` generates the unit ideal of `B`. -/
theorem annihilator_map_eq_top_of_subsingleton_tensorProduct {A B C : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup C] [Module A C] [Module.Finite A C]
    [Subsingleton (B ⊗[A] C)] :
    (Module.annihilator A C).map (algebraMap A B) = ⊤ := by
  apply top_le_iff.mp
  rw [← (TauCeti.fittingIdeal_zero_map_eq_top_iff (R := A) (M := C) B).mpr inferInstance]
  exact Ideal.map_mono TauCeti.fittingIdeal_zero_le_annihilator

end TauCeti.Module

/-- If the extended annihilator of a quotient is the unit ideal, a semilinear map carrying
its defining submodule into a target submodule carries every element into that submodule. -/
theorem LinearMap.apply_mem_of_annihilator_quotient_map_eq_top
    {R S M P : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module S P] {φ : R →+* S} (f : M →ₛₗ[φ] P)
    (N : Submodule R M) (Q : Submodule S P) (hN : N ≤ Q.comap f)
    (hunit : (Module.annihilator R (M ⧸ N)).map φ = ⊤) (x : M) : f x ∈ Q := by
  have h1 : (1 : S) ∈ (Module.annihilator R (M ⧸ N)).map φ := hunit ▸ Submodule.mem_top
  suffices ∀ b ∈ (Module.annihilator R (M ⧸ N)).map φ, b • f x ∈ Q by
    simpa using this 1 h1
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨a, ha, rfl⟩ := hb
    rw [← f.map_smulₛₗ]
    apply hN
    have h := Module.mem_annihilator.mp ha (Submodule.Quotient.mk x)
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  | zero => simp
  | add x y _ _ hx hy => simpa [add_smul] using add_mem hx hy
  | smul c x _ hx => simpa [mul_smul] using Q.smul_mem c hx
