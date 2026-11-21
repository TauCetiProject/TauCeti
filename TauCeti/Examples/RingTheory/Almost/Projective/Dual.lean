/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Projective.Dual
import TauCeti.RingTheory.Almost.Module
import TauCeti.RingTheory.Almost.ValuationRing

/-!
# Checks of almost duality

The comparison maps become isomorphisms in the almost category, including for the basic ideal,
which need not be finitely generated. A classical torsion module gives a negative control:
its dual–tensor–Hom comparison is not an almost isomorphism. The zero setup nevertheless
accepts the same comparison, as all its modules are almost zero.
-/

open CategoryTheory LinearMap Module TensorProduct
open TauCeti.Almost TauCeti.Almost.BasicSetup

universe u

variable {V : Type u} [CommRing V] (S : BasicSetup V)

-- These are actual isomorphisms in the Serre quotient, not bijections of ordinary modules.
example {M N : Type u} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]
    (h : S.IsAlmostFiniteProjective M) :
    IsIso ((TauCeti.Almost.Module.toAlmost S).map
      (ModuleCat.ofHom (dualTensorHom V M N) :
        ModuleCat.of V (Dual V M ⊗[V] N) ⟶ ModuleCat.of V (M →ₗ[V] N))) :=
  (TauCeti.Almost.Module.isIso_toAlmost_map_iff S _).mpr h.isAlmostIso_dualTensorHom

-- The basic ideal is allowed even when it is not finite as an ordinary module.
example : S.IsAlmostIso (M := S.ideal) (N := Dual V (Dual V S.ideal)) (Dual.eval V S.ideal) :=
  (S.isAlmostIso_subtype.isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective S)).isAlmostIso_eval

example : S.IsAlmostFiniteProjective (Dual V S.ideal) :=
  (S.isAlmostIso_subtype.isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective S)).dual

-- In particular, almost reflexivity applies to a genuinely non-finite module.
example {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    (h : ¬ (IsLocalRing.maximalIdeal O).FG) :
    ¬ Module.Finite O (IsLocalRing.maximalIdeal O) ∧
      (ofValuationRing h).IsAlmostIso
        (M := IsLocalRing.maximalIdeal O) (N := Dual O (Dual O (IsLocalRing.maximalIdeal O)))
        (Dual.eval O (IsLocalRing.maximalIdeal O)) := by
  refine ⟨fun hf ↦ h (Module.Finite.iff_fg.mp hf), ?_⟩
  have hm : (ofValuationRing h).IsAlmostFiniteProjective (IsLocalRing.maximalIdeal O) := by
    rw [← ofValuationRing_ideal h]
    exact (isAlmostIso_subtype _).isAlmostFiniteProjective_iff.mpr
      (isAlmostFiniteProjective_of_finite_of_projective _)
  exact hm.isAlmostIso_eval

-- The hypothesis is essential: the identity of ℤ/2 cannot be represented by dual tensors.
example : ¬ (classical ℤ).IsAlmostIso
    (M := Dual ℤ (ZMod 2) ⊗[ℤ] ZMod 2) (N := ZMod 2 →ₗ[ℤ] ZMod 2)
    (dualTensorHom ℤ (ZMod 2) (ZMod 2)) := by
  intro h
  obtain ⟨t, ht⟩ := (isAlmostIso_classical_iff.mp h).surjective 1
  have := Module.Projective.of_one_mem_range_dualTensorHom ⟨t, ht⟩
  have h₂ : IsSMulRegular ℤ (2 : ℤ) := .of_ne_zero two_ne_zero
  exact one_ne_zero (h₂.of_flat (S := ZMod 2) (a₁ := 1) (a₂ := 0) (by decide))

-- The same torsion example is an almost isomorphism for the zero setup.
example : (zero ℤ).IsAlmostIso
    (M := Dual ℤ (ZMod 2) ⊗[ℤ] ZMod 2) (N := ZMod 2 →ₗ[ℤ] ZMod 2)
    (dualTensorHom ℤ (ZMod 2) (ZMod 2)) :=
  (isAlmostFiniteProjective_zero (N := ZMod 2)).isAlmostIso_dualTensorHom

-- A free rank-two example fixes the evaluation convention: (2,3) pairs with (5,7) to give 31.
example : Dual.eval ℤ (Fin 2 → ℤ) ![2, 3]
    (5 • LinearMap.proj 0 + 7 • LinearMap.proj 1) = 31 := by
  norm_num [Dual.eval_apply]
