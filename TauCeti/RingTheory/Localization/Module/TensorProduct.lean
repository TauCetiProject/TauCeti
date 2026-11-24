/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor kernels after localization

Localization makes a tensor map injective exactly when every element of the original tensor
kernel is killed by an element of the localization submonoid.
-/

public section

open TensorProduct LinearMap

namespace IsLocalizedModule

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- A tensor map is injective after localization exactly when its original kernel is torsion
with respect to the localization submonoid. -/
theorem lTensor_injective_iff (T : Submonoid S)
    {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
    (l : M →ₗ[S] Mp) [IsLocalizedModule T l]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    Function.Injective (f.lTensor Mp) ↔
      ∀ t : M ⊗[R] N, f.lTensor M t = 0 → ∃ s ∈ T, s • t = 0 := by
  let g := AlgebraTensorModule.rTensor R N l
  let h := AlgebraTensorModule.rTensor R N' l
  have : IsLocalizedModule T g := IsLocalizedModule.rTensor (A := S) T l
  have : IsLocalizedModule T h := IsLocalizedModule.rTensor (A := S) T l
  have square (t : M ⊗[R] N) : f.lTensor Mp (g t) = h (f.lTensor M t) := by
    simp only [g, h, AlgebraTensorModule.coe_rTensor]
    exact LinearMap.lTensor_rTensor_comm (l.restrictScalars R) f t
  constructor
  · intro hf t ht
    have hg : g t = 0 := hf (by rw [square, ht, map_zero, map_zero])
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff T (f := g)).mp hg
    exact ⟨s, s.property, hs⟩
  · intro hf
    refine IsLocalizedModule.injective_of_map_zero T g (g :=
      AlgebraTensorModule.lTensor S Mp f) fun t ht ↦ ?_
    have hh : h (f.lTensor M t) = 0 := (square t).symm.trans ht
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff T (f := h)).mp hh
    obtain ⟨u, hu, hut⟩ := hf (s.val • t) (by
      rw [← AlgebraTensorModule.coe_lTensor (A := S), map_smul]
      exact hs)
    apply IsLocalizedModule.smul_injective g (⟨u, hu⟩ * s)
    simp only [Submonoid.smul_def, Submonoid.coe_mul]
    rw [← map_smul, mul_smul, hut, map_zero, smul_zero]

end IsLocalizedModule
