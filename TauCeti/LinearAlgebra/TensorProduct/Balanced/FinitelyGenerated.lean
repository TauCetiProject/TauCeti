/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite support in balanced tensor products

A balanced tensor whose right-module factor is a submodule `I` already comes
from tensoring a finitely generated submodule of `I`. This reduction lets
one test injectivity of tensoring inclusions of right ideals on finitely
generated right ideals. It uses Mathlib's
`Submodule.exists_fg_le_eq_rTensor_inclusion` on the tensor over `ℤ`
before taking the balanced quotient.
-/

public section

open MulOpposite

namespace Submodule

open TauCeti
open TauCeti.BalancedTensorProduct (map_tmul mkQ_tmul)

variable {A P M : Type*} [Ring A]
  [AddCommGroup P] [Module Aᵐᵒᵖ P] [AddCommGroup M] [Module A M]

/-- Every balanced tensor over a right submodule `I` is the image of a tensor over a
finitely generated right submodule contained in `I`. -/
theorem exists_fg_le_eq_balancedTensor_map_inclusion (I : Submodule Aᵐᵒᵖ P)
    (x : BalancedTensorProduct ℤ A I M) :
    ∃ (J : Submodule Aᵐᵒᵖ P) (_ : J.FG) (hJI : J ≤ I)
      (y : BalancedTensorProduct ℤ A J M),
      x = BalancedTensorProduct.map ((J.inclusion hJI).restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
        (fun a j ↦ (J.inclusion hJI).map_smul (op a) j) (fun _ _ ↦ rfl) y := by
  obtain ⟨t, rfl⟩ := BalancedTensorProduct.mkQ_surjective ℤ A x
  obtain ⟨S, ⟨s, hs⟩, hSI, t, rfl⟩ :=
    Submodule.exists_fg_le_eq_rTensor_inclusion (I := I.restrictScalars ℤ) t
  let J : Submodule Aᵐᵒᵖ P := Submodule.span Aᵐᵒᵖ (s : Set P)
  have hSJ : S ≤ J.restrictScalars ℤ := hs ▸ Submodule.span_le.mpr Submodule.subset_span
  have hJI : J ≤ I := Submodule.span_le.mpr fun p hp ↦
    hSI (hs ▸ Submodule.subset_span hp)
  let i : S →ₗ[ℤ] I := S.inclusion hSI
  let j : S →ₗ[ℤ] J := S.inclusion hSJ
  let f := BalancedTensorProduct.map ((J.inclusion hJI).restrictScalars ℤ)
    (LinearMap.id : M →ₗ[ℤ] M) (fun a p ↦ (J.inclusion hJI).map_smul (op a) p) (fun _ _ ↦ rfl)
  refine ⟨J, Submodule.fg_span s.finite_toSet, hJI,
    BalancedTensorProduct.mkQ ℤ A (j.rTensor M t), ?_⟩
  have h : (BalancedTensorProduct.mkQ ℤ A).comp (i.rTensor M) =
      f.comp ((BalancedTensorProduct.mkQ ℤ A).comp (j.rTensor M)) := by
    apply TensorProduct.ext'
    intro p m
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, mkQ_tmul]
    exact (map_tmul ((J.inclusion hJI).restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
      (fun a j ↦ (J.inclusion hJI).map_smul (op a) j) (fun _ _ ↦ rfl) (j p) m).symm
  exact DFunLike.congr_fun h t

end Submodule
