/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Tensoring a contraction with a fixed differential module

A graded contraction `M ⇄ N` extends to `M ⊗ P ⇄ N ⊗ P` for the signed tensor
endomorphisms `d ⊗ 1 + ε ⊗ dP`. The maps are `i ⊗ 1`, `p ⊗ 1`, and `h ⊗ 1`.
The two mixed homotopy terms cancel because the degree-minus-one homotopy
anticommutes with the parity operator. Special contractions remain special.

This construction applies in particular with `P` the bar coalgebra of an
A-infinity algebra, before perturbing by the higher module operations.
No square-zero assumption is needed for the contraction identities themselves.

The convention follows Gugenheim--Lambe--Stasheff,
*Perturbation theory in differential homological algebra II*.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uM uN uP

variable {R : Type uR} [CommRing R]
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  {dM : Module.End R M} {dN : Module.End R N}
  (G : InternalGrading R M) (H : InternalGrading R N) (dP : Module.End R P)

namespace LinearContraction

variable (c : LinearContraction dM dN)
  (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
  (hi : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
  (hp : LinearMap.IsHomogeneous c.proj G.piece H.piece 0)

/-- Tensor a graded contraction on the right with a fixed module with endomorphism.
The tensor endomorphisms use the Koszul sign on the second summand. -/
noncomputable def tensorRight :
    LinearContraction
      (TensorProduct.map dM LinearMap.id + TensorProduct.map (G.koszulTwist 1) dP)
      (TensorProduct.map dN LinearMap.id + TensorProduct.map (H.koszulTwist 1) dP) where
  incl := c.incl.rTensor P
  proj := c.proj.rTensor P
  homotopy := c.homotopy.rTensor P
  dM_comp_incl := by
    apply TensorProduct.ext'
    intro x y
    have h := hi.koszulTwist_apply 1 x
    simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at h
    simp [h]
  proj_comp_dM := by
    apply TensorProduct.ext'
    intro x y
    have h := hp.koszulTwist_apply 1 x
    simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at h
    simp [h]
  proj_comp_incl := by ext x y; simp
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply TensorProduct.ext'
    intro x y
    have h := hh.koszulTwist_apply 1 x
    simp only [one_mul, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg,
      Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at h
    have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at hc
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      TensorProduct.map_tmul, LinearMap.id_apply, map_add, LinearMap.sub_apply]
    rw [h, TensorProduct.neg_tmul]
    calc
      _ = (dM (c.homotopy x) + c.homotopy (dM x)) ⊗ₜ[R] y := by
        rw [TensorProduct.add_tmul]
        abel
      _ = _ := by rw [hc, TensorProduct.sub_tmul]

@[simp]
theorem tensorRight_incl : (c.tensorRight G H dP hh hi hp).incl = c.incl.rTensor P := (rfl)

@[simp]
theorem tensorRight_proj : (c.tensorRight G H dP hh hi hp).proj = c.proj.rTensor P := (rfl)

@[simp]
theorem tensorRight_homotopy :
    (c.tensorRight G H dP hh hi hp).homotopy = c.homotopy.rTensor P := (rfl)

end LinearContraction

namespace LinearSpecialContraction

variable (c : LinearSpecialContraction dM dN)
  (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
  (hi : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
  (hp : LinearMap.IsHomogeneous c.proj G.piece H.piece 0)

/-- Tensoring a graded special contraction with a fixed differential module preserves
all three side conditions. -/
noncomputable def tensorRight :
    LinearSpecialContraction
      (TensorProduct.map dM LinearMap.id + TensorProduct.map (G.koszulTwist 1) dP)
      (TensorProduct.map dN LinearMap.id + TensorProduct.map (H.koszulTwist 1) dP) where
  toLinearContraction := c.toLinearContraction.tensorRight G H dP hh hi hp
  homotopy_comp_incl := by ext x y; simp
  proj_comp_homotopy := by ext x y; simp
  homotopy_comp_homotopy := by ext x y; simp

@[simp]
theorem tensorRight_incl : (c.tensorRight G H dP hh hi hp).incl = c.incl.rTensor P := (rfl)

@[simp]
theorem tensorRight_proj : (c.tensorRight G H dP hh hi hp).proj = c.proj.rTensor P := (rfl)

@[simp]
theorem tensorRight_homotopy :
    (c.tensorRight G H dP hh hi hp).homotopy = c.homotopy.rTensor P := (rfl)

end LinearSpecialContraction

end TauCeti
