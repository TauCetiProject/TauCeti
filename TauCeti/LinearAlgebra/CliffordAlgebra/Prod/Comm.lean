/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Comm
import Mathlib.Tactic.Module

/-!
# Koszul symmetry of the graded tensor product of Clifford modules

The Koszul commutor of two graded Clifford modules intertwines the tensor actions after
exchanging the quadratic-form summands by `QuadraticMap.IsometryEquiv.prodComm`. Thus the
symmetry of the tensor product has a minus sign on two odd vectors, and preserves the
product grading. The intertwining equation holds for every Clifford element, not only
for the generating vectors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section
noncomputable section

namespace AlgHom

open CliffordAlgebra TensorProduct Module.End

variable {R M₁ M₂ E F : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : Function.Involutive γ) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F) (δ : Module.End R F)
  (hδ : Function.Involutive δ) (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ))

/-- The Koszul commutor intertwines the graded Clifford tensor actions under exchange of
quadratic-form summands. -/
theorem koszulComm_cliffordProdTensor (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] F) :
    γ.koszulComm δ hγ hδ (cliffordProdTensor ρ₁ γ (LinearMap.ext hγ) hγρ ρ₂ a z) =
      cliffordProdTensor ρ₂ δ (LinearMap.ext hδ) hδρ ρ₁
        (CliffordAlgebra.map (QuadraticMap.IsometryEquiv.prodComm Q₁ Q₂).toIsometry a)
        (γ.koszulComm δ hγ hδ z) := by
  induction a using CliffordAlgebra.induction generalizing z with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hx := LinearMap.congr_fun (hγρ v.1) x
      have hy := LinearMap.congr_fun (hδρ v.2) y
      simp only [mul_apply_eq_comp, LinearMap.neg_apply] at hx hy
      simp only [map_apply_ι, QuadraticMap.IsometryEquiv.toIsometry_apply,
        QuadraticMap.IsometryEquiv.prodComm_toFun, Prod.fst_swap, Prod.snd_swap,
        cliffordProdTensor_ι_tmul, map_add, koszulComm_tmul, map_smul, map_sub,
        hγ x, hδ y, hx, hy, tmul_neg, neg_tmul]
      module
    | add a b ha hb => simp only [map_add, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | mul a b ha hb => simp only [map_mul, mul_apply_eq_comp, ha, hb]

end AlgHom
