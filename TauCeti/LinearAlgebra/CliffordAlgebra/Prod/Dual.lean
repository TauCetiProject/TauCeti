/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dual
public import TauCeti.LinearAlgebra.TensorProduct.Dual

/-!
# Reverse duality of graded Clifford tensor products

For a Clifford module `E` with grading `γ`, the reverse-dual action on `E*` has grading
`γᵀ`: transposition preserves the square-one and anticommutation equations. The canonical
pairing `(φ ⊗ ψ)(e ⊗ f) = φ(e) ψ(f)` identifies the graded tensor product of reverse duals
with the reverse dual of the graded tensor product. Its vector action on either side is

`c₁(v)ᵀ ⊗ 1 + γᵀ ⊗ c₂(w)ᵀ`.

No extra sign occurs in this pairing: these are reverse-dual Clifford actions, not super
transposes. Likewise the dual grading is the transpose of the chosen grading, which need
not be the intrinsic chirality of the reverse dual.

The intertwining identity holds without finiteness assumptions. For finite projective modules,
Mathlib's `TensorProduct.dualDistribEquiv` makes it an isomorphism of Clifford modules. The same
canonical map intertwines the tensor gradings by
`LinearMap.dualDistrib_comp_map_dualMap`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open CliffordAlgebra TensorProduct Module

namespace AlgHom

variable {R V W E F : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

variable (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- Tensor duality intertwines the graded product of reverse-dual actions with the reverse
dual of the graded product. This identity needs no finiteness or nondegeneracy assumption. -/
theorem dualDistrib_cliffordProdTensor (a : CliffordAlgebra (Q₁.prod Q₂)) :
    dualDistrib R E F ∘ₗ
        cliffordProdTensor ρ₁.cliffordReverseDual γ.dualMap
          (by
            rw [Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap,
              ← Module.End.mul_eq_comp, hγ]
            exact LinearMap.dualMap_id)
          (dualMap_mul_cliffordReverseDual_ι ρ₁ γ hγρ) ρ₂.cliffordReverseDual a =
      (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib R E F := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => ext z x; simp
  | ι v =>
    ext φ ψ e f
    simp [cliffordProdTensor_ι, LinearMap.rTensor]
  | add a b ha hb =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- For finite projective modules the canonical tensor-dual equivalence identifies the two
Clifford actions. In particular this applies to all finite-dimensional spinor modules. -/
theorem cliffordReverseDual_cliffordProdTensor_eq_conj
    [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F] (a : CliffordAlgebra (Q₁.prod Q₂)) :
    (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv R E F).conj
        (cliffordProdTensor ρ₁.cliffordReverseDual γ.dualMap
          (by
            rw [Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap,
              ← Module.End.mul_eq_comp, hγ]
            exact LinearMap.dualMap_id)
          (dualMap_mul_cliffordReverseDual_ι ρ₁ γ hγρ) ρ₂.cliffordReverseDual a) := by
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := (dualDistribEquiv R E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv,
    LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (dualDistrib_cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a) z).symm

end AlgHom
