/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Involution
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Eigenspaces of a tensor product of involutions

Let `f` and `g` be involutions of modules `X` and `Y` over a commutative ring `k` in which `2` is
invertible, so that `X = X⁺ ⊕ X⁻` and `Y = Y⁺ ⊕ Y⁻` split into their `±1`-eigenspaces. The
tensor product `f ⊗ g` is again an involution, and its eigenspaces are

`Eig(f ⊗ g, 1) ≃ X⁺ ⊗ Y⁺ × X⁻ ⊗ Y⁻`,  `Eig(f ⊗ g, -1) ≃ X⁺ ⊗ Y⁻ × X⁻ ⊗ Y⁺`.

This is the even and odd part of the tensor product of two `ℤ/2`-graded modules, each grading being
given by its parity operator. Both cases are the single statement
`Eig(f ⊗ g, μ) ≃ Eig(f, 1) ⊗ Eig(g, μ) × Eig(f, -1) ⊗ Eig(g, -μ)` for a scalar with `μ² = 1`.

No flatness is needed: each eigenspace is a direct summand, cut out by the projection
`½ (1 + μ g)` (`Module.End.eigenProjOfInvolutive`), so tensoring the inclusions stays injective.
The equivalence applies these projections to both factors, and its inverse adds the two tensor
products of the inclusions; the two pieces add up to `½ (1 + μ (f ⊗ g))`, which is the identity on
`Eig(f ⊗ g, μ)`.

## Main definitions

* `Module.End.eigenspaceTensorMapEquiv`: `Eig(f ⊗ g, μ) ≃ Eig(f, 1) ⊗ Eig(g, μ) × Eig(f, -1) ⊗
  Eig(g, -μ)` for involutions `f`, `g` and `μ * μ = 1`.

## Main results

* `Module.End.eigenspaceTensorMapEquiv_apply`: the forward map applies the tensor products of the
  eigenspace projections.
* `Module.End.coe_eigenspaceTensorMapEquiv_symm_apply`: the inverse is the sum of the two tensor
  products of the eigenspace inclusions.
-/

public section

noncomputable section

namespace Module.End

open TensorProduct

variable {k X Y : Type*} [CommRing k] [Invertible (2 : k)]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

variable {f : Module.End k X} {g : Module.End k Y}

/-- The map `Eig(f, 1) ⊗ Eig(g, μ) × Eig(f, -1) ⊗ Eig(g, -μ) → X ⊗ Y` adding the two tensor
products of the eigenspace inclusions. -/
private def eigenspaceTensorIncl (μ : k) :
    (f.eigenspace 1 ⊗[k] g.eigenspace μ) × (f.eigenspace (-1) ⊗[k] g.eigenspace (-μ)) →ₗ[k]
      X ⊗[k] Y :=
  .coprod (map (f.eigenspace 1).subtype (g.eigenspace μ).subtype)
    (map (f.eigenspace (-1)).subtype (g.eigenspace (-μ)).subtype)

omit [Invertible (2 : k)] in
private theorem eigenspaceTensorIncl_mem (μ : k)
    (p : (f.eigenspace 1 ⊗[k] g.eigenspace μ) × (f.eigenspace (-1) ⊗[k] g.eigenspace (-μ))) :
    eigenspaceTensorIncl μ p ∈ eigenspace (map f g) μ := by
  rw [mem_eigenspace_iff]
  obtain ⟨p₁, p₂⟩ := p
  simp only [eigenspaceTensorIncl, LinearMap.coprod_apply, map_add, smul_add]
  congr 1
  · induction p₁ using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [map_tmul, Submodule.subtype_apply, mem_eigenspace_iff.1 x.2,
        mem_eigenspace_iff.1 y.2, one_smul, tmul_smul]
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  · induction p₂ using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [map_tmul, Submodule.subtype_apply, mem_eigenspace_iff.1 x.2,
        mem_eigenspace_iff.1 y.2, tmul_smul, smul_tmul', smul_smul, mul_neg, mul_one, neg_neg]
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]

/-- On `X ⊗ Y` the two projections, tensored and added, are `½ (1 + μ (f ⊗ g))`. -/
private theorem eigenspaceTensorIncl_proj (hf : Function.Involutive f)
    (hg : Function.Involutive g) {μ : k} (hμ : μ * μ = 1) (z : X ⊗[k] Y) :
    map (f.eigenspace 1).subtype (g.eigenspace μ).subtype
        (map (eigenProjOfInvolutive hf (one_mul 1)) (eigenProjOfInvolutive hg hμ) z) +
      map (f.eigenspace (-1)).subtype (g.eigenspace (-μ)).subtype
        (map (eigenProjOfInvolutive hf ((neg_mul_neg (1 : k) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive hg ((neg_mul_neg μ μ).trans hμ)) z) =
      (⅟2 : k) • (z + μ • map f g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [map_tmul, Submodule.subtype_apply, coe_eigenProjOfInvolutive_apply, one_smul,
      neg_smul, tmul_add, add_tmul, ← smul_tmul', tmul_smul, smul_add, smul_neg, tmul_neg, neg_tmul]
    -- The cross terms cancel and the diagonal terms double, which `2 * ⅟2 = 1` absorbs.
    linear_combination (norm := module)
      (⅟2 : k) • (mul_invOf_self (2 : k)) • (x ⊗ₜ[k] y + μ • (f x ⊗ₜ[k] g y))
  | add a b ha hb =>
    simp only [map_add]
    rw [add_add_add_comm, ha, hb]
    module

variable (f g) in
/-- **The eigenspaces of a tensor product of involutions.** For involutions `f` of `X` and `g` of
`Y` over a ring in which `2` is invertible, and a scalar with `μ * μ = 1`,

`Eig(f ⊗ g, μ) ≃ Eig(f, 1) ⊗ Eig(g, μ) × Eig(f, -1) ⊗ Eig(g, -μ)`.

For `μ = 1` this is the even part `X⁺ ⊗ Y⁺ ⊕ X⁻ ⊗ Y⁻` of the tensor product of the graded modules
`(X, f)` and `(Y, g)`, and for `μ = -1` its odd part `X⁺ ⊗ Y⁻ ⊕ X⁻ ⊗ Y⁺`. -/
def eigenspaceTensorMapEquiv (hf : Function.Involutive f) (hg : Function.Involutive g) {μ : k}
    (hμ : μ * μ = 1) :
    eigenspace (map f g) μ ≃ₗ[k]
      (f.eigenspace 1 ⊗[k] g.eigenspace μ) × (f.eigenspace (-1) ⊗[k] g.eigenspace (-μ)) :=
  .symm <| .ofLinearMap
    (LinearMap.codRestrict _ (eigenspaceTensorIncl μ) (eigenspaceTensorIncl_mem μ))
    (LinearMap.prod (map (eigenProjOfInvolutive hf (one_mul 1)) (eigenProjOfInvolutive hg hμ))
        (map (eigenProjOfInvolutive hf ((neg_mul_neg (1 : k) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive hg ((neg_mul_neg μ μ).trans hμ))) ∘ₗ
      (eigenspace (map f g) μ).subtype)
    (by
      ext z
      have hz := mem_eigenspace_iff.1 z.2
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
        Submodule.subtype_apply, LinearMap.prod_apply, Function.prod, eigenspaceTensorIncl,
        LinearMap.coprod_apply, LinearMap.id_coe, id_eq]
      rw [eigenspaceTensorIncl_proj hf hg hμ, hz, smul_smul, hμ, one_smul, ← two_smul k,
        invOf_smul_smul])
    (by
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro x y <;>
        simp [eigenspaceTensorIncl, hμ])

/-- The forward map of `Module.End.eigenspaceTensorMapEquiv` applies the tensor products of the
eigenspace projections `½ (1 + f)`, `½ (1 + μ g)` and `½ (1 - f)`, `½ (1 - μ g)`. -/
@[simp]
theorem eigenspaceTensorMapEquiv_apply (hf : Function.Involutive f) (hg : Function.Involutive g)
    {μ : k} (hμ : μ * μ = 1) (z : eigenspace (map f g) μ) :
    eigenspaceTensorMapEquiv f g hf hg hμ z =
      (map (eigenProjOfInvolutive hf (one_mul 1)) (eigenProjOfInvolutive hg hμ) z,
        map (eigenProjOfInvolutive hf ((neg_mul_neg (1 : k) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive hg ((neg_mul_neg μ μ).trans hμ)) z) :=
  (rfl)

/-- The inverse of `Module.End.eigenspaceTensorMapEquiv` adds the two tensor products of the
eigenspace inclusions. -/
@[simp]
theorem coe_eigenspaceTensorMapEquiv_symm_apply (hf : Function.Involutive f)
    (hg : Function.Involutive g) {μ : k} (hμ : μ * μ = 1)
    (p : (f.eigenspace 1 ⊗[k] g.eigenspace μ) × (f.eigenspace (-1) ⊗[k] g.eigenspace (-μ))) :
    ((eigenspaceTensorMapEquiv f g hf hg hμ).symm p : X ⊗[k] Y) =
      map (f.eigenspace 1).subtype (g.eigenspace μ).subtype p.1 +
        map (f.eigenspace (-1)).subtype (g.eigenspace (-μ)).subtype p.2 :=
  (rfl)

end Module.End
