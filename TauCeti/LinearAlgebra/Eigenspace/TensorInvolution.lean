/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
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
`½ (1 + μ g)`, so tensoring the inclusions stays injective. The inverse of the equivalence applies
these projections to both factors; the two pieces add up to `½ (1 + μ (f ⊗ g))`, which is the
identity on `Eig(f ⊗ g, μ)`.

## Main definitions

* `TauCeti.eigenspaceTensorMapEquiv`: `Eig(f ⊗ g, μ) ≃ Eig(f, 1) ⊗ Eig(g, μ) × Eig(f, -1) ⊗
  Eig(g, -μ)` for involutions `f`, `g` and `μ * μ = 1`.

## Main results

* `TauCeti.coe_eigenspaceTensorMapEquiv_symm_apply`: the inverse is the sum of the two tensor
  products of the eigenspace inclusions.
-/

public section

noncomputable section

namespace TauCeti

open Module Module.End TensorProduct

variable {k X Y : Type*} [CommRing k] [Invertible (2 : k)]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- The projection `½ (1 + μ g)` of `Y` onto the `μ`-eigenspace of an involution `g`, for
`μ * μ = 1`. -/
private def eigenProj {g : Module.End k Y} (hg : Function.Involutive g) {μ : k}
    (hμ : μ * μ = 1) : Y →ₗ[k] g.eigenspace μ :=
  LinearMap.codRestrict _ ((⅟2 : k) • (LinearMap.id + μ • g)) fun y ↦ by
    rw [mem_eigenspace_iff]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add,
      hg y, smul_add, smul_smul]
    rw [mul_left_comm, hμ, mul_one, mul_comm μ, add_comm]

private theorem coe_eigenProj {g : Module.End k Y} (hg : Function.Involutive g) {μ : k}
    (hμ : μ * μ = 1) (y : Y) : (eigenProj hg hμ y : Y) = (⅟2 : k) • (y + μ • g y) :=
  (rfl)

/-- The projection onto the `μ`-eigenspace fixes the `μ`-eigenspace. -/
private theorem eigenProj_of_mem {g : Module.End k Y} (hg : Function.Involutive g) {μ : k}
    (hμ : μ * μ = 1) (y : g.eigenspace μ) : eigenProj hg hμ y = y := by
  apply Subtype.ext
  rw [coe_eigenProj, (mem_eigenspace_iff.1 y.2), smul_smul, hμ, one_smul, ← two_smul k,
    smul_smul, invOf_mul_self, one_smul]

/-- The projection onto the `μ`-eigenspace kills the `ν`-eigenspace when `μ ν = -1`, that is, when
`ν = -μ`. -/
private theorem eigenProj_of_mem_neg {g : Module.End k Y} (hg : Function.Involutive g) {μ ν : k}
    (hμ : μ * μ = 1) (hν : μ * ν = -1) (y : g.eigenspace ν) : eigenProj hg hμ y = 0 := by
  apply Subtype.ext
  rw [coe_eigenProj, (mem_eigenspace_iff.1 y.2), smul_smul, hν, neg_one_smul, add_neg_cancel,
    smul_zero, ZeroMemClass.coe_zero]

omit [Invertible (2 : k)] in
/-- `(-μ) * (-μ) = 1` whenever `μ * μ = 1`. -/
private theorem neg_mul_neg_self_eq_one {μ : k} (hμ : μ * μ = 1) : -μ * -μ = 1 := by
  rw [neg_mul_neg, hμ]

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
        (map (eigenProj hf (one_mul 1)) (eigenProj hg hμ) z) +
      map (f.eigenspace (-1)).subtype (g.eigenspace (-μ)).subtype
        (map (eigenProj hf (neg_mul_neg_self_eq_one (one_mul 1)))
          (eigenProj hg (neg_mul_neg_self_eq_one hμ)) z) =
      (⅟2 : k) • (z + μ • map f g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [map_tmul, Submodule.subtype_apply, coe_eigenProj, one_smul, neg_smul,
      tmul_add, add_tmul, ← smul_tmul', tmul_smul, smul_add, smul_neg, tmul_neg, neg_tmul]
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
    (LinearMap.prod (map (eigenProj hf (one_mul 1)) (eigenProj hg hμ))
        (map (eigenProj hf (neg_mul_neg_self_eq_one (one_mul 1)))
          (eigenProj hg (neg_mul_neg_self_eq_one hμ))) ∘ₗ
      (eigenspace (map f g) μ).subtype)
    (by
      ext z
      have hz := mem_eigenspace_iff.1 z.2
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
        Submodule.subtype_apply, LinearMap.prod_apply, Function.prod, eigenspaceTensorIncl,
        LinearMap.coprod_apply, LinearMap.id_coe, id_eq]
      rw [eigenspaceTensorIncl_proj hf hg hμ, hz, smul_smul, hμ, one_smul, ← two_smul k, smul_smul,
        invOf_mul_self, one_smul])
    (by
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro x y <;>
        simp [eigenspaceTensorIncl, eigenProj_of_mem, eigenProj_of_mem_neg, hμ])

/-- The inverse of `TauCeti.eigenspaceTensorMapEquiv` adds the two tensor products of the
eigenspace inclusions. -/
@[simp]
theorem coe_eigenspaceTensorMapEquiv_symm_apply (hf : Function.Involutive f)
    (hg : Function.Involutive g) {μ : k} (hμ : μ * μ = 1)
    (p : (f.eigenspace 1 ⊗[k] g.eigenspace μ) × (f.eigenspace (-1) ⊗[k] g.eigenspace (-μ))) :
    ((eigenspaceTensorMapEquiv f g hf hg hμ).symm p : X ⊗[k] Y) =
      map (f.eigenspace 1).subtype (g.eigenspace μ).subtype p.1 +
        map (f.eigenspace (-1)).subtype (g.eigenspace (-μ)).subtype p.2 :=
  (rfl)

end TauCeti
