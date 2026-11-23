/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.SymmetricProduct.Basic
import Mathlib.Tactic.Ring

/-!
# Metric properties of the symmetric exterior product on the exterior square

On real inner product spaces with a finite-dimensional codomain `F` (and arbitrary real inner
product space domain `E`), the inner product of `symmMap₂ f g (a ∧ b)` with `u ∧ w` is given by
the mixed-space coefficient formula
`(⟪f a, u⟫ * ⟪g b, w⟫ + ⟪g a, u⟫ * ⟪f b, w⟫ - ⟪f a, w⟫ * ⟪g b, u⟫ - ⟪g a, w⟫ * ⟪f b, u⟫) / 2`,
which has the same sign convention as `TauCeti.FourTensor.kulkarniNomizu` (i.e.
`LinearMap.BilinForm.kulkarniNomizu` with the final two slots swapped); when `E = F`, it equals
`(1 / 2) * TauCeti.FourTensor.kulkarniNomizu h k ![a, b, u, w]` for the bilinear forms
`h x y = ⟪f x, y⟫` and `k x y = ⟪g x, y⟫`. When both `E` and `F` are finite-dimensional, it
follows that `(symmMap₂ f g)* = symmMap₂ f* g*`, so symmetric endomorphisms `f, g` have a
symmetric exterior product `symmMap₂ f g`.

## Main results

* `exteriorPower.inner_symmMap₂_ιMulti_two`: inner product of `symmMap₂ f g (a ∧ b)` against
  `u ∧ w`.
* `exteriorPower.adjoint_symmMap₂`: `(symmMap₂ f g)* = symmMap₂ f* g*`.
* `LinearMap.IsSymmetric.symmMap₂`: symmetry of `symmMap₂ f g` for symmetric `f` and `g`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, §1–2.
-/

public section

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- For a finite-dimensional codomain `F` (and arbitrary real inner product space `E`), the inner
product of `symmMap₂ f g (a ∧ b)` with `u ∧ w` satisfies the mixed-space coefficient formula
`(⟪f a, u⟫ * ⟪g b, w⟫ + ⟪g a, u⟫ * ⟪f b, w⟫ - ⟪f a, w⟫ * ⟪g b, u⟫ - ⟪g a, w⟫ * ⟪f b, u⟫) / 2`,
sharing the sign convention of `TauCeti.FourTensor.kulkarniNomizu`
(`LinearMap.BilinForm.kulkarniNomizu` with the final two slots swapped) and specializing to
`(1 / 2) * TauCeti.FourTensor.kulkarniNomizu h k ![a, b, u, w]` when `E = F` with
`h x y = ⟪f x, y⟫` and `k x y = ⟪g x, y⟫`. -/
theorem inner_symmMap₂_ιMulti_two (f g : E →ₗ[ℝ] F) (a b : E) (u w : F) :
    ⟪symmMap₂ f g (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ =
      (⟪f a, u⟫ * ⟪g b, w⟫ + ⟪g a, u⟫ * ⟪f b, w⟫ -
        ⟪f a, w⟫ * ⟪g b, u⟫ - ⟪g a, w⟫ * ⟪f b, u⟫) / 2 := by
  rw [symmMap₂_apply_ιMulti, real_inner_smul_left, inner_add_left,
    inner_ιMulti_two, inner_ιMulti_two, invOf_eq_inv]
  ring

/-- The adjoint of `symmMap₂ f g` on `⋀[ℝ]^2` is `symmMap₂ f* g*`. -/
@[simp]
theorem adjoint_symmMap₂ (f g : E →ₗ[ℝ] F) :
    (symmMap₂ f g).adjoint = symmMap₂ f.adjoint g.adjoint :=
  linearMap_ext_inner_ιMulti_two fun a b u w ↦ by
    rw [LinearMap.adjoint_inner_left, real_inner_comm _ (ιMulti ℝ 2 ![a, b]),
      inner_symmMap₂_ιMulti_two, inner_symmMap₂_ιMulti_two]
    simp only [LinearMap.adjoint_inner_left, real_inner_comm]
    ring

/-- The symmetric exterior product of two symmetric endomorphisms of `E` is a symmetric
endomorphism of `⋀[ℝ]^2 E`. -/
theorem _root_.LinearMap.IsSymmetric.symmMap₂ {f g : Module.End ℝ E}
    (hf : f.IsSymmetric) (hg : g.IsSymmetric) :
    (exteriorPower.symmMap₂ f g).IsSymmetric := fun x y ↦ by
  rw [← LinearMap.adjoint_inner_right, adjoint_symmMap₂, hf.adjoint_eq, hg.adjoint_eq]

end exteriorPower
