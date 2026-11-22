/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.MonoidAlgebra.GaussNorm
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
import TauCeti.Algebra.Group.Hom.Instances
import TauCeti.Algebra.Group.UniqueProds.Submonoid
import TauCeti.Algebra.Group.UniqueProds.TorsionFree

/-!
# Gauss norms on toric chart algebras and on a group algebra with torsion

On the monoid algebra `K[σ^∨ ∩ M]` of the dual semigroup of a toric cone, the Gauss norm of a
nonarchimedean absolute value is multiplicative: the dual semigroup is a submonoid of the
torsion-free character lattice, so it has unique sums. Torsion in the exponents breaks this: in
`K[ℤ/2]` the product `(1 + χ) * (1 - χ) = 1 - χ²` vanishes although both factors have Gauss
norm `1`.
-/

public section

namespace TauCeti.Examples.MonoidAlgebraGaussNorm

open AddMonoidAlgebra

/-- The Gauss norm on the coordinate ring `K[σ^∨ ∩ M]` of an affine toric chart is
multiplicative. -/
example {N V K : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    (hi : TauCeti.Toric.IsIntegralLattice i) (σ : PointedCone ℝ V) [Field K]
    {v : AbsoluteValue K ℝ} (hna : IsNonarchimedean v)
    (f g : AddMonoidAlgebra K (TauCeti.Toric.dualSemigroup hi σ)) :
    gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g :=
  gaussNorm_mul hna f g

/-- In `K[ℤ/2]` both `1 + χ` and `1 - χ` have Gauss norm `1`, but their product is `0`, so the
unique-sums hypothesis of `AddMonoidAlgebra.gaussNorm_mul` cannot be dropped. -/
theorem gaussNorm_mul_ne_zmod_two {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    gaussNorm v ((single 0 1 + single 1 1 : AddMonoidAlgebra K (ZMod 2)) *
        (single 0 1 - single 1 1)) = 0 ∧
      gaussNorm v (single 0 1 + single 1 1 : AddMonoidAlgebra K (ZMod 2)) *
        gaussNorm v (single 0 1 - single 1 1 : AddMonoidAlgebra K (ZMod 2)) = 1 := by
  have hcoeff (c : K) (m : ZMod 2) : v ((single 0 1 + single 1 c :
      AddMonoidAlgebra K (ZMod 2)).coeff m) = if m = 0 then 1 else v c := by
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    obtain rfl | rfl : m = 0 ∨ m = 1 := by revert m; decide
    all_goals simp [h10]
  have hnorm (c : K) (hc : v c = 1) :
      gaussNorm v (single 0 1 + single 1 c : AddMonoidAlgebra K (ZMod 2)) = 1 := by
    refine le_antisymm ((gaussNorm_le_iff v zero_le_one).2 fun m ↦ ?_) ?_
    · rw [hcoeff]
      split_ifs <;> simp [hc]
    · have := le_gaussNorm v (single 0 1 + single 1 c : AddMonoidAlgebra K (ZMod 2)) 0
      rw [hcoeff] at this
      simpa using this
  refine ⟨?_, ?_⟩
  · have : ((single 0 1 + single 1 1 : AddMonoidAlgebra K (ZMod 2)) *
        (single 0 1 - single 1 1)) = 0 := by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp only [add_mul, mul_sub, single_mul_single, mul_one, add_zero, zero_add, h11]
      abel
    simp [this]
  · rw [sub_eq_add_neg, ← single_neg, hnorm 1 (by simp), hnorm (-1) (by simp), one_mul]

end TauCeti.Examples.MonoidAlgebraGaussNorm
