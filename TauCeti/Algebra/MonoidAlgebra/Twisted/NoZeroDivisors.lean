/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Nonzero divisors in twisted monoid algebras

In the twisted monoid algebra `twistedMonoidAlgebra k G α` of a normalized factor set
`α : G → G → kˣ`, multiplying two basis elements scales the product basis element by the unit
`α g h`. Consequently, whenever a pair `(g₀, h₀)` in the supports of `x` and `y` represents its
product `g₀ * h₀` uniquely (`UniqueMul`), the `(g₀ * h₀)`-coordinate of `x * y` is
`x_{g₀} * y_{h₀} * α g₀ h₀`.

When `k` has no zero divisors and `G` has unique products (`UniqueProds G` — in particular for
`Multiplicative L` of any torsion-free abelian group `L`), `twistedMonoidAlgebra k G α` therefore
has no zero divisors.

## Main results

* `TauCeti.TwistedMonoidAlgebra.repr_mul_apply_mul_of_uniqueMul`: a uniquely represented product of
  support elements carries coordinate `x_{g₀} * y_{h₀} * α g₀ h₀`.
* `TauCeti.TwistedMonoidAlgebra.instNoZeroDivisors`: `NoZeroDivisors (twistedMonoidAlgebra k G α)`
  from `[NoZeroDivisors k]` and `[UniqueProds G]`.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

open Finsupp

section Coordinates

variable {k G : Type*} [CommSemiring k] [Monoid G] {α : G → G → kˣ} [IsFactorSet α]

/-- If `(g₀, h₀)` is the unique pair in the supports of `x` and `y` with product `g₀ * h₀`, then
the `(g₀ * h₀)`-coordinate of `x * y` is `x_{g₀} * y_{h₀} * α g₀ h₀`. -/
theorem repr_mul_apply_mul_of_uniqueMul {x y : twistedMonoidAlgebra k G α} {g₀ h₀ : G}
    (h : UniqueMul ((basis k G α).repr x).support ((basis k G α).repr y).support g₀ h₀) :
    (basis k G α).repr (x * y) (g₀ * h₀) =
      (basis k G α).repr x g₀ * (basis k G α).repr y h₀ * (α g₀ h₀ : k) := by
  classical
  rw [repr_mul]
  simp_rw [Finsupp.sum_apply, single_apply, sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (g₀, h₀) ?_ ?_).trans (ite_eq_left rfl) <;>
    simp_rw [Finset.mem_product]
  · refine fun gh hmem hne ↦ ite_eq_right fun he ↦ hne <| Prod.ext ?_ ?_
    exacts [(h hmem.1 hmem.2 he).1, (h hmem.1 hmem.2 he).2]
  · refine fun hnotMem ↦ ite_eq_right_iff.mpr fun _ ↦ ?_
    rcases not_and_or.mp hnotMem with gx | hy
    · rw [notMem_support_iff.mp gx, zero_mul, zero_mul]
    · rw [notMem_support_iff.mp hy, mul_zero, zero_mul]

/-- If `k` has no zero divisors and `G` has unique products, the twisted monoid algebra
`twistedMonoidAlgebra k G α` has no zero divisors. -/
instance instNoZeroDivisors [NoZeroDivisors k] [UniqueProds G] :
    NoZeroDivisors (twistedMonoidAlgebra k G α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    contrapose! hxy
    have hx : ((basis k G α).repr x).support.Nonempty :=
      support_nonempty_iff.mpr ((basis k G α).repr.map_eq_zero_iff.not.mpr hxy.1)
    have hy : ((basis k G α).repr y).support.Nonempty :=
      support_nonempty_iff.mpr ((basis k G α).repr.map_eq_zero_iff.not.mpr hxy.2)
    obtain ⟨g₀, hg₀, h₀, hh₀, huniq⟩ := UniqueProds.uniqueMul_of_nonempty hx hy
    intro hzero
    have hcoord : (basis k G α).repr (x * y) (g₀ * h₀) = 0 := by simp [hzero]
    rw [repr_mul_apply_mul_of_uniqueMul huniq] at hcoord
    have hprod : (basis k G α).repr x g₀ * (basis k G α).repr y h₀ = 0 := by
      have hunit := congrArg (· * (((α g₀ h₀)⁻¹ : kˣ) : k)) hcoord
      simpa [mul_assoc, ← Units.val_mul] using hunit
    exact mul_ne_zero (mem_support_iff.mp hg₀) (mem_support_iff.mp hh₀) hprod

end Coordinates

end TauCeti.TwistedMonoidAlgebra
