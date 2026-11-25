/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Connected
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent

/-!
# The stable component group of `ℂ`

Every `GLₙ(ℂ)` is path connected, so the stable identity component of `GL_∞(ℂ)` is the whole
group and the stable component group `GL_∞(ℂ) / GL_∞(ℂ)₀` is trivial. Since algebraic
`K₁(ℂ) = ℂˣ` is not trivial, the comparison `TauCeti.AlgebraicK1.toStableComponentGroup` of
algebraic `K₁` with the stable component group is not injective in general.

## Main results

* `TauCeti.StableGeneralLinearGroup.identityComponent_complex`: the stable identity component of
  `GL_∞(ℂ)` is everything.
* The `Subsingleton` instance on `TauCeti.StableComponentGroup ℂ`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.2.
-/

public section

namespace TauCeti

/-! ## Complex matrices -/

/-- The stable identity component of `GL_∞(ℂ)` is the whole group, since every `GLₙ(ℂ)` is
connected. -/
@[simp]
theorem StableGeneralLinearGroup.identityComponent_complex :
    identityComponent ℂ = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_of x
  exact of_mem_identityComponent (by simp)

/-- The stable component group of `ℂ` is trivial, although algebraic `K₁(ℂ) = ℂˣ` is not. -/
instance : Subsingleton (StableComponentGroup ℂ) where
  allEq x y := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact QuotientGroup.eq.2 (by simp)

end TauCeti
