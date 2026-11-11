/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.Collection

/-!
# Positive-root collection in the characteristic-three G₂ carrier

`commutatorElement_positive_simple_eq_root_product` gives the four-factor Chevalley collection
formula in the short-root carrier generated over 𝔽₃. The factors are normalized by the actual
numbered opposite-root words. In particular, the cubic parameter terms persist over arbitrary
𝔽₃-algebras; they are not replaced by their values on 𝔽₃ itself.

The formula transfers through the faithful matrix inclusions and the existing comparison of
numbered root points. It neither identifies this generated carrier with specialization of the
integral toral closure nor with an independently constructed pinned simply connected group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The formal inputs are the integral collection formula in
`G2.ShortRoot.IntegralToralClosure.RootRelations.Collection` and the root-point comparison in
`G2.ShortRoot.PrimeField.PointsFunctor`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open scoped commutatorElement

universe v

/-- **The positive-simple-root Chevalley collection formula over 𝔽₃.** The four factors
have roots α₁+α₂, 2α₁+α₂, 3α₁+α₂, and 3α₁+2α₂, with their parameters normalized by
the displayed conjugating words. The formula includes nonreduced coefficient algebras. -/
theorem commutatorElement_positive_simple_eq_root_product
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] (a b : A) :
    let x := fun (i : Fin 2) (t : A) ↦ rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t)
    let n := fun i ↦ x i 1 * rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) * x i 1
    ⁅x 0 a, x 1 b⁆ =
      (n 1 * x 0 (-a * b) * (n 1)⁻¹) *
      ((n 0 * n 1) * x 0 (a ^ 2 * b) * (n 0 * n 1)⁻¹) *
      (n 0 * x 1 (a ^ 3 * b) * (n 0)⁻¹) *
      ((n 1 * n 0) * x 1 (2 * a ^ 3 * b ^ 2) * (n 1 * n 0)⁻¹) := by
  have h := congrArg (IntegralToralClosure.points A).subtype
    (IntegralToralClosure.commutatorElement_positive_simple_eq_root_product A a b)
  dsimp only at h ⊢
  apply Subtype.ext
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootSubgroupPoints]
  simpa only [commutatorElement_def, map_mul, map_inv, Subgroup.subtype_apply] using h

end TauCeti.G2ShortRoot.PrimeField
