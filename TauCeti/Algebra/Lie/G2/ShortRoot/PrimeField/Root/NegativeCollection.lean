/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Root.NegativeCollection

/-!
# Negative-root Chevalley collection over the prime field of characteristic three

The two negative simple-root points of the carrier generated over `𝔽₃` satisfy the
four-factor Chevalley collection formula, with the nonsimple-root factors normalized
by explicit Weyl words. The identity holds over every commutative `𝔽₃`-algebra,
including nonreduced algebras, and retains the cubic short-root parameter.

`commutatorElement_rootSubgroupPoints_inr_zero_inr_one` transfers the integral identity through
the existing comparisons of the simple-root matrices. It does not identify this
carrier with the specialization of the integral toral closure or with an independently
pinned simply connected group.

The formal input is the integral collection theorem in the imported module and
`PrimeField.coe_rootSubgroupPoints`. See R. W. Carter, *Simple Groups of Lie Type*,
Theorem 5.2.2, and R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped commutatorElement

namespace TauCeti.G2ShortRoot.PrimeField

universe v

/-- The negative-simple-root commutator in the characteristic-three carrier is the
ordered product of the four Weyl-normalized nonsimple-root points. -/
theorem commutatorElement_rootSubgroupPoints_inr_zero_inr_one (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (a b : A) :
    let x := fun k t => rootSubgroupPoints k A (Multiplicative.ofAdd t)
    let n := fun i => x (.inl i) 1 * x (.inr i) (-1) * x (.inl i) 1
    ⁅x (.inr 0) a, x (.inr 1) b⁆ =
      (n 1 * x (.inr 0) (a * b) * (n 1)⁻¹) *
      ((n 0 * n 1) * x (.inr 0) (a ^ 2 * b) * (n 0 * n 1)⁻¹) *
      (n 0 * x (.inr 1) (-(a ^ 3 * b)) * (n 0)⁻¹) *
      ((n 1 * n 0) * x (.inr 1) (2 * a ^ 3 * b ^ 2) * (n 1 * n 0)⁻¹) := by
  have h := congrArg (fun g : IntegralToralClosure.points A =>
    (g : Matrix.GeneralLinearGroup (Fin 7) A))
    (IntegralToralClosure.commutatorElement_rootSubgroupPoints_inr_zero_inr_one A a b)
  apply Subtype.ext
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootSubgroupPoints] using h

end TauCeti.G2ShortRoot.PrimeField
