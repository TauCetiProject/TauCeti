/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.Ring.NNRat
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree

/-!
# Coefficient semifields

A *coefficient semifield* in the sense of Fomin and Zelevinsky is a commutative group `P`,
written multiplicatively, with an *auxiliary addition* that is commutative, associative and
over which the multiplication distributes. Unlike a `Semifield`, it has no zero element.
Coefficient semifields are the groups in which the coefficients of a cluster algebra live: the
mutation rule for coefficients uses the auxiliary addition, while the cluster variables live in
a field over the group ring `ℤ[P]`.

The auxiliary addition, usually written `⊕`, is here the `+` of `P`. This agrees with the
examples in which it is an honest sum, such as the positive rationals or the subtraction-free
rational functions, and for the tropical examples it means that `+` denotes a minimum.

## Main declarations

* `TauCeti.CoefficientSemifield`: the class of coefficient semifields.
* The `HasUniqueRoots` instance: a coefficient semifield is torsion-free as a group (Fomin and
  Zelevinsky, *Cluster algebras I*, §5). With `HasUniqueRoots.to_twoUniqueProds` it follows that
  the group ring `MonoidAlgebra ℤ P` is a domain, so that it has a field of fractions.
* Instances for the one-element group, for products and indexed products, and for the unit
  group of a `Semifield` in which nonzero elements have nonzero sums, such as `ℚ≥0`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §5.
* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  Definition 2.1.
-/

public section

universe u

namespace TauCeti

/-- A *coefficient semifield* is a commutative group, written multiplicatively, together with a
commutative and associative auxiliary addition `+` over which the multiplication distributes.
There is no zero, in contrast with `Semifield`. -/
class CoefficientSemifield (P : Type*) extends CommGroup P, AddCommSemigroup P, Distrib P

namespace CoefficientSemifield

variable {P : Type*} [CoefficientSemifield P]

/-- Division distributes over the auxiliary addition. -/
protected theorem add_div (a b c : P) : (a + b) / c = a / c + b / c := by
  simp only [div_eq_mul_inv, add_mul]

/-- The sum of two inverses, over a common denominator. -/
protected theorem inv_add_inv (a b : P) : a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  simp [CoefficientSemifield.add_div, add_comm]

/-- Every `p` has a geometric sum `g = 1 + p + ⋯ + p ^ n`, which is described here, without
finite sums, by the identity `g + p ^ (n + 1) = 1 + p * g`. -/
private theorem exists_add_pow_eq_one_add_mul (p : P) (n : ℕ) :
    ∃ g : P, g + p ^ (n + 1) = 1 + p * g := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨g + p ^ (n + 1), ?_⟩
    calc g + p ^ (n + 1) + p ^ (n + 1 + 1)
        = 1 + p * g + p * p ^ (n + 1) := by rw [hg, pow_succ' p (n + 1)]
      _ = 1 + p * (g + p ^ (n + 1)) := by rw [add_assoc, mul_add]

/-- A coefficient semifield has no torsion: if `p ^ n = 1` with `n ≠ 0`, then multiplication by
`p` fixes the geometric sum `1 + p + ⋯ + p ^ (n - 1)`, so `p = 1`. -/
private theorem eq_one_of_pow_eq_one {p : P} {n : ℕ} (hn : n ≠ 0) (h : p ^ n = 1) : p = 1 := by
  obtain _ | _ | n := n
  · contradiction
  · simpa using h
  · obtain ⟨g, hg⟩ := exists_add_pow_eq_one_add_mul p n
    have hfix : p * (g + p ^ (n + 1)) = g + p ^ (n + 1) := by
      rw [mul_add, ← pow_succ', h, hg, add_comm]
    exact mul_eq_right.mp hfix

/-- A coefficient semifield is torsion-free as a group: taking `n`-th powers is injective for
`n ≠ 0`. -/
instance : HasUniqueRoots P where
  pow_left_injective _ hn a b (hab : a ^ _ = b ^ _) :=
    div_eq_one.mp <| eq_one_of_pow_eq_one hn <| by rw [div_pow, hab, div_self']

/-- The group ring of a coefficient semifield is a domain. -/
example : IsDomain (MonoidAlgebra ℤ P) := inferInstance

/-! ### Constructions -/

/-- The one-element coefficient semifield. -/
instance instPUnit : CoefficientSemifield PUnit.{u + 1} :=
  { PUnit.commGroup, PUnit.commRing with }

/-- The product of two coefficient semifields, with componentwise operations. -/
instance instProd {Q : Type*} [CoefficientSemifield Q] : CoefficientSemifield (P × Q) :=
  { Prod.instCommGroup, Prod.instAddCommSemigroup, Prod.instDistrib with }

/-- The product of a family of coefficient semifields, with componentwise operations. -/
instance instPi {ι : Type*} {A : ι → Type*} [∀ i, CoefficientSemifield (A i)] :
    CoefficientSemifield (∀ i, A i) :=
  { Pi.commGroup, Pi.addCommSemigroup, Pi.distrib with }

section Units

variable {F : Type*} [Semifield F] [Subsingleton (AddUnits F)]

/-- The units of a semifield in which nonzero elements have nonzero sums form a coefficient
semifield, the auxiliary addition being the addition of the semifield. The hypothesis is stated
as the triviality of the additive units; it holds for `ℚ≥0` and fails for every field. -/
instance instUnits : CoefficientSemifield Fˣ where
  add a b := Units.mk0 (a + b) (by simp)
  add_assoc a b c := Units.ext (add_assoc (a : F) b c)
  add_comm a b := Units.ext (add_comm (a : F) b)
  left_distrib a b c := Units.ext (mul_add (a : F) b c)
  right_distrib a b c := Units.ext (add_mul (a : F) b c)

end Units

/-- The positive rationals, as the units of `ℚ≥0`, form a coefficient semifield. -/
example : CoefficientSemifield ℚ≥0ˣ := inferInstance

end CoefficientSemifield

end TauCeti

namespace Units

variable {F : Type*} [Semifield F] [Subsingleton (AddUnits F)]

/-- The auxiliary addition of units of a semifield is the addition of the semifield. -/
@[simp, norm_cast]
theorem val_add_of_subsingleton_addUnits (a b : Fˣ) : ((a + b : Fˣ) : F) = a + b :=
  (rfl)

end Units
