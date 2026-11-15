/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.NegativeShort

/-!
# Negative nonsimple short-root subgroups of the characteristic-three G₂ carrier

Conjugating the negative short simple-root subgroup by rank-one root words gives the
subgroups at `-(α₁ + α₂)` and `-(2α₁ + α₂)`. Their matrices are quadratic in the additive
parameter, not just the identity plus a tangent vector. The formulas and parameter recovery
hold over every commutative `𝔽₃`-algebra, including nonreduced algebras, by specialization
of the corresponding results for the integral toral closure over arbitrary commutative rings.

These are subgroups of the carrier generated over `𝔽₃`. Their points are identified, as
matrices, with their integral-toral-closure counterparts. No group-level identification of the
carrier with the reduction of the integral toral closure, or with the pinned simply connected
group scheme, is asserted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The rank-one-word construction follows the negative long-root tangent construction in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.NegativeLong`. The coefficient matrices
use the weight basis of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

private def shortConjugator (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  if i = 0 then rankOneWord 1 A else rankOneWord 0 A * rankOneWord 1 A

/-- The negative short-root homomorphism at `-(α₁ + α₂)` (index zero) or
`-(2α₁ + α₂)` (index one). Conjugate `rootSubgroupPoints (.inr 0)` by
`rankOneWord 1 A` or `rankOneWord 0 A * rankOneWord 1 A`, respectively.
See `negativeShortRootSubgroupPoints_apply` for the normalization. -/
def negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  (MulAut.conj (shortConjugator i A)).toMonoidHom.comp (rootSubgroupPoints (.inr 0) A)

/-- The chosen normalization is conjugation of the negative short simple-root subgroup. -/
theorem negativeShortRootSubgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    let c := if i = 0 then rankOneWord 1 A else rankOneWord 0 A * rankOneWord 1 A
    negativeShortRootSubgroupPoints i A u = c * rootSubgroupPoints (.inr 0) A u * c⁻¹ := by
  rfl

/-- A negative short-root point has the same matrix as its integral toral-closure counterpart. -/
theorem coe_negativeShortRootSubgroupPoints_eq_integral (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    (negativeShortRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) =
      (IntegralToralClosure.negativeShortRootSubgroupPoints i A u :
        Matrix.GeneralLinearGroup (Fin 7) A) := by
  rw [negativeShortRootSubgroupPoints_apply,
    IntegralToralClosure.negativeShortRootSubgroupPoints_apply]
  split_ifs <;>
    simp only [rankOneWord_def, Subgroup.coe_mul, Subgroup.coe_inv,
      IntegralToralClosure.coe_rankOneWordPoints,
      UniversalEnvelopingAlgebra.kostantToralWeylPoint_def,
      UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints,
      ← IntegralToralClosure.coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix,
      coe_rootSubgroupPoints]

/-- The exact quadratic root formula over every commutative coefficient algebra. -/
@[simp↓]
theorem coe_negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      1 + u.toAdd • (negativeShortRootMatrix i).map (Int.castRingHom A) +
        u.toAdd ^ 2 • (negativeShortRootDividedSquareMatrix i).map (Int.castRingHom A) := by
  rw [coe_negativeShortRootSubgroupPoints_eq_integral,
    IntegralToralClosure.coe_negativeShortRootSubgroupPoints]

/-- An entry recovers the additive parameter, with no nontriviality assumption on the algebra. -/
theorem negativeShortRootSubgroupPoints_entry (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) (if i = 0 then 2 else 4) (if i = 0 then 0 else 1) = u.toAdd := by
  rw [coe_negativeShortRootSubgroupPoints_eq_integral,
    IntegralToralClosure.negativeShortRootSubgroupPoints_entry]

/-- Entry `(2, 0)` recovers the parameter at `-(α₁ + α₂)`. -/
@[simp↓]
theorem negativeShortRootSubgroupPoints_zero_entry (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints 0 A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) 2 0 = u.toAdd :=
  negativeShortRootSubgroupPoints_entry 0 A u

/-- Entry `(4, 1)` recovers the parameter at `-(2α₁ + α₂)`. -/
@[simp↓]
theorem negativeShortRootSubgroupPoints_one_entry (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints 1 A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) 4 1 = u.toAdd :=
  negativeShortRootSubgroupPoints_entry 1 A u

/-- Each negative short-root parametrization is injective over every coefficient algebra. -/
theorem negativeShortRootSubgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Function.Injective (negativeShortRootSubgroupPoints i A) := by
  intro u v huv
  apply IntegralToralClosure.negativeShortRootSubgroupPoints_injective i A
  apply Subtype.ext
  simpa only [coe_negativeShortRootSubgroupPoints_eq_integral] using congrArg Subtype.val huv

/-- Changing coefficients preserves the chosen negative short-root parameters. -/
@[simp↓]
theorem pointsMap_negativeShortRootSubgroupPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) (u : Multiplicative A) :
    pointsMap f (negativeShortRootSubgroupPoints i A u) =
      negativeShortRootSubgroupPoints i B (Multiplicative.ofAdd (f u.toAdd)) := by
  fin_cases i <;>
    simp [negativeShortRootSubgroupPoints, shortConjugator, rankOneWord_def, map_mul, map_inv]

/-- The torus acts by the integral root character `-(α₁ + α₂)` or `-(2α₁ + α₂)`.
These are entries five and six of the existing short-root weight diagram. -/
@[simp]
theorem weightTorusPoints_conj_negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * negativeShortRootSubgroupPoints i A u *
        (weightTorusPoints A s)⁻¹ =
      negativeShortRootSubgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (weight (if i = 0 then 5 else 6)) : A) * u.toAdd)) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (IntegralToralClosure.weightTorusPoints_conj_negativeShortRootSubgroupPoints i A s u)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_weightTorusPoints,
    coe_negativeShortRootSubgroupPoints_eq_integral] using h

end

end TauCeti.G2ShortRoot.PrimeField
