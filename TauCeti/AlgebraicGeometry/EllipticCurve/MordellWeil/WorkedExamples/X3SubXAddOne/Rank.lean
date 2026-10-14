/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.RankBound
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.WorkedExamples.X3SubXAddOne.Torsion
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.WorkedExamples.Cubic23.Invariants

/-!
# The Mordell–Weil group of `y² = x³ - x + 1` is `ℤ`

This file computes the Mordell–Weil group of the elliptic curve `E : y² = x³ - x + 1` over `ℚ`: it
has rank `1`, and since its torsion is trivial (`torsion_curveX3SubXAddOne_eq_bot`) it is
isomorphic to `ℤ`.

The upper bound is explicit `2`-descent (Silverman X.1), in the form
`WeierstrassCurve.Affine.pow_rank_add_one_le_prod`: for an integral equation `y² = f(x)` whose
cubic `f` has discriminant vanishing to order at most `1` at every prime,

`2 ^ (rank E(ℚ) + 1) · #E(ℚ)[2] ≤ ∏ₚ 2 ^ (rₚ + 1) · #Clₚ[2]`,

the product running over the irreducible factors `p` of `f`, with `rₚ` the unit rank and `Clₚ` the
class group of the ring of integers of `ℚ[X] ⧸ (p)`. Here `disc f = -23` is squarefree, and `f` is
irreducible, since it is irreducible modulo `2`. The cubic field `ℚ[X] ⧸ (f)` is the field of
discriminant `-23` of `TauCeti/NumberTheory/NumberField/WorkedExamples/Cubic23/Invariants.lean`:
if `t` is the class of `X`, then `1 / t = 1 - t²` is an algebraic integer with minimal polynomial
`X³ - X² + 1` generating the field. That field has unit rank `1` and class number `1`, and
`E(ℚ)[2]` is trivial, so the bound reads `2 ^ (rank E(ℚ) + 1) ≤ 4`.

The lower bound is the rational point `(1, 1)`, which has infinite order because `E(ℚ)` is
torsion-free.

## Main results

* `TauCeti.WorkedExamples.irreducible_f_curveX3SubXAddOne`: `x³ - x + 1` is irreducible over `ℚ`.
* `TauCeti.WorkedExamples.finrank_point_curveX3SubXAddOne_le_one`: `rank E(ℚ) ≤ 1`, by
  `2`-descent.
* `TauCeti.WorkedExamples.finrank_point_curveX3SubXAddOne`: `rank E(ℚ) = 1`.
* `TauCeti.WorkedExamples.nonempty_addEquiv_int_point_curveX3SubXAddOne`: `E(ℚ) ≃+ ℤ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.

## Provenance

The same rank computation, for the same equation, accompanies the explicit `2`-descent of Michael
Stoll's `EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0,
commit `3bfe124`), from which the descent bound used here was adapted. Here the arithmetic of the
cubic field enters through the certified invariants of the field of discriminant `-23`.
-/

public section

open Polynomial WeierstrassCurve Affine NumberField Module

namespace TauCeti.WorkedExamples

/-- The cubic `f` of `y² = f(x)` over `ℚ` is `x³ - x + 1`. -/
theorem f_curveX3SubXAddOne :
    (curveX3SubXAddOne.baseChange ℚ).toAffine.f = X ^ 3 - X + 1 := by
  simp [Affine.f, curveX3SubXAddOne, sub_eq_add_neg]

/-- `x³ - x + 1` is irreducible over `ℚ`: its reduction modulo `2` is irreducible. -/
theorem irreducible_f_curveX3SubXAddOne :
    Irreducible (curveX3SubXAddOne.baseChange ℚ).toAffine.f := by
  have hmon : (X ^ 3 - X + 1 : ℤ[X]).Monic := by monicity!
  have hZ : Irreducible (X ^ 3 - X + 1 : ℤ[X]) := by
    refine hmon.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _ ?_
    convert Polynomial.irreducible_X_pow_three_add_X_add_one_zmod_two using 1
    simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, CharTwo.sub_eq_add]
  rw [f_curveX3SubXAddOne]
  convert (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hZ using 1
  simp

section CubicField

/-! ### The cubic field `ℚ[X] ⧸ (x³ - x + 1)` -/

local instance : Fact (Irreducible (curveX3SubXAddOne.baseChange ℚ).toAffine.f) :=
  ⟨irreducible_f_curveX3SubXAddOne⟩

local notation "𝕃" => AdjoinRoot (WeierstrassCurve.Affine.f (WeierstrassCurve.toAffine
    (WeierstrassCurve.baseChange curveX3SubXAddOne ℚ)))

-- the root `t` of `x³ - x + 1` in `𝕃`
local notation "𝕥" => AdjoinRoot.root (WeierstrassCurve.Affine.f (WeierstrassCurve.toAffine
    (WeierstrassCurve.baseChange curveX3SubXAddOne ℚ)))

/-- `t³ - t + 1 = 0` in `𝕃`. -/
private theorem root_pow_three_sub_root_add_one : 𝕥 ^ 3 - 𝕥 + 1 = 0 := by
  have h : AdjoinRoot.mk _ (X ^ 3 - X + 1 : ℚ[X]) = 𝕥 ^ 3 - 𝕥 + 1 := by
    simp [AdjoinRoot.mk_X]
  rw [← h, ← f_curveX3SubXAddOne, AdjoinRoot.mk_self]

/-- `1 - t² = 1 / t` is a root of `X ^ 3 - X ^ 2 + 1`. -/
private theorem one_sub_root_sq_pow_three :
    (1 - 𝕥 ^ 2) ^ 3 - (1 - 𝕥 ^ 2) ^ 2 + 1 = 0 := by
  linear_combination (-𝕥 ^ 3 + 𝕥 + 1) * root_pow_three_sub_root_add_one

/-- The algebraic integer `1 - t² = 1 / t` of `𝕃`. -/
private noncomputable def cubic23Generator : 𝓞 𝕃 :=
  ⟨1 - 𝕥 ^ 2, ⟨X ^ 3 - X ^ 2 + 1, by monicity!, by simpa using one_sub_root_sq_pow_three⟩⟩

/-- The value of `cubic23Generator` in `𝕃`. -/
private theorem coe_cubic23Generator : (cubic23Generator : 𝕃) = 1 - 𝕥 ^ 2 := rfl

/-- The minimal polynomial of `1 / t` over `ℤ` is `X³ - X² + 1`. -/
private theorem minpoly_cubic23Generator : minpoly ℤ cubic23Generator = X ^ 3 - X ^ 2 + 1 := by
  have hs : IsIntegral ℤ cubic23Generator := RingOfIntegers.isIntegral _
  have hP : aeval cubic23Generator (X ^ 3 - X ^ 2 + 1 : ℤ[X]) = 0 := by
    simp only [map_add, map_sub, map_pow, aeval_X, map_one]
    apply RingOfIntegers.coe_injective
    rw [map_add, map_sub, map_pow, map_pow, map_one, map_zero]
    exact one_sub_root_sq_pow_three
  exact eq_of_monic_of_associated (minpoly.monic hs) (by monicity!)
    ((minpoly.irreducible hs).associated_of_dvd TauCeti.NumberField.Cubic23.irreducible_polynomial
      (minpoly.isIntegrallyClosed_dvd hs hP))

/-- `1 / t` generates `𝕃` over `ℚ`. -/
private theorem adjoin_cubic23Generator :
    Algebra.adjoin ℚ {(cubic23Generator : 𝕃)} = ⊤ := by
  have hroot : 𝕥 ∈ Algebra.adjoin ℚ {(cubic23Generator : 𝕃)} := by
    have h : 𝕥 = (1 - 𝕥 ^ 2) - (1 - 𝕥 ^ 2) ^ 2 := by
      linear_combination 𝕥 * root_pow_three_sub_root_add_one
    rw [h, ← coe_cubic23Generator]
    have hθ := Algebra.self_mem_adjoin_singleton ℚ (cubic23Generator : 𝕃)
    exact sub_mem hθ (pow_mem hθ 2)
  -- `AdjoinRoot.adjoinRoot_eq_top` is stated for the `ℚ`-algebra structure
  -- `AdjoinRoot.instAlgebra`, which agrees with `DivisionRing.toRatAlgebra` by `Subsingleton.elim`
  have htop := AdjoinRoot.adjoinRoot_eq_top (f := (curveX3SubXAddOne.baseChange ℚ).toAffine.f)
  rw [Subsingleton.elim (α := Algebra ℚ 𝕃) (AdjoinRoot.instAlgebra _)
    DivisionRing.toRatAlgebra] at htop
  exact eq_top_iff.2 (htop ▸ Algebra.adjoin_le (Set.singleton_subset_iff.2 hroot))

/-! ### The `2`-descent bound -/

/-- `x³ - x + 1` is its own only monic irreducible factor over `ℚ`. -/
noncomputable instance : Unique (curveX3SubXAddOne.baseChange ℚ).toAffine.f.Factors where
  default := ⟨_, irreducible_f_curveX3SubXAddOne, monic_f _, dvd_rfl⟩
  uniq p := Subtype.ext <| eq_of_monic_of_associated p.monic (monic_f _)
    (p.irreducible.associated_of_dvd irreducible_f_curveX3SubXAddOne p.dvd)

/-- The ring of integers of the cubic field `ℚ[X] ⧸ (x³ - x + 1)` has unit rank `1`. -/
private theorem finrank_units_ringOfIntegersFactor :
    finrank ℤ (Additive ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ)
      default)ˣ) = 1 :=
  (finrank_units_integralClosure ℚ 𝕃).trans
    (TauCeti.NumberField.Cubic23.units_rank_eq_one minpoly_cubic23Generator adjoin_cubic23Generator)

/-- The ring of integers of the cubic field `ℚ[X] ⧸ (x³ - x + 1)` has trivial class group, so the
`2`-torsion of its class group is trivial. -/
private theorem card_ker_powMonoidHom_classGroup_ringOfIntegersFactor :
    Nat.card (powMonoidHom 2 : ClassGroup
      ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) default) →* _).ker ≤
      1 := by
  have : IsPrincipalIdealRing
      ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) default) :=
    (isPrincipalIdealRing_integralClosure_iff ℚ 𝕃).mpr
      (TauCeti.NumberField.Cubic23.isPrincipalIdealRing minpoly_cubic23Generator
        adjoin_cubic23Generator)
  refine (Subgroup.card_le_card_group _).trans ?_
  rw [Nat.card_eq_fintype_card, card_classGroup_eq_one]

/-- **The Mordell–Weil rank of `y² = x³ - x + 1` over `ℚ` is at most `1`**, by explicit
`2`-descent. -/
theorem finrank_point_curveX3SubXAddOne_le_one :
    finrank ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point ≤ 1 := by
  set W := (curveX3SubXAddOne.baseChange ℚ).toAffine
  have hdiscr : W.f.discr = -(23 : ℕ) := by
    rw [discr_f]
    simp [W, curveX3SubXAddOne]
    norm_num
  -- `pow_rank_add_one_le_prod` is stated with classical decidability instances, so its point group
  -- is reconciled with the one here by `convert`
  have hbound : 2 ^ (finrank ℤ W.Point + 1) * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker ≤
      ∏ p : W.f.Factors, 2 ^ (finrank ℤ (Additive (W.ringOfIntegersFactor (𝓞 ℚ) p)ˣ) + 1) *
        Nat.card (powMonoidHom 2 : ClassGroup (W.ringOfIntegersFactor (𝓞 ℚ) p) →* _).ker := by
    convert W.pow_rank_add_one_le_prod (fun v ↦ by simp [W, curveX3SubXAddOne])
      (fun v ↦ by simp [W, curveX3SubXAddOne]) (fun v ↦ by simp [W, curveX3SubXAddOne])
      (fun v ↦ by
        rw [hdiscr, Valuation.map_neg]
        exact Rat.HeightOneSpectrum.exp_neg_one_le_valuation_natCast_of_squarefree v
          (by norm_num : Nat.Prime 23).squarefree)
      (fun ⟨r, hr⟩ ↦ by nlinarith [mul_self_nonneg r])
  have htors : Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker = 1 := by
    rw [(AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree two_ne_zero), AddSubgroup.card_bot]
  rw [Fintype.prod_unique, finrank_units_ringOfIntegersFactor, htors, mul_one] at hbound
  have h4 : 2 ^ (finrank ℤ W.Point + 1) ≤ 2 ^ 2 :=
    hbound.trans (Nat.mul_le_mul_left _ card_ker_powMonoidHom_classGroup_ringOfIntegersFactor)
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
  omega

end CubicField

/-! ### The rank and the group -/

/-- **The Mordell–Weil rank of `y² = x³ - x + 1` over `ℚ` is at least `1`**: the rational point
`(1, 1)` is nonzero, and the point group is torsion-free. -/
theorem one_le_finrank_point_curveX3SubXAddOne :
    1 ≤ finrank ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point := by
  have : Module.Finite ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr fg_point_of_numberField
  have hP := nonsingular_one_one_curveX3SubXAddOne
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨.some 1 1 hP, Point.some_ne_zero hP⟩

/-- **The Mordell–Weil group of `y² = x³ - x + 1` over `ℚ` has rank `1`.** -/
theorem finrank_point_curveX3SubXAddOne :
    finrank ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point = 1 :=
  finrank_point_curveX3SubXAddOne_le_one.antisymm one_le_finrank_point_curveX3SubXAddOne

/-- **The Mordell–Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic**: it is finitely
generated, torsion-free and of rank `1`. -/
theorem nonempty_addEquiv_int_point_curveX3SubXAddOne :
    Nonempty ((curveX3SubXAddOne.baseChange ℚ).toAffine.Point ≃+ ℤ) :=
  have : Module.Finite ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr fg_point_of_numberField
  ⟨((Module.basisUnique Unit finrank_point_curveX3SubXAddOne).equivFun.trans
    (LinearEquiv.funUnique Unit ℤ ℤ)).toAddEquiv⟩

end TauCeti.WorkedExamples
