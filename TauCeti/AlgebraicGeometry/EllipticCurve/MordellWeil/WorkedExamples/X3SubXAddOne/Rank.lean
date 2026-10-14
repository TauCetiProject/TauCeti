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
import Mathlib.Tactic.NormNum.Prime
import TauCeti.Algebra.Squarefree
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.TwoTorsion
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.WorkedExamples.Cubic23.Invariants
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# The Mordell–Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic

This file computes the rank of `E : y² = f(x) = x³ - x + 1` over `ℚ` by explicit `2`-descent: it
is one, and since `E(ℚ)` is torsion-free (`TauCeti.WorkedExamples.torsion_curveX3SubXAddOne_eq_bot`)
the Mordell–Weil group `E(ℚ)` is isomorphic to `ℤ`.

The upper bound is the `2`-descent rank bound `WeierstrassCurve.Affine.pow_rank_add_one_le_prod`,
`2 ^ (rank E(ℚ) + 1) · #E(ℚ)[2] ≤ ∏ₚ 2 ^ (rₚ + 1) · #Clₚ[2]`, the product running over the
irreducible factors `p` of `f`, with `rₚ` the unit rank and `Clₚ` the class group of the ring of
integers of `ℚ[x] ⧸ (p)`. Its inputs here are as follows.

* `f` is irreducible over `ℚ`: a rational root `e` would give the rational `2`-torsion point
  `(e, 0)`, and `E(ℚ)` has none. So the étale algebra of `f` is the cubic field `L = ℚ(α)`,
  `α³ - α + 1 = 0`, and the product has a single factor.
* The discriminant of `f` is the squarefree integer `-23`, so it vanishes to order at most `1` at
  every prime, and the coefficients of `f` are integers: no prime of `ℚ` is excluded.
* `θ = 1 - α² = α⁻¹` has minimal polynomial `X³ - X² + 1` over `ℤ` and generates `L`, so `L` is
  the cubic field of discriminant `-23` of `TauCeti.NumberField.Cubic23`. Its ring of integers is
  a principal ideal domain and its unit rank is `1`, so the single factor is `2 ^ 2 · 1 = 4`.

Since `E(ℚ)[2]` is trivial, the bound reads `2 ^ (rank E(ℚ) + 1) ≤ 4`, so the rank is at most `1`.
Conversely `(1, 1)` is a nonzero point of the torsion-free group `E(ℚ)`, so it has infinite order
and the rank is at least `1`.

## Main results

* `TauCeti.WorkedExamples.not_isOfFinAddOrder_curveX3SubXAddOnePoint`: the point `(1, 1)` has
  infinite order.
* `TauCeti.WorkedExamples.finrank_point_curveX3SubXAddOne`: the rank of `E(ℚ)` is one.
* `TauCeti.WorkedExamples.nonempty_point_curveX3SubXAddOne_addEquiv_int`: `E(ℚ) ≅ ℤ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1 and X.1.

## Provenance

The argument follows Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `3bfe124`),
`EllipticCurves/RankExample.lean`, which proves `E(ℚ) ≅ ℤ` for the same curve through the same
`2`-Selmer bound, the point `(1, 1)` and the triviality of the rational torsion. There the
irreducibility of `f` comes from reduction modulo `2`, and the class number and unit rank of `L`
from a bound on its discriminant; here the irreducibility comes from the triviality of `E(ℚ)[2]`,
and the arithmetic of `L` from `TauCeti.NumberField.Cubic23`, reached through the generator
`θ = α⁻¹`.
-/

public section

open Polynomial WeierstrassCurve Affine IsDedekindDomain NumberField Module

namespace TauCeti.WorkedExamples

/-! ### The cubic `x³ - x + 1` -/

private theorem f_curveX3SubXAddOne :
    (curveX3SubXAddOne.baseChange ℚ).toAffine.f = X ^ 3 - X + 1 := by
  simp [Affine.f, curveX3SubXAddOne, WeierstrassCurve.baseChange]
  ring

/-- `E(ℚ)[2]` is trivial. The decidable equality on `ℚ` is a variable because the group law
depends on it, and the rank bound below is stated with the classical one. -/
private theorem card_ker_nsmul_two_curveX3SubXAddOne [DecidableEq ℚ] :
    Nat.card (nsmulAddMonoidHom (α := (curveX3SubXAddOne.baseChange ℚ).toAffine.Point) 2).ker =
      1 := by
  obtain rfl : ‹DecidableEq ℚ› = instDecidableEqRat := Subsingleton.elim _ _
  have hker : (nsmulAddMonoidHom (α := (curveX3SubXAddOne.baseChange ℚ).toAffine.Point) 2).ker =
      ⊥ := by
    refine eq_bot_iff.mpr fun P hP ↦ ?_
    rw [← torsion_curveX3SubXAddOne_eq_bot]
    exact (AddCommGroup.mem_torsion P).mpr
      (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, two_pos, AddMonoidHom.mem_ker.mp hP⟩)
  rw [hker, AddSubgroup.card_bot]

/-- `x³ - x + 1` has no rational root, since a root `e` would give the `2`-torsion point
`(e, 0)`. -/
private theorem eval_f_curveX3SubXAddOne_ne_zero (x : ℚ) :
    (curveX3SubXAddOne.baseChange ℚ).toAffine.f.eval x ≠ 0 := by
  classical
  intro hx
  have h := (curveX3SubXAddOne.baseChange ℚ).toAffine.card_ker_nsmul_two
  rw [card_ker_nsmul_two_curveX3SubXAddOne] at h
  replace h := Nat.card_eq_zero.mp (by omega : Nat.card
    {x : ℚ // (curveX3SubXAddOne.baseChange ℚ).toAffine.f.eval x = 0} = 0)
  have : Finite {x : ℚ // (curveX3SubXAddOne.baseChange ℚ).toAffine.f.eval x = 0} :=
    Set.Finite.to_subtype (Polynomial.finite_setOfPred_isRoot (Affine.f_ne_zero _))
  rcases h with h | h
  · exact h.false ⟨x, hx⟩
  · exact h.not_finite this

private theorem irreducible_f_curveX3SubXAddOne :
    Irreducible (curveX3SubXAddOne.baseChange ℚ).toAffine.f :=
  irreducible_of_degree_le_three_of_not_isRoot (by rw [Affine.natDegree_f]; decide)
    eval_f_curveX3SubXAddOne_ne_zero

private theorem coe_factors_curveX3SubXAddOne
    (p : (curveX3SubXAddOne.baseChange ℚ).toAffine.f.Factors) :
    (p : ℚ[X]) = (curveX3SubXAddOne.baseChange ℚ).toAffine.f :=
  eq_of_monic_of_associated p.monic (Affine.monic_f _)
    (p.irreducible.associated_of_dvd irreducible_f_curveX3SubXAddOne p.dvd)

/-! ### The cubic field -/

section Field

variable (p : (curveX3SubXAddOne.baseChange ℚ).toAffine.f.Factors)

private theorem root_pow_three_sub_root_add_one :
    AdjoinRoot.root (p : ℚ[X]) ^ 3 - AdjoinRoot.root (p : ℚ[X]) + 1 = 0 := by
  have h := (congrArg (eval₂ (AdjoinRoot.of (p : ℚ[X])) (AdjoinRoot.root (p : ℚ[X])))
    ((coe_factors_curveX3SubXAddOne p).trans f_curveX3SubXAddOne)).symm.trans
      (AdjoinRoot.eval₂_root (p : ℚ[X]))
  simpa using h

private theorem isIntegral_root : _root_.IsIntegral ℤ (AdjoinRoot.root (p : ℚ[X])) :=
  ⟨X ^ 3 - X + 1, by monicity!, by
    simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_one]
    exact root_pow_three_sub_root_add_one p⟩

/-- The field `ℚ(α)`, `α³ - α + 1 = 0`, is generated by `θ = 1 - α² = α⁻¹`, an integer with
minimal polynomial `X³ - X² + 1`. -/
private theorem exists_minpoly_eq [NumberField (AdjoinRoot (p : ℚ[X]))] :
    ∃ θ : 𝓞 (AdjoinRoot (p : ℚ[X])), minpoly ℤ θ = X ^ 3 - X ^ 2 + 1 ∧
      Algebra.adjoin ℚ {(θ : AdjoinRoot (p : ℚ[X]))} = ⊤ := by
  have hα := root_pow_three_sub_root_add_one p
  set α := AdjoinRoot.root (p : ℚ[X])
  let θ : 𝓞 (AdjoinRoot (p : ℚ[X])) :=
    ⟨1 - α ^ 2, isIntegral_one.sub ((isIntegral_root p).pow 2)⟩
  have hθ : (θ : AdjoinRoot (p : ℚ[X])) = 1 - α ^ 2 := rfl
  have hg : Irreducible (X ^ 3 - X ^ 2 + 1 : ℤ[X]) :=
    Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _ (by monicity!) (by
      convert Polynomial.irreducible_X_pow_three_add_X_sq_add_one_zmod_two using 1
      simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, CharTwo.sub_eq_add])
  have haeval : aeval θ (X ^ 3 - X ^ 2 + 1 : ℤ[X]) = 0 := by
    apply RingOfIntegers.ext
    simp only [map_add, map_sub, map_pow, aeval_X, map_one, map_zero, hθ]
    linear_combination (-α ^ 3 + α + 1) * hα
  refine ⟨θ, ?_, ?_⟩
  · exact eq_of_monic_of_associated (minpoly.monic (RingOfIntegers.isIntegral θ)) (by monicity!)
      ((minpoly.irreducible (RingOfIntegers.isIntegral θ)).associated_of_dvd hg
        (minpoly.isIntegrallyClosed_dvd (RingOfIntegers.isIntegral θ) haeval))
  · have hmem : α ∈ Algebra.adjoin ℚ {(θ : AdjoinRoot (p : ℚ[X]))} := by
      have : α = (θ : AdjoinRoot (p : ℚ[X])) - (θ : AdjoinRoot (p : ℚ[X])) ^ 2 := by
        rw [hθ]
        linear_combination α * hα
      rw [this]
      have hθmem :
          (θ : AdjoinRoot (p : ℚ[X])) ∈ Algebra.adjoin ℚ {(θ : AdjoinRoot (p : ℚ[X]))} :=
        Algebra.subset_adjoin (Set.mem_singleton _)
      exact sub_mem hθmem (pow_mem hθmem 2)
    -- `Algebra.adjoin` here is for the `ℚ`-algebra structure of the number field, not that of
    -- `AdjoinRoot`, so `AdjoinRoot.adjoinRoot_eq_top` does not apply; argue on polynomials.
    refine Algebra.eq_top_iff.mpr fun x ↦ ?_
    induction x using AdjoinRoot.induction_on with
    | ih g =>
      induction g using Polynomial.induction_on with
      | C c =>
        have hc := Subalgebra.algebraMap_mem (Algebra.adjoin ℚ {(θ : AdjoinRoot (p : ℚ[X]))}) c
        rwa [eq_ratCast, ← eq_ratCast (AdjoinRoot.of (p : ℚ[X])), ← AdjoinRoot.mk_C] at hc
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | monomial n c ih =>
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
        exact mul_mem ih hmem

/-- The factor of the rank bound at the single field factor `L` is `2 ^ (1 + 1) · 1 = 4`: the ring
of integers of `L` is a principal ideal domain with unit rank `1`. -/
private theorem two_pow_mul_card_ker_eq_four :
    2 ^ (finrank ℤ (Additive
        ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p)ˣ) + 1) *
      Nat.card (powMonoidHom 2 :
        ClassGroup ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p) →*
          ClassGroup ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p)).ker =
      4 := by
  have : NumberField (AdjoinRoot (p : ℚ[X])) := .of_module_finite ℚ _
  obtain ⟨θ, hmin, hgen⟩ := exists_minpoly_eq p
  let e : (curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p ≃ₐ[𝓞 ℚ]
      𝓞 (AdjoinRoot (p : ℚ[X])) :=
    IsIntegralClosure.equiv (𝓞 ℚ) (integralClosure (𝓞 ℚ) (AdjoinRoot (p : ℚ[X])))
      (AdjoinRoot (p : ℚ[X])) (𝓞 (AdjoinRoot (p : ℚ[X])))
  have hrank : finrank ℤ (Additive
      ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p)ˣ) = 1 := by
    rw [LinearEquiv.finrank_eq
      (MulEquiv.toAdditive (Units.mapEquiv e.toRingEquiv.toMulEquiv)).toIntLinearEquiv,
      NumberField.Units.finrank_eq, TauCeti.NumberField.Cubic23.units_rank_eq_one hmin hgen]
  have := TauCeti.NumberField.Cubic23.isPrincipalIdealRing hmin hgen
  have : IsPrincipalIdealRing
      ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
  have : Subsingleton
      (ClassGroup ((curveX3SubXAddOne.baseChange ℚ).toAffine.ringOfIntegersFactor (𝓞 ℚ) p)) :=
    Fintype.card_le_one_iff_subsingleton.mp card_classGroup_eq_one.le
  rw [hrank, Nat.card_unique]
  norm_num

end Field

/-! ### The rank -/

private theorem discr_f_curveX3SubXAddOne :
    (curveX3SubXAddOne.baseChange ℚ).toAffine.f.discr = -23 := by
  rw [f_curveX3SubXAddOne, Polynomial.discr_of_degree_eq_three (by compute_degree!)]
  norm_num [coeff_add, coeff_sub, coeff_X_pow, coeff_one, coeff_X]

private theorem exp_neg_one_le_valuation_neg_twenty_three (v : HeightOneSpectrum (𝓞 ℚ)) :
    WithZero.exp (-1) ≤ v.valuation ℚ (-23) := by
  have hsq : Squarefree (-23 : 𝓞 ℚ) := by
    rw [← squarefree_map_iff Rat.ringOfIntegersEquiv, map_neg, map_ofNat]
    exact Int.squarefree_natAbs.mp (by norm_num : Nat.Prime 23).squarefree
  rw [show (-23 : ℚ) = algebraMap (𝓞 ℚ) ℚ (-23) by rw [map_neg, map_ofNat],
    v.valuation_of_algebraMap]
  exact v.exp_neg_one_le_intValuation_of_squarefree hsq

/-- The rational point `(1, 1)` of `y² = x³ - x + 1`. -/
def curveX3SubXAddOnePoint : (curveX3SubXAddOne.baseChange ℚ).toAffine.Point :=
  .some 1 1 (nonsingular_curveX3SubXAddOne (by norm_num))

/-- `curveX3SubXAddOnePoint` is the point `(1, 1)`. -/
@[simp]
theorem curveX3SubXAddOnePoint_def :
    curveX3SubXAddOnePoint = .some 1 1 (nonsingular_curveX3SubXAddOne (by norm_num)) := (rfl)

/-- **The point `(1, 1)` of `y² = x³ - x + 1` has infinite order**, since it is nonzero and the
rational point group is torsion-free. -/
theorem not_isOfFinAddOrder_curveX3SubXAddOnePoint :
    ¬IsOfFinAddOrder curveX3SubXAddOnePoint :=
  fun h ↦ Point.some_ne_zero _ h.eq_zero'

/-- The rank bound of explicit `2`-descent gives `rank E(ℚ) ≤ 1`. It is stated with the classical
decidable equality on `ℚ`, which is substituted for the variable one. -/
private theorem finrank_point_curveX3SubXAddOne_le_one [DecidableEq ℚ] :
    finrank ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point ≤ 1 := by
  obtain rfl : ‹DecidableEq ℚ› = fun a b ↦ Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  have : Fintype (curveX3SubXAddOne.baseChange ℚ).toAffine.f.Factors :=
    @Fintype.ofFinite _ (Polynomial.Factors.finite (Affine.f_ne_zero _))
  have hcard : Fintype.card (curveX3SubXAddOne.baseChange ℚ).toAffine.f.Factors = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨_, irreducible_f_curveX3SubXAddOne, Affine.monic_f _,
      dvd_rfl⟩, fun q ↦ Subtype.ext (coe_factors_curveX3SubXAddOne q)⟩
  have h := (curveX3SubXAddOne.baseChange ℚ).toAffine.pow_rank_add_one_le_prod
    (fun v ↦ by simp) (fun v ↦ by simp) (fun v ↦ by simp)
    (fun v ↦ discr_f_curveX3SubXAddOne ▸ exp_neg_one_le_valuation_neg_twenty_three v)
    (fun ⟨r, hr⟩ ↦ by nlinarith [mul_self_nonneg r])
  rw [@card_ker_nsmul_two_curveX3SubXAddOne fun a b ↦ Classical.propDecidable (a = b), mul_one,
    Finset.prod_congr rfl fun p _ ↦ two_pow_mul_card_ker_eq_four p, Finset.prod_const,
    Finset.card_univ, hcard, pow_one] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    (h.trans_eq (by norm_num : 4 = 2 ^ 2))
  omega

/-- **The rank of `y² = x³ - x + 1` over `ℚ` is one**: the `2`-descent bound gives at most one,
and the point `(1, 1)` of infinite order at least one. -/
theorem finrank_point_curveX3SubXAddOne :
    finrank ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point = 1 := by
  refine le_antisymm finrank_point_curveX3SubXAddOne_le_one ?_
  have : Module.Finite ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr fg_point_of_numberField
  refine Nat.one_le_iff_ne_zero.mpr fun h ↦ not_isOfFinAddOrder_curveX3SubXAddOnePoint ?_
  obtain ⟨a, ha, hP⟩ := Module.finrank_eq_zero_iff.mp h curveX3SubXAddOnePoint
  exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, ha, hP⟩

/-- **The Mordell–Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic**: it is finitely
generated and torsion-free, so free, and of rank one. -/
theorem nonempty_point_curveX3SubXAddOne_addEquiv_int :
    Nonempty ((curveX3SubXAddOne.baseChange ℚ).toAffine.Point ≃+ ℤ) := by
  have : Module.Finite ℤ (curveX3SubXAddOne.baseChange ℚ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr fg_point_of_numberField
  exact ⟨((finBasisOfFinrankEq ℤ _ finrank_point_curveX3SubXAddOne).equivFun.trans
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ)).toAddEquiv⟩

end TauCeti.WorkedExamples
