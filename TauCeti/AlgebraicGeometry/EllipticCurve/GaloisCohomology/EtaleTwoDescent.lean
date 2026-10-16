/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.TwoDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.RingTheory.AdjoinRoot.Factors
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The cohomological and étale-algebra `2`-descent maps

This file compares the Kummer map for multiplication by two with the explicit `x - T` descent
map into the square classes of the étale algebra of the cubic `2`-division polynomial. The
comparison is made one irreducible factor at a time. For a factor `p`, its universal root
`θ ∈ K[X]/(p)` gives a rational point `(θ, 0)` of order two after base change. Applying the Weil
pairing character attached to this point to the restricted cohomological Kummer class recovers
the `p`-component of the explicit descent map.

This is the factorwise compatibility needed to assemble the explicit and cohomological
`2`-Selmer groups.

## Main definitions

* `TauCeti.TwoDescent.explicitFactor`: projection of an étale-algebra square class to the power
  classes of one irreducible factor.
* `TauCeti.TwoDescent.factorCohomologicalMap`: restriction to the factor field followed by the
  Weil-pairing character attached to its universal root.

## Main results

* `TauCeti.TwoDescent.explicitFactor_μ₀_eq_twoDescentUnit`: the explicit factor of `μ₀(P)` is the
  power class of the rootwise descent unit.
* `TauCeti.TwoDescent.factorCohomologicalMap_kummerMap`: the factorwise cohomological image of
  the Kummer class of `P` is the Kummer class of that same rootwise descent unit.

Together these are the factorwise comparison. The remaining roadmap target is to assemble the
factors and identify the explicit and cohomological local conditions.

## Roadmap

This advances `TauCetiRoadmap/EllipticCurves/README.md`, Layer 7, the target comparing the
explicit étale-algebra `2`-Selmer group with the abstract cohomological `Sel₂(E/K)`.

## Provenance

The comparison proof is new glue over the existing `TwoDescent`, `Restriction`, and `XSubT`
APIs; no code is copied. The rootwise identity is the classical calculation in Silverman X.1.4.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.4.
-/

public section

noncomputable section

open Polynomial TauCeti.ContCohomology

namespace TauCeti

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

namespace TwoDescent

local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

variable [W.IsElliptic] [W.toAffine.IsCharNeTwoNF]

omit [DecidableEq K] [W.IsElliptic] in
/-- The universal root of a factor of the `2`-division cubic lies on the base-changed curve. -/
private theorem factorRoot_equation (p : W.toAffine.f.Factors) :
    (W.baseChange (𝕃 p)).toAffine.Equation (θ p) 0 := by
  let : (W.baseChange (𝕃 p)).toAffine.IsCharNeTwoNF :=
    W.toAffine.isCharNeTwoNF_map (ι p)
  rw [WeierstrassCurve.Affine.equation_iff_eval_f_eq_sq]
  rw [zero_pow two_ne_zero, W.toAffine.baseChange_f]
  rw [Polynomial.eval_map]
  obtain ⟨q, hq⟩ := p.dvd
  calc
    _ = Polynomial.eval₂ (ι p) (θ p) ((p : K[X]) * q) := congrArg _ hq
    _ = 0 := by
      rw [Polynomial.eval₂_mul, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, zero_mul]

omit [DecidableEq K] in
/-- The universal root of a factor of the `2`-division cubic is a nonsingular point of the
base-changed elliptic curve. -/
theorem factorRoot_nonsingular (p : W.toAffine.f.Factors) :
    (W.baseChange (𝕃 p)).toAffine.Nonsingular (θ p) 0 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (factorRoot_equation W p)

omit [DecidableEq K] [W.IsElliptic] in
/-- In characteristic-`≠ 2` normal form, the universal root point `(θ, 0)` is killed by two. -/
theorem factorRoot_polynomialY (p : W.toAffine.f.Factors) :
    (W.baseChange (𝕃 p)).toAffine.polynomialY.evalEval (θ p) 0 = 0 := by
  let : (W.baseChange (𝕃 p)).toAffine.IsCharNeTwoNF :=
    W.toAffine.isCharNeTwoNF_map (ι p)
  rw [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.a₁_of_isCharNeTwoNF, WeierstrassCurve.a₃_of_isCharNeTwoNF]
  ring

omit [DecidableEq K] [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
/-- Invertibility of `2` passes from the ground field to every factor field. -/
private theorem isUnit_two_factor (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K)) :
    IsUnit ((2 : ℕ) : 𝕃 p) := by
  simpa only [map_natCast] using h2.map (ι p)

/-- Projection of an étale-algebra square class to the power classes of one irreducible factor. -/
noncomputable def explicitFactor (p : W.toAffine.f.Factors) :
    W.toAffine.M →* powerClassQuotient (𝕃 p)ˣ 2 :=
  (QuotientGroup.quotientMulEquivOfEq
      (powerSubgroup_eq_range_powMonoidHom (𝕃 p)ˣ 2).symm).toMonoidHom.comp
    ((Pi.evalMonoidHom _ p).comp
      (AdjoinRoot.modPowEquivPiFactors W.toAffine.f_ne_zero
        W.toAffine.squarefree_f 2).toMonoidHom)

omit [DecidableEq K] in
/-- `explicitFactor` is the corresponding component of `modPowEquivPiFactors`. -/
@[simp]
theorem explicitFactor_apply (p : W.toAffine.f.Factors) (m : W.toAffine.M) :
    explicitFactor W p m =
      QuotientGroup.quotientMulEquivOfEq
        (powerSubgroup_eq_range_powMonoidHom (𝕃 p)ˣ 2).symm
        (AdjoinRoot.modPowEquivPiFactors W.toAffine.f_ne_zero W.toAffine.squarefree_f 2 m p) :=
  (rfl)

omit [DecidableEq K] in
open scoped Classical in
/- The component at an irreducible factor of the explicit étale-algebra descent map is the
rootwise descent unit `x - θ`, including the corrected value at a `2`-torsion point. -/
private theorem explicitFactor_eq_twoDescentUnit (p : W.toAffine.f.Factors)
    (P : W.toAffine.Point) :
    AdjoinRoot.modPowEquivPiFactors W.toAffine.f_ne_zero W.toAffine.squarefree_f 2
        (W.toAffine.μ₀ P) p =
      QuotientGroup.mk ((W.baseChange (𝕃 p)).twoDescentUnit
        (factorRoot_nonsingular W p) (factorRoot_polynomialY W p)
        (W.toAffine.pointMap (𝕃 p) P)) := by
  let : (W.baseChange (𝕃 p)).toAffine.IsCharNeTwoNF :=
    W.toAffine.isCharNeTwoNF_map (ι p)
  match P with
  | .zero =>
      have hμ : W.toAffine.μ₀ (.zero) = 1 := W.toAffine.μ₀_zero
      have hP : W.toAffine.pointMap (𝕃 p) (.zero) = 0 := map_zero _
      rw [hμ, map_one, Pi.one_apply, hP, WeierstrassCurve.twoDescentUnit_zero,
        QuotientGroup.mk_one]
  | .some x y h =>
      rw [WeierstrassCurve.Affine.μ₀_some]
      by_cases hx : W.toAffine.f.eval x = 0
      · rw [W.toAffine.μX_of_eval_f_eq_zero hx,
          AdjoinRoot.modPowEquivPiFactors_unit]
        apply congrArg QuotientGroup.mk
        apply Units.ext
        simp only [IsUnit.unit_spec]
        rw [W.toAffine.pointMap_some]
        rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X]
        by_cases hxe : ι p x = θ p
        · rw [WeierstrassCurve.coe_twoDescentUnit_some_of_eq _ _ _ _ hxe]
          rw [AdjoinRoot.algebraMap_eq] at hxe
          rw [hxe,
            sub_self, zero_add, ← AdjoinRoot.aeval_eq]
          simp only [AdjoinRoot.aeval_eq, map_add, map_pow, AdjoinRoot.mk_X, map_mul,
            AdjoinRoot.mk_C]
          rw [WeierstrassCurve.Affine.evalEval_polynomialX,
            WeierstrassCurve.a₁_of_isCharNeTwoNF]
          simp only [zero_mul, zero_sub, neg_neg]
          rw [hxe]
          rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₂,
            WeierstrassCurve.map_a₄, AdjoinRoot.algebraMap_eq]
          ring
        · rw [WeierstrassCurve.coe_twoDescentUnit_some_of_ne _ _ _ _ hxe]
          rw [AdjoinRoot.algebraMap_eq] at hxe
          have hprod : AdjoinRoot.mk (p : K[X]) (W.toAffine.fCofactor x) *
              (θ p - AdjoinRoot.of (p : K[X]) x) = 0 := by
            calc
              _ = AdjoinRoot.mk (p : K[X])
                  (W.toAffine.fCofactor x * (X - C x)) := by
                    rw [map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
              _ = AdjoinRoot.mk (p : K[X]) W.toAffine.f := by
                    exact congrArg (AdjoinRoot.mk (p : K[X]))
                      (W.toAffine.f_eq_mul_of_eval_eq_zero hx).symm
              _ = 0 := AdjoinRoot.mk_eq_zero.mpr p.dvd
          have hc : AdjoinRoot.mk (p : K[X]) (W.toAffine.fCofactor x) = 0 :=
            (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (Ne.symm hxe))
          rw [hc, add_zero, AdjoinRoot.algebraMap_eq]
      · rw [W.toAffine.μX_of_eval_f_ne_zero hx,
          AdjoinRoot.modPowEquivPiFactors_unit]
        apply congrArg QuotientGroup.mk
        apply Units.ext
        simp only [IsUnit.unit_spec]
        rw [W.toAffine.pointMap_some]
        rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X]
        have hxe : ι p x ≠ θ p := by
          intro he
          apply hx
          apply (ι p).injective
          rw [map_zero]
          have hroot : (W.baseChange (𝕃 p)).toAffine.f.eval (θ p) = 0 := by
            simpa using (WeierstrassCurve.Affine.equation_iff_eval_f_eq_sq
              (W := (W.baseChange (𝕃 p)).toAffine) (θ p) 0).mp
                (factorRoot_equation W p)
          calc
            ι p (W.toAffine.f.eval x) =
                (W.baseChange (𝕃 p)).toAffine.f.eval (ι p x) :=
              (W.toAffine.eval_baseChange_f (𝕃 p) x).symm
            _ = (W.baseChange (𝕃 p)).toAffine.f.eval (θ p) :=
              congrArg (fun z => (W.baseChange (𝕃 p)).toAffine.f.eval z) he
            _ = 0 := hroot
        rw [WeierstrassCurve.coe_twoDescentUnit_some_of_ne _ _ _ _ hxe]
        rw [AdjoinRoot.algebraMap_eq]

omit [DecidableEq K] in
open scoped Classical in
/-- The named factor projection sends `μ₀(P)` to the power class of its rootwise descent unit. -/
theorem explicitFactor_μ₀_eq_twoDescentUnit (p : W.toAffine.f.Factors)
    (P : W.toAffine.Point) :
    explicitFactor W p (W.toAffine.μ₀ P) =
      powerClassHom (𝕃 p)ˣ 2
        ((W.baseChange (𝕃 p)).twoDescentUnit
          (factorRoot_nonsingular W p) (factorRoot_polynomialY W p)
          (W.toAffine.pointMap (𝕃 p) P)) := by
  rw [explicitFactor_apply, explicitFactor_eq_twoDescentUnit, powerClassHom_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]

/-- The Weil-pairing character associated to the universal root point of a factor of the
`2`-division cubic. -/
def factorTorsionCharacter (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K)) :
    (W.baseChange (𝕃 p)).TorsionCoeff 2 →+[AbsoluteGaloisGroup (𝕃 p)]
      KummerCoeff (𝕃 p) 2 :=
  (W.baseChange (𝕃 p)).twoTorsionCharacter
    (factorRoot_nonsingular W p) (factorRoot_polynomialY W p) (isUnit_two_factor W p h2)

/-- Restriction to a factor field followed by the Weil-pairing character of its universal root. -/
noncomputable def factorCohomologicalMap (p : W.toAffine.f.Factors)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
    (h2 : IsUnit ((2 : ℕ) : K)) :
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) →+
      H1 (AbsoluteGaloisGroup (𝕃 p)) (KummerCoeff (𝕃 p) 2) :=
  (explicitCoeff1 (AbsoluteGaloisGroup (𝕃 p))
      ((W.baseChange (𝕃 p)).TorsionCoeff 2) (factorTorsionCharacter W p h2)
      continuous_of_discreteTopology).comp (W.torsionRes τ 2)

/-- The Kummer class of the rootwise descent unit attached to a rational point. -/
noncomputable def rootwiseKummerClass (p : W.toAffine.f.Factors)
    (h2 : IsUnit ((2 : ℕ) : K)) (P : W.toAffine.Point) :
    H1 (AbsoluteGaloisGroup (𝕃 p)) (KummerCoeff (𝕃 p) 2) :=
  Multiplicative.toAdd
    (kummerMap (𝕃 p) 2 (isUnit_two_factor W p h2)
      ((W.baseChange (𝕃 p)).twoDescentUnit
        (factorRoot_nonsingular W p) (factorRoot_polynomialY W p)
        (W.toAffine.pointMap (𝕃 p) P)))

omit [DecidableEq K] in
private theorem factorCohomologicalMap_apply (p : W.toAffine.f.Factors)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
    (h2 : IsUnit ((2 : ℕ) : K))
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    factorCohomologicalMap W p τ h2 c =
      explicitCoeff1 (AbsoluteGaloisGroup (𝕃 p))
        ((W.baseChange (𝕃 p)).TorsionCoeff 2) (factorTorsionCharacter W p h2)
        continuous_of_discreteTopology (W.torsionRes τ 2 c) :=
  (rfl)

/-- Restricting the cohomological Kummer class to a factor field and applying its universal-root
character gives the Kummer class of the same rootwise descent unit that occurs in
`explicitFactor_μ₀_eq_twoDescentUnit`. -/
theorem factorCohomologicalMap_kummerMap (p : W.toAffine.f.Factors)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
    (h2 : IsUnit ((2 : ℕ) : K)) (P : W.toAffine.Point) :
    factorCohomologicalMap W p τ h2 (W.kummerMap 2 h2 P) =
      rootwiseKummerClass W p h2 P := by
  let h2p : IsUnit ((2 : ℕ) : 𝕃 p) := isUnit_two_factor W p h2
  rw [factorCohomologicalMap_apply, W.torsionRes_kummerMap τ h2 P]
  simpa only [factorTorsionCharacter, rootwiseKummerClass] using
    (W.baseChange (𝕃 p)).explicitCoeff1_twoTorsionCharacter_kummerMap
      (factorRoot_nonsingular W p) (factorRoot_polynomialY W p) h2p
      (W.toAffine.pointMap (𝕃 p) P)

end TwoDescent

end TauCeti
