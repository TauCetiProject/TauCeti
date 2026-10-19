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
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EmbeddingIndependence
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition

/-!
# The cohomological and étale-algebra `2`-descent maps

This file compares the Kummer map for multiplication by two with the explicit `x - T` descent
map into the square classes of the étale algebra of the cubic `2`-division polynomial. The
comparison is first made one irreducible factor at a time. For a factor `p`, its universal root
`θ ∈ K[X]/(p)` gives a rational point `(θ, 0)` of order two after base change. Applying the Weil
pairing character attached to this point to the restricted cohomological Kummer class recovers
the `p`-component of the explicit descent map.

The square classes of the étale algebra are the product of the square classes of its field
factors, and the Kummer isomorphism identifies the square classes of each factor field with its
`H¹(G, μ₂)`. Reading the factorwise maps through these identifications assembles them into one
cohomological `2`-descent map

```text
H¹(G_K, E[2]) ⟶ (K[X] ⧸ (f))ˣ ⧸ squares,
```

which does not depend on the embeddings of separable closures used for the restrictions. Composed
with the Kummer map `E(K) → H¹(G_K, E[2])` it is the explicit `x - T` descent map. The explicit
and cohomological `2`-Selmer groups are compared through this map; that comparison also needs its
injectivity and the agreement of the local conditions, which are not proved in this file. The
rootwise identity is the classical calculation in Silverman X.1.4.

## Main definitions

* `TauCeti.TwoDescent.explicitFactor`: projection of an étale-algebra square class to the power
  classes of one irreducible factor.
* `TauCeti.TwoDescent.explicitFactorEquiv`: the square classes of the étale algebra as the product
  of the square classes of its field factors.
* `TauCeti.TwoDescent.factorCohomologicalMap`: restriction to the factor field followed by the
  Weil-pairing character attached to its universal root.
* `TauCeti.TwoDescent.cohomologicalMap`: the cohomological `2`-descent map
  `H¹(G_K, E[2]) → (K[X] ⧸ (f))ˣ ⧸ squares`.

## Main results

* `TauCeti.TwoDescent.explicitFactor_μ₀_eq_twoDescentUnit`: the explicit factor of `μ₀(P)` is the
  power class of the rootwise descent unit.
* `TauCeti.TwoDescent.factorCohomologicalMap_kummerMap`: the factorwise cohomological image of
  the Kummer class of `P` is the Kummer class of that same rootwise descent unit.
* `TauCeti.TwoDescent.kummerIso_explicitFactor_cohomologicalMap`: the factor components of the
  cohomological descent map, for any embeddings of separable closures.
* `TauCeti.TwoDescent.cohomologicalMap_eq_one_iff`: a class lies in the kernel of the
  cohomological descent map exactly when all of its factorwise images vanish.
* `TauCeti.TwoDescent.cohomologicalMap_kummerMap`: on the Kummer class of `P`, the cohomological
  descent map is the explicit descent map `μ₀(P)`.

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
@[simp]
theorem factorRoot_polynomialY (p : W.toAffine.f.Factors) :
    (W.baseChange (𝕃 p)).toAffine.polynomialY.evalEval (θ p) 0 = 0 := by
  let : (W.baseChange (𝕃 p)).toAffine.IsCharNeTwoNF :=
    W.toAffine.isCharNeTwoNF_map (ι p)
  rw [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.a₁_of_isCharNeTwoNF, WeierstrassCurve.a₃_of_isCharNeTwoNF]
  ring

/-- The square classes of the étale algebra are the product of the square classes of its field
factors. -/
noncomputable def explicitFactorEquiv :
    W.toAffine.M ≃* ((p : W.toAffine.f.Factors) → powerClassQuotient (𝕃 p)ˣ 2) :=
  (AdjoinRoot.modPowEquivPiFactors W.toAffine.f_ne_zero W.toAffine.squarefree_f 2).trans
    (MulEquiv.piCongrRight fun p ↦ QuotientGroup.quotientMulEquivOfEq
      (powerSubgroup_eq_range_powMonoidHom (𝕃 p)ˣ 2).symm)

/-- Projection of an étale-algebra square class to the power classes of one irreducible factor:
the component at `p` of `explicitFactorEquiv`. -/
noncomputable def explicitFactor (p : W.toAffine.f.Factors) :
    W.toAffine.M →* powerClassQuotient (𝕃 p)ˣ 2 :=
  (Pi.evalMonoidHom _ p).comp (explicitFactorEquiv W).toMonoidHom

omit [DecidableEq K] in
/-- The components of `explicitFactorEquiv` are the projections `explicitFactor`. -/
@[simp]
theorem explicitFactorEquiv_apply (m : W.toAffine.M) (p : W.toAffine.f.Factors) :
    explicitFactorEquiv W m p = explicitFactor W p m :=
  (rfl)

omit [DecidableEq K] in
/-- `explicitFactor` is the corresponding component of `modPowEquivPiFactors`. -/
@[simp]
theorem explicitFactor_apply (p : W.toAffine.f.Factors) (m : W.toAffine.M) :
    explicitFactor W p m =
      QuotientGroup.quotientMulEquivOfEq
        (powerSubgroup_eq_range_powMonoidHom (𝕃 p)ˣ 2).symm
        (AdjoinRoot.modPowEquivPiFactors W.toAffine.f_ne_zero W.toAffine.squarefree_f 2 m p) :=
  (rfl)

omit [DecidableEq K] [W.IsElliptic] in
/-- If `x = θ` in the factor field, the cofactor `f / (X - x)` takes there the value
`c_T = -W_X(θ, 0)` of the rootwise descent unit at the `2`-torsion point `(θ, 0)`. -/
private theorem mk_fCofactor_of_eq (p : W.toAffine.f.Factors) {x : K} (hxe : ι p x = θ p) :
    AdjoinRoot.mk (p : K[X]) (W.toAffine.fCofactor x) =
      -(W.baseChange (𝕃 p)).toAffine.polynomialX.evalEval (θ p) 0 := by
  let : (W.baseChange (𝕃 p)).toAffine.IsCharNeTwoNF :=
    W.toAffine.isCharNeTwoNF_map (ι p)
  rw [AdjoinRoot.algebraMap_eq] at hxe
  simp only [WeierstrassCurve.Affine.fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, hxe, WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.a₁_of_isCharNeTwoNF, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, AdjoinRoot.algebraMap_eq]
  ring

omit [DecidableEq K] [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
/-- At a root `x` of the `2`-division cubic with `x ≠ θ` in the factor field, the cofactor
`f / (X - x)` vanishes there. -/
private theorem mk_fCofactor_of_ne (p : W.toAffine.f.Factors) {x : K}
    (hx : W.toAffine.f.eval x = 0) (hxe : ι p x ≠ θ p) :
    AdjoinRoot.mk (p : K[X]) (W.toAffine.fCofactor x) = 0 := by
  have hprod : AdjoinRoot.mk (p : K[X]) (W.toAffine.fCofactor x * (X - C x)) = 0 := by
    rw [← W.toAffine.f_eq_mul_of_eval_eq_zero hx]
    exact AdjoinRoot.mk_eq_zero.mpr p.dvd
  rw [map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq] at hprod
  exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hxe.symm)

omit [DecidableEq K] [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
/-- A non-root `x` of the `2`-division cubic is distinct from `θ` in the factor field. -/
private theorem ne_root_of_eval_f_ne_zero (p : W.toAffine.f.Factors) {x : K}
    (hx : W.toAffine.f.eval x ≠ 0) : ι p x ≠ θ p := by
  intro he
  apply hx
  apply (ι p).injective
  rw [map_zero, ← Polynomial.eval₂_at_apply, he, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_eq_zero.mpr p.dvd

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
  match P with
  | 0 =>
      rw [W.toAffine.μ₀_zero, map_one, Pi.one_apply, map_zero,
        WeierstrassCurve.twoDescentUnit_zero, QuotientGroup.mk_one]
  | .some x y h =>
      rw [WeierstrassCurve.Affine.μ₀_some]
      by_cases hx : W.toAffine.f.eval x = 0
      · rw [W.toAffine.μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
        refine congrArg QuotientGroup.mk (Units.ext ?_)
        simp only [IsUnit.unit_spec]
        rw [W.toAffine.pointMap_some, AdjoinRoot.projFactor_mk, map_add, map_sub,
          AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq]
        by_cases hxe : ι p x = θ p
        · rw [WeierstrassCurve.coe_twoDescentUnit_some_of_eq _ _ _ _ hxe,
            mk_fCofactor_of_eq W p hxe, hxe, sub_self, zero_add]
        · rw [WeierstrassCurve.coe_twoDescentUnit_some_of_ne _ _ _ _ hxe,
            mk_fCofactor_of_ne W p hx hxe, add_zero]
      · rw [W.toAffine.μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
        refine congrArg QuotientGroup.mk (Units.ext ?_)
        simp only [IsUnit.unit_spec]
        rw [W.toAffine.pointMap_some, AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq,
          WeierstrassCurve.coe_twoDescentUnit_some_of_ne _ _ _ _
            (ne_root_of_eval_f_ne_zero W p hx)]

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
    (factorRoot_nonsingular W p) (factorRoot_polynomialY W p)
    (by simpa only [map_natCast] using h2.map (ι p))

omit [DecidableEq K] in
/-- `factorTorsionCharacter` is the two-torsion character of the universal root point. -/
theorem factorTorsionCharacter_def (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K))
    (h2p : IsUnit ((2 : ℕ) : 𝕃 p)) :
    factorTorsionCharacter W p h2 =
      (W.baseChange (𝕃 p)).twoTorsionCharacter
        (factorRoot_nonsingular W p) (factorRoot_polynomialY W p) h2p :=
  (rfl)

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
    (kummerMap (𝕃 p) 2 (by simpa only [map_natCast] using h2.map (ι p))
      ((W.baseChange (𝕃 p)).twoDescentUnit
        (factorRoot_nonsingular W p) (factorRoot_polynomialY W p)
        (W.toAffine.pointMap (𝕃 p) P)))

omit [DecidableEq K] in
/-- `rootwiseKummerClass` is the additive Kummer class of the rootwise descent unit. -/
theorem rootwiseKummerClass_def (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K))
    (h2p : IsUnit ((2 : ℕ) : 𝕃 p)) (P : W.toAffine.Point) :
    rootwiseKummerClass W p h2 P =
      Multiplicative.toAdd
        (kummerMap (𝕃 p) 2 h2p
          ((W.baseChange (𝕃 p)).twoDescentUnit
            (factorRoot_nonsingular W p) (factorRoot_polynomialY W p)
            (W.toAffine.pointMap (𝕃 p) P))) :=
  (rfl)

omit [DecidableEq K] in
/-- `factorCohomologicalMap` applies the universal-root character to the restricted class. -/
@[simp]
theorem factorCohomologicalMap_apply (p : W.toAffine.f.Factors)
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
  have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
  rw [factorCohomologicalMap_apply, W.torsionRes_kummerMap τ h2 P]
  simpa only [factorTorsionCharacter_def W p h2 h2p, rootwiseKummerClass_def W p h2 h2p] using
    (W.baseChange (𝕃 p)).explicitCoeff1_twoTorsionCharacter_kummerMap
      (factorRoot_nonsingular W p) (factorRoot_polynomialY W p) h2p
      (W.toAffine.pointMap (𝕃 p) P)

omit [DecidableEq K] in
/-- `factorCohomologicalMap` is independent of the embedding of separable closures. -/
theorem factorCohomologicalMap_eq_factorCohomologicalMap (p : W.toAffine.f.Factors)
    (τ τ' : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) (h2 : IsUnit ((2 : ℕ) : K)) :
    factorCohomologicalMap W p τ h2 = factorCohomologicalMap W p τ' h2 := by
  unfold factorCohomologicalMap
  rw [W.torsionRes_eq_torsionRes τ τ' 2]

/-! ### The assembled cohomological descent map -/

/-- **The cohomological `2`-descent map** `H¹(G_K, E[2]) → (K[X] ⧸ (f))ˣ ⧸ squares`, where `f`
is the `2`-division cubic. Its component at an irreducible factor `p` of `f` is
`factorCohomologicalMap`, read in the square classes of `K[X] ⧸ (p)` through the Kummer
isomorphism. The restriction to `K[X] ⧸ (p)` uses a fixed embedding of separable closures;
`TauCeti.TwoDescent.kummerIso_explicitFactor_cohomologicalMap` holds for every embedding. -/
noncomputable def cohomologicalMap (h2 : IsUnit ((2 : ℕ) : K)) :
    Multiplicative (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) →* W.toAffine.M :=
  (explicitFactorEquiv W).symm.toMonoidHom.comp <| MonoidHom.pi fun p ↦
    (kummerIso (𝕃 p) 2 (by simpa only [map_natCast] using h2.map (ι p))).symm.toMonoidHom.comp
      (factorCohomologicalMap W p IsSepClosed.lift h2).toMultiplicative

omit [DecidableEq K] in
/-- The component at `p` of the cohomological descent map, for the fixed embedding of separable
closures used to define it. -/
private theorem explicitFactor_cohomologicalMap (p : W.toAffine.f.Factors)
    (h2 : IsUnit ((2 : ℕ) : K)) (h2p : IsUnit ((2 : ℕ) : 𝕃 p))
    (x : Multiplicative (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2))) :
    explicitFactor W p (cohomologicalMap W h2 x) =
      (kummerIso (𝕃 p) 2 h2p).symm
        (.ofAdd (factorCohomologicalMap W p IsSepClosed.lift h2 x.toAdd)) :=
  -- `cohomologicalMap` is by definition `(explicitFactorEquiv W).symm` of the family of components
  congrFun ((explicitFactorEquiv W).apply_symm_apply _) p

omit [DecidableEq K] in
/-- **The components of the cohomological descent map.** Through the Kummer isomorphism, the
component at `p` of the image of a class `c` is `factorCohomologicalMap W p τ h2 c`, for every
embedding `τ` of separable closures. -/
theorem kummerIso_explicitFactor_cohomologicalMap (p : W.toAffine.f.Factors)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) (h2 : IsUnit ((2 : ℕ) : K))
    (h2p : IsUnit ((2 : ℕ) : 𝕃 p)) (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    kummerIso (𝕃 p) 2 h2p (explicitFactor W p (cohomologicalMap W h2 (.ofAdd c))) =
      .ofAdd (factorCohomologicalMap W p τ h2 c) := by
  simp only [explicitFactor_cohomologicalMap W p h2 h2p, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    factorCohomologicalMap_eq_factorCohomologicalMap W p IsSepClosed.lift τ]

omit [DecidableEq K] in
/-- **The kernel of the cohomological descent map**: a class is sent to the trivial square class
exactly when its restriction to every factor field is killed by the universal-root character. -/
theorem cohomologicalMap_eq_one_iff
    (τ : (p : W.toAffine.f.Factors) → SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
    (h2 : IsUnit ((2 : ℕ) : K)) (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    cohomologicalMap W h2 (.ofAdd c) = 1 ↔ ∀ p, factorCohomologicalMap W p (τ p) h2 c = 0 := by
  refine ⟨fun h p ↦ ?_, fun h ↦ (explicitFactorEquiv W).injective (funext fun p ↦ ?_)⟩
  all_goals have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
  · have hp := kummerIso_explicitFactor_cohomologicalMap W p (τ p) h2 h2p c
    simpa only [h, map_one, ofAdd_eq_one] using hp.symm
  · simp only [explicitFactorEquiv_apply, map_one]
    apply (kummerIso (𝕃 p) 2 h2p).injective
    simp only [kummerIso_explicitFactor_cohomologicalMap W p (τ p) h2 h2p c, h p, map_one,
      ofAdd_zero]

/-- **The cohomological descent map extends the explicit one**: on the Kummer class of a rational
point `P`, the cohomological `2`-descent map is the `x - T` descent map `μ₀(P)` into the square
classes of the étale algebra of the `2`-division cubic (Silverman X.1.4). -/
theorem cohomologicalMap_kummerMap (h2 : IsUnit ((2 : ℕ) : K)) (P : W.toAffine.Point) :
    cohomologicalMap W h2 (.ofAdd (W.kummerMap 2 h2 P)) = W.toAffine.μ₀ P := by
  -- `explicitFactor_μ₀_eq_twoDescentUnit` is stated for the classical decidable equality
  obtain rfl : ‹DecidableEq K› = Classical.decEq K := Subsingleton.elim _ _
  refine (explicitFactorEquiv W).injective (funext fun p ↦ ?_)
  simp only [explicitFactorEquiv_apply]
  have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
  apply (kummerIso (𝕃 p) 2 h2p).injective
  simp only [kummerIso_explicitFactor_cohomologicalMap W p IsSepClosed.lift h2 h2p,
    factorCohomologicalMap_kummerMap, rootwiseKummerClass_def W p h2 h2p, ofAdd_toAdd,
    explicitFactor_μ₀_eq_twoDescentUnit, kummerIso_apply, kummerClassMap_powerClassHom]

/-- The homomorphism form of `TauCeti.TwoDescent.cohomologicalMap_kummerMap`: the cohomological
descent map composed with the Kummer map is the explicit descent homomorphism `μ`. -/
theorem cohomologicalMap_comp_kummerMap (h2 : IsUnit ((2 : ℕ) : K)) :
    (cohomologicalMap W h2).comp (W.kummerMap 2 h2).toMultiplicative = W.toAffine.μ := by
  refine MonoidHom.ext fun P ↦ ?_
  simpa only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, ofAdd_toAdd] using
    (cohomologicalMap_kummerMap W h2 P.toAdd).trans (WeierstrassCurve.Affine.μ_apply P.toAdd).symm

end TwoDescent

end TauCeti
