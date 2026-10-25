/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.TwoDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.RingTheory.AdjoinRoot.Factors
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EmbeddingIndependence
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.FieldTheory.Normal.Embeddings
import TauCeti.GroupTheory.SpecificGroups.KleinFour
import TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula

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
with the Kummer map `E(K) → H¹(G_K, E[2])` it is the explicit `x - T` descent map. The rootwise
identity is the classical calculation in Silverman X.1.4.

The cohomological descent map is injective. A class whose factorwise images vanish is represented
by a cocycle `z` with `e₂(z(g), T)` trivial whenever `g` fixes `T ∈ E(Kˢ)[2]`, since the fixer of
a point `(x, 0)` of order two is the absolute Galois group of the factor field embedded by
`θ ↦ x`. Such a cocycle is a coboundary, because `E(Kˢ)[2]` is a Klein four-group on which two
distinct nonzero points pair to `-1`. Consequently a class lies in the image of the Kummer map
exactly when its cohomological descent image lies in the image of the explicit `x - T` map.

The cohomological descent map is natural under change of field. A root of the `2`-division cubic
in any extension `M` of `K` is the image `g(θ)` of the universal root of a factor `p` under a
`K`-embedding `g` of `K[X] ⧸ (p)` into `M`; reading a square class at that root means taking its
component at `p` and applying `g`. Since the Kummer isomorphism and the Weil pairing commute with
restriction, the cohomological descent class of `c` read at `g(θ)` is the restriction of `c` to
`M` paired with `(g(θ), 0)`. For an extension `L / K`, every irreducible factor `q` of the cubic
over `L` has a root lying over a factor `p` over `K`, and comparing the two readings at that root
shows that restricting to `L` and then applying the descent map of `W⁄L` is the same as applying
the descent map of `W` and then the base change of square classes. This is the compatibility that
identifies the cohomological local conditions with the explicit local conditions of `2`-descent.

The image of the cohomological descent map satisfies the norm condition of `2`-descent: every
class has square norm. Through the Kummer isomorphisms, the norm of a factor field
`K[X] ⧸ (p)` is corestriction from its absolute Galois group, so the norm class of the image of `c`
is the sum, over the factors, of the corestrictions of the restriction of `c` paired with
`(θ, 0)`. By the projection formula each term is the cup product of `c`, through the Weil pairing,
with the corestriction `∑ᵤ u • (σ θ, 0)` of the point `(σ θ, 0)` for an embedding `σ` of the
factor field into `Kˢ`, that is with the sum of the points `(x, 0)` over the roots `x` of `p`.
Summed over the factors these run through the three points of order two, whose sum is zero.

## Main definitions

* `TauCeti.TwoDescent.explicitFactor`: projection of an étale-algebra square class to the power
  classes of one irreducible factor.
* `TauCeti.TwoDescent.explicitFactorEquiv`: the square classes of the étale algebra as the product
  of the square classes of its field factors.
* `TauCeti.TwoDescent.factorCohomologicalMap`: restriction to the factor field followed by the
  Weil-pairing character attached to its universal root.
* `TauCeti.TwoDescent.cohomologicalMap`: the cohomological `2`-descent map
  `H¹(G_K, E[2]) → (K[X] ⧸ (f))ˣ ⧸ squares`.
* `TauCeti.TwoDescent.embeddingTorsionCoeff`: the point `(σ θ, 0)` of `E(Kˢ)[2]` attached to an
  embedding `σ` of a factor field into `Kˢ`.

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
* `TauCeti.TwoDescent.eq_zero_of_forall_factorCohomologicalMap_eq_zero`: a class of
  `H¹(G_K, E[2])` whose factorwise images all vanish is zero.
* `TauCeti.TwoDescent.cohomologicalMap_injective`: the cohomological descent map is injective.
* `TauCeti.TwoDescent.cohomologicalMap_mem_range_μ_iff`: the cohomological descent image of a
  class lies in the explicit descent image exactly when the class is a Kummer class.
* `TauCeti.TwoDescent.kummerIso_powerClassMap_explicitFactor_cohomologicalMap`: the cohomological
  descent class read at a root `g(θ)` of the `2`-division cubic in an extension `M` is the
  restriction to `M` paired with `(g(θ), 0)`.
* `TauCeti.TwoDescent.explicitFactor_localRes`: base change of square classes, read on the factor
  fields.
* `TauCeti.TwoDescent.cohomologicalMap_torsionRes`: the cohomological descent map commutes with
  restriction to an extension field and base change of square classes.
* `TauCeti.TwoDescent.bijective_embeddingTorsionCoeff`: the points `(σ θ, 0)` are the nonzero
  points of `E(Kˢ)[2]`, each attained by exactly one embedding of one factor field.
* `TauCeti.TwoDescent.normM_cohomologicalMap` and
  `TauCeti.TwoDescent.range_cohomologicalMap_le_ker_normM`: the image of the cohomological descent
  map lies in the kernel of the norm `(K[X] ⧸ (f))ˣ ⧸ squares → Kˣ ⧸ squares`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.4.
* A. Brumer and K. Kramer, *The rank of elliptic curves*, Duke Math. J. 44 (1977), for the
  `2`-descent through the cubic étale algebra and its norm condition.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3) and the
  display after (6.2.1), for the projection formula and the norm as corestriction.
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

omit [DecidableEq K] in
/-- The universal root of a factor of the `2`-division cubic is a nonsingular point of the
base-changed elliptic curve. -/
theorem factorRoot_nonsingular (p : W.toAffine.f.Factors) :
    (W.baseChange (𝕃 p)).toAffine.Nonsingular (θ p) 0 :=
  W.toAffine.nonsingular_baseChange_of_aeval_eq_zero <| by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact p.dvd

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

omit [DecidableEq K] in
/-- The component at a factor `p` of the square class of a unit `u` of the étale algebra is the
square class of the component of `u` in `K[X] ⧸ (p)`. -/
theorem explicitFactor_mk (p : W.toAffine.f.Factors) (u : W.toAffine.Aˣ) :
    explicitFactor W p (u : W.toAffine.M) = QuotientGroup.mk (Units.map
      (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f p).toRingHom.toMonoidHom
        u) := by
  rw [explicitFactor_apply, AdjoinRoot.modPowEquivPiFactors_mk,
    QuotientGroup.quotientMulEquivOfEq_mk]

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
        (factorRoot_nonsingular W p)
        (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _)
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
          (factorRoot_nonsingular W p)
          (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _)
          (W.toAffine.pointMap (𝕃 p) P)) := by
  rw [explicitFactor_apply, explicitFactor_eq_twoDescentUnit, powerClassHom_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]

/-- The Weil-pairing character associated to the universal root point of a factor of the
`2`-division cubic. -/
def factorTorsionCharacter (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K)) :
    (W.baseChange (𝕃 p)).TorsionCoeff 2 →+[AbsoluteGaloisGroup (𝕃 p)]
      KummerCoeff (𝕃 p) 2 :=
  (W.baseChange (𝕃 p)).twoTorsionCharacter
    (factorRoot_nonsingular W p)
    (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _)
    (by simpa only [map_natCast] using h2.map (ι p))

omit [DecidableEq K] in
/-- `factorTorsionCharacter` is the two-torsion character of the universal root point. -/
theorem factorTorsionCharacter_def (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K))
    (h2p : IsUnit ((2 : ℕ) : 𝕃 p)) :
    factorTorsionCharacter W p h2 =
      (W.baseChange (𝕃 p)).twoTorsionCharacter
        (factorRoot_nonsingular W p)
        (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _) h2p :=
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
        (factorRoot_nonsingular W p)
        (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _)
        (W.toAffine.pointMap (𝕃 p) P)))

omit [DecidableEq K] in
/-- `rootwiseKummerClass` is the additive Kummer class of the rootwise descent unit. -/
theorem rootwiseKummerClass_def (p : W.toAffine.f.Factors) (h2 : IsUnit ((2 : ℕ) : K))
    (h2p : IsUnit ((2 : ℕ) : 𝕃 p)) (P : W.toAffine.Point) :
    rootwiseKummerClass W p h2 P =
      Multiplicative.toAdd
        (kummerMap (𝕃 p) 2 h2p
          ((W.baseChange (𝕃 p)).twoDescentUnit
            (factorRoot_nonsingular W p)
            (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _)
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
      (factorRoot_nonsingular W p)
      (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _) h2p
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

/-! ### Injectivity of the cohomological descent map -/

omit [DecidableEq K] [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
/-- A class restricted along `τ` and killed by a map `χ` into coefficients with trivial action is
killed by `χ` pointwise on the restricted cocycle. -/
-- Stated over an arbitrary extension `L`: elaborating the same unfolding directly over a factor
-- field `K[X] ⧸ (p)` is much slower.
private theorem apply_torsionCoeffBaseChange_eq_zero {L : Type*} [Field L] [Algebra K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) {m : ℕ} {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [DistribMulAction (AbsoluteGaloisGroup L) A]
    [ContinuousSMul (AbsoluteGaloisGroup L) A]
    (htriv : ∀ (g : AbsoluteGaloisGroup L) (a : A), g • a = a)
    (χ : (W.baseChange L).TorsionCoeff m →+[AbsoluteGaloisGroup L] A) (hχ : Continuous χ)
    {z : Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (hz : explicitCoeff1 _ _ χ hχ (W.torsionRes τ m (z : H1 _ _)) = 0)
    (h : AbsoluteGaloisGroup L) :
    χ (W.torsionCoeffBaseChange τ m
      ((z : AbsoluteGaloisGroup K → W.TorsionCoeff m) (absoluteGaloisGroupMap τ h))) = 0 := by
  rw [WeierstrassCurve.torsionRes_eq_explicitMap1, explicitMap1_mk, explicitCoeff1_mk,
    H1pi_eq_zero_iff, B1_eq_bot_of_smul_eq_self htriv, AddSubgroup.mem_bot] at hz
  have hval := (cocyclesMap1_apply _ _ _ _ _ _ _ _ _ h).symm.trans (congrFun hz h)
  rwa [cocyclesMap1_apply] at hval

omit [DecidableEq K] [W.toAffine.IsCharNeTwoNF] in
/-- **Pairing with a sum of points of order two.** For a family `m` of square roots of unity
indexed by `E(Kˢ)[2]`, the sum of the points `T` with `m T ≠ 0` pairs with a nonzero point `S` to
`∑ T, m T - m O - m S`, as two distinct nonzero points of order two pair to `-1`. -/
theorem torsionCoeffWeilPairing_sum_ite (h2 : IsUnit ((2 : ℕ) : K))
    [Fintype (W.TorsionCoeff 2)] (m : W.TorsionCoeff 2 → KummerCoeff K 2)
    [DecidablePred (m · = 0)] {S : W.TorsionCoeff 2} (hS : S ≠ 0) :
    W.torsionCoeffWeilPairing 2 h2 (∑ T, if m T = 0 then 0 else T) S =
      (∑ T, m T) - m 0 - m S := by
  classical
  have hterm (T : W.TorsionCoeff 2) :
      W.torsionCoeffWeilPairing 2 h2 (if m T = 0 then 0 else T) S =
        m T - (if T = 0 then m T else 0) - (if T = S then m T else 0) := by
    by_cases hT0 : T = 0
    · simp [hT0, Ne.symm hS]
    by_cases hTS : T = S
    · subst hTS
      rcases eq_or_ne (m T) 0 with h | h <;> simp [h, hS]
    simp only [hT0, hTS, ↓reduceIte, sub_zero]
    have : Invertible (2 : K) := (by simpa using h2 : IsUnit (2 : K)).invertible
    rcases eq_zero_or_eq_mu2NegOne (m T) with h | h
    · simp [h]
    · simp only [h, mu2NegOne_ne_zero, ↓reduceIte]
      exact WeierstrassCurve.torsionCoeffWeilPairing_two_eq_mu2NegOne h2 hT0 hS hTS
  simp only [map_sum, AddMonoidHom.finsetSum_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit [DecidableEq K] [W.toAffine.IsCharNeTwoNF] in
/-- **A cocycle into `E(Kˢ)[2]` killed on stabilizers is a coboundary.** If `z : G_K → E(Kˢ)[2]`
is a `1`-cocycle and `e₂(z(g), T) = 0` whenever `g` fixes `T`, then `z` is a `1`-coboundary. -/
private theorem isCoboundary₁_of_torsionCoeffWeilPairing_eq_zero
    (h2 : IsUnit ((2 : ℕ) : K)) {z : AbsoluteGaloisGroup K → W.TorsionCoeff 2}
    (hz : groupCohomology.IsCocycle₁ z)
    (H : ∀ (T : W.TorsionCoeff 2) (g : AbsoluteGaloisGroup K), g • T = T →
      W.torsionCoeffWeilPairing 2 h2 (z g) T = 0) :
    groupCohomology.IsCoboundary₁ z := by
  classical
  have := Fintype.ofFinite (W.TorsionCoeff 2)
  set e := W.torsionCoeffWeilPairing 2 h2
  have he (g : AbsoluteGaloisGroup K) (P Q : W.TorsionCoeff 2) : e (g • P) (g • Q) = e P Q := by
    rw [WeierstrassCurve.torsionCoeffWeilPairing_smul, mu2_smul_eq_self]
  -- a representative `r T` of the orbit of `T`, and an element `γ T` moving it to `T`
  let r (T : W.TorsionCoeff 2) : W.TorsionCoeff 2 :=
    (Quotient.mk (MulAction.orbitRel (AbsoluteGaloisGroup K) _) T).out
  have hr (g : AbsoluteGaloisGroup K) (T : W.TorsionCoeff 2) : r (g • T) = r T :=
    congrArg Quotient.out (Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit T g)))
  have hγ (T : W.TorsionCoeff 2) : ∃ g : AbsoluteGaloisGroup K, g • r T = T := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
      (Quotient.mk_out (s := MulAction.orbitRel (AbsoluteGaloisGroup K) _) T))
    exact ⟨g⁻¹, by simp only [r, ← hg, inv_smul_smul]⟩
  choose γ hγ using hγ
  -- `m T = e₂(z(g), T)` for every `g` moving `r T` to `T`, as `z` is killed on the fixer of `r T`
  let m (T : W.TorsionCoeff 2) : KummerCoeff K 2 := e (z (γ T)) T
  have hm {g : AbsoluteGaloisGroup K} {T : W.TorsionCoeff 2} (hg : g • r T = T) :
      e (z g) T = m T := by
    have hfix : ((γ T)⁻¹ * g) • r T = r T := by rw [mul_smul, hg, inv_smul_eq_iff, hγ]
    have hzg := hz (γ T) ((γ T)⁻¹ * g)
    rw [mul_inv_cancel_left] at hzg
    have h0 : e (γ T • z ((γ T)⁻¹ * g)) T = 0 := by
      calc e (γ T • z ((γ T)⁻¹ * g)) T = e (γ T • z ((γ T)⁻¹ * g)) (γ T • r T) := by rw [hγ T]
        _ = 0 := by rw [he, H _ _ hfix]
    rw [hzg, map_add, AddMonoidHom.add_apply, h0, zero_add]
  -- so `e₂(z(g), T) = m T - m (g⁻¹ T)`
  have hzm (g : AbsoluteGaloisGroup K) (T : W.TorsionCoeff 2) :
      e (z g) T = m T - m (g⁻¹ • T) := by
    have hg : (g * γ (g⁻¹ • T)) • r T = T := by
      rw [mul_smul, ← hr g⁻¹ T, hγ, smul_inv_smul]
    have h := hm hg
    rw [hz _ _, map_add, AddMonoidHom.add_apply] at h
    rw [← h, ← smul_inv_smul g T, he, smul_inv_smul,
      hm (by rw [hγ] : γ (g⁻¹ • T) • r (g⁻¹ • T) = g⁻¹ • T)]
    abel
  -- the sum `P` of the `T` with `m T ≠ 0` has `e₂(P, S) = ∑ m - m O - m S` for `S ≠ O`
  let P : W.TorsionCoeff 2 := ∑ T, if m T = 0 then 0 else T
  have hP {S : W.TorsionCoeff 2} (hS : S ≠ 0) : e P S = (∑ T, m T) - m 0 - m S :=
    torsionCoeffWeilPairing_sum_ite W h2 m hS
  -- and `z` is the coboundary of `P`, by nondegeneracy of the Weil pairing
  refine ⟨P, fun g ↦ ?_⟩
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero]
  refine W.torsionCoeffWeilPairing_nondegenerate 2 h2 fun S ↦ ?_
  by_cases hS : S = 0
  · rw [hS, map_zero]
  have hS' : g⁻¹ • S ≠ 0 := by rwa [ne_eq, smul_eq_zero_iff_eq]
  have hgP : e (g • P) S = e P (g⁻¹ • S) := by rw [← he g⁻¹, inv_smul_smul]
  rw [map_sub, map_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, hgP, hP hS, hP hS',
    hzm]
  abel

omit [DecidableEq K] [W.IsElliptic] in
open scoped Classical in
/-- A nonzero point of `E(Kˢ)[2]` is `(x, 0)` for a root `x` of an irreducible factor of the
`2`-division cubic. -/
private theorem exists_factor_of_ne_zero (h2 : IsUnit ((2 : ℕ) : K)) {T : W.TorsionCoeff 2}
    (hT : T ≠ 0) :
    ∃ (p : W.toAffine.f.Factors) (x : SeparableClosure K) (_ : aeval x (p : K[X]) = 0)
      (h : (W.baseChange (SeparableClosure K)).toAffine.Nonsingular x 0),
      (T : W.PointCoeff) = W.pointCoeffEquiv (.some x 0 h) := by
  obtain ⟨Q, hQ⟩ := W.pointCoeffEquiv.surjective T
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd (Subtype.ext (hQ.symm.trans (map_zero _))) hT
  -- `2 (x, y) = O` forces `ψ₂(x, y) = 2y = 0`
  have h2T := AddSubgroup.torsionBy.nsmul_iff.1 T.2
  rw [← hQ, ← map_nsmul, two_nsmul, AddEquiv.map_eq_zero_iff,
    WeierstrassCurve.Affine.Point.some_add_self_eq_zero_iff h,
    WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.a₁_of_isCharNeTwoNF,
    WeierstrassCurve.a₃_of_isCharNeTwoNF, zero_mul, add_zero, add_zero] at h2T
  obtain rfl : y = 0 := (mul_eq_zero.1 h2T).resolve_left (by
    simpa using h2.natCast_ne_zero_of_algebra (L := SeparableClosure K))
  -- so `x` is a root of `f`, hence of one of its irreducible factors
  have hfx := (WeierstrassCurve.Affine.equation_iff_eval_f_eq_sq _ x 0).1 h.1
  rw [WeierstrassCurve.Affine.baseChange_f, zero_pow two_ne_zero] at hfx
  obtain ⟨p, hp⟩ := Polynomial.Factors.exists_dvd_map (algebraMap K (SeparableClosure K))
    W.toAffine.f_ne_zero (prime_X_sub_C x) (dvd_iff_isRoot.2 hfx)
  refine ⟨p, x, ?_, h, hQ.symm⟩
  rw [aeval_def, ← eval_map]
  exact dvd_iff_isRoot.1 hp

omit [DecidableEq K] in
/-- If every factorwise image of the class of a cocycle `z` vanishes, then `e₂(z(g), T)` is
trivial whenever `g` fixes `T ∈ E(Kˢ)[2]`. -/
private theorem torsionCoeffWeilPairing_eq_zero_of_smul_eq (h2 : IsUnit ((2 : ℕ) : K))
    {z : Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)}
    (hz : ∀ p τ, factorCohomologicalMap W p τ h2 (z : H1 _ _) = 0)
    {T : W.TorsionCoeff 2} {g : AbsoluteGaloisGroup K} (hg : g • T = T) :
    W.torsionCoeffWeilPairing 2 h2 ((z : AbsoluteGaloisGroup K → W.TorsionCoeff 2) g) T = 0 := by
  by_cases hT : T = 0
  · rw [hT, map_zero]
  obtain ⟨p, x, hx, hxT, hT'⟩ := exists_factor_of_ne_zero W h2 hT
  -- the embedding `σ : K[X] ⧸ (p) → Kˢ` with `θ ↦ x`, and the induced identification `τ`
  let σ : 𝕃 p →ₐ[K] SeparableClosure K := AdjoinRoot.liftAlgHom _ (Algebra.ofId K _) x hx
  have hσ : σ (θ p) = x := AdjoinRoot.liftAlgHom_root _ _ _ _
  let τ := separableClosureAlgEquiv K (𝕃 p) σ
  -- `g` fixes `x`, hence the image of `σ`
  have hgx : g x = x := by
    classical
    have h := congrArg Subtype.val hg
    rw [WeierstrassCurve.coe_smul_torsionCoeff, hT', WeierstrassCurve.smul_pointCoeffEquiv,
      WeierstrassCurve.Affine.Point.map_some] at h
    simpa using h
  have hgσ : g ∈ σ.fieldRange.fixingSubgroup := by
    have hcomp : (g : SeparableClosure K →ₐ[K] SeparableClosure K).comp σ = σ :=
      AdjoinRoot.algHom_ext (by rw [AlgHom.comp_apply, hσ, AlgEquiv.coe_toAlgHom, hgx])
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨a, rfl⟩
    exact AlgHom.congr_fun hcomp a
  -- the element `h` of `G_{𝕃 p}` restricting to `g`
  let h : AbsoluteGaloisGroup (𝕃 p) :=
    (absoluteGaloisGroupEquivFixingSubgroup K (𝕃 p) σ).symm ⟨g, hgσ⟩
  have hh : absoluteGaloisGroupMap (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) h =
      g := by
    rw [absoluteGaloisGroupMap_separableClosureAlgEquiv, ContinuousMonoidHom.comp_toFun,
      ContinuousMonoidHom.coe_coe, ContinuousMonoidHom.subgroupSubtype_apply,
      ContinuousMulEquiv.apply_symm_apply]
  -- the universal-root character kills `τ (z g)`, so `τ (z g)` is `O` or `(θ, 0)`
  have hzp := hz p τ
  rw [factorCohomologicalMap_apply] at hzp
  have hval := apply_torsionCoeffBaseChange_eq_zero W _ (mu2_smul_eq_self _)
    (factorTorsionCharacter W p h2) continuous_of_discreteTopology hzp h
  rw [hh, factorTorsionCharacter_def W p h2 (by simpa only [map_natCast] using h2.map (ι p)),
    WeierstrassCurve.twoTorsionCharacter_eq_zero_iff,
    WeierstrassCurve.coe_torsionCoeffBaseChange] at hval
  -- `τ` carries `T = (x, 0)` to `(θ, 0)`
  have hτT : W.pointCoeffBaseChange τ (T : W.PointCoeff) =
      (W.baseChange (𝕃 p)).basePointCoeff (.some (θ p) 0 (factorRoot_nonsingular W p)) := by
    have hτx : τ x = algebraMap (𝕃 p) (SeparableClosure (𝕃 p)) (θ p) := by
      rw [← hσ]
      exact (separableClosureAlgEquiv_apply K (𝕃 p) σ _).trans
        (separableClosureRingEquiv_symm_apply_eq_algebraMap K (𝕃 p) σ (θ p))
    rw [hT', WeierstrassCurve.pointCoeffBaseChange_pointCoeffEquiv_some,
      WeierstrassCurve.basePointCoeff_some]
    simp only [AlgEquiv.coe_toAlgHom, hτx, map_zero]
  -- hence `z g` is `O` or `T`, as `τ` is injective on points
  have hinj := (W.pointCoeffBaseChange_bijective
    (τ := (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))) τ.bijective).1
  rcases hval with h0 | h1
  · have hz0 : ((z : AbsoluteGaloisGroup K → W.TorsionCoeff 2) g : W.PointCoeff) =
        ((0 : W.TorsionCoeff 2) : W.PointCoeff) :=
      hinj (by rw [h0, ZeroMemClass.coe_zero, map_zero])
    rw [Subtype.ext hz0, map_zero, AddMonoidHom.zero_apply]
  · rw [Subtype.ext (hinj (h1.trans hτT.symm)), WeierstrassCurve.torsionCoeffWeilPairing_self]

omit [DecidableEq K] in
/-- **A class of `H¹(G_K, E[2])` is detected by its factorwise images** (Silverman X.1.4): if its
restriction to every factor field `K[X] ⧸ (p)` of the `2`-division cubic is killed by the
universal-root character, for some embeddings of separable closures, the class is zero. -/
theorem eq_zero_of_forall_factorCohomologicalMap_eq_zero (h2 : IsUnit ((2 : ℕ) : K))
    (τ : (p : W.toAffine.f.Factors) → SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)}
    (hc : ∀ p, factorCohomologicalMap W p (τ p) h2 c = 0) : c = 0 := by
  -- the factorwise images vanish along every embedding of separable closures
  have hc' (p : W.toAffine.f.Factors) (τ' : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) :
      factorCohomologicalMap W p τ' h2 c = 0 :=
    (DFunLike.congr_fun (factorCohomologicalMap_eq_factorCohomologicalMap W p τ' (τ p) h2) c).trans
      (hc p)
  induction c using QuotientAddGroup.induction_on with
  | _ z =>
  rw [H1pi_eq_zero_iff, mem_B1_iff]
  exact isCoboundary₁_of_torsionCoeffWeilPairing_eq_zero W h2 (mem_Z1_iff.1 z.2).2
    fun _ _ hg ↦ torsionCoeffWeilPairing_eq_zero_of_smul_eq W h2 hc' hg

omit [DecidableEq K] in
/-- **The cohomological `2`-descent map is injective** (Silverman X.1.4):
`H¹(G_K, E[2]) → (K[X] ⧸ (f))ˣ ⧸ squares` embeds the Galois cohomology of `E[2]` into the square
classes of the étale algebra of the `2`-division cubic `f`. -/
theorem cohomologicalMap_injective (h2 : IsUnit ((2 : ℕ) : K)) :
    Function.Injective (cohomologicalMap W h2) := by
  refine (injective_iff_map_eq_one _).2 fun c hc ↦ Multiplicative.toAdd.injective ?_
  exact eq_zero_of_forall_factorCohomologicalMap_eq_zero W h2 (fun _ ↦ IsSepClosed.lift)
    ((cohomologicalMap_eq_one_iff W _ h2 c.toAdd).1 hc)

/-- **The cohomological and explicit local conditions agree.** The image of a cohomology class
under the cohomological `2`-descent map lies in the image of the explicit `x - T` descent map if
and only if the class itself lies in the image of the cohomological Kummer map. -/
theorem cohomologicalMap_mem_range_μ_iff (h2 : IsUnit ((2 : ℕ) : K))
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)} :
    cohomologicalMap W h2 (.ofAdd c) ∈ (WeierstrassCurve.Affine.μ (W := W.toAffine)).range ↔
      c ∈ (W.kummerMap 2 h2).range := by
  rw [← cohomologicalMap_comp_kummerMap W h2, MonoidHom.range_comp,
    Subgroup.mem_map_iff_mem (cohomologicalMap_injective W h2),
    MonoidHom.coe_toMultiplicative_range, Multiplicative.mem_toSubgroup, toAdd_ofAdd]

/-! ### Naturality under change of field -/

section ChangeOfField

/- The universal-root character at `(e, 0)` does not depend on the proofs that `(e, 0)` is a point
of order two, and it is transported along an equality of curves. -/
omit [DecidableEq K] [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
private theorem twoTorsionCharacter_congr {M : Type*} [Field M] [DecidableEq M]
    {V : WeierstrassCurve M} [V.IsElliptic] {e e' : M} (he : e = e')
    (hT : V.toAffine.Nonsingular e 0) (hψ : V.toAffine.polynomialY.evalEval e 0 = 0)
    (hT' : V.toAffine.Nonsingular e' 0) (hψ' : V.toAffine.polynomialY.evalEval e' 0 = 0)
    (h2 : IsUnit ((2 : ℕ) : M)) :
    V.twoTorsionCharacter hT hψ h2 = V.twoTorsionCharacter hT' hψ' h2 := by
  subst he
  rfl

omit [DecidableEq K] in
/-- **The cohomological descent map at a root of the `2`-division cubic.** Let `g` embed the
factor field `K[X] ⧸ (p)` into a field `M` over `K`, so that `g(θ)` is a root of the `2`-division
cubic in `M`. Through the Kummer isomorphism over `M`, the image under `g` of the component at `p`
of the cohomological descent class of `c` is the image of the restriction of `c` to `M` under the
character `e₂(·, (g(θ), 0))`. For `g` the identity this is
`TauCeti.TwoDescent.kummerIso_explicitFactor_cohomologicalMap`. -/
theorem kummerIso_powerClassMap_explicitFactor_cohomologicalMap
    {M : Type*} [Field M] [Algebra K M] [DecidableEq M] (p : W.toAffine.f.Factors)
    (g : 𝕃 p →ₐ[K] M) (τ : SeparableClosure K →ₐ[K] SeparableClosure M)
    (h2 : IsUnit ((2 : ℕ) : K)) (h2M : IsUnit ((2 : ℕ) : M))
    (hT : (W.baseChange M).toAffine.Nonsingular (g (θ p)) 0)
    (hψ : (W.baseChange M).toAffine.polynomialY.evalEval (g (θ p)) 0 = 0)
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    kummerIso M 2 h2M (powerClassMap 2 (Units.map (g : 𝕃 p →* M))
        (explicitFactor W p (cohomologicalMap W h2 (.ofAdd c)))) =
      .ofAdd (explicitCoeff1 _ _ ((W.baseChange M).twoTorsionCharacter hT hψ h2M)
        continuous_of_discreteTopology (W.torsionRes τ 2 c)) := by
  -- regard `M` as an extension of the factor field through `g`
  let : Algebra (𝕃 p) M := g.toRingHom.toAlgebra
  have : IsScalarTower K (𝕃 p) M := IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
  exact W.kummerIso_powerClassMap_of_kummerIso_eq IsSepClosed.lift τ
    (factorRoot_nonsingular W p)
    (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _) _ _ h2p h2M c
    (kummerIso_explicitFactor_cohomologicalMap W p IsSepClosed.lift h2 h2p c)

omit [DecidableEq K] in
/-- **Base change of square classes, on the factor fields.** If a `K`-embedding
`g : K[X] ⧸ (p) → L[X] ⧸ (q)` of the factor fields of the `2`-division cubic over `K` and over
an extension `L` sends the universal root of `p` to that of `q`, then the component at `q` of the
base change of a square class is the image under `g` of its component at `p`. -/
theorem explicitFactor_localRes {L : Type*} [Field L] [Algebra K L]
    [(W.baseChange L).toAffine.IsCharNeTwoNF] (p : W.toAffine.f.Factors)
    (q : (W.baseChange L).toAffine.f.Factors) (g : 𝕃 p →ₐ[K] AdjoinRoot (q : L[X]))
    (hg : g (θ p) = AdjoinRoot.root (q : L[X])) (m : W.toAffine.M) :
    explicitFactor (W.baseChange L) q (W.toAffine.localRes L m) =
      powerClassMap 2 (Units.map (g : 𝕃 p →* AdjoinRoot (q : L[X]))) (explicitFactor W p m) := by
  -- on the étale algebra, both composites `K[X] ⧸ (f) → L[X] ⧸ (q)` evaluate at the root of `q`
  have key (a : W.toAffine.A) :
      AdjoinRoot.projFactor (W.baseChange L).toAffine.f_ne_zero
          (W.baseChange L).toAffine.squarefree_f q (W.toAffine.mapA L a) =
        g (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f p a) := by
    induction a using AdjoinRoot.induction_on with
    | ih h =>
      rw [WeierstrassCurve.Affine.mapA_mk, AdjoinRoot.projFactor_mk, AdjoinRoot.projFactor_mk,
        ← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, hg,
        Polynomial.aeval_map_algebraMap]
  induction m using QuotientGroup.induction_on with
  | H u =>
    rw [WeierstrassCurve.Affine.localRes_mk, explicitFactor_apply, explicitFactor_apply,
      AdjoinRoot.modPowEquivPiFactors_mk, AdjoinRoot.modPowEquivPiFactors_mk,
      QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientMulEquivOfEq_mk,
      powerClassMap_mk]
    exact congrArg QuotientGroup.mk (Units.ext (key u))

omit [DecidableEq K] in
/-- **The cohomological descent map is natural under change of field** (Silverman X.1.4): for a
field extension `L / K`, restricting a class of `H¹(G_K, E[2])` to `L` and applying the
cohomological descent map of `W⁄L` is applying the cohomological descent map of `W` and then the
base change `(K[X] ⧸ (f))ˣ ⧸ squares → (L[X] ⧸ (f))ˣ ⧸ squares` of square classes. -/
theorem cohomologicalMap_torsionRes {L : Type*} [Field L] [Algebra K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (h2 : IsUnit ((2 : ℕ) : K))
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    cohomologicalMap (W.baseChange L) (by simpa only [map_natCast] using h2.map (algebraMap K L))
        (.ofAdd (W.torsionRes τ 2 c)) =
      W.toAffine.localRes L (cohomologicalMap W h2 (.ofAdd c)) := by
  have h2L : IsUnit ((2 : ℕ) : L) := by simpa only [map_natCast] using h2.map (algebraMap K L)
  refine (explicitFactorEquiv (W.baseChange L)).injective (funext fun q ↦ ?_)
  simp only [explicitFactorEquiv_apply]
  -- The root of `q` is a root of `f` over `K`; its minimal polynomial is the factor `p` of `f`
  -- below `q`, and `g : K[X] ⧸ (p) → L[X] ⧸ (q)` sends the root of `p` to the root of `q`.
  have hθ : aeval (AdjoinRoot.root (q : L[X])) W.toAffine.f = 0 := by
    rw [← aeval_map_algebraMap L, ← W.toAffine.baseChange_f L, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_eq_zero.mpr q.dvd]
  have hint : IsIntegral K (AdjoinRoot.root (q : L[X])) :=
    IsAlgebraic.isIntegral ⟨_, W.toAffine.f_ne_zero, hθ⟩
  let p : W.toAffine.f.Factors :=
    ⟨minpoly K (AdjoinRoot.root (q : L[X])), minpoly.irreducible hint, minpoly.monic hint,
      minpoly.dvd K _ hθ⟩
  let g : 𝕃 p →ₐ[K] AdjoinRoot (q : L[X]) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K _) _ (minpoly.aeval K (AdjoinRoot.root (q : L[X])))
  have hg : g (θ p) = AdjoinRoot.root (q : L[X]) := AdjoinRoot.liftAlgHom_root _ _ _ _
  have h2q : IsUnit ((2 : ℕ) : AdjoinRoot (q : L[X])) := by
    simpa only [map_natCast] using h2L.map (algebraMap L (AdjoinRoot (q : L[X])))
  apply (kummerIso (AdjoinRoot (q : L[X])) 2 h2q).injective
  let τq : SeparableClosure L →ₐ[L] SeparableClosure (AdjoinRoot (q : L[X])) := IsSepClosed.lift
  let τN : SeparableClosure K →ₐ[K] SeparableClosure (AdjoinRoot (q : L[X])) := IsSepClosed.lift
  have hT := W.toAffine.nonsingular_baseChange_of_aeval_eq_zero hθ
  have hψ := WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF
    (W.baseChange (AdjoinRoot (q : L[X]))).toAffine (AdjoinRoot.root (q : L[X]))
  have hT0 := factorRoot_nonsingular (W.baseChange L) q
  have hψ0 := WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF
    ((W.baseChange L).baseChange (AdjoinRoot (q : L[X]))).toAffine (AdjoinRoot.root (q : L[X]))
  -- the component at `q` of the left side is computed over `L`, from the root of `q`
  have hL : kummerIso (AdjoinRoot (q : L[X])) 2 h2q (explicitFactor (W.baseChange L) q
      (cohomologicalMap (W.baseChange L) h2L (.ofAdd (W.torsionRes τ 2 c)))) =
      .ofAdd (explicitCoeff1 _ _
        (((W.baseChange L).baseChange (AdjoinRoot (q : L[X]))).twoTorsionCharacter hT0 hψ0 h2q)
        continuous_of_discreteTopology ((W.baseChange L).torsionRes τq 2 (W.torsionRes τ 2 c))) :=
    kummerIso_explicitFactor_cohomologicalMap (W.baseChange L) q τq h2L h2q _
  -- the component at `q` of the right side is computed over `K`, through the factor field of `p`
  have hR := (congrArg (kummerIso (AdjoinRoot (q : L[X])) 2 h2q)
    (explicitFactor_localRes W p q g hg (cohomologicalMap W h2 (.ofAdd c)))).trans
    (kummerIso_powerClassMap_explicitFactor_cohomologicalMap W p g τN h2 h2q (hg ▸ hT)
      (hg ▸ hψ) c)
  -- Both are the restriction to `L[X] ⧸ (q)` paired with `(θ_q, 0)`. Term-mode composition keeps
  -- the elaborator from unfolding the factor fields, which `rw` does at great cost here.
  refine hL.trans ((congrArg Multiplicative.ofAdd ?_).trans hR.symm)
  exact (W.explicitCoeff1_twoTorsionCharacter_torsionRes_torsionRes τ τq τN hT0 hψ0 hT hψ h2q
    c).trans (congrArg (fun χ ↦ explicitCoeff1 _ _ χ continuous_of_discreteTopology
      (W.torsionRes τN 2 c)) (twoTorsionCharacter_congr hg.symm hT hψ _ _ h2q))

end ChangeOfField

/-! ### The norm condition -/

section NormCondition

omit [DecidableEq K]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open scoped Classical in
/-- The point `(x, 0)` of `E(Kˢ)[2]` at a root `x` of the `2`-division cubic. -/
private def rootTorsionCoeff {x : SeparableClosure K} (hx : aeval x W.toAffine.f = 0) :
    W.TorsionCoeff 2 :=
  have h : (W.baseChange (SeparableClosure K)).toAffine.Nonsingular x 0 :=
    W.toAffine.nonsingular_baseChange_of_aeval_eq_zero hx
  AddEquiv.torsionByCongr W.pointCoeffEquiv 2
    (⟨WeierstrassCurve.Affine.Point.some x 0 h,
      WeierstrassCurve.Affine.Point.some_mem_torsionBy_two h
        (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _)⟩ :
      AddSubgroup.torsionBy (W.baseChange (SeparableClosure K)).toAffine.Point (2 : ℕ))

open scoped Classical in
/-- The point `(x, 0)` as a point of `E(Kˢ)`. -/
private theorem coe_rootTorsionCoeff {x : SeparableClosure K} (hx : aeval x W.toAffine.f = 0) :
    (rootTorsionCoeff W hx : W.PointCoeff) = W.pointCoeffEquiv
      (WeierstrassCurve.Affine.Point.some x 0
        (W.toAffine.nonsingular_baseChange_of_aeval_eq_zero hx)) := by
  rw [rootTorsionCoeff, AddEquiv.torsionByCongr_apply_coe]

/-- A Galois automorphism moves `(x, 0)` to `(g x, 0)`. -/
private theorem smul_rootTorsionCoeff (g : AbsoluteGaloisGroup K) {x : SeparableClosure K}
    (hx : aeval x W.toAffine.f = 0) (hgx : aeval (g x) W.toAffine.f = 0) :
    g • rootTorsionCoeff W hx = rootTorsionCoeff W hgx := by
  classical
  refine Subtype.ext ?_
  rw [WeierstrassCurve.coe_smul_torsionCoeff, coe_rootTorsionCoeff, coe_rootTorsionCoeff,
    WeierstrassCurve.smul_pointCoeffEquiv, WeierstrassCurve.Affine.Point.map_some]
  simp

/-- The points `(x, 0)` and `(y, 0)` agree only for `x = y`. -/
private theorem rootTorsionCoeff_injective {x y : SeparableClosure K}
    (hx : aeval x W.toAffine.f = 0) (hy : aeval y W.toAffine.f = 0)
    (h : rootTorsionCoeff W hx = rootTorsionCoeff W hy) : x = y := by
  classical
  have h' := congrArg (fun T : W.TorsionCoeff 2 ↦ W.pointCoeffEquiv.symm (T : W.PointCoeff)) h
  simp only [coe_rootTorsionCoeff, AddEquiv.symm_apply_apply] at h'
  exact (WeierstrassCurve.Affine.Point.some.inj h').1

omit [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
/-- The image of the universal root of a factor under an embedding is a root of the cubic. -/
theorem aeval_embedding_root_f (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) : aeval (σ (θ p)) W.toAffine.f = 0 := by
  rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero.mpr p.dvd, map_zero]

/-- The point `(σ θ, 0)` of `E(Kˢ)[2]` attached to an embedding `σ` of a factor field. -/
def embeddingTorsionCoeff (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) : W.TorsionCoeff 2 :=
  rootTorsionCoeff W (aeval_embedding_root_f W p σ)

open scoped Classical in
/-- The point `(σ θ, 0)` as a point of `E(Kˢ)`. -/
@[simp]
theorem coe_embeddingTorsionCoeff (p : W.toAffine.f.Factors) (σ : 𝕃 p →ₐ[K] SeparableClosure K) :
    (embeddingTorsionCoeff W p σ : W.PointCoeff) = W.pointCoeffEquiv
      (WeierstrassCurve.Affine.Point.some (σ (θ p)) 0
        (W.toAffine.nonsingular_baseChange_of_aeval_eq_zero (aeval_embedding_root_f W p σ))) :=
  coe_rootTorsionCoeff W _

omit [W.IsElliptic] [W.toAffine.IsCharNeTwoNF] in
/-- An automorphism of `Kˢ` fixes the image of an embedding of a factor field exactly when it
fixes the image of the universal root. -/
private theorem mem_fixingSubgroup_fieldRange_iff (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) {g : AbsoluteGaloisGroup K} :
    g ∈ σ.fieldRange.fixingSubgroup ↔ g (σ (θ p)) = σ (θ p) := by
  rw [← galoisSubgroup_toSubgroup, OpenSubgroup.mem_toSubgroup]
  exact mem_galoisSubgroup_iff_apply_eq_of_adjoin_eq_top K (𝕃 p) σ AdjoinRoot.adjoinRoot_eq_top

/-- The point `(σ θ, 0)` is fixed by the absolute Galois group of the factor field. -/
private def embeddingH0 (p : W.toAffine.f.Factors) (σ : 𝕃 p →ₐ[K] SeparableClosure K) :
    H0 σ.fieldRange.fixingSubgroup (W.TorsionCoeff 2) :=
  ⟨embeddingTorsionCoeff W p σ, fun g ↦ by
    have hg := (mem_fixingSubgroup_fieldRange_iff W p σ).1 g.2
    rw [Subgroup.smul_def, embeddingTorsionCoeff,
      smul_rootTorsionCoeff W _ _ (hg.symm ▸ aeval_embedding_root_f W p σ)]
    -- the two points agree since `g` fixes `σ θ`, which `congr` closes from `hg`
    congr 1⟩

/-- The invariant attached to `σ` is the point `(σ θ, 0)`. -/
private theorem coe_embeddingH0 (p : W.toAffine.f.Factors) (σ : 𝕃 p →ₐ[K] SeparableClosure K) :
    (embeddingH0 W p σ : W.TorsionCoeff 2) = embeddingTorsionCoeff W p σ :=
  (rfl)

/-- **The universal-root character, read in `Kˢ`.** Transported along the identification of
separable closures attached to an embedding `σ` of a factor field, the character `e₂(·, (θ, 0))`
of the factor field is the Weil pairing with `(σ θ, 0)`. -/
theorem kummerCoeffMapSymm_factorTorsionCharacter (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) (h2 : IsUnit ((2 : ℕ) : K)) (S : W.TorsionCoeff 2) :
    kummerCoeffMapSymm K 2 (𝕃 p) σ (factorTorsionCharacter W p h2
      (W.torsionCoeffBaseChange
        (separableClosureAlgEquiv K (𝕃 p) σ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
        2 S)) =
      W.torsionCoeffWeilPairing 2 h2 S (embeddingTorsionCoeff W p σ) := by
  classical
  set τ := (separableClosureAlgEquiv K (𝕃 p) σ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
  have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
  -- `τ` carries `(σ θ, 0)` to `(θ, 0)`
  have hT : (W.baseChange (𝕃 p)).twoTorsionCoeff (factorRoot_nonsingular W p)
      (WeierstrassCurve.Affine.evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF _ _) =
      W.torsionCoeffBaseChange τ 2 (embeddingTorsionCoeff W p σ) := by
    have hτx : τ (σ (θ p)) = algebraMap (𝕃 p) (SeparableClosure (𝕃 p)) (θ p) :=
      (separableClosureAlgEquiv_apply K (𝕃 p) σ _).trans
        (separableClosureRingEquiv_symm_apply_eq_algebraMap K (𝕃 p) σ (θ p))
    refine Subtype.ext ?_
    rw [WeierstrassCurve.coe_twoTorsionCoeff, WeierstrassCurve.coe_torsionCoeffBaseChange,
      embeddingTorsionCoeff, coe_rootTorsionCoeff,
      WeierstrassCurve.pointCoeffBaseChange_pointCoeffEquiv_some,
      WeierstrassCurve.basePointCoeff_some]
    simp only [hτx, map_zero]
  rw [factorTorsionCharacter_def W p h2 h2p, WeierstrassCurve.twoTorsionCharacter_eq_weilPairing,
    hT, WeierstrassCurve.torsionCoeffWeilPairing_torsionCoeffBaseChange _ h2]
  exact Additive.toMul.injective <| Subtype.ext <| Units.ext <| by
    simp [τ, separableClosureAlgEquiv_apply]

/-- **Corestriction of the factorwise descent class** (the projection formula): corestricting the
factorwise image of `c` from the factor field `K[X] ⧸ (p)`, embedded by `σ`, to `K` is the cup
product of `c`, through the Weil pairing, with the corestriction `∑ᵤ u • (σ θ, 0)` of the point
`(σ θ, 0)`. -/
private theorem kummerCor_factorCohomologicalMap (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) (h2 : IsUnit ((2 : ℕ) : K))
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    kummerCor K 2 (𝕃 p) σ (.ofAdd (factorCohomologicalMap W p
        (separableClosureAlgEquiv K (𝕃 p) σ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
        h2 c)) =
      .ofAdd (explicitCup10 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) (W.TorsionCoeff 2)
        (KummerCoeff K 2) (W.torsionCoeffWeilPairing 2 h2) continuous_of_discreteTopology
        (W.torsionCoeffWeilPairing_smul 2 h2) c
        (explicitCor0 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) σ.fieldRange.fixingSubgroup
          (embeddingH0 W p σ))) := by
  have hU := isOpen_fixingSubgroup_fieldRange K (𝕃 p) σ
  have key : explicitMap1 (AbsoluteGaloisGroup (𝕃 p)) (KummerCoeff (𝕃 p) 2)
      ↥σ.fieldRange.fixingSubgroup (KummerCoeff K 2)
      ((absoluteGaloisGroupEquivFixingSubgroup K (𝕃 p) σ).symm :
        ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup (𝕃 p))
      (kummerCoeffMapSymm K 2 (𝕃 p) σ) continuous_of_discreteTopology
      (kummerCoeffMapSymm_smul K 2 (𝕃 p) σ)
      (factorCohomologicalMap W p
        (separableClosureAlgEquiv K (𝕃 p) σ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
        h2 c) =
      explicitCup10 σ.fieldRange.fixingSubgroup (W.TorsionCoeff 2) (W.TorsionCoeff 2)
        (KummerCoeff K 2) (W.torsionCoeffWeilPairing 2 h2) continuous_of_discreteTopology
        (fun g m y ↦ W.torsionCoeffWeilPairing_smul 2 h2 (g : AbsoluteGaloisGroup K) m y)
        (explicitRes1 _ _ σ.fieldRange.fixingSubgroup c) (embeddingH0 W p σ) := by
    induction c using QuotientAddGroup.induction_on with
    | _ z =>
    simp only [factorCohomologicalMap_apply, WeierstrassCurve.torsionRes_eq_explicitMap1,
      explicitMap1_mk, explicitCoeff1_mk, explicitRes1_mk, explicitCup10_mk]
    refine congrArg _ (Subtype.ext (funext fun g ↦ ?_))
    -- unfold the three nested `cocyclesMap1` applications; `rw`/`simp only [cocyclesMap1_apply]`
    -- cannot, as the compatibility proof of the inner application is `map_smul` of the underlying
    -- `MulActionHom` of `factorTorsionCharacter`, which matches its expected type only after
    -- unfolding `ContinuousMonoidHom.id`, so the rewrite motive is not type-correct
    refine ((cocyclesMap1_apply ..).trans (congrArg _ ((cocyclesMap1_apply ..).trans
      (congrArg _ (cocyclesMap1_apply ..))))).trans ?_
    -- the element of `G_{K[X] ⧸ (p)}` attached to `g` restricts to `g`
    have hg : absoluteGaloisGroupMap
        (separableClosureAlgEquiv K (𝕃 p) σ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
        (ContinuousMonoidHom.id (AbsoluteGaloisGroup (𝕃 p))
          (((absoluteGaloisGroupEquivFixingSubgroup K (𝕃 p) σ).symm :
            ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup (𝕃 p)) g)) = g := by
      rw [absoluteGaloisGroupMap_separableClosureAlgEquiv]
      simp
    rw [hg]
    refine (kummerCoeffMapSymm_factorTorsionCharacter W p σ h2 _).trans ?_
    dsimp only
    rw [cocyclesMap1_apply, (embeddingH0 W p σ).2 g, AddMonoidHom.id_apply,
      ContinuousMonoidHom.subgroupSubtype_apply, coe_embeddingH0]
  refine Multiplicative.toAdd.injective ((toAdd_kummerCor K 2 (𝕃 p) σ _).trans ?_)
  exact (congrArg _ key).trans
    (explicitCup_projection10_res_left _ _ _ _ _ hU _ _ _ c (embeddingH0 W p σ))

/-- A Galois automorphism moves the point `(σ θ, 0)` to `(g (σ θ), 0)`. -/
theorem smul_embeddingTorsionCoeff (g : AbsoluteGaloisGroup K) (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) :
    g • embeddingTorsionCoeff W p σ =
      embeddingTorsionCoeff W p ((g : SeparableClosure K →ₐ[K] SeparableClosure K).comp σ) :=
  smul_rootTorsionCoeff W g _ _

/-- The point `(σ θ, 0)` attached to an embedding `σ` of a factor field is nonzero. -/
theorem embeddingTorsionCoeff_ne_zero (p : W.toAffine.f.Factors)
    (σ : 𝕃 p →ₐ[K] SeparableClosure K) : embeddingTorsionCoeff W p σ ≠ 0 := by
  classical
  intro h
  have h' := congrArg (fun T : W.TorsionCoeff 2 ↦ (T : W.PointCoeff)) h
  simp [embeddingTorsionCoeff, coe_rootTorsionCoeff] at h'

/-- **The embeddings of the factor fields are the nonzero points of order two.** Sending an
embedding `σ` of the factor field `K[X] ⧸ (p)` into `Kˢ` to the point `(σ θ, 0)` is a bijection
from the embeddings of all the factor fields onto the nonzero points of `E(Kˢ)[2]`. -/
theorem bijective_embeddingTorsionCoeff (h2 : IsUnit ((2 : ℕ) : K)) :
    Function.Bijective (fun i : Σ p : W.toAffine.f.Factors, 𝕃 p →ₐ[K] SeparableClosure K ↦
      (⟨embeddingTorsionCoeff W i.1 i.2, embeddingTorsionCoeff_ne_zero W i.1 i.2⟩ :
        {S : W.TorsionCoeff 2 // S ≠ 0})) := by
  classical
  have hroot (p : W.toAffine.f.Factors) (τ : 𝕃 p →ₐ[K] SeparableClosure K) :
      aeval (τ (θ p)) (p : K[X]) = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, τ⟩ ⟨q, τ'⟩ h
    have hx := rootTorsionCoeff_injective W (aeval_embedding_root_f W p τ)
      (aeval_embedding_root_f W q τ') (congrArg Subtype.val h)
    -- distinct factors are coprime, so they have no common root
    obtain rfl : p = q := by
      by_contra hpq
      obtain ⟨a, b, hab⟩ := Polynomial.Factors.isCoprime hpq
      have := congrArg (aeval (τ (θ p))) hab
      rw [map_add, map_mul, map_mul, hroot, hx, hroot, map_one] at this
      simp at this
    exact Sigma.ext rfl (heq_of_eq (AdjoinRoot.algHom_ext hx))
  · rintro ⟨S, hS⟩
    obtain ⟨p, x, hx, h, hS'⟩ := exists_factor_of_ne_zero W h2 hS
    refine ⟨⟨p, AdjoinRoot.liftAlgHom _ (Algebra.ofId K _) x hx⟩, Subtype.ext (Subtype.ext ?_)⟩
    simp only [embeddingTorsionCoeff, coe_rootTorsionCoeff, hS']
    congr 2
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The embeddings of the factor fields, identified with the nonzero points of `E(Kˢ)[2]` by
`σ ↦ (σ θ, 0)`. -/
private def sigmaEmbeddingEquivNonzeroTorsion (h2 : IsUnit ((2 : ℕ) : K)) :
    (Σ p : W.toAffine.f.Factors, 𝕃 p →ₐ[K] SeparableClosure K) ≃
      {S : W.TorsionCoeff 2 // S ≠ 0} :=
  Equiv.ofBijective _ (bijective_embeddingTorsionCoeff W h2)

/-- **The conjugates of the points `(σ θ, 0)` are the three points of order two.** Over the
irreducible factors `p` of the `2`-division cubic, with embeddings `σ p` of their factor fields
into `Kˢ`, the translates `u • (σ p θ, 0)` by representatives `u` of the cosets of the absolute
Galois groups of the factor fields run through the nonzero points of `E(Kˢ)[2]`, each exactly
once. So they sum to zero. -/
private theorem sum_sum_out_smul_embeddingTorsionCoeff [Fintype W.toAffine.f.Factors]
    (h2 : IsUnit ((2 : ℕ) : K)) (σ : (p : W.toAffine.f.Factors) → 𝕃 p →ₐ[K] SeparableClosure K) :
    ∑ p, ∑ u : AbsoluteGaloisGroup K ⧸ (σ p).fieldRange.fixingSubgroup,
      Quotient.out u • embeddingTorsionCoeff W p (σ p) = 0 := by
  classical
  have := W.isAddKleinFour_torsionCoeff_two h2
  have := Fintype.ofFinite (W.TorsionCoeff 2)
  -- the translates are the points `(τ θ, 0)` over all embeddings `τ` of the factor fields
  have hsum (p : W.toAffine.f.Factors) :
      ∑ u : AbsoluteGaloisGroup K ⧸ (σ p).fieldRange.fixingSubgroup,
        Quotient.out u • embeddingTorsionCoeff W p (σ p) =
      ∑ τ : 𝕃 p →ₐ[K] SeparableClosure K, embeddingTorsionCoeff W p τ := by
    refine Fintype.sum_equiv (FieldTheory.fixingSubgroupQuotientEquivAlgHom (σ p)) _ _ fun u ↦ ?_
    conv_rhs => rw [← QuotientGroup.out_eq' u, FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk]
    exact smul_embeddingTorsionCoeff W _ p (σ p)
  simp only [hsum]
  rw [← Fintype.sum_sigma' (fun p τ ↦ embeddingTorsionCoeff W p τ),
    Fintype.sum_equiv (sigmaEmbeddingEquivNonzeroTorsion W h2)
      (fun i ↦ embeddingTorsionCoeff W i.1 i.2) (fun S ↦ (S : W.TorsionCoeff 2))
      (fun _ ↦ rfl),
    ← Finset.sum_subtype {S | S ≠ 0} (fun _ ↦ by simp) (fun S ↦ S), Finset.sum_filter_ne_zero]
  exact IsAddKleinFour.sum_univ_eq_zero

/-- The norm class of a square class of the étale algebra is the product of the norm classes of
its components at the field factors. -/
private theorem quotientMulEquivOfEq_normM [Fintype W.toAffine.f.Factors] (m : W.toAffine.M) :
    QuotientGroup.quotientMulEquivOfEq (powerSubgroup_eq_range_powMonoidHom Kˣ 2).symm
        (W.toAffine.normM m) =
      ∏ p, powerClassMap 2 (Algebra.normUnits K) (explicitFactor W p m) := by
  induction m using QuotientGroup.induction_on with
  | H u =>
  simp only [WeierstrassCurve.Affine.normM_mk, QuotientGroup.quotientMulEquivOfEq_mk,
    explicitFactor_apply, AdjoinRoot.modPowEquivPiFactors_mk, powerClassMap_mk,
    ← QuotientGroup.mk_prod]
  refine congrArg QuotientGroup.mk (Units.ext ?_)
  simpa [Units.coe_prod] using AdjoinRoot.norm_eq_prod_norm_projFactor _ _ (u : W.toAffine.A)

/-- **The cohomological `2`-descent map satisfies the norm condition**: the image of every class
of `H¹(G_K, E[2])` in the square classes of the étale algebra `K[X] ⧸ (f)` has square norm. -/
@[simp]
theorem normM_cohomologicalMap (h2 : IsUnit ((2 : ℕ) : K))
    (c : Multiplicative (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2))) :
    W.toAffine.normM (cohomologicalMap W h2 c) = 1 := by
  classical
  have : Finite W.toAffine.f.Factors := Polynomial.Factors.finite W.toAffine.f_ne_zero
  have := Fintype.ofFinite W.toAffine.f.Factors
  -- an embedding of each factor field into `Kˢ`
  have hσ (p : W.toAffine.f.Factors) : Nonempty (𝕃 p →ₐ[K] SeparableClosure K) := by
    have := AdjoinRoot.isSeparable_of_separable (WeierstrassCurve.Affine.separable_f W.toAffine) p
    exact ⟨IsSepClosed.lift⟩
  let σ (p : W.toAffine.f.Factors) : 𝕃 p →ₐ[K] SeparableClosure K := (hσ p).some
  refine (QuotientGroup.quotientMulEquivOfEq
    (powerSubgroup_eq_range_powMonoidHom Kˣ 2).symm).injective ?_
  refine (kummerIso K 2 h2).injective ?_
  rw [map_one, map_one, quotientMulEquivOfEq_normM, map_prod]
  -- each factor is the corestriction of the factorwise class, a cup product with `c`
  have hfac (p : W.toAffine.f.Factors) :
      kummerIso K 2 h2 (powerClassMap 2 (Algebra.normUnits K)
        (explicitFactor W p (cohomologicalMap W h2 c))) =
      .ofAdd (explicitCup10 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) (W.TorsionCoeff 2)
        (KummerCoeff K 2) (W.torsionCoeffWeilPairing 2 h2) continuous_of_discreteTopology
        (W.torsionCoeffWeilPairing_smul 2 h2) c.toAdd
        (explicitCor0 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) (σ p).fieldRange.fixingSubgroup
          (embeddingH0 W p (σ p)))) := by
    have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
    -- term-mode composition: rewriting here unfolds the factor fields at great cost
    exact (kummerIso_norm K 2 (𝕃 p) (σ p) h2p _).symm.trans
      ((congrArg (kummerCor K 2 (𝕃 p) (σ p)) (kummerIso_explicitFactor_cohomologicalMap W p
        (separableClosureAlgEquiv K (𝕃 p) (σ p) :
          SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) h2 h2p c.toAdd)).trans
        (kummerCor_factorCohomologicalMap W p (σ p) h2 c.toAdd))
  -- and the corestricted points sum to zero
  have hzero : ∑ p, explicitCor0 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)
      (σ p).fieldRange.fixingSubgroup (embeddingH0 W p (σ p)) = 0 := by
    refine Subtype.ext ?_
    simpa [coe_explicitCor0, coe_embeddingH0] using sum_sum_out_smul_embeddingTorsionCoeff W h2 σ
  refine (Finset.prod_congr rfl fun p _ ↦ hfac p).trans ?_
  rw [← ofAdd_sum, ← map_sum, hzero, map_zero, ofAdd_zero]

/-- **The image of the cohomological `2`-descent map lies in the kernel of the norm**, the
subgroup of the square classes of `K[X] ⧸ (f)` in which the explicit `2`-Selmer group is cut out
by local conditions. -/
theorem range_cohomologicalMap_le_ker_normM (h2 : IsUnit ((2 : ℕ) : K)) :
    (cohomologicalMap W h2).range ≤ W.toAffine.normM.ker := by
  rintro _ ⟨c, rfl⟩
  exact normM_cohomologicalMap W h2 c

end NormCondition

end TwoDescent

end TauCeti
