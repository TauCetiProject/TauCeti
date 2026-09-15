/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Evaluation
public import TauCeti.RingTheory.MvPowerSeries.Substitution
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Evaluating the `w`-expansion and the formal inverse at a parameter

For a Weierstrass curve `W` over a complete linearly topologised ring `O`, the `w`-expansion of
`FormalGroup/WExpansion.lean` and the formal inverse of `FormalGroup/Inverse.lean` can both be
evaluated at a parameter `t` for which the evaluation converges. This file provides those
evaluations, the identities they inherit from the series, and their membership, unit and
non-vanishing properties.

Three hypotheses appear here, and they do different work. `PowerSeries.HasEval t` is what
evaluation itself requires, and most results ask for it directly. Others ask instead for an ideal
`I` whose adic topology is the ambient one, together with a membership `t ∈ I` that supplies the
convergence: `isUnit_formalUEval`, `formalWEval_ne_zero`, `algebraMap_formalWEval_ne_zero` and
`hasEval_formalInverseEval`. `formalUEval_sub_one_mem` is the one result asking for both.
`isUnit_thirdRootDenom` asks for neither: it is a statement about the curve's coefficients and a
topologically nilpotent element, so it takes `IsTopologicallyNilpotent` directly, and
`[NonarchimedeanRing O]` in place of the ambient `[IsTopologicalRing O]`. `formalWEval_zero` asks
for neither either, being an evaluation at a parameter that needs no convergence hypothesis.

Only two of the five values are confined to `I ^ k`: `w(t)` and `ι(t)`. Of the four unit
statements, only `u(t)`'s needs the ideal; the denominator `d(t) = 1 - a₁ t - a₃ w(t)` and its
series inverse need nothing beyond evaluation, and the chord cubic's leading coefficient
`1 + a₂l + a₄l² + a₆l³` needs only that `l` is topologically nilpotent. Each declaration's own
docstring says where its conclusion comes from.

## Main definitions

* `WeierstrassCurve.formalWEval` : the value `w(t)` of the `w`-expansion at `t`.
* `WeierstrassCurve.formalUEval` : the value `u(t)` of its unit part `w(z) / z ^ 3`.
* `WeierstrassCurve.formalInverseDenomEval` : the value of the denominator `1 - a₁ z - a₃ w(z)`.
* `WeierstrassCurve.formalInverseDenomInvEval` : the value of that denominator's series inverse.
* `WeierstrassCurve.formalInverseEval` : the value `ι(t)` of the formal inverse at `t`.

## Main results

* `WeierstrassCurve.formalWEval_eq_pow_mul_formalUEval` : the factorisation `w(t) = t ^ 3 * u(t)`.
* `WeierstrassCurve.algebraMap_formalInverseEval_div_algebraMap_formalWEval_formalInverseEval` and
  `WeierstrassCurve.neg_one_div_algebraMap_formalWEval_formalInverseEval` : the two division
  identities the inverse law rests on, over a field and with no nonvanishing hypothesis. Where
  `w(t) ≠ 0` they say `ι` fixes the `x`-coordinate `t / w(t)` and sends `-1 / w(t)` to the curve's
  `negY` of it, `y ↦ -y - a₁x - a₃`.
* `WeierstrassCurve.formalWEval_zero` : `w(0) = 0`, an immediate consequence of that
  factorisation and the reason the zero parameter carries no affine coordinates.
* `WeierstrassCurve.formalWEval_mem`, `WeierstrassCurve.formalInverseEval_mem` : a parameter in
  `I ^ k` has `w(t)` and `ι(t)` in `I ^ k`.
* `WeierstrassCurve.formalUEval_sub_one_mem` : `u(t)` is congruent to `1` modulo `I ^ k`.
* `WeierstrassCurve.isUnit_formalUEval`, `WeierstrassCurve.isUnit_formalInverseDenomEval`,
  `WeierstrassCurve.isUnit_formalInverseDenomInvEval` : three of the four unit statements.
* `WeierstrassCurve.isUnit_thirdRootDenom` : the fourth — the leading coefficient
  `1 + a₂l + a₄l² + a₆l³` of the chord cubic, which Vieta's formula for the third root divides
  by, is a unit at any topologically nilpotent `l`.
* `WeierstrassCurve.formalInverseDenomEval_eq`, `WeierstrassCurve.formalInverseEval_eq` and
  `WeierstrassCurve.formalInverseEval_mul_formalInverseDenomEval` : the defining formulas for
  `d(t)` and `ι(t)`, the last in the form `ι(t) * d(t) = -t` that avoids the series inverse.
* `WeierstrassCurve.formalWEval_wEquation` : the `w`-equation at a parameter.
* `WeierstrassCurve.eq_formalWEval_of_wEquation` : **`w(t)` is the only solution of the
  `w`-equation lying in the ideal**, the evaluated counterpart of `WExpansion.lean`'s
  `eq_of_wEquation`.
* `WeierstrassCurve.formalWEval_ne_zero`, `WeierstrassCurve.formalInverseEval_ne_zero` : the two
  non-vanishing statements, and `WeierstrassCurve.algebraMap_formalWEval_ne_zero` for the image of
  `w(t)` in a nontrivial domain over `O`.
* `WeierstrassCurve.formalInverseEval_formalInverseEval` : the involution `ι(ι(t)) = t`, and
  `WeierstrassCurve.formalWEval_formalInverseEval` : `w(ι(t)) = -(w(t) * d(t)⁻¹)`. Both ask only
  that `t` and `ι(t)` admit evaluation; `WeierstrassCurve.hasEval_formalInverseEval` supplies the
  second from an adic ideal when that is how a consumer holds it.

## Implementation notes

The evaluation is Mathlib's `PowerSeries.eval₂` at the identity ring hom. The adic hypothesis is
carried as an explicit `IsAdic I` argument rather than through a `WithIdeal` instance, matching
`MvPowerSeries.eval₂_mem_pow`, which these results call. `WithIdeal` would supply the topology
itself at `priority := 100`, so on a ring that already carries one — `ℤ_[p]`, whose topology comes
from its metric — the adic topology is shadowed and the results become inapplicable. `IsAdic` is
instead a *proposition about* the ambient topology, so it can be supplied for such a ring.

Names follow the series on this side rather than the source's: the evaluation of `formalW` is
`formalWEval`, and so on. The source's names do not transfer, because the source-to-repository map
is not order-preserving — the source's `uSeries` is this repository's `formalInverseDenom`, while
`formalU` is the source's `vSeries` — and every series here has the same type, so a mismatched
pairing would compile.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`, whose full expansion is
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`),
`EllipticCurves/WeierstrassFormalGroup/Eval.lean` — its evaluation layer down to the formal
inverse, declarations `wEval`, `vEval`, `wEval_mem`, `wEval_eq`, `wEval_eq_cube_mul`,
`vEval_sub_one_mem`, `isUnit_vEval`, `uEval`, `duEval`, `iotaEval`, `uEval_eq`,
`uEval_mul_duEval`, `isUnit_uEval`, `isUnit_chordCoeff`, `iotaEval_eq`, `iotaEval_mem`,
`wEval_iotaEval` and `iotaEval_iotaEval`.

Four things are spelled differently here.

* The source evaluates through its own `ChabautyColeman.MvPSeries.eval`, which is by definition
  `MvPowerSeries.eval₂ (RingHom.id _)`. That wrapper is not ported; the definitions use Mathlib's
  `PowerSeries.eval₂` directly, as `TauCeti/RingTheory/MvPowerSeries/Evaluation.lean` already does
  for the membership estimates this file calls.
* The source's three `eval_mem_maximalIdeal_pow` lemmas are that same file's
  `MvPowerSeries.eval₂_mem_pow`, `_mul` and `_add_mul`, which are stated for an arbitrary adic
  ideal rather than the maximal one, so none of the three is re-ported.
* The source obtains unit-ness from `IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal`. Here it comes
  instead from `IsTopologicallyNilpotent.isUnit_one_add` — Wedhorn 5.38, already in this repository
  — which the ambient completeness makes available and which needs no hypothesis relating `I` to
  the Jacobson radical. `IsLocalRing` is therefore not needed in this file at all.
* The source's `wPoly` is this repository's `WeierstrassCurve.wEquationRHS`, which is generic over
  an algebra, so evaluating it at `O` gives the element-level equation without a second
  definition.
* The source's private `eval_subst_single` is not ported. It is `MvPSeries.eval_subst`
  specialised, and this repository's `PowerSeries.aeval_subst` already states that fact without
  the `DiscreteUniformity` hypotheses Mathlib's `MvPowerSeries.eval₂_subst` carries — which a
  general adic ring does not supply, coefficients and values here being the same such ring. The
  two involution proofs call it directly.

The adic hypothesis is carried as an explicit `IsAdic I` argument for the reason given under
implementation notes above.
-/

public section

open PowerSeries

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]

/-- Evaluation at a parameter admitting one, as a ring homomorphism `O⟦X⟧ →+* O`. Every identity
in this file is the image of an identity of series under this map, so it is factored out here; it
is private because the file's statements are about the individual values, not about the vehicle
that transports them. -/
private noncomputable def evalAt {t : O} (ht : PowerSeries.HasEval t) : PowerSeries O →+* O :=
  PowerSeries.eval₂Hom (φ := RingHom.id O) (by simpa using continuous_id) ht

/-- `evalAt` is `PowerSeries.eval₂` at the identity ring hom, as a function. -/
private theorem coe_evalAt {t : O} (ht : PowerSeries.HasEval t) :
    ⇑(evalAt ht) = eval₂ (RingHom.id O) t :=
  PowerSeries.coe_eval₂Hom (φ := RingHom.id O) _ ht

namespace WeierstrassCurve

variable (W : WeierstrassCurve O)

/-- The value of the `w`-expansion at a parameter. -/
noncomputable def formalWEval (t : O) : O := eval₂ (RingHom.id O) t W.formalW

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalWEval` is evaluation of `formalW` through the identity ring hom. -/
theorem formalWEval_def (t : O) : W.formalWEval t = eval₂ (RingHom.id O) t W.formalW := (rfl)

/-- The value of the unit part `u(z) = w(z) / z ^ 3` at a parameter. -/
noncomputable def formalUEval (t : O) : O := eval₂ (RingHom.id O) t W.formalU

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalUEval` is evaluation of `formalU` through the identity ring hom. -/
theorem formalUEval_def (t : O) : W.formalUEval t = eval₂ (RingHom.id O) t W.formalU := (rfl)

/-- **The factorisation `w(t) = t ^ 3 * u(t)`** at a parameter, from the corresponding
factorisation `formalW_eq_X_pow_mul_formalU` of the series. -/
theorem formalWEval_eq_pow_mul_formalUEval {t : O} (ht : PowerSeries.HasEval t) :
    W.formalWEval t = t ^ 3 * W.formalUEval t := by
  have h := congrArg (evalAt ht) W.formalW_eq_X_pow_mul_formalU
  rw [map_mul, map_pow] at h
  simpa [formalWEval, formalUEval, coe_evalAt, PowerSeries.eval₂_X] using h

/-- **The `w`-expansion vanishes at the zero parameter**, `w` being a multiple of `z ^ 3`. This is
why the zero parameter is the point at infinity: the coordinates `t / w(t)` and `-1 / w(t)` have no
value there. -/
@[simp]
theorem formalWEval_zero : W.formalWEval 0 = 0 := by
  simp [W.formalWEval_eq_pow_mul_formalUEval PowerSeries.HasEval.zero]

/-- The value of the `w`-expansion at a parameter of `I ^ k` again lies in `I ^ k`: it is
`t ^ 3` times the value of the unit part. -/
theorem formalWEval_mem {I : Ideal O} {k : ℕ} {t : O} (ht : PowerSeries.HasEval t)
    (htk : t ∈ I ^ k) : W.formalWEval t ∈ I ^ k := by
  rw [W.formalWEval_eq_pow_mul_formalUEval ht]
  exact Ideal.mul_mem_right _ _ (by rw [pow_succ]; exact Ideal.mul_mem_left _ _ htk)

/-- The value of the unit part differs from `1` by an element of `I ^ k` when the parameter lies
there: its constant coefficient is `1`, and every other monomial carries a factor of the
parameter. -/
theorem formalUEval_sub_one_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t : O}
    (ht : PowerSeries.HasEval t) (htk : t ∈ I ^ k) : W.formalUEval t - 1 ∈ I ^ k := by
  have key := MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) (by simpa using continuous_id)
    (PowerSeries.hasEval ht) hI (fun _ ↦ htk) (W.formalU - 1) (by
      rw [← PowerSeries.constantCoeff_eq]
      simp [W.constantCoeff_formalU])
  -- `eval₂` is additive only through `eval₂Hom`, which needs the continuity and `HasEval` data.
  have hsplit : eval₂ (RingHom.id O) t (W.formalU - 1) = W.formalUEval t - 1 := by
    have h := map_sub (evalAt ht) W.formalU 1
    rw [map_one] at h
    simpa [formalUEval, coe_evalAt] using h
  rw [← hsplit]
  simpa [eval₂] using key

/-- The value of the unit part at a parameter of `I` is a unit: it differs from `1` by an element
of `I`, which is topologically nilpotent, so Wedhorn 5.38 applies. -/
theorem isUnit_formalUEval {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    IsUnit (W.formalUEval t) := by
  have : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  have hsub : W.formalUEval t - 1 ∈ I := by
    simpa using W.formalUEval_sub_one_mem hI (k := 1)
      (hI.isTopologicallyNilpotent_of_mem ht) (by simpa using ht)
  simpa using (hI.isTopologicallyNilpotent_of_mem hsub).isUnit_one_add

omit [IsTopologicalRing O] in
/-- **The leading coefficient of the chord cubic is a unit** at any topologically nilpotent
element. Substituting `w = λz + ν` into the Weierstrass equation produces a cubic in `z` whose
leading coefficient is `1 + a₂λ + a₄λ² + a₆λ³`; Vieta's formula for its third root divides by that
coefficient, so dividing is legitimate exactly when this holds.

Stated for an arbitrary topologically nilpotent element rather than for the evaluated slope, since
that is all the statement needs; `IsAdic.isTopologicallyNilpotent_of_mem` supplies it from
membership in an adic ideal when that is how a consumer holds it. `[NonarchimedeanRing O]` stands
in for the ambient `[IsTopologicalRing O]`, which it implies.

Not the same fact as `Add/PairSubst.lean`'s `subst_pair_thirdRootDenom_ne_zero`, which says the
corresponding multivariate *power series* is nonzero over a nontrivial base. That one lives in the
series world and concludes nonvanishing; this one concludes invertibility, which is what dividing
by it requires. -/
theorem isUnit_thirdRootDenom [NonarchimedeanRing O] {l : O}
    (hl : IsTopologicallyNilpotent l) :
    IsUnit (1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3) := by
  -- the nonconstant part is a multiple of `l`, hence topologically nilpotent, so Wedhorn 5.38
  -- applies; unlike `isUnit_formalUEval` this needs no monomial estimate and hence no ideal
  have hfac : W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3 =
      l * (W.a₂ + W.a₄ * l + W.a₆ * l ^ 2) := by ring
  have h := (hl.mul_right (W.a₂ + W.a₄ * l + W.a₆ * l ^ 2)).isUnit_one_add
  rw [← hfac] at h
  simpa [add_assoc] using h

/-! ### The inverse-side evaluations

Note which series these evaluate. The source's `uSeries` is this repository's
`formalInverseDenom`, **not** `formalU`; `formalU` is the source's `vSeries`, evaluated above as
`formalUEval`. Both are `PowerSeries O`, so pairing an evaluation with the wrong one would compile.
-/

/-- The value of the formal inverse's denominator `1 - a₁ z - a₃ w(z)` at a parameter. -/
noncomputable def formalInverseDenomEval (t : O) : O :=
  eval₂ (RingHom.id O) t W.formalInverseDenom

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInverseDenomEval` is evaluation of `formalInverseDenom` through the identity ring
hom. -/
theorem formalInverseDenomEval_def (t : O) :
    W.formalInverseDenomEval t = eval₂ (RingHom.id O) t W.formalInverseDenom := (rfl)

/-- The value at a parameter of the power-series inverse of `formalInverseDenom`. -/
noncomputable def formalInverseDenomInvEval (t : O) : O :=
  eval₂ (RingHom.id O) t (PowerSeries.invOfUnit W.formalInverseDenom 1)

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInverseDenomInvEval` is evaluation of the series inverse of `formalInverseDenom`
through the identity ring hom. -/
theorem formalInverseDenomInvEval_def (t : O) : W.formalInverseDenomInvEval t =
    eval₂ (RingHom.id O) t (PowerSeries.invOfUnit W.formalInverseDenom 1) := (rfl)

/-- The value of the formal inverse `ι(z)` at a parameter. -/
noncomputable def formalInverseEval (t : O) : O := eval₂ (RingHom.id O) t W.formalInverse

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInverseEval` is evaluation of `formalInverse` through the identity ring hom. -/
theorem formalInverseEval_def (t : O) :
    W.formalInverseEval t = eval₂ (RingHom.id O) t W.formalInverse := (rfl)

/-- The denominator's value and the value of its series inverse multiply to `1`. -/
theorem formalInverseDenomEval_mul_inv {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseDenomEval t * W.formalInverseDenomInvEval t = 1 := by
  have h := congrArg (evalAt ht) W.mul_invOfUnit_formalInverseDenom
  rw [map_mul, map_one] at h
  simpa [formalInverseDenomEval, formalInverseDenomInvEval, coe_evalAt] using h

/-- The denominator's value at a parameter is a unit. -/
theorem isUnit_formalInverseDenomEval {t : O} (ht : PowerSeries.HasEval t) :
    IsUnit (W.formalInverseDenomEval t) :=
  IsUnit.of_mul_eq_one _ (W.formalInverseDenomEval_mul_inv ht)

/-- The value of the series inverse of the denominator is a unit. -/
theorem isUnit_formalInverseDenomInvEval {t : O} (ht : PowerSeries.HasEval t) :
    IsUnit (W.formalInverseDenomInvEval t) :=
  IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact W.formalInverseDenomEval_mul_inv ht)

/-- **The defining formula for the denominator's value**: `1 - a₁ t - a₃ w(t)`. -/
theorem formalInverseDenomEval_eq {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseDenomEval t = 1 - W.a₁ * t - W.a₃ * W.formalWEval t := by
  have h := congrArg (evalAt ht) W.formalInverseDenom_def
  rw [map_sub, map_sub, map_one, map_mul, map_mul] at h
  simpa [formalInverseDenomEval, formalWEval, coe_evalAt, PowerSeries.eval₂_C,
    PowerSeries.eval₂_X] using h

/-- **The defining formula for the formal inverse's value**: `ι(t) = -t / (1 - a₁ t - a₃ w(t))`,
written through the series inverse of the denominator. -/
theorem formalInverseEval_eq {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseEval t = -(t * W.formalInverseDenomInvEval t) := by
  have h := congrArg (evalAt ht) W.formalInverse_def
  rw [map_neg, map_mul] at h
  simpa [formalInverseEval, formalInverseDenomInvEval, coe_evalAt, PowerSeries.eval₂_X] using h

/-- **The defining formula for `ι(t)` cleared of the series inverse**: `ι(t)` times the concrete
denominator `1 - a₁ t - a₃ w(t)` is `-t`. -/
theorem formalInverseEval_mul_formalInverseDenomEval {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseEval t * W.formalInverseDenomEval t = -t := by
  rw [W.formalInverseEval_eq ht, neg_mul, mul_assoc, mul_comm (W.formalInverseDenomInvEval t),
    W.formalInverseDenomEval_mul_inv ht, mul_one]

/-- The formal inverse maps a parameter of `I ^ k` back into `I ^ k`: it is `-t` times a value. -/
theorem formalInverseEval_mem {I : Ideal O} {k : ℕ} {t : O} (ht : PowerSeries.HasEval t)
    (htk : t ∈ I ^ k) : W.formalInverseEval t ∈ I ^ k := by
  rw [W.formalInverseEval_eq ht]
  exact neg_mem (Ideal.mul_mem_right _ _ htk)

/-- **The `w`-equation at a parameter.** Evaluating `formalW_wEquation` at `t` shows `w(t)` is a
fixed point of `v ↦ wEquationRHS W t v`, which is the Weierstrass equation in the coordinates
`x = z / w`, `y = -1 / w`. -/
theorem formalWEval_wEquation {t : O} (ht : PowerSeries.HasEval t) :
    W.formalWEval t = wEquationRHS W t (W.formalWEval t) := by
  have h := congrArg (evalAt ht) W.formalW_wEquation
  rw [wEquationRHS_powerSeries] at h
  simp only [map_add, map_mul, map_pow] at h
  simpa [formalWEval, wEquationRHS_def, coe_evalAt, PowerSeries.eval₂_C,
    PowerSeries.eval₂_X] using h

/-- **Uniqueness of the solution of the `w`-equation at a parameter.** For a parameter `t` of an
adic ideal `I`, the value `w(t)` is the only element of `I` solving the `w`-equation at `t`. Both
membership hypotheses are used: `t ∈ I` is what makes `w` converge at `t`, and `s ∈ I` is what
confines the competing solution.

This is the evaluated counterpart of `WExpansion.lean`'s `eq_of_wEquation`. It is what recognises
a point of the curve as a parametrised one: the coordinates of such a point supply *some* solution
of the `w`-equation, and this is what identifies that solution as `w(t)`. -/
theorem eq_formalWEval_of_wEquation {I : Ideal O} (hI : IsAdic I) {t s : O} (ht : t ∈ I)
    (hs : s ∈ I) (h : s = wEquationRHS W t s) : s = W.formalWEval t := by
  -- `eq_of_wEquation` compares coefficients, and a value has none. Instead the difference of the
  -- two sides of the equation factors as `(1 - c) * (s - w(t))` with `c` a combination of the
  -- coefficients and of the two solutions lying in `I`; membership in `I` makes `c` topologically
  -- nilpotent, so `1 - c` is a unit by Wedhorn 5.38 and the difference vanishes.
  have : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  have hE : PowerSeries.HasEval t := hI.isTopologicallyNilpotent_of_mem ht
  set w := W.formalWEval t with hw_def
  have hw : w = wEquationRHS W t w := W.formalWEval_wEquation hE
  have hwI : w ∈ I := by simpa using W.formalWEval_mem (k := 1) hE (by simpa using ht)
  -- the factor pulled out of the difference of the two sides of the equation
  set c := W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (s + w) + W.a₄ * (t * (s + w)) +
    W.a₆ * (s ^ 2 + s * w + w ^ 2) with hc_def
  have hsw : s + w ∈ I := add_mem hs hwI
  have hcI : c ∈ I := by
    refine add_mem (add_mem (add_mem (add_mem (Ideal.mul_mem_left _ _ ht)
      (Ideal.mul_mem_left _ _ ?_)) (Ideal.mul_mem_left _ _ hsw))
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hsw))) (Ideal.mul_mem_left _ _ ?_)
    · rw [sq]; exact Ideal.mul_mem_left _ _ ht
    · exact add_mem (add_mem (by rw [sq]; exact Ideal.mul_mem_left _ _ hs)
        (Ideal.mul_mem_left _ _ hwI)) (by rw [sq]; exact Ideal.mul_mem_left _ _ hwI)
  have hzero : (1 - c) * (s - w) = 0 := by
    rw [wEquationRHS_def] at h hw
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at h hw
    rw [hc_def]
    linear_combination h - hw
  exact sub_eq_zero.mp
    (((hI.isTopologicallyNilpotent_of_mem hcI).isUnit_one_sub.mul_right_eq_zero).mp hzero)

/-- `w` does not vanish at a parameter of `I` whose cube is nonzero: the factorisation
`w(t) = t ^ 3 * u(t)` has a unit second factor. Over a domain the hypothesis is `t ≠ 0`. -/
theorem formalWEval_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ^ 3 ≠ 0) : W.formalWEval t ≠ 0 := by
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht)]
  exact fun h ↦ ht0 ((W.isUnit_formalUEval hI ht).mul_left_eq_zero.mp h)

/-- **`w(t)` has nonzero image** in any nontrivial domain over `O` once the image of `t` does:
the expansion factors as `t ^ 3 * u(t)` with `u(t)` a unit, and both factors have nonzero image —
the cube because there are no zero divisors, the unit because units map to units. Unlike
`formalWEval_ne_zero` this needs no hypothesis on `t ^ 3`, because the cube is checked in the
codomain. -/
theorem algebraMap_formalWEval_ne_zero {S : Type*} [CommRing S] [Nontrivial S] [NoZeroDivisors S]
    [Algebra O S] {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : algebraMap O S t ≠ 0) : algebraMap O S (W.formalWEval t) ≠ 0 := by
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht), map_mul,
    map_pow]
  exact mul_ne_zero (pow_ne_zero _ ht0)
    ((W.isUnit_formalUEval hI ht).map (algebraMap O S)).ne_zero

/-- The formal inverse does not vanish at a nonzero parameter: `ι(t)` is `-t` times a unit, and
multiplying by a unit cannot create a zero. No hypothesis on `t ^ 3` is needed — unlike
`formalWEval_ne_zero`, whose factor `t ^ 3` can vanish at a nonzero nilpotent `t`. -/
theorem formalInverseEval_ne_zero {t : O} (ht : PowerSeries.HasEval t) (ht0 : t ≠ 0) :
    W.formalInverseEval t ≠ 0 := by
  rw [W.formalInverseEval_eq ht, neg_ne_zero]
  exact fun h ↦ ht0 ((W.isUnit_formalInverseDenomInvEval ht).mul_left_eq_zero.mp h)

/-! ### The involution

`ι` is an involution on the series (`subst_formalInverse_self`), and evaluating that identity at a
parameter needs evaluation of a substitution. Mathlib's `MvPowerSeries.eval₂_subst` is not
applicable at this generality: it carries `[DiscreteUniformity R] [DiscreteUniformity S]`, and a
general adic ring supplies no such instance. These two therefore go through
`PowerSeries.aeval_subst`, which is the same statement with an arbitrary uniform structure on the
coefficients.
-/

/-- **`ι(t)` admits evaluation** when `t` is drawn from an ideal carrying the ambient topology:
`formalInverseEval_mem` puts it in the same ideal. This is the adic route to the second hypothesis
of the two identities below, which do not themselves need an ideal. -/
theorem hasEval_formalInverseEval {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    PowerSeries.HasEval (W.formalInverseEval t) :=
  hI.isTopologicallyNilpotent_of_mem <| by
    simpa using W.formalInverseEval_mem (k := 1)
      (hI.isTopologicallyNilpotent_of_mem ht) (by simpa using ht)

/-- **The inverse series evaluates to the inverse of the parameter**: the algebra map
`PowerSeries.aeval` and the `eval₂` defining `formalInverseEval` agree on `formalInverse`. -/
private theorem aeval_formalInverse {t : O} (hE : PowerSeries.HasEval t) :
    PowerSeries.aeval hE W.formalInverse = W.formalInverseEval t := by
  -- the coercion lands on `eval₂ (algebraMap O O)`, which is `RingHom.id O` only up to
  -- definitional unfolding, so the ascription is what lets `rw` fire
  have hcoe : ∀ f : PowerSeries O, PowerSeries.aeval hE f = eval₂ (RingHom.id O) t f :=
    congrFun (PowerSeries.coe_aeval hE)
  rw [hcoe, ← W.formalInverseEval_def]

/-- **The `w`-expansion at an inverted parameter**: `w(ι(t)) = -(w(t) * d(t)⁻¹)`, the evaluation of
the series identity `subst_formalInverse_formalW`. -/
theorem formalWEval_formalInverseEval {t : O} (hE : PowerSeries.HasEval t)
    (hV : PowerSeries.HasEval (W.formalInverseEval t)) :
    W.formalWEval (W.formalInverseEval t) =
      -(W.formalWEval t * W.formalInverseDenomInvEval t) := by
  have hcoe : ∀ f : PowerSeries O, PowerSeries.aeval hE f = eval₂ (RingHom.id O) t f :=
    congrFun (PowerSeries.coe_aeval hE)
  have hV' : PowerSeries.HasEval (PowerSeries.aeval hE W.formalInverse) :=
    W.aeval_formalInverse hE ▸ hV
  have h := PowerSeries.aeval_subst W.hasSubst_formalInverse
    (PowerSeries.continuous_aeval hE) hV' W.formalW
  rw [W.subst_formalInverse_formalW, map_neg, map_mul,
    congrFun (PowerSeries.coe_aeval hV') W.formalW, W.aeval_formalInverse hE] at h
  simpa [hcoe, formalWEval, formalInverseEval, formalInverseDenomInvEval] using h.symm

/-- **The formal inverse fixes the `x`-coordinate.** `ι(t) = -(t · d(t)⁻¹)` and
`w(ι t) = -(w(t) · d(t)⁻¹)` share the unit `d(t)⁻¹ = formalInverseDenomInvEval t`, so the sign and
that unit cancel in the ratio. No nonvanishing is needed: if `w(t) = 0` then `w(ι t) = 0` too and
both sides are zero. -/
theorem algebraMap_formalInverseEval_div_algebraMap_formalWEval_formalInverseEval
    {K : Type*} [Field K] [Algebra O K] {t : O} (hE : PowerSeries.HasEval t)
    (hEV : PowerSeries.HasEval (W.formalInverseEval t)) :
    algebraMap O K (W.formalInverseEval t) /
        algebraMap O K (W.formalWEval (W.formalInverseEval t)) =
      algebraMap O K t / algebraMap O K (W.formalWEval t) := by
  have hiota := congrArg (algebraMap O K) (W.formalInverseEval_eq hE)
  have hwiota := congrArg (algebraMap O K) (W.formalWEval_formalInverseEval hE hEV)
  simp only [map_neg, map_mul] at hiota hwiota
  by_cases hWt : algebraMap O K (W.formalWEval t) = 0
  · simp [hwiota, hWt]
  have hU0 : algebraMap O K (W.formalInverseDenomInvEval t) ≠ 0 :=
    ((W.isUnit_formalInverseDenomInvEval hE).map (algebraMap O K)).ne_zero
  rw [hiota, hwiota]
  field_simp

/-- **The formal inverse's `y`-value in closed form**: `d(t)⁻¹` inverts `d(t) = 1 - a₁t - a₃w(t)`,
which is what turns `-1 / w(ι t)` into the displayed ratio. The identity holds with no nonvanishing
hypothesis, both sides being zero when `w(t) = 0`.

**When `w(t) ≠ 0` the right-hand side is the curve's `negY`** at the coordinates `t / w(t)` and
`-1 / w(t)`, so the formal inverse applies `y ↦ -y - a₁x - a₃` rather than plain negation. That
reading needs the hypothesis: at `w(t) = 0` both ratios are zero by field division, while
`negY 0 0 = -a₃`. -/
theorem neg_one_div_algebraMap_formalWEval_formalInverseEval {K : Type*} [Field K] [Algebra O K]
    {t : O} (hE : PowerSeries.HasEval t)
    (hEV : PowerSeries.HasEval (W.formalInverseEval t)) :
    -1 / algebraMap O K (W.formalWEval (W.formalInverseEval t)) =
      (1 - (W.baseChange K).a₁ * algebraMap O K t -
          (W.baseChange K).a₃ * algebraMap O K (W.formalWEval t)) /
        algebraMap O K (W.formalWEval t) := by
  have hwiota := congrArg (algebraMap O K) (W.formalWEval_formalInverseEval hE hEV)
  simp only [map_neg, map_mul] at hwiota
  by_cases hWt : algebraMap O K (W.formalWEval t) = 0
  · simp [hwiota, hWt]
  have hU0 : algebraMap O K (W.formalInverseDenomInvEval t) ≠ 0 :=
    ((W.isUnit_formalInverseDenomInvEval hE).map (algebraMap O K)).ne_zero
  have hDU := congrArg (algebraMap O K) (W.formalInverseDenomEval_mul_inv hE)
  have hD := congrArg (algebraMap O K) (W.formalInverseDenomEval_eq hE)
  simp only [map_mul, map_sub, map_one] at hDU hD
  -- `d(t)⁻¹` inverts the closed form of `d(t)`; cross-multiplying leaves exactly that
  have hUD : algebraMap O K (W.formalInverseDenomInvEval t) *
      (1 - algebraMap O K W.a₁ * algebraMap O K t -
        algebraMap O K W.a₃ * algebraMap O K (W.formalWEval t)) = 1 := by
    rw [← hD, mul_comm]; exact hDU
  simp only [baseChange, map_a₁, map_a₃]
  rw [hwiota, div_neg, neg_div, neg_neg, div_eq_div_iff (mul_ne_zero hWt hU0) hWt]
  linear_combination -algebraMap O K (W.formalWEval t) * hUD

/-- **The formal inverse is an involution at a parameter**: `ι(ι(t)) = t`. This is `-(-P) = P` for
the group law near the origin, evaluated at `t`. -/
theorem formalInverseEval_formalInverseEval {t : O} (hE : PowerSeries.HasEval t)
    (hV : PowerSeries.HasEval (W.formalInverseEval t)) :
    W.formalInverseEval (W.formalInverseEval t) = t := by
  have hcoe : ∀ f : PowerSeries O, PowerSeries.aeval hE f = eval₂ (RingHom.id O) t f :=
    congrFun (PowerSeries.coe_aeval hE)
  have hV' : PowerSeries.HasEval (PowerSeries.aeval hE W.formalInverse) :=
    W.aeval_formalInverse hE ▸ hV
  have h := PowerSeries.aeval_subst W.hasSubst_formalInverse
    (PowerSeries.continuous_aeval hE) hV' W.formalInverse
  rw [W.subst_formalInverse_self,
    congrFun (PowerSeries.coe_aeval hV') W.formalInverse, W.aeval_formalInverse hE] at h
  simpa [hcoe, formalInverseEval, PowerSeries.eval₂_X] using h.symm

end WeierstrassCurve
