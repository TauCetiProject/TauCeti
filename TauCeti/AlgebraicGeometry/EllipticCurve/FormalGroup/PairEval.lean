/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Eval
public import TauCeti.RingTheory.MvPowerSeries.Substitution
-- Proof-only: supplies `MvPowerSeries.aeval_rename`, the transport of an evaluation along a
-- renaming, named in no statement here.
import TauCeti.RingTheory.MvPowerSeries.Rename
-- Proof-only: supplies the shared `constantCoeff_subst_pair_formalAdd`. Not redundant with the
-- `Add.Inverse` and `Add.Assoc` imports below: both import `Add.PairSubst` non-`public`, so
-- nothing it declares is re-exported through them.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
-- Proof-only: supplies the series-level inverse law `F(z, ι(z)) = 0`, named in no statement here.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Inverse
-- Proof-only: supplies the series-level associativity `F(F(z₁,z₂),z₃) = F(z₁,F(z₂,z₃))`.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc

/-!
# Evaluating the chord construction at a pair of parameters

The chord construction of `FormalGroup/Chord.lean` and the addition series of
`FormalGroup/Add/Series.lean` are two-variable power series. This file evaluates them at a pair
of parameters, as `FormalGroup/Eval.lean` evaluates the one-variable series at a single one, and
carries the identities of series over to identities of values.

The pair is the family `Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂` on `Unit ⊕ Unit`, and it admits
evaluation as soon as each parameter does — the decay condition is vacuous over finitely many
variables, so `MvPowerSeries.hasEval_of_finite_of_isTopologicallyNilpotent` applies.

## Main definitions

* `WeierstrassCurve.formalSlopeEval` : the slope `λ(t₁, t₂)` of the chord.
* `WeierstrassCurve.formalInterceptEval` : the intercept `ν(t₁, t₂)`.
* `WeierstrassCurve.formalThirdRootEval` : the parameter `t₃(t₁, t₂)` of the third point.
* `WeierstrassCurve.formalAddEval` : the value `F(t₁, t₂)` of the addition series.

## Main results

* `WeierstrassCurve.formalSlopeEval_mul_sub` : `λ(t₁, t₂) * (t₂ - t₁) = w(t₂) - w(t₁)`.
* `WeierstrassCurve.formalInterceptEval_eq` : `ν(t₁, t₂) = w(t₁) - λ(t₁, t₂) * t₁`, and
  `WeierstrassCurve.formalInterceptEval_eq_inr` : `ν(t₁, t₂) = w(t₂) - λ(t₁, t₂) * t₂`, the same
  intercept read from either parameter.
* `WeierstrassCurve.formalWEval_formalThirdRootEval` :
  `w(t₃(t₁, t₂)) = λ(t₁, t₂) * t₃(t₁, t₂) + ν(t₁, t₂)`, the `w`-expansion at the third root
  agreeing with the chord line there.
* `WeierstrassCurve.formalSlopeEval_mem`, `WeierstrassCurve.formalThirdRootEval_mem` : parameters
  in `I ^ k` keep the slope and the third root there.
* `WeierstrassCurve.formalThirdRootEval_relation` : Vieta's formula at a pair, cleared of the
  inverse of the cubic's leading coefficient.
* `WeierstrassCurve.formalThirdRootEval_ne_zero` : the third root is nonzero once
  `t₁ * w(t₂) ≠ t₂ * w(t₁)` — an inequality that forces both parameters nonzero, and over a
  field also makes their `x`-coordinates distinct.
* `WeierstrassCurve.hasEval_formalThirdRootEval` : the third root admits evaluation as soon as
  the two parameters do, the ideal-free counterpart of `formalThirdRootEval_mem`.
* `WeierstrassCurve.formalAddEval_eq` : `F(t₁, t₂) = ι(t₃(t₁, t₂))`.
* `WeierstrassCurve.formalAddEval_formalInverseEval` : `F(t, ι(t)) = 0`, the inverse law.
* `WeierstrassCurve.formalAddEval_zero_right` and
  `WeierstrassCurve.formalAddEval_zero_left` : the unit laws `F(t, 0) = t` and `F(0, t) = t`.
* `WeierstrassCurve.formalAddEval_comm` : commutativity `F(t₁, t₂) = F(t₂, t₁)`.
* `WeierstrassCurve.formalAddEval_assoc` : `F(F(t₁, t₂), t₃) = F(t₁, F(t₂, t₃))`, the group
  law's associativity read at parameters.
* `WeierstrassCurve.hasEval_formalAddEval` : `F(t₁, t₂)` admits evaluation as soon as `t₁` and
  `t₂` do — the ideal-free closure law.
* `WeierstrassCurve.formalAddEval_sub_add_mem` : `F(t₁, t₂) - (t₁ + t₂) ∈ I ^ (2 * k)` for
  parameters in `I ^ k`, so the group law is `t₁ + t₂` to first order, and
  `WeierstrassCurve.formalAddEval_mem` : each level `I ^ k` is therefore closed under the
  addition series.

## Implementation notes

Two of the series are built from one-variable ones through `PowerSeries.toMvPowerSeries` and
`MvPowerSeries.subst`; evaluating those is `PowerSeries.eval₂_id_toMvPowerSeries` and
`MvPowerSeries.aeval_subst`, neither of which requires the coefficient ring to be discrete —
which matters here, because the ambient adic ring need not be.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`, whose full expansion is
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`),
`EllipticCurves/WeierstrassFormalGroup/Eval.lean` — its pair-evaluation layer, declarations
`slopeEval`, `interceptEval`, `thirdRootEval`, `addEval`, `hasEval_pairElim`, `eval_pair_rename`,
`eval_pair_subst_single`, `slopeEval_mul_sub`, `interceptEval_eq`, `slopeEval_mem`,
`thirdRootEval_mem`, `thirdRootEval_relation`, `addEval_eq`, `addEval_sub_add_mem`,
`addEval_iotaEval`, `wEval_thirdRootEval` (here `formalWEval_formalThirdRootEval`),
`interceptEval_eq'` (here `formalInterceptEval_eq_inr`) and `thirdRootEval_ne_zero` (here
`formalThirdRootEval_ne_zero`, whose source carries an `[IsDomain O]` the argument does not use).

`hasEval_formalThirdRootEval` and `hasEval_formalAddEval` have no counterpart in the source, which
reads evaluability off membership in `IsLocalRing.maximalIdeal O`; they are this repository's
ideal-free replacements for that step.

The unit laws `formalAddEval_zero_right` and `formalAddEval_zero_left`, and the associativity
`formalAddEval_assoc`, follow the same project's
`EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Points.lean`, where they are the `zero_add`,
`add_zero` and `add_assoc` fields of the `AddCommMonoid` instance on `FormalGroupLaw.Points`
(`def Points _Φ := ι → maximalIdeal O`). Associativity's series-level input is that project's
`assoc_addSeries`, which is `FormalGroup/Add/Assoc.lean`'s `formalAdd_assoc` here. That generic
formal-group scaffolding is not ported here: Mathlib's `RingTheory/FormalGroup` supersedes it, and
its `FormalGroup.Point` is a different object — series carrying `PowerSeries.HasSubst`, not
elements of an ideal — so the laws are stated as standalone lemmas about `formalAddEval`,
ideal-free and taking `PowerSeries.HasEval`.

Four things are spelled differently here.

* The source's `eval_pair_rename` transports along `MvPowerSeries.rename`; this repository builds
  the one-variable series into two variables with `PowerSeries.toMvPowerSeries` instead, so the
  transport is `PowerSeries.eval₂_id_toMvPowerSeries`.
* The source states everything over `IsLocalRing.maximalIdeal O` at `k = 1`; the membership
  results here are over an arbitrary adic ideal and an arbitrary power of it, and the identities
  that use no ideal at all take `PowerSeries.HasEval` on each parameter, matching
  `FormalGroup/Eval.lean`.
* The source evaluates through its own `ChabautyColeman.MvPSeries.eval`, a wrapper for
  `MvPowerSeries.eval₂ (RingHom.id _)`, which is not ported.
* The source writes the evaluated inverse series as `iotaEval`; here it is
  `FormalGroup/Eval.lean`'s `formalInverseEval`, so its `addEval_iotaEval` is
  `formalAddEval_formalInverseEval`.
-/

public section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)

omit [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O] in
/-- Both entries of the pair lie in `I ^ k` as soon as the two parameters do. -/
private theorem pair_mem {I : Ideal O} {k : ℕ} {t₁ t₂ : O} (hk₁ : t₁ ∈ I ^ k) (hk₂ : t₂ ∈ I ^ k) :
    ∀ i, (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂ : Unit ⊕ Unit → O) i ∈ I ^ k := by
  rintro (_ | _) <;> [exact hk₁; exact hk₂]

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- The identity ring homomorphism is continuous. -/
private theorem continuous_ringHomId : Continuous (RingHom.id O) := by simpa using continuous_id

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- A pair of parameters admits evaluation as soon as each of them does. -/
private theorem hasEval_pair {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    MvPowerSeries.HasEval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂ : Unit ⊕ Unit → O) :=
  MvPowerSeries.hasEval_of_finite_of_isTopologicallyNilpotent <| by rintro (_ | _) <;> assumption

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- A parameter drawn from a positive power of an adic ideal admits evaluation: it lies in `I`,
and every element of `I` is topologically nilpotent for the `I`-adic topology. -/
private theorem hasEval_of_mem_pow {I : Ideal O} (hI : IsAdic I) {k : ℕ} (hk : k ≠ 0) {t : O}
    (ht : t ∈ I ^ k) : PowerSeries.HasEval t :=
  hI.isTopologicallyNilpotent_of_mem (Ideal.pow_le_self hk ht)

/-- Evaluation at a pair of parameters, as a ring homomorphism. The transport lemmas below take
identities of series to identities of values along this map. -/
private noncomputable def evalPair {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) : MvPowerSeries (Unit ⊕ Unit) O →+* O :=
  MvPowerSeries.eval₂Hom (φ := RingHom.id O) continuous_ringHomId (hasEval_pair h₁ h₂)

/-- `evalPair` is `MvPowerSeries.eval₂` at the identity ring hom, as a function. -/
private theorem coe_evalPair {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    ⇑(evalPair h₁ h₂) = MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) :=
  MvPowerSeries.coe_eval₂Hom (φ := RingHom.id O) _ (hasEval_pair h₁ h₂)

/-- The value of the slope series at a pair of parameters. -/
noncomputable def formalSlopeEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.formalSlope

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalSlopeEval` is evaluation of `formalSlope` at the pair, through the identity ring hom. -/
theorem formalSlopeEval_def (t₁ t₂ : O) :
    W.formalSlopeEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalSlope := (rfl)

/-- The value of the intercept series at a pair of parameters. -/
noncomputable def formalInterceptEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.formalIntercept

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInterceptEval` is evaluation of `formalIntercept` at the pair, through the identity
ring hom. -/
theorem formalInterceptEval_def (t₁ t₂ : O) :
    W.formalInterceptEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalIntercept := (rfl)

/-- The value of the third-root series at a pair of parameters. -/
noncomputable def formalThirdRootEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.formalThirdRoot

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalThirdRootEval` is evaluation of `formalThirdRoot` at the pair, through the identity
ring hom. -/
theorem formalThirdRootEval_def (t₁ t₂ : O) :
    W.formalThirdRootEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalThirdRoot := (rfl)

/-- The value of the addition series at a pair of parameters. -/
noncomputable def formalAddEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.formalAdd

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalAddEval` is evaluation of `formalAdd` at the pair, through the identity ring hom. -/
theorem formalAddEval_def (t₁ t₂ : O) :
    W.formalAddEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalAdd := (rfl)

open MvPowerSeries.WithPiTopology in
/-- **The group law is closed on evaluable parameters**: `F(t₁, t₂)` admits evaluation as soon as
`t₁` and `t₂` do. This is the ideal-free counterpart of `formalAddEval_mem`, and it is what lets
the associativity statement take only its three parameters. -/
theorem hasEval_formalAddEval {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) : PowerSeries.HasEval (W.formalAddEval t₁ t₂) := by
  -- `formalAdd` is topologically nilpotent because its constant coefficient vanishes; evaluation
  -- is a continuous ring hom, so it carries that property to the value.
  have hnil := isTopologicallyNilpotent_of_constantCoeff_zero (constantCoeff_formalAdd W)
  have h := IsTopologicallyNilpotent.map (φ := MvPowerSeries.aeval (hasEval_pair h₁ h₂))
    (MvPowerSeries.continuous_aeval (hasEval_pair h₁ h₂)) hnil
  simpa [formalAddEval, MvPowerSeries.coe_aeval, Algebra.algebraMap_self] using h

/-- **The evaluated slope identity**: `λ(t₁, t₂) * (t₂ - t₁) = w(t₂) - w(t₁)`. -/
theorem formalSlopeEval_mul_sub {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalSlopeEval t₁ t₂ * (t₂ - t₁) = W.formalWEval t₂ - W.formalWEval t₁ := by
  have h := congrArg (evalPair h₁ h₂) W.formalSlope_mul_sub
  rw [map_mul, map_sub, map_sub] at h
  simpa [formalSlopeEval, W.formalWEval_def, coe_evalPair, Sum.elim_inl, Sum.elim_inr,
    PowerSeries.eval₂_id_toMvPowerSeries (hasEval_pair h₁ h₂),
    MvPowerSeries.eval₂_X] using h

/-- **The evaluated intercept identity**: `ν(t₁, t₂) = w(t₁) - λ(t₁, t₂) * t₁`. -/
theorem formalInterceptEval_eq {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalInterceptEval t₁ t₂ = W.formalWEval t₁ - W.formalSlopeEval t₁ t₂ * t₁ := by
  have h := congrArg (evalPair h₁ h₂) W.formalIntercept_def
  rw [map_sub, map_mul] at h
  simpa [formalInterceptEval, formalSlopeEval, W.formalWEval_def, coe_evalPair, Sum.elim_inl,
    Sum.elim_inr, PowerSeries.eval₂_id_toMvPowerSeries (hasEval_pair h₁ h₂),
    MvPowerSeries.eval₂_X] using h

/-- **The evaluated intercept identity, read from the second point**:
`ν(t₁, t₂) = w(t₂) - λ(t₁, t₂) * t₂`. Together with `formalInterceptEval_eq` this says the chord
meets the curve at both parameters, which is what makes the intercept symmetric in them. -/
theorem formalInterceptEval_eq_inr {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalInterceptEval t₁ t₂ = W.formalWEval t₂ - W.formalSlopeEval t₁ t₂ * t₂ := by
  have h := congrArg (evalPair h₁ h₂) W.formalIntercept_eq_inr
  rw [map_sub, map_mul] at h
  simpa [formalInterceptEval, formalSlopeEval, W.formalWEval_def, coe_evalPair, Sum.elim_inl,
    Sum.elim_inr, PowerSeries.eval₂_id_toMvPowerSeries (hasEval_pair h₁ h₂),
    MvPowerSeries.eval₂_X] using h

/-- The slope of the chord at parameters of `I ^ k` again lies in `I ^ k`: the slope series has
vanishing constant coefficient. -/
theorem formalSlopeEval_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (hk₁ : t₁ ∈ I ^ k) (hk₂ : t₂ ∈ I ^ k) : W.formalSlopeEval t₁ t₂ ∈ I ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) continuous_ringHomId
      (hasEval_pair (hasEval_of_mem_pow hI hk hk₁) (hasEval_of_mem_pow hI hk hk₂)) hI
      (pair_mem hk₁ hk₂) W.formalSlope (by simp)

/-- The third point's parameter at parameters of `I ^ k` again lies in `I ^ k`. -/
theorem formalThirdRootEval_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (hk₁ : t₁ ∈ I ^ k) (hk₂ : t₂ ∈ I ^ k) : W.formalThirdRootEval t₁ t₂ ∈ I ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) continuous_ringHomId
      (hasEval_pair (hasEval_of_mem_pow hI hk hk₁) (hasEval_of_mem_pow hI hk hk₂)) hI
      (pair_mem hk₁ hk₂) W.formalThirdRoot (by simp)

/-- **Vieta's formula at a pair of parameters**, cleared of the inverse of the cubic's leading
coefficient: the third root satisfies
`(1 + a₂λ + a₄λ² + a₆λ³)(t₃ + t₁ + t₂) = -(a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν)`. -/
theorem formalThirdRootEval_relation {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    (1 + W.a₂ * W.formalSlopeEval t₁ t₂ + W.a₄ * W.formalSlopeEval t₁ t₂ ^ 2 +
        W.a₆ * W.formalSlopeEval t₁ t₂ ^ 3) *
      (W.formalThirdRootEval t₁ t₂ + t₁ + t₂) =
      -(W.a₁ * W.formalSlopeEval t₁ t₂ + W.a₂ * W.formalInterceptEval t₁ t₂ +
        W.a₃ * W.formalSlopeEval t₁ t₂ ^ 2 +
        2 * W.a₄ * W.formalSlopeEval t₁ t₂ * W.formalInterceptEval t₁ t₂ +
        3 * W.a₆ * W.formalSlopeEval t₁ t₂ ^ 2 * W.formalInterceptEval t₁ t₂) := by
  have hT := congrArg (evalPair h₁ h₂) W.formalThirdRoot_def
  have hD := congrArg (evalPair h₁ h₂) (MvPowerSeries.mul_invOfUnit
    (1 + MvPowerSeries.C W.a₂ * W.formalSlope + MvPowerSeries.C W.a₄ * W.formalSlope ^ 2 +
      MvPowerSeries.C W.a₆ * W.formalSlope ^ 3) 1 (by simp))
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat, coe_evalPair,
    MvPowerSeries.eval₂_X, MvPowerSeries.eval₂_C, RingHom.id_apply, Sum.elim_inl,
    Sum.elim_inr] at hT hD
  simp only [← W.formalSlopeEval_def, ← W.formalInterceptEval_def,
    ← W.formalThirdRootEval_def] at hT hD
  set L := W.formalSlopeEval t₁ t₂
  set N := W.formalInterceptEval t₁ t₂
  set T := W.formalThirdRootEval t₁ t₂
  set d := MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
    (MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.formalSlope +
      MvPowerSeries.C W.a₄ * W.formalSlope ^ 2 + MvPowerSeries.C W.a₆ * W.formalSlope ^ 3) 1)
  clear_value L N T d
  linear_combination (1 + W.a₂ * L + W.a₄ * L ^ 2 + W.a₆ * L ^ 3) * hT -
    (W.a₁ * L + W.a₂ * N + W.a₃ * L ^ 2 + 2 * W.a₄ * L * N + 3 * W.a₆ * L ^ 2 * N) * hD

open MvPowerSeries.WithPiTopology in
/-- **The third root admits evaluation as soon as the two parameters do.** Like
`hasEval_formalAddEval`, this is the ideal-free counterpart of `formalThirdRootEval_mem`, and it
is what lets the identities below take only their two parameters. -/
theorem hasEval_formalThirdRootEval {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) : PowerSeries.HasEval (W.formalThirdRootEval t₁ t₂) := by
  -- `formalThirdRoot` is topologically nilpotent because its constant coefficient vanishes, and
  -- evaluation is a continuous ring hom, so it carries that property to the value.
  have hnil := isTopologicallyNilpotent_of_constantCoeff_zero (constantCoeff_formalThirdRoot W)
  have h := IsTopologicallyNilpotent.map (φ := MvPowerSeries.aeval (hasEval_pair h₁ h₂))
    (MvPowerSeries.continuous_aeval (hasEval_pair h₁ h₂)) hnil
  simpa [formalThirdRootEval, MvPowerSeries.coe_aeval, Algebra.algebraMap_self] using h

/-- **The evaluated on-line identity**: `w(t₃(t₁, t₂)) = λ(t₁, t₂) * t₃(t₁, t₂) + ν(t₁, t₂)`, so
the `w`-expansion read at the third root agrees with the chord line read there. Over a field, where
the parameters carry the coordinates `x = t / w` and `y = -1 / w`, this is what says the third root
parametrises a point *on* the chord and not merely a root of the chord cubic. -/
theorem formalWEval_formalThirdRootEval {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalWEval (W.formalThirdRootEval t₁ t₂) =
      W.formalSlopeEval t₁ t₂ * W.formalThirdRootEval t₁ t₂ + W.formalInterceptEval t₁ t₂ := by
  have hae : MvPowerSeries.aeval (hasEval_pair h₁ h₂) W.formalThirdRoot =
      W.formalThirdRootEval t₁ t₂ :=
    congrFun (MvPowerSeries.coe_aeval (hasEval_pair h₁ h₂)) W.formalThirdRoot
  have hT' : PowerSeries.HasEval (MvPowerSeries.aeval (hasEval_pair h₁ h₂) W.formalThirdRoot) := by
    rw [hae]; exact W.hasEval_formalThirdRootEval h₁ h₂
  have h := MvPowerSeries.aeval_subst W.hasSubst_formalThirdRoot
    (MvPowerSeries.continuous_aeval (hasEval_pair h₁ h₂))
    (PowerSeries.hasEval hT') W.formalW
  -- distribute while the evaluation is still an algebra map: after `coe_aeval` rewrites it to
  -- `eval₂`, `map_add` and `map_mul` no longer apply.
  rw [W.subst_formalThirdRoot_formalW, map_add, map_mul] at h
  simpa [W.formalWEval_def, formalSlopeEval, formalInterceptEval, ← W.formalThirdRootEval_def,
    MvPowerSeries.coe_aeval, PowerSeries.eval₂] using h.symm

/-- **The third root does not vanish once `t₁ * w(t₂) ≠ t₂ * w(t₁)`.** The inequality forces both
parameters to be nonzero, `w` vanishing at `0`; and over a field a nonzero parameter `t` carries
the affine coordinates `x = t / w(t)`, `y = -1 / w(t)`, so it then also says the two
`x`-coordinates differ. The conclusion is that the chord through the two points is not the
vertical line. -/
theorem formalThirdRootEval_ne_zero {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂)
    (hx : t₁ * W.formalWEval t₂ ≠ t₂ * W.formalWEval t₁) :
    W.formalThirdRootEval t₁ t₂ ≠ 0 := by
  intro h
  have hT := W.hasEval_formalThirdRootEval h₁ h₂
  have honl := W.formalWEval_formalThirdRootEval h₁ h₂
  rw [h, mul_zero, zero_add, W.formalWEval_eq_pow_mul_formalUEval (h ▸ hT)] at honl
  -- `w` vanishes at the zero parameter, so the on-line identity collapses to `ν = 0`
  rw [zero_pow (by norm_num), zero_mul] at honl
  refine hx ?_
  -- the two intercept identities, read from either parameter, give `ν · (t₂ - t₁)` symmetrically
  have hnu : W.formalInterceptEval t₁ t₂ * (t₂ - t₁) =
      t₂ * W.formalWEval t₁ - t₁ * W.formalWEval t₂ := by
    linear_combination t₂ * W.formalInterceptEval_eq h₁ h₂ -
      t₁ * W.formalInterceptEval_eq_inr h₁ h₂
  rw [← honl, zero_mul] at hnu
  linear_combination hnu

/-- **The addition series at a pair of parameters is the formal inverse of the third root**:
`F(t₁, t₂) = ι(t₃(t₁, t₂))`, the sum of two points being the negative of the third point of the
chord through them. -/
theorem formalAddEval_eq {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalAddEval t₁ t₂ = W.formalInverseEval (W.formalThirdRootEval t₁ t₂) := by
  have hae : MvPowerSeries.aeval (hasEval_pair h₁ h₂) W.formalThirdRoot =
      W.formalThirdRootEval t₁ t₂ :=
    congrFun (MvPowerSeries.coe_aeval (hasEval_pair h₁ h₂)) W.formalThirdRoot
  have hT' : PowerSeries.HasEval (MvPowerSeries.aeval (hasEval_pair h₁ h₂) W.formalThirdRoot) := by
    rw [hae]; exact W.hasEval_formalThirdRootEval h₁ h₂
  have h := MvPowerSeries.aeval_subst W.hasSubst_formalThirdRoot
    (MvPowerSeries.continuous_aeval (hasEval_pair h₁ h₂))
    (PowerSeries.hasEval hT') W.formalInverse
  rw [← W.formalAdd_def] at h
  simpa [formalAddEval, W.formalInverseEval_def, MvPowerSeries.coe_aeval, PowerSeries.eval₂,
    ← W.formalThirdRootEval_def] using h

/-- **The inverse law at parameters**: `F(t, ι(t)) = 0`, so the value of the inverse series at `t`
is the additive inverse of `t` under the group law read at parameters. -/
@[simp]
theorem formalAddEval_formalInverseEval {t : O} (ht : PowerSeries.HasEval t)
    (hι : PowerSeries.HasEval (W.formalInverseEval t)) :
    W.formalAddEval t (W.formalInverseEval t) = 0 := by
  have hid : (algebraMap O O) = RingHom.id O := rfl
  -- Evaluating the substituted pair at `t` is evaluating at the pair `(t, ι(t))`.
  have hfam : (fun s : Unit ⊕ Unit ↦ MvPowerSeries.eval₂ (RingHom.id O) (fun _ : Unit ↦ t)
        (Sum.elim MvPowerSeries.X (fun _ ↦ formalInverse W) s)) =
      Sum.elim (fun _ ↦ t) fun _ ↦ W.formalInverseEval t := by
    funext s
    rcases s with _ | _ <;> simp [W.formalInverseEval_def, PowerSeries.eval₂]
  have hpair : MvPowerSeries.HasEval
      (fun s : Unit ⊕ Unit ↦ MvPowerSeries.aeval (PowerSeries.hasEval ht)
        (Sum.elim MvPowerSeries.X (fun _ ↦ formalInverse W) s)) := by
    simp only [MvPowerSeries.coe_aeval, hid, hfam]
    exact hasEval_pair ht hι
  have h := MvPowerSeries.aeval_subst W.hasSubst_invPair
    (MvPowerSeries.continuous_aeval (PowerSeries.hasEval ht)) hpair W.formalAdd
  rw [W.subst_invPair_formalAdd] at h
  simpa [formalAddEval, MvPowerSeries.coe_aeval, hid, hfam, map_zero] using h.symm

/-- **The group law is `t₁ + t₂` to first order**: at parameters of `I ^ k` the addition series
deviates from their sum by an element of `I ^ (2 * k)`, because it agrees with `z₁ + z₂` below
total degree two. -/
theorem formalAddEval_sub_add_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (hk₁ : t₁ ∈ I ^ k) (hk₂ : t₂ ∈ I ^ k) :
    W.formalAddEval t₁ t₂ - (t₁ + t₂) ∈ I ^ (2 * k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have h₁ : PowerSeries.HasEval t₁ := hasEval_of_mem_pow hI hk hk₁
  have h₂ : PowerSeries.HasEval t₂ := hasEval_of_mem_pow hI hk hk₂
  have heval : MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
      (W.formalAdd - MvPowerSeries.X (Sum.inl ()) - MvPowerSeries.X (Sum.inr ())) =
      W.formalAddEval t₁ t₂ - (t₁ + t₂) := by
    rw [← coe_evalPair h₁ h₂, map_sub, map_sub]
    simp [coe_evalPair, formalAddEval, MvPowerSeries.eval₂_X, Sum.elim_inl, Sum.elim_inr, sub_sub]
  rw [← heval]
  exact MvPowerSeries.eval₂_mem_pow_mul (φ := RingHom.id O) continuous_ringHomId
    (hasEval_pair h₁ h₂) hI (pair_mem hk₁ hk₂) _
    (fun d hd ↦ W.coeff_formalAdd_sub_eq_zero_of_degree_lt hd)

/-- **The levels of the filtration are closed under the group law**: the addition series carries
a pair of parameters of `I ^ k` back into `I ^ k`, because it deviates from their sum by an
element of `I ^ (2 * k)`. -/
theorem formalAddEval_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (hk₁ : t₁ ∈ I ^ k) (hk₂ : t₂ ∈ I ^ k) : W.formalAddEval t₁ t₂ ∈ I ^ k := by
  have hle : I ^ (2 * k) ≤ I ^ k := Ideal.pow_le_pow_right (by omega)
  have := Ideal.add_mem _ (hle (W.formalAddEval_sub_add_mem hI hk₁ hk₂))
    (Ideal.add_mem _ hk₁ hk₂)
  simpa using this

/-- **Commutativity of the group law at parameters**: `F(t₁, t₂) = F(t₂, t₁)`. -/
theorem formalAddEval_comm {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) : W.formalAddEval t₁ t₂ = W.formalAddEval t₂ t₁ := by
  have h := congrArg (MvPowerSeries.aeval (hasEval_pair h₁ h₂)) (rename_swap_formalAdd W)
  rw [MvPowerSeries.aeval_rename Sum.swap (hasEval_pair h₁ h₂) (hasEval_pair h₂ h₁)
    (by rintro (_ | _) <;> rfl)] at h
  simpa [formalAddEval, MvPowerSeries.coe_aeval, Algebra.algebraMap_self] using h.symm

/-- **Associativity of the group law at parameters**: `F(F(t₁, t₂), t₃) = F(t₁, F(t₂, t₃))`. -/
theorem formalAddEval_assoc {t₁ t₂ t₃ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) (h₃ : PowerSeries.HasEval t₃) :
    W.formalAddEval (W.formalAddEval t₁ t₂) t₃ =
      W.formalAddEval t₁ (W.formalAddEval t₂ t₃) := by
  have h₁₂ := W.hasEval_formalAddEval h₁ h₂
  have h₂₃ := W.hasEval_formalAddEval h₂ h₃
  have ht : MvPowerSeries.HasEval (Sum.elim (fun _ ↦ t₁) (Sum.elim (fun _ ↦ t₂) fun _ ↦ t₃) :
      Unit ⊕ Unit ⊕ Unit → O) :=
    MvPowerSeries.hasEval_of_finite_of_isTopologicallyNilpotent <| by
      rintro (_ | _ | _) <;> assumption
  set T := (Sum.elim (fun _ ↦ t₁) (Sum.elim (fun _ ↦ t₂) fun _ ↦ t₃) :
    Unit ⊕ Unit ⊕ Unit → O) with hT
  -- one step of the transport, generic in the two substituends
  have hstep {q₁ q₂ : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O} {u v : O}
      (hq₁ : MvPowerSeries.constantCoeff q₁ = 0)
      (hq₂ : MvPowerSeries.constantCoeff q₂ = 0)
      (hu : MvPowerSeries.eval₂ (RingHom.id O) T q₁ = u)
      (hv : MvPowerSeries.eval₂ (RingHom.id O) T q₂ = v)
      (hu' : PowerSeries.HasEval u) (hv' : PowerSeries.HasEval v) :
      MvPowerSeries.eval₂ (RingHom.id O) T (MvPowerSeries.subst
        (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O) W.formalAdd) =
        W.formalAddEval u v := by
    have hfam : (fun s : Unit ⊕ Unit ↦ MvPowerSeries.eval₂ (RingHom.id O) T
          ((Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
            Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O) s)) =
        Sum.elim (fun _ ↦ u) fun _ ↦ v := by
      funext s
      rcases s with _ | _ <;> simp [hu, hv]
    have hev : MvPowerSeries.HasEval fun s : Unit ⊕ Unit ↦ MvPowerSeries.aeval ht
        ((Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O) s) := by
      simp only [MvPowerSeries.coe_aeval, Algebra.algebraMap_self, hfam]
      exact hasEval_pair hu' hv'
    have h := MvPowerSeries.aeval_subst (MvPowerSeries.hasSubst_pair hq₁ hq₂)
      (MvPowerSeries.continuous_aeval ht) hev W.formalAdd
    simpa [formalAddEval, MvPowerSeries.coe_aeval, Algebra.algebraMap_self, hfam] using h
  have hX (s : Unit ⊕ Unit ⊕ Unit) :
      MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hL := hstep (q₁ := MvPowerSeries.subst (Sum.elim
      (fun _ ↦ (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O))
      (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inl ()))) :
        Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O) W.formalAdd)
    (q₂ := MvPowerSeries.X (Sum.inr (Sum.inr ())))
    (constantCoeff_subst_pair_formalAdd W (hX _) (hX _)) (hX _)
    (hstep (hX _) (hX _) (by simp [hT]) (by simp [hT]) h₁ h₂) (by simp [hT]) h₁₂ h₃
  have hR := hstep (q₁ := MvPowerSeries.X (Sum.inl ()))
    (q₂ := MvPowerSeries.subst (Sum.elim
      (fun _ ↦ (MvPowerSeries.X (Sum.inr (Sum.inl ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O))
      (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inr ()))) :
        Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O) W.formalAdd)
    (hX _) (constantCoeff_subst_pair_formalAdd W (hX _) (hX _))
    (by simp [hT]) (hstep (hX _) (hX _) (by simp [hT]) (by simp [hT]) h₂ h₃) h₁ h₂₃
  rw [← hL, ← hR]
  exact congrArg _ (formalAdd_assoc W)

/-- **The right unit law at parameters**: `F(t, 0) = t`, so the origin's parameter is neutral for
the group law read at parameters. -/
@[simp]
theorem formalAddEval_zero_right {t : O} (ht : PowerSeries.HasEval t) :
    W.formalAddEval t 0 = t := by
  have hfam : (fun s : Unit ⊕ Unit ↦ MvPowerSeries.eval₂ (RingHom.id O) (fun _ : Unit ↦ t)
        ((Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
          Unit ⊕ Unit → MvPowerSeries Unit O) s)) =
      Sum.elim (fun _ ↦ t) fun _ ↦ (0 : O) := by
    funext s
    rcases s with _ | _
    · simp
    · simpa using
        MvPowerSeries.eval₂_C (φ := RingHom.id O) (a := fun _ : Unit ↦ t) (0 : O)
  have hev : MvPowerSeries.HasEval fun s : Unit ⊕ Unit ↦
      MvPowerSeries.aeval (PowerSeries.hasEval ht)
        ((Sum.elim MvPowerSeries.X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O) s) := by
    simp only [MvPowerSeries.coe_aeval, Algebra.algebraMap_self, hfam]
    exact hasEval_pair ht IsTopologicallyNilpotent.zero
  have h := MvPowerSeries.aeval_subst
    (MvPowerSeries.hasSubst_pair (q₁ := MvPowerSeries.X ()) (q₂ := 0) (by simp) (by simp))
    (MvPowerSeries.continuous_aeval (PowerSeries.hasEval ht)) hev W.formalAdd
  rw [W.subst_unitR_formalAdd] at h
  simpa [formalAddEval, MvPowerSeries.coe_aeval, Algebra.algebraMap_self, hfam,
    PowerSeries.X, MvPowerSeries.eval₂_X] using h.symm

/-- **The left unit law at parameters**: `F(0, t) = t`. -/
@[simp]
theorem formalAddEval_zero_left {t : O} (ht : PowerSeries.HasEval t) :
    W.formalAddEval 0 t = t := by
  have hfam : (fun s : Unit ⊕ Unit ↦ MvPowerSeries.eval₂ (RingHom.id O) (fun _ : Unit ↦ t)
        ((Sum.elim (fun _ ↦ 0) MvPowerSeries.X :
          Unit ⊕ Unit → MvPowerSeries Unit O) s)) =
      Sum.elim (fun _ ↦ (0 : O)) fun _ ↦ t := by
    funext s
    rcases s with _ | _
    · simpa using
        MvPowerSeries.eval₂_C (φ := RingHom.id O) (a := fun _ : Unit ↦ t) (0 : O)
    · simp
  have hev : MvPowerSeries.HasEval fun s : Unit ⊕ Unit ↦
      MvPowerSeries.aeval (PowerSeries.hasEval ht)
        ((Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O) s) := by
    simp only [MvPowerSeries.coe_aeval, Algebra.algebraMap_self, hfam]
    exact hasEval_pair IsTopologicallyNilpotent.zero ht
  have h := MvPowerSeries.aeval_subst
    (MvPowerSeries.hasSubst_pair (q₁ := 0) (q₂ := MvPowerSeries.X ()) (by simp) (by simp))
    (MvPowerSeries.continuous_aeval (PowerSeries.hasEval ht)) hev W.formalAdd
  rw [W.subst_unitL_formalAdd] at h
  simpa [formalAddEval, MvPowerSeries.coe_aeval, Algebra.algebraMap_self, hfam,
    PowerSeries.X, MvPowerSeries.eval₂_X] using h.symm

end WeierstrassCurve
