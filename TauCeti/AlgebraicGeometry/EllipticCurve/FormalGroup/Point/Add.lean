/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.PairEval
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Basic
-- Proof-only: `chord_point_add` is used inside a private helper's proof.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint

/-!
# The parametrisation carries the group law: the chord case

`FormalGroup/Point/Basic.lean` sends a parameter `t` of an adic ideal to a point of `W⁄K`, and
`FormalGroup/PairEval.lean` gives the group law `F(t₁, t₂)` on parameters. This file joins them in
the case where the chord through the two points is not vertical: the point of the parameter
`F(t₁, t₂)` is the sum of the points of `t₁` and `t₂`.

This is one case of the additivity of `formalPoint`, not the whole of it. The zero parameter, the
doubling case `t₁ = t₂`, and the inverse case, where the two points share an `x`-coordinate, each
need a different argument and are not treated here. Only with all of them does `formalPoint` become
a homomorphism, and only then are the parameters of an adic ideal a subgroup of the points of `W⁄K`
rather than an indexed family of them.

## The hypotheses

`t₁ * w(t₂) ≠ t₂ * w(t₁)` is the chord condition: over a field, where a nonzero parameter `t`
carries the coordinates `x = t / w(t)` and `y = -1 / w(t)`, it says the two points have distinct
`x`-coordinates, so the line through them is not vertical. It is what excludes the doubling and
inverse cases, which need a different argument and are not treated here.

Nothing further is asked of the parameters. `w` vanishes at `0`, so the chord condition already
excludes the zero parameter on either side; the sum is nonzero for the same reason, since
`formalAddEval_eq` writes it as the formal inverse of the third root,
`formalThirdRootEval_ne_zero` gives the third root's nonvanishing from the chord condition, and
`formalInverseEval_ne_zero` carries it across; and `formalAddEval_mem` supplies the membership
`formalPoint` needs of its argument, which is why the conclusion names that term rather than a
hypothesis.

## Main results

* `WeierstrassCurve.add_eq_formalPoint_formalAddEval_of_X_ne`: the point of `F(t₁, t₂)` is the
  sum of the points of `t₁` and `t₂`, for parameters whose points have distinct `x`-coordinates.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves` @ `66889eada51a`, Apache-2.0),
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declaration `paramPoint_add`.

The argument here is a transposition of this repository's own `FormalGroup/Add/Assoc.lean`, whose
private `thetaPoint_add` runs the same chord computation one level up — over a fraction field of
the power-series ring rather than at a parameter — for the associativity of `formalAdd`. The
scalar inputs come from the `Eval` and `PairEval` layers instead of that file's substitution
layer, and `formalPoint` replaces its `thetaPoint`.
-/

open Polynomial

public section

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)
variable {K : Type*} [Field K] [Algebra O K]

/-! ### The points

`formalPoint` needs the base-changed curve to be elliptic and the structure map to be injective.
The group law on points needs decidable equality on `K`, which the two declarations that add points
supply locally by classical reasoning rather than asking it of callers. The first below adds
nothing, so it needs neither.

The argument runs in two steps: the chord construction identifies the sum with the third point of
the line, and the formal inverse identifies that point's negation with the point of `F(t₁, t₂)`. -/

variable [(W.baseChange K).IsElliptic] [FaithfulSMul O K]

omit [FaithfulSMul O K] [(W.baseChange K).IsElliptic] in
/-- **The chord's third point, negated, is the point at the sum's parameter.** The formal inverse
`F(t₁, t₂) = i(T(t₁, t₂))` is what turns the chord construction into the group law; this is that
step read off on coordinates. Both nonsingularity proofs are taken rather than built, so the
statement says exactly which witnesses the dependent equality is between. -/
private theorem some_formalThirdRootEval_eq_some_formalAddEval {I : Ideal O} (hI : IsAdic I)
    {t₁ t₂ : O} (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I)
    (h₃ : (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K (W.formalThirdRootEval t₁ t₂) /
        algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)))
      ((1 - (W.baseChange K).a₁ * algebraMap O K (W.formalThirdRootEval t₁ t₂) -
          (W.baseChange K).a₃ * algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂))) /
        algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂))))
    (hnF : (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K (W.formalAddEval t₁ t₂) /
        algebraMap O K (W.formalWEval (W.formalAddEval t₁ t₂)))
      (-1 / algebraMap O K (W.formalWEval (W.formalAddEval t₁ t₂)))) :
    Affine.Point.some _ _ h₃ = Affine.Point.some _ _ hnF := by
  have hE₁ : PowerSeries.HasEval t₁ := hI.isTopologicallyNilpotent_of_mem h₁
  have hE₂ : PowerSeries.HasEval t₂ := hI.isTopologicallyNilpotent_of_mem h₂
  have hET : PowerSeries.HasEval (W.formalThirdRootEval t₁ t₂) :=
    W.hasEval_formalThirdRootEval hE₁ hE₂
  have hTmem : W.formalThirdRootEval t₁ t₂ ∈ I := by
    simpa using W.formalThirdRootEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂)
  -- the three the coordinate comparison consumes, stated so that `grind` can match on them
  have hF : algebraMap O K (W.formalAddEval t₁ t₂) =
      -(algebraMap O K (W.formalThirdRootEval t₁ t₂) *
        algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂))) := by
    rw [W.formalAddEval_eq hE₁ hE₂, W.formalInverseEval_eq hET]
    simp [map_neg, map_mul]
  have hu : algebraMap O K (W.formalInverseDenomEval (W.formalThirdRootEval t₁ t₂)) *
      algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂)) = 1 := by
    rw [← map_mul, ← map_one (algebraMap O K)]
    exact congrArg (algebraMap O K) (W.formalInverseDenomEval_mul_inv hET)
  have hden : algebraMap O K (W.formalInverseDenomEval (W.formalThirdRootEval t₁ t₂)) =
      1 - (W.baseChange K).a₁ * algebraMap O K (W.formalThirdRootEval t₁ t₂) -
        (W.baseChange K).a₃ *
          algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)) := by
    simpa [baseChange, map_sub, map_mul, map_one, map_a₁, map_a₃] using
      congrArg (algebraMap O K) (W.formalInverseDenomEval_eq hET)
  have hwF : algebraMap O K (W.formalWEval (W.formalAddEval t₁ t₂)) =
      -(algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)) *
        algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂))) := by
    rw [W.formalAddEval_eq hE₁ hE₂,
      W.formalWEval_formalInverseEval hET (W.hasEval_formalInverseEval hI hTmem)]
    simp [map_neg, map_mul]
  -- the coordinates of the two points agree, so the points do
  grind

omit [(W.baseChange K).IsElliptic] in
open scoped Classical in
/-- The group law of `W⁄K` at the two parametrised points, each written as an `Affine.Point.some`
at the coordinates `x = t / w(t)` and `y = -1 / w(t)`. The three nonsingularity proofs are taken
rather than built, so the statement says exactly which witnesses the dependent equality is
between. -/
private theorem some_add_some_formalAddEval_of_X_ne {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (h₁0 : t₁ ≠ 0) (h₂0 : t₂ ≠ 0)
    (hx : t₁ * W.formalWEval t₂ ≠ t₂ * W.formalWEval t₁)
    (hn₁ : (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K t₁ / algebraMap O K (W.formalWEval t₁))
      (-1 / algebraMap O K (W.formalWEval t₁)))
    (hn₂ : (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K t₂ / algebraMap O K (W.formalWEval t₂))
      (-1 / algebraMap O K (W.formalWEval t₂)))
    (hnF : (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K (W.formalAddEval t₁ t₂) /
        algebraMap O K (W.formalWEval (W.formalAddEval t₁ t₂)))
      (-1 / algebraMap O K (W.formalWEval (W.formalAddEval t₁ t₂)))) :
    Affine.Point.some _ _ hn₁ + Affine.Point.some _ _ hn₂ = Affine.Point.some _ _ hnF := by
  have hE₁ : PowerSeries.HasEval t₁ := hI.isTopologicallyNilpotent_of_mem h₁
  have hE₂ : PowerSeries.HasEval t₂ := hI.isTopologicallyNilpotent_of_mem h₂
  have hET : PowerSeries.HasEval (W.formalThirdRootEval t₁ t₂) :=
    W.hasEval_formalThirdRootEval hE₁ hE₂
  have hne : ∀ {s : O}, s ≠ 0 → algebraMap O K s ≠ 0 := fun hs0 ↦ by simpa using hs0
  have hTmem : W.formalThirdRootEval t₁ t₂ ∈ I := by
    simpa using W.formalThirdRootEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂)
  have hwT0 := W.algebraMap_formalWEval_ne_zero (S := K) hI hTmem
    (hne (W.formalThirdRootEval_ne_zero hE₁ hE₂ hx))
  -- the chord data, read in `K`: each is the image under `algebraMap O K` of an identity of the
  -- `Eval` and `PairEval` layers, pushed through the ring hom into the shape `chord_point_add` and
  -- the coordinate comparison consume
  have hq₁ := congrArg (algebraMap O K) (W.formalWEval_wEquation hE₁)
  have hq₂ := congrArg (algebraMap O K) (W.formalWEval_wEquation hE₂)
  have hslope := congrArg (algebraMap O K) (W.formalSlopeEval_mul_sub hE₁ hE₂)
  have hint := congrArg (algebraMap O K) (W.formalInterceptEval_eq hE₁ hE₂)
  have hrel := congrArg (algebraMap O K) (W.formalThirdRootEval_relation hE₁ hE₂)
  have hwT := congrArg (algebraMap O K) (W.formalWEval_formalThirdRootEval hE₁ hE₂)
  rw [wEquationRHS_def] at hq₁ hq₂
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_one,
    map_ofNat] at hq₁ hq₂ hslope hint hrel hwT
  -- the group law of `W⁄K`, applied to the two parametrised points
  -- the chord cubic's leading coefficient is a unit in `O`, so nonzero in `K`
  have : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  have hA := ((W.isUnit_thirdRootDenom (hI.isTopologicallyNilpotent_of_mem (by
    simpa using W.formalSlopeEval_mem hI (k := 1) (by simpa using h₁)
      (by simpa using h₂)))).map (algebraMap O K)).ne_zero
  rw [map_add, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow, map_one] at hA
  -- the numerator of the difference of the two `x`-coordinates
  have hxK := hne (sub_ne_zero.2 hx)
  rw [map_sub, map_mul, map_mul] at hxK
  obtain ⟨h₃, hadd⟩ := chord_point_add (W.baseChange K) hq₁ hq₂ hslope hint hrel hwT hA
    (W.algebraMap_formalWEval_ne_zero hI h₁ (hne h₁0))
    (W.algebraMap_formalWEval_ne_zero hI h₂ (hne h₂0)) hwT0 hxK hn₁ hn₂
  exact hadd.trans (W.some_formalThirdRootEval_eq_some_formalAddEval hI h₁ h₂ h₃ hnF)

open scoped Classical in
/-- **The parametrisation carries the group law**, for two nonzero parameters whose points have
distinct `x`-coordinates: the point of `F(t₁, t₂)` is the sum of the points of `t₁` and `t₂`.

The chord through the two points meets the curve again at the parameter `t₃(t₁, t₂)`, and the
addition series is the formal inverse of that third root, so the group law of `W⁄K` applied to the
two points computes `F(t₁, t₂)`. -/
@[simp]
theorem add_eq_formalPoint_formalAddEval_of_X_ne {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (hx : t₁ * W.formalWEval t₂ ≠ t₂ * W.formalWEval t₁) :
    W.formalPoint (K := K) hI h₁ + W.formalPoint (K := K) hI h₂ =
      W.formalPoint (K := K) hI (pow_one I ▸ W.formalAddEval_mem hI (k := 1)
        ((pow_one I).symm ▸ h₁) ((pow_one I).symm ▸ h₂)) := by
  -- the chord condition already excludes the zero parameter, `w` vanishing there
  have h₁0 : t₁ ≠ 0 := by rintro rfl; simp at hx
  have h₂0 : t₂ ≠ 0 := by rintro rfl; simp at hx
  have hE₁ : PowerSeries.HasEval t₁ := hI.isTopologicallyNilpotent_of_mem h₁
  have hE₂ : PowerSeries.HasEval t₂ := hI.isTopologicallyNilpotent_of_mem h₂
  -- the sum is nonzero because the third root is, the formal inverse preserving nonvanishing
  have hF0 : W.formalAddEval t₁ t₂ ≠ 0 :=
    (W.formalAddEval_eq hE₁ hE₂).trans_ne <| W.formalInverseEval_ne_zero
      (W.hasEval_formalThirdRootEval hE₁ hE₂) (W.formalThirdRootEval_ne_zero hE₁ hE₂ hx)
  have hF : W.formalAddEval t₁ t₂ ∈ I :=
    pow_one I ▸ W.formalAddEval_mem hI (k := 1) ((pow_one I).symm ▸ h₁) ((pow_one I).symm ▸ h₂)
  have hne : ∀ {s : O}, s ≠ 0 → algebraMap O K s ≠ 0 := fun hs0 ↦ by simpa using hs0
  -- `equation_iff_nonsingular` states the `y`-coordinate as `-(w(t))⁻¹`, the chord lemmas as
  -- `-1 / w(t)`; `neg_div` and `one_div` bridge the two
  have hn : ∀ {s : O} (hs : s ∈ I), s ≠ 0 → (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K s / algebraMap O K (W.formalWEval s))
      (-1 / algebraMap O K (W.formalWEval s)) := fun hs hs0 ↦ by
    simpa only [neg_div, one_div] using Affine.equation_iff_nonsingular.mp
      (W.equation_formalPoint (hI.isTopologicallyNilpotent_of_mem hs)
        (W.algebraMap_formalWEval_ne_zero hI hs (hne hs0)))
  rw [W.formalPoint_of_param_ne_zero hI h₁ h₁0, W.formalPoint_of_param_ne_zero hI h₂ h₂0,
    W.formalPoint_of_param_ne_zero hI _ hF0]
  -- `Affine.Point.mk` is the `some` constructor at `-(w(t))⁻¹`
  simpa only [Affine.Point.mk, neg_div, one_div] using
    W.some_add_some_formalAddEval_of_X_ne hI h₁ h₂ h₁0 h₂0 hx (hn h₁ h₁0) (hn h₂ h₂0) (hn hF hF0)

end WeierstrassCurve
