/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Eval

/-!
# Points of a Weierstrass curve from formal-group parameters

Over a complete ring `O` carrying the `I`-adic topology, a parameter `t ∈ I` gives a point of
`W` over any field `K` whose structure map `O → K` is injective: the `w`-expansion converges at
`t`, and the pair
`(t / w(t), -1 / w(t))` satisfies the Weierstrass equation because the `w`-equation *is* that
equation read in the coordinates `x = t / w`, `y = -1 / w`. The parameter `t = 0` gives the point
at infinity.

`equation_formalPoint` needs nothing beyond that: the pair lies on the curve for any `W`. Turning
it into a *point* does need the curve over `K` to be elliptic, so everything from `formalPoint`
onwards assumes `[(W.baseChange K).IsElliptic]` — weaker than asking `W` itself to be elliptic
over `O`, which would exclude an integral model whose discriminant is nonzero but not a unit.

The two coordinates are recorded in closed form as well. Since `w(t) = t ^ 3 * u(t)` with `u(t)`
a unit, the `x`-coordinate is inverse to `t ^ 2 * u(t)` and the `y`-coordinate to
`-(t ^ 3 * u(t))`. Both are stated as products in `K`, so no inverse of either factor has to be
named; the powers `2` and `3` of `t` they exhibit are what a valuation on `K` would later turn
into pole orders, but no order or valuation hypothesis is assumed here.

## Main definitions

* `WeierstrassCurve.formalPoint`: the point of `W⁄K` attached to a parameter of an adic ideal.

## Main results

* `WeierstrassCurve.equation_formalPoint`: the parametrized pair lies on the curve.
* `WeierstrassCurve.neg_xCoord_div_yCoord_formalPoint`: the parameter read back off the point as
  `-x / y`, and with it `WeierstrassCurve.formalPoint_eq_zero_iff` and
  `WeierstrassCurve.formalPoint_injective`.
* `WeierstrassCurve.formalPoint_of_param_eq_zero` and
  `WeierstrassCurve.formalPoint_of_param_ne_zero`: the two branches of the definition.
* `WeierstrassCurve.formalPoint_formalInverseEval`: **the parametrisation respects negation** —
  the formal inverse on parameters becomes the group inverse on points, which on a generalised
  Weierstrass curve sends `y` to `-y - a₁x - a₃` rather than to `-y`.
* `WeierstrassCurve.xRep_formalPoint_eq_iff`: two parameters have points with the same
  `x`-coordinate exactly when they are equal or exchanged by the formal inverse, with
  `WeierstrassCurve.mul_formalWEval_eq_mul_formalWEval_iff` its chord form.
* `WeierstrassCurve.xCoord_formalPoint` and `WeierstrassCurve.yCoord_formalPoint`: the point's
  coordinates, through which the closed forms
  `WeierstrassCurve.xCoord_formalPoint_mul_eq_one` and
  `WeierstrassCurve.yCoord_formalPoint_mul_eq_neg_one` are stated.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2.

## Provenance

The same parametrization is formalised in Michael Stoll's elliptic-curve development
(`github.com/MichaelStollBayreuth/EllipticCurves` @ `66889eada51a`, Apache-2.0), file
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declarations `formalPoint`,
`formalPoint_of_param_eq_zero`, `formalPoint_of_param_ne_zero`, `formalPoint_nonsingular` and
`formalPoint_negPoint`. The first three keep their source names; the fourth is not restated,
`Affine.Point.mk` carrying the equation-to-nonsingularity step itself.

`formalPoint_formalInverseEval` is that source's `formalPoint_negPoint`. It is what makes the
parameters of an adic ideal closed under inverses as *points*, so that the chord case of
additivity in `Point/Add.lean` can read the addition series as a negated third root. Its name
takes this repository's vocabulary, `formalInverseEval` rather than the source's `negPoint`,
since the object being applied is the evaluated formal inverse.

`mul_formalWEval_eq_mul_formalWEval_iff` is that source's `eq_or_eq_negPoint_of_x_cond`, private
there and stated in one direction only; `xRep_formalPoint_eq_iff` is the form on `xRep` that it
specialises.

That development states them over `v.adicCompletion K` for a height-one prime of a Dedekind domain
and builds nonsingularity from a chord lemma of its own. The declarations below are stated over an
arbitrary complete adic ring mapping injectively to a field, and read the nonsingularity off
Mathlib's `equation_iff_nonsingular`, which `Affine.Point.mk` also uses.
-/

public section

open PowerSeries

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {K : Type*} [Field K] [Algebra O K]

namespace WeierstrassCurve

variable (W : WeierstrassCurve O)

/-- **A formal-group parameter gives a point of the curve**: the pair `(t / w(t), -1 / w(t))`
satisfies the Weierstrass equation over `K`. The hypothesis is `w(t) ≠ 0` rather than `t ≠ 0`,
because that is what the two denominators need; `algebraMap_formalWEval_ne_zero` supplies it
from a nonzero image `algebraMap O K t ≠ 0`, which `FaithfulSMul O K` below derives from
`t ≠ 0`. -/
theorem equation_formalPoint {t : O} (ht : PowerSeries.HasEval t)
    (hw : algebraMap O K (W.formalWEval t) ≠ 0) : (W.baseChange K).toAffine.Equation
      (algebraMap O K t / algebraMap O K (W.formalWEval t))
      (-(algebraMap O K (W.formalWEval t))⁻¹) := by
  have hkey := congrArg (algebraMap O K) (W.formalWEval_wEquation ht)
  rw [wEquationRHS_def] at hkey
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hkey
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  field_simp
  linear_combination hkey

variable [(W.baseChange K).IsElliptic]

variable [FaithfulSMul O K]

open scoped Classical in
/-- **The point attached to a formal-group parameter**: a nonzero `t` in an adic ideal gives the
affine point `(t / w(t), -1 / w(t))`, and `t = 0` gives the point at infinity. -/
noncomputable def formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    (W.baseChange K).toAffine.Point :=
  if h0 : t = 0 then 0
  else
    have hT : algebraMap O K t ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr h0
    .mk (W.equation_formalPoint (K := K) (hI.isTopologicallyNilpotent_of_mem ht)
      (W.algebraMap_formalWEval_ne_zero hI ht hT))

open scoped Classical in
/-- The parameter `0` gives the point at infinity. -/
@[simp]
theorem formalPoint_of_param_eq_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (h0 : t = 0) :
    W.formalPoint (K := K) hI ht = 0 := by
  simp [formalPoint, h0]

open scoped Classical in
/-- A nonzero parameter gives the affine point, with its coordinates in the form
`equation_formalPoint` states them. -/
-- Not a simp lemma: the right-hand side is `Affine.Point.mk` applied to a large proof term, so
-- rewriting left to right does not simplify, and it would take the coordinate lemmas below out of
-- simp-normal form. Rewrite with it explicitly.
theorem formalPoint_of_param_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (h0 : t ≠ 0) :
    W.formalPoint (K := K) hI ht =
      .mk (W.equation_formalPoint (K := K) (hI.isTopologicallyNilpotent_of_mem ht)
        (W.algebraMap_formalWEval_ne_zero hI ht
          ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr h0))) := by
  simp [formalPoint, h0]

open scoped Classical in
/-- **The `x`-coordinate of the parametrized point** is `t / w(t)`. -/
@[simp]
theorem xCoord_formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) (h0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).xCoord =
      algebraMap O K t / algebraMap O K (W.formalWEval t) := by
  rw [W.formalPoint_of_param_ne_zero hI ht h0]
  exact Affine.Point.xCoord_some _

open scoped Classical in
/-- **The `y`-coordinate of the parametrized point** is `-1 / w(t)`. -/
@[simp]
theorem yCoord_formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) (h0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).yCoord = -(algebraMap O K (W.formalWEval t))⁻¹ := by
  rw [W.formalPoint_of_param_ne_zero hI ht h0]
  exact Affine.Point.yCoord_some _

/-- **The `x`-coordinate in closed form**: since `w(t) = t ^ 3 * u(t)` with `u(t)` a unit, the
`x`-coordinate `t / w(t)` is the inverse of `t ^ 2 * u(t)`. Stated as a product so that it needs
no inverse; the exponent `2` is what a valuation would read as the pole order. -/
-- Not a simp lemma: `xCoord_formalPoint` already rewrites the `xCoord` on the left, so this
-- left-hand side is not in simp-normal form.
theorem xCoord_formalPoint_mul_eq_one {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).xCoord * algebraMap O K (t ^ 2 * W.formalUEval t) = 1 := by
  rw [W.xCoord_formalPoint hI ht ht0]
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hT : algebraMap O K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht0
  have hU : algebraMap O K (W.formalUEval t) ≠ 0 :=
    ((W.isUnit_formalUEval hI ht).map (algebraMap O K)).ne_zero
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht)]
  push_cast [map_mul, map_pow]
  field_simp

/-- **The `y`-coordinate in closed form**: `-1 / w(t)` is minus the inverse of `t ^ 3 * u(t)`,
with exponent `3` where the `x`-coordinate has `2`. -/
-- Not a simp lemma, for the reason given on the `x`-side: `yCoord_formalPoint` rewrites the
-- `yCoord` on the left.
theorem yCoord_formalPoint_mul_eq_neg_one {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).yCoord * algebraMap O K (t ^ 3 * W.formalUEval t) = -1 := by
  rw [W.yCoord_formalPoint hI ht ht0]
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hT : algebraMap O K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht0
  have hU : algebraMap O K (W.formalUEval t) ≠ 0 :=
    ((W.isUnit_formalUEval hI ht).map (algebraMap O K)).ne_zero
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht)]
  push_cast [map_mul, map_pow]
  field_simp

open scoped Classical in
/-- **The parameter is recovered from the point** as `-x / y`: the coordinates are `t / w(t)` and
`-1 / w(t)`, so their ratio cancels `w(t)`. This is the identity that makes the parametrization
injective, and hence the candidate injective side of `Ê(𝔪) ≅ E₁(K)`. It covers the zero branch
as well, where both coordinates and the parameter are `0`. -/
@[simp]
theorem neg_xCoord_div_yCoord_formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    -(W.formalPoint (K := K) hI ht).xCoord / (W.formalPoint (K := K) hI ht).yCoord =
      algebraMap O K t := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp
  · rw [W.xCoord_formalPoint hI ht h0, W.yCoord_formalPoint hI ht h0]
    have hw := W.algebraMap_formalWEval_ne_zero (S := K) hI ht
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr h0)
    field_simp

open scoped Classical in
/-- **The parametrization vanishes exactly at the zero parameter**: the fibre over the point at
infinity is exactly `{0}`. Calling that a kernel would be premature — no additive structure on
the parameters is established here. -/
@[simp]
theorem formalPoint_eq_zero_iff {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalPoint (K := K) hI ht = 0 ↔ t = 0 := by
  refine ⟨fun h ↦ ?_, W.formalPoint_of_param_eq_zero hI ht⟩
  have hrec := W.neg_xCoord_div_yCoord_formalPoint (K := K) hI ht
  rw [h] at hrec
  simp at hrec
  exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mp hrec.symm

open scoped Classical in
/-- **The parametrization is injective** on the parameters of `I`. Recovering the parameter as
`-x / y` reduces this to injectivity of the structure map, and it is what would make the map the
injective side of an identification with the kernel of reduction. -/
theorem formalPoint_injective {I : Ideal O} (hI : IsAdic I) :
    Function.Injective fun t : I ↦ W.formalPoint (K := K) hI t.property := by
  intro t₁ t₂ h
  refine Subtype.ext (FaithfulSMul.algebraMap_injective O K ?_)
  rw [← W.neg_xCoord_div_yCoord_formalPoint (K := K) hI t₁.property,
    ← W.neg_xCoord_div_yCoord_formalPoint (K := K) hI t₂.property]
  exact congrArg (fun P ↦ -P.xCoord / P.yCoord) h

open scoped Classical in
/-- **The parametrisation respects negation.** The formal inverse `ι` on parameters becomes the
group inverse on points — on a generalised Weierstrass curve the `negY` transformation
`y ↦ -y - a₁x - a₃`, not plain negation — so `formalPoint` carries the inverse law across.

Tagged `@[simp]` in the reducing orientation, towards point negation. Note that `simp` reaches it
only where the parameter is syntactically `formalInverseEval t`: the parameter sits in the
membership proof's type, so matching it otherwise would need higher-order unification. -/
@[simp]
theorem formalPoint_formalInverseEval {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalPoint (K := K) hI (pow_one I ▸ W.formalInverseEval_mem
        (hI.isTopologicallyNilpotent_of_mem ht) (k := 1) ((pow_one I).symm ▸ ht)) =
      -W.formalPoint (K := K) hI ht := by
  have hE : PowerSeries.HasEval t := hI.isTopologicallyNilpotent_of_mem ht
  by_cases h0 : t = 0
  · subst h0
    rw [W.formalPoint_of_param_eq_zero hI ht rfl, neg_zero,
      W.formalPoint_of_param_eq_zero hI _ (by simp [W.formalInverseEval_eq hE])]
  have hV0 : W.formalInverseEval t ≠ 0 := W.formalInverseEval_ne_zero hE h0
  have hVmem : W.formalInverseEval t ∈ I := by
    simpa using W.formalInverseEval_mem (I := I) (k := 1) hE (by simpa using ht)
  have hWt : algebraMap O K (W.formalWEval t) ≠ 0 := W.algebraMap_formalWEval_ne_zero hI ht
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr h0)
  rw [W.formalPoint_of_param_ne_zero hI hVmem hV0,
    W.formalPoint_of_param_ne_zero hI ht h0]
  -- `Point.mk` is the `some` constructor, and `negY` at the original point is the negated
  -- `y`-coordinate the second lemma computes
  simp only [Affine.Point.mk, Affine.Point.neg_some, Affine.Point.some.injEq, Affine.negY]
  refine ⟨W.algebraMap_formalInverseEval_div_algebraMap_formalWEval_formalInverseEval hE
      (W.hasEval_formalInverseEval hI ht), ?_⟩
  have hy := W.neg_one_div_algebraMap_formalWEval_formalInverseEval (K := K) hE
    (W.hasEval_formalInverseEval hI ht)
  rw [neg_div, one_div] at hy
  rw [hy]
  field_simp

/-- **Two parameters have points with the same `x`-coordinate exactly when they are equal or
exchanged by the formal inverse.** Over a field the `x`-coordinate determines a point up to
negation, and the parametrisation respects negation, so `t₁` and `ι(t₁)` are the only candidates.

Stated at equality of `xRep`, Mathlib's projective `x`-coordinate, which asks nothing of either
parameter: the point at infinity has `xRep = ![1, 0]` and an affine point `![x, 1]`, so the
left-hand side already forces the two parameters to vanish together. The right-hand side is about
the parameters alone, so the field the coordinates are read in is an explicit argument. -/
@[simp]
theorem xRep_formalPoint_eq_iff (K : Type*) [Field K] [Algebra O K]
    [(W.baseChange K).IsElliptic] [FaithfulSMul O K] {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) :
    (W.formalPoint (K := K) hI h₂).xRep = (W.formalPoint (K := K) hI h₁).xRep ↔
      t₂ = t₁ ∨ t₂ = W.formalInverseEval t₁ := by
  have hιmem : W.formalInverseEval t₁ ∈ I := by
    simpa using W.formalInverseEval_mem (I := I) (k := 1)
      (hI.isTopologicallyNilpotent_of_mem h₁) (by simpa using h₁)
  rw [Affine.Point.xRep_eq_xRep_iff]
  refine ⟨fun hc ↦ ?_, ?_⟩
  · rcases hc with hc | hc
    · exact Or.inl (congrArg Subtype.val
        (W.formalPoint_injective (K := K) hI (a₁ := ⟨t₂, h₂⟩) (a₂ := ⟨t₁, h₁⟩) hc))
    · rw [← W.formalPoint_formalInverseEval hI h₁] at hc
      exact Or.inr (congrArg Subtype.val (W.formalPoint_injective (K := K) hI
        (a₁ := ⟨t₂, h₂⟩) (a₂ := ⟨W.formalInverseEval t₁, hιmem⟩) hc))
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (W.formalPoint_formalInverseEval hI h₁)

/-- The chord form of `xRep_formalPoint_eq_iff`: when the cross-product of parameters against
`w`-values agrees.

`w` vanishes at `0`, so a vanishing parameter satisfies the cross-product whatever the other one
is; those two cases are therefore disjuncts of the conclusion rather than hypotheses. With both
parameters nonzero the remaining two disjuncts are the dichotomy of `xRep_formalPoint_eq_iff`.

Not a `simp` lemma, unlike `xRep_formalPoint_eq_iff`: neither side names the field, so `K` and its
instances would be left as metavariables that `simp` cannot solve. Rewrite with it explicitly. -/
theorem mul_formalWEval_eq_mul_formalWEval_iff (K : Type*) [Field K] [Algebra O K]
    [(W.baseChange K).IsElliptic] [FaithfulSMul O K] {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) :
    t₁ * W.formalWEval t₂ = t₂ * W.formalWEval t₁ ↔
      t₁ = 0 ∨ t₂ = 0 ∨ t₂ = t₁ ∨ t₂ = W.formalInverseEval t₁ := by
  rcases eq_or_ne t₁ 0 with rfl | h₁0
  · simp [W.formalWEval_zero]
  rcases eq_or_ne t₂ 0 with rfl | h₂0
  · simp [W.formalWEval_zero]
  have hred : (t₁ = 0 ∨ t₂ = 0 ∨ t₂ = t₁ ∨ t₂ = W.formalInverseEval t₁) ↔
      (t₂ = t₁ ∨ t₂ = W.formalInverseEval t₁) := by simp [h₁0, h₂0]
  have hnz : ∀ {s : O}, s ≠ 0 → algebraMap O K s ≠ 0 := fun hs0 ↦ by simpa using hs0
  have hw₁ : algebraMap O K (W.formalWEval t₁) ≠ 0 :=
    W.algebraMap_formalWEval_ne_zero hI h₁ (hnz h₁0)
  have hw₂ : algebraMap O K (W.formalWEval t₂) ≠ 0 :=
    W.algebraMap_formalWEval_ne_zero hI h₂ (hnz h₂0)
  rw [hred, ← W.xRep_formalPoint_eq_iff K hI h₁ h₂,
    W.formalPoint_of_param_ne_zero hI h₂ h₂0, W.formalPoint_of_param_ne_zero hI h₁ h₁0]
  simp only [Affine.Point.mk, Affine.Point.xRep_some, Matrix.vecCons_inj, and_true]
  rw [div_eq_div_iff hw₂ hw₁, ← map_mul, ← map_mul,
    (FaithfulSMul.algebraMap_injective O K).eq_iff, eq_comm]

end WeierstrassCurve
