/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Wronskian
public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod.Basic
-- Proof-only: the quotient rule `(N / D)' = W(D, N) / D²`.
import TauCeti.Analysis.Calculus.Deriv.Polynomial
-- Proof-only: the real points over an abscissa, and the finite kernel of an isogeny on points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Real
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
-- Proof-only: the image of an open set under `N / D` is σ-compact, hence measurable, and the
-- integrand `1 / √Ψ₂Sq` is measurable.
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Topology.Algebra.Polynomial
-- Proof-only: the intermediate value argument for `N / D`, through a local minimum at a pole and
-- the growth of `N / D` at infinity.
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
-- Proof-only: translation by a point of order two, and `-W_X` there from the roots of `Ψ₂Sq`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant

/-!
# The real period under an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over `ℝ`, with `x ∘ φ = r(x)` for
`r = N / D = φ.xRatFunc`, pulling the invariant differential back as `φ^*ω₂ = c ω₁`. Over `ℝ` every
isogeny is separable, so `c ≠ 0`. This file shows that `|c|` times the real period integral of
`W₁` is the integral of `dx' / √Ψ₂Sq₂(x')` over `Ψ₂Sq₂(x') > 0`, weighted by the number of `x` with
`Ψ₂Sq₁(x) > 0` and `r(x) = x'`; when almost every such fibre has `n` elements,
`|c| Ω(W₁) = n Ω(W₂)`.

This is the substitution theorem
`WeierstrassCurve.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard` applied to the
substitution `x' = r(x)`. Its two hypotheses, `r' = c s` and `Ψ₂Sq₂(r) = s² Ψ₂Sq₁`, hold off the
finitely many zeros of `D` and of the Wronskian `w = D N' - D' N`, with `s = w / (c D²)`: the first
is the quotient rule, the second is `TauCeti.Isogeny.eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq`.

The fibres are counted by the kernel of `φ` on real points. Let `P` be a real point of `W₂` not of
order two, with abscissa `x'`. The `x` with `Ψ₂Sq₁(x) > 0`, off the poles, and `r(x) = x'` are the
abscissas of the real points over `P`: such an `x` carries two real points `±Q`, and `φ` sends one
of them to `P`, because `φ(Q)` has abscissa `x'` and `φ(-Q) = -φ(Q)`. Two points over `P` never
share an abscissa, as `-P ≠ P`. So the fibre has `#ker φ(ℝ)` elements when `P` is in the image
`φ(W₁(ℝ))`, and is empty otherwise. Hence `|c|` times the real period integral of `W₁` is
`#ker φ(ℝ)` times the integral of `dx' / √Ψ₂Sq₂(x')` over the abscissas of the image, and
`|c| Ω(W₁) = #ker φ(ℝ) · Ω(W₂)` when `φ` is onto on real points.

In general `|c| Ω(W₁) · [W₂(ℝ) : φ(W₁(ℝ))] = #ker φ(ℝ) · Ω(W₂)`, and the proof shows that the
index is `1` or `2`. Let `e` be the largest real root of `Ψ₂Sq₂`. Every `x' ≥ e` is `r(x)` for
some `x` off the poles with `Ψ₂Sq₁(x) ≥ 0`, by the intermediate value theorem. Beyond the larger
`p` of the largest root of `Ψ₂Sq₁` and the largest pole, `r` is continuous and tends to `∞`, as
`deg N > deg D`. Some `x₀ ≥ p` off the poles has `Ψ₂Sq₂(r(x₀)) = 0`, so `r(x₀) ≤ e`. If `p` is
not a pole, it is a root of `Ψ₂Sq₁`, and `x₀ = p` works. If `p` is a pole, `r` tends to `∞` at
`p` as well, so it attains a minimum at some `x₀` in `(p, ∞)`, where `r' = 0`; there `w = 0`, so
again `Ψ₂Sq₂(r(x₀)) = 0`. So the image contains every real point over `[e, ∞)`. If `e` is the
only real root, there are no other real points. Otherwise `Ψ₂Sq₂ = 4 (x - e₁)(x - e₂)(x - e)`
with `e₁ < e₂ < e`, and the remaining real points lie over `[e₁, e₂]`. Translation by the point
`T` of order two over `e₁` carries them over `[e, ∞)`, since
`(x(P + T) - e₁)(x(P) - e₁) = (e₁ - e₂)(e₁ - e)`. So `φ` is onto if `T` is in the image.
Otherwise the image has index two and its affine points lie exactly over `[e, ∞)`. Those with
`Ψ₂Sq₂ > 0` lie over `(e, ∞)`, which carries half of the period
(`WeierstrassCurve.realPeriodLIntegral_eq_two_mul_setLIntegral_Ioi`).

## Main results

* `TauCeti.Isogeny.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard`: the fibre-counted
  transformation formula for the real period integral under an isogeny.
* `TauCeti.Isogeny.abs_mul_realPeriod_eq_of_ae_encard_eq`: `|c| Ω(W₁) = n Ω(W₂)` when almost every
  fibre has `n` elements.
* `TauCeti.Isogeny.xCoord_image_preimage_pointMap` and
  `TauCeti.Isogeny.injOn_xCoord_preimage_pointMap`: over a real point `P` not of order two, the
  abscissa is a bijection from the real points over `P` onto the fibre of `r` over `x(P)`.
* `TauCeti.Isogeny.encard_setOf_eval_div_eq_xCoord_of_mem_range` and
  `TauCeti.Isogeny.setOf_eval_div_eq_xCoord_eq_empty_of_notMem_range`: that fibre has
  `#ker φ(ℝ)` elements over the image of `φ`, and is empty off it.
* `TauCeti.Isogeny.ofReal_abs_mul_realPeriodLIntegral_eq_card_ker_mul_setLIntegral`: `|c|` times
  the real period integral of `W₁` is `#ker φ(ℝ)` times the integral over the abscissas of the
  image.
* `TauCeti.Isogeny.abs_mul_realPeriod_eq_card_ker_mul_of_surjective`:
  `|c| Ω(W₁) = #ker φ(ℝ) · Ω(W₂)` when `φ` is onto on real points.
* `TauCeti.Isogeny.mem_range_pointMapHom_of_le_xCoord`: the image of `φ` contains every real point
  of `W₂` over `[e, ∞)`, for `e` the largest real root of `Ψ₂Sq₂`.
* `TauCeti.Isogeny.abs_mul_realPeriod_mul_index_eq_card_ker_mul`: **the real period under an
  isogeny**, `|c| Ω(W₁) · [W₂(ℝ) : φ(W₁(ℝ))] = #ker φ(ℝ) · Ω(W₂)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.5.
-/

public section

open Filter MeasureTheory Polynomial Set WeierstrassCurve.Affine
open scoped ENNReal Topology

namespace TauCeti.Isogeny

variable {W₁ W₂ : WeierstrassCurve.Affine ℝ} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The exceptional set where the substitution theorem's hypotheses may fail: the zeros of `D` and
of the Wronskian, finitely many since both are nonzero polynomials. -/
private theorem countable_exceptional (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    ({x | φ.xRatFunc.denom.IsRoot x} ∪
      {x | (wronskian φ.xRatFunc.denom φ.xRatFunc.num).IsRoot x}).Countable :=
  ((finite_setOfPred_isRoot φ.xRatFunc.denom_ne_zero).union (finite_setOfPred_isRoot
    (wronskian_xRatFunc_ne_zero hc
      (ne_zero_of_pullbackDifferential_eq_smul φ hc)))).countable

/-- The odd part `s = w / (c D²)` of `φ`, as a function on `ℝ`. -/
private noncomputable def oddPart (φ : Isogeny W₁ W₂) (c x : ℝ) : ℝ :=
  (wronskian φ.xRatFunc.denom φ.xRatFunc.num).eval x / (c * φ.xRatFunc.denom.eval x ^ 2)

/-- The hypotheses of the substitution theorem, off the zeros of `D` and of the Wronskian. -/
private theorem substitution_hypotheses (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {x : ℝ} (hD : φ.xRatFunc.denom.eval x ≠ 0)
    (hw : (wronskian φ.xRatFunc.denom φ.xRatFunc.num).eval x ≠ 0) :
    HasDerivAt (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) (c * oddPart φ c x) x ∧
      oddPart φ c x ≠ 0 ∧
      W₂.Ψ₂Sq.eval (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) =
        oddPart φ c x ^ 2 * W₁.Ψ₂Sq.eval x := by
  have hc0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  refine ⟨?_, div_ne_zero hw (mul_ne_zero hc0 (pow_ne_zero 2 hD)), ?_⟩
  · convert hasDerivAt_eval_div_eval hD using 1
    rw [oddPart]
    field_simp
  · rw [oddPart, div_pow, div_mul_eq_mul_div,
      eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq hc hD]
    field_simp

/-- **The real period integral under an isogeny, counting fibres.** Let `φ : W₁ → W₂` be an
isogeny over `ℝ` with `φ^*ω₂ = c ω₁` and `x ∘ φ = r(x)`, where `r = N / D = φ.xRatFunc`. Then
`|c|` times the real period integral of `W₁` is the integral over `Ψ₂Sq₂(x') > 0` of
`dx' / √Ψ₂Sq₂(x')`, weighted by the number of `x` with `Ψ₂Sq₁(x) > 0` and `N(x) / D(x) = x'`. -/
theorem ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    ENNReal.ofReal |c| * W₁.realPeriodLIntegral =
      ∫⁻ y in {y | 0 < W₂.Ψ₂Sq.eval y},
        ({x | 0 < W₁.Ψ₂Sq.eval x} ∩
            (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) ⁻¹' {y}).encard *
          ENNReal.ofReal (√(W₂.Ψ₂Sq.eval y))⁻¹ := by
  refine W₁.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard
    (countable_exceptional φ hc)
    (s := oddPart φ c)
    (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) <;>
  · simp only [mem_union, mem_ofPred_eq, IsRoot.def, not_or] at hx
    have := substitution_hypotheses φ hc hx.1 hx.2
    tauto

/-- **The real period under an isogeny with constant fibre count.** Let `φ : W₁ → W₂` be an
isogeny over `ℝ` with `φ^*ω₂ = c ω₁` and `x ∘ φ = r(x)`, where `r = N / D = φ.xRatFunc`. If
almost every `x'` with `Ψ₂Sq₂(x') > 0` is `N(x) / D(x)` for exactly `n` values `x` with
`Ψ₂Sq₁(x) > 0`, then `|c| Ω(W₁) = n Ω(W₂)`. -/
theorem abs_mul_realPeriod_eq_of_ae_encard_eq (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {n : ℕ} (hn : ∀ᵐ y, 0 < W₂.Ψ₂Sq.eval y → ({x | 0 < W₁.Ψ₂Sq.eval x} ∩
      (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) ⁻¹' {y}).encard = n) :
    |c| * W₁.realPeriod = n * W₂.realPeriod := by
  refine W₁.abs_mul_realPeriod_eq_of_ae_encard_eq (countable_exceptional φ hc)
    (s := oddPart φ c)
    (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) hn <;>
  · simp only [mem_union, mem_ofPred_eq, IsRoot.def, not_or] at hx
    have := substitution_hypotheses φ hc hx.1 hx.2
    tauto

section Fibres

/-- The abscissa of a real point over `P`, for `P` not of order two, lies in the fibre of
`N / D` over `x(P)`, off the poles of `N / D`. -/
private theorem mem_fibre_of_pointMap_eq (φ : Isogeny W₁ W₂) {P : W₂.Point} (hP : -P ≠ P)
    {Q : W₁.Point} (hQ : (Hom.ofIsogeny φ).pointMap Q = P) :
    0 < W₁.Ψ₂Sq.eval Q.xCoord ∧ φ.xRatFunc.denom.eval Q.xCoord ≠ 0 ∧
      φ.xRatFunc.num.eval Q.xCoord / φ.xRatFunc.denom.eval Q.xCoord = P.xCoord := by
  have hP0 := (Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq.mp hP).1
  -- `Q` is not of order two either, since `φ(-Q) = -P`
  have hQ' : -Q ≠ Q := fun h ↦ hP <| by rw [← hQ, ← Hom.pointMap_neg, h]
  obtain ⟨hQ0, hpos⟩ := Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq.mp hQ'
  obtain ⟨x, y, h, rfl⟩ := Point.exists_eq_some_of_ne_zero hQ0
  have hD : φ.xRatFunc.denom.eval x ≠ 0 := fun hD ↦
    hP0 (hQ ▸ (pointMap_ofIsogeny_some_eq_zero_iff h).mpr hD)
  rw [Point.xCoord_some] at hpos ⊢
  exact ⟨hpos, hD, by rw [← hQ, xCoord_pointMap_ofIsogeny_some h hD]⟩

/-- Conversely, an `x` in the fibre of `N / D` over `x(P)`, with `Ψ₂Sq₁(x) > 0` and off the
poles, is the abscissa of a real point over `P`: of one of the two real points over `x`. -/
private theorem exists_pointMap_eq_of_mem_fibre (φ : Isogeny W₁ W₂) {P : W₂.Point} (hP : P ≠ 0)
    {x : ℝ} (hx : 0 < W₁.Ψ₂Sq.eval x) (hD : φ.xRatFunc.denom.eval x ≠ 0)
    (hr : φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x = P.xCoord) :
    ∃ Q : W₁.Point, Q.xCoord = x ∧ (Hom.ofIsogeny φ).pointMap Q = P := by
  obtain ⟨y, h⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq hx.le
  have h0 : (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0 :=
    (pointMap_ofIsogeny_some_eq_zero_iff h).not.mpr hD
  -- `φ(x, y)` has the abscissa of `P`, so it is `P` or `-P`
  rcases Point.eq_or_eq_neg_of_xCoord_eq h0 hP ((xCoord_pointMap_ofIsogeny_some h hD).trans hr)
    with he | he
  · exact ⟨.some x y h, Point.xCoord_some h, he⟩
  · exact ⟨-.some x y h, (Point.xCoord_neg _).trans (Point.xCoord_some h),
      by rw [Hom.pointMap_neg, he, neg_neg]⟩

/-- **The abscissas of the real points over `P`.** For a real point `P` of `W₂` not of order two,
the abscissas of the real points of `W₁` that `φ` sends to `P` are exactly the `x` with
`Ψ₂Sq₁(x) > 0`, `D(x) ≠ 0` and `N(x) / D(x) = x(P)`, where `N / D = φ.xRatFunc`. -/
theorem xCoord_image_preimage_pointMap (φ : Isogeny W₁ W₂) {P : W₂.Point} (hP : -P ≠ P) :
    Point.xCoord '' ((Hom.ofIsogeny φ).pointMap ⁻¹' {P}) =
      {x | 0 < W₁.Ψ₂Sq.eval x ∧ φ.xRatFunc.denom.eval x ≠ 0 ∧
        φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x = P.xCoord} := by
  ext x
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact mem_fibre_of_pointMap_eq φ hP hQ
  · rintro ⟨hx, hD, hr⟩
    obtain ⟨Q, rfl, hQ⟩ := exists_pointMap_eq_of_mem_fibre φ
      (Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq.mp hP).1 hx hD hr
    exact ⟨Q, hQ, rfl⟩

/-- **Distinct real points over `P` have distinct abscissas**, for `P` not of order two: two
points with the same abscissa are equal or opposite, and opposite points lie over `P` and `-P`. -/
theorem injOn_xCoord_preimage_pointMap (φ : Isogeny W₁ W₂) {P : W₂.Point} (hP : -P ≠ P) :
    InjOn Point.xCoord ((Hom.ofIsogeny φ).pointMap ⁻¹' {P}) := by
  intro Q₁ hQ₁ Q₂ hQ₂ hx
  rw [mem_preimage, mem_singleton_iff] at hQ₁ hQ₂
  have h0 (Q : W₁.Point) (hQ : (Hom.ofIsogeny φ).pointMap Q = P) : Q ≠ 0 := by
    rintro rfl
    exact (Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq.mp hP).1 (hQ ▸ Hom.pointMap_zero _)
  refine (Point.eq_or_eq_neg_of_xCoord_eq (h0 _ hQ₁) (h0 _ hQ₂) hx).resolve_right fun he ↦ hP ?_
  rw [← hQ₂, ← Hom.pointMap_neg, ← he, hQ₁, hQ₂]

/-- **Over the image of `φ`, the fibre of `x ↦ N(x) / D(x)` is counted by the kernel.** For a real
point `P = φ(Q)` of `W₂` not of order two, there are exactly `#ker φ(ℝ)` values `x` with
`Ψ₂Sq₁(x) > 0`, `D(x) ≠ 0` and `N(x) / D(x) = x(P)`, where `N / D = φ.xRatFunc`. -/
theorem encard_setOf_eval_div_eq_xCoord_of_mem_range (φ : Isogeny W₁ W₂) {P : W₂.Point}
    (hP : -P ≠ P) (hφ : P ∈ (Hom.ofIsogeny φ).pointMapHom.range) :
    {x | 0 < W₁.Ψ₂Sq.eval x ∧ φ.xRatFunc.denom.eval x ≠ 0 ∧
        φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x = P.xCoord}.encard =
      Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
  rw [← xCoord_image_preimage_pointMap φ hP, (injOn_xCoord_preimage_pointMap φ hP).encard_image]
  obtain ⟨Q, rfl⟩ := hφ
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  rw [encard, ← ENat.card_eq_coe_natCard, ← Hom.coe_pointMapHom]
  exact ENat.card_congr ((Hom.ofIsogeny φ).pointMapHom.fiberEquivKer Q)

/-- **Off the image of `φ`, the fibre of `x ↦ N(x) / D(x)` is empty.** For a real point `P` of
`W₂` not of order two and not in `φ(W₁(ℝ))`, no `x` has `Ψ₂Sq₁(x) > 0`, `D(x) ≠ 0` and
`N(x) / D(x) = x(P)`, where `N / D = φ.xRatFunc`. -/
theorem setOf_eval_div_eq_xCoord_eq_empty_of_notMem_range (φ : Isogeny W₁ W₂) {P : W₂.Point}
    (hP : -P ≠ P) (hφ : P ∉ (Hom.ofIsogeny φ).pointMapHom.range) :
    {x | 0 < W₁.Ψ₂Sq.eval x ∧ φ.xRatFunc.denom.eval x ≠ 0 ∧
        φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x = P.xCoord} = ∅ := by
  rw [← xCoord_image_preimage_pointMap φ hP, image_eq_empty, eq_empty_iff_forall_notMem]
  exact fun Q hQ ↦ hφ ⟨Q, (Hom.pointMapHom_apply _ Q).trans hQ⟩

/-- Over `x' ≠ 0` the poles of `N / D`, where Lean's `N(x) / 0 = 0`, lie in no fibre. -/
private theorem inter_preimage_eq_setOf (φ : Isogeny W₁ W₂) {y : ℝ} (hy : y ≠ 0) :
    {x | 0 < W₁.Ψ₂Sq.eval x} ∩
        (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) ⁻¹' {y} =
      {x | 0 < W₁.Ψ₂Sq.eval x ∧ φ.xRatFunc.denom.eval x ≠ 0 ∧
        φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x = y} := by
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  refine ⟨fun ⟨hx, hr⟩ ↦ ⟨hx, fun hD ↦ hy ?_, hr⟩, fun ⟨hx, _, hr⟩ ↦ ⟨hx, hr⟩⟩
  rw [← hr, hD, div_zero]

/-- The abscissas `x'` with `Ψ₂Sq₂(x') > 0` of the affine points of the image of `φ` form a
measurable set: off the poles they are the image under `N / D` of an open set on which `N / D` is
continuous, and such an image is σ-compact. -/
private theorem measurableSet_setOf_xCoord_mem_range (φ : Isogeny W₁ W₂) :
    MeasurableSet {y | 0 < W₂.Ψ₂Sq.eval y ∧
      ∃ P ∈ (Hom.ofIsogeny φ).pointMapHom.range, P ≠ 0 ∧ P.xCoord = y} := by
  set r := fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x
  set S := {x | 0 < W₁.Ψ₂Sq.eval x ∧ φ.xRatFunc.denom.eval x ≠ 0}
  have hBS : {y | 0 < W₂.Ψ₂Sq.eval y ∧
      ∃ P ∈ (Hom.ofIsogeny φ).pointMapHom.range, P ≠ 0 ∧ P.xCoord = y} =
      {y | 0 < W₂.Ψ₂Sq.eval y} ∩ r '' S := by
    ext y
    refine ⟨fun ⟨hy, P, ⟨Q, hQ⟩, hP0, hPy⟩ ↦ ⟨hy, ?_⟩, fun ⟨hy, x, ⟨hx, hD⟩, hr⟩ ↦ ⟨hy, ?_⟩⟩
    · have hP : -P ≠ P := Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq.mpr ⟨hP0, hPy ▸ hy⟩
      obtain ⟨hx, hD, hr⟩ :=
        mem_fibre_of_pointMap_eq φ hP ((Hom.pointMapHom_apply _ Q).symm.trans hQ)
      exact ⟨Q.xCoord, ⟨hx, hD⟩, hr.trans hPy⟩
    · obtain ⟨y', h⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq hx.le
      exact ⟨(Hom.ofIsogeny φ).pointMap (.some x y' h), ⟨_, Hom.pointMapHom_apply _ _⟩,
        (pointMap_ofIsogeny_some_eq_zero_iff h).not.mpr hD,
        (xCoord_pointMap_ofIsogeny_some h hD).trans hr⟩
  have hSo : IsOpen S := (isOpen_lt continuous_const W₁.Ψ₂Sq.continuous).inter
    (isOpen_ne_fun φ.xRatFunc.denom.continuous continuous_const)
  have : LocallyCompactSpace S := hSo.locallyCompactSpace
  have hrS : ContinuousOn r S := fun x hx ↦
    (φ.xRatFunc.num.continuous.continuousAt.div φ.xRatFunc.denom.continuous.continuousAt
      hx.2).continuousWithinAt
  obtain ⟨K, hK, hKS⟩ :=
    (isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance).image_of_continuousOn hrS
  rw [hBS, ← hKS]
  exact (measurableSet_lt measurable_const W₂.Ψ₂Sq.continuous.measurable).inter
    (MeasurableSet.iUnion fun k ↦ (hK k).measurableSet)

/-- The fibre of `N / D` over `x' ≠ 0` with `Ψ₂Sq₂(x') > 0` has `#ker φ(ℝ)` elements when `x'` is
the abscissa of an affine point of the image of `φ`, and none otherwise. -/
private theorem encard_inter_preimage_eq_indicator (φ : Isogeny W₁ W₂) {y : ℝ} (hy0 : y ≠ 0)
    (hy : 0 < W₂.Ψ₂Sq.eval y) :
    ({x | 0 < W₁.Ψ₂Sq.eval x} ∩
        (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) ⁻¹' {y}).encard =
      {y | 0 < W₂.Ψ₂Sq.eval y ∧
          ∃ P ∈ (Hom.ofIsogeny φ).pointMapHom.range, P ≠ 0 ∧ P.xCoord = y}.indicator
        (fun _ ↦ (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℕ∞)) y := by
  -- the fibre is counted at a real point `P` with abscissa `x'`
  obtain ⟨y', h⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq hy.le
  have hP := (Point.neg_some_ne_some_iff_pos_eval_Ψ₂Sq h).mpr hy
  rw [inter_preimage_eq_setOf φ hy0]
  by_cases hφ : Point.some y y' h ∈ (Hom.ofIsogeny φ).pointMapHom.range
  · have he := encard_setOf_eval_div_eq_xCoord_of_mem_range φ hP hφ
    rw [Point.xCoord_some] at he
    rw [he, indicator_of_mem]
    exact ⟨hy, _, hφ, Point.some_ne_zero h, Point.xCoord_some h⟩
  · have he := setOf_eval_div_eq_xCoord_eq_empty_of_notMem_range φ hP hφ
    rw [Point.xCoord_some] at he
    rw [he, encard_empty, indicator_of_notMem]
    -- the only other point with abscissa `x'` is `-P`, which is not in the image either
    rintro ⟨-, Q, hQ, hQ0, hQy⟩
    rcases Point.eq_or_eq_neg_of_xCoord_eq hQ0 (Point.some_ne_zero h)
      (hQy.trans (Point.xCoord_some h).symm) with rfl | rfl
    · exact hφ hQ
    · exact hφ (neg_neg (Point.some y y' h) ▸ neg_mem hQ)

/-- **The real period integral under an isogeny, over the image.** Let `φ : W₁ → W₂` be an
isogeny over `ℝ` with `φ^*ω₂ = c ω₁`. Then `|c|` times the real period integral of `W₁` is
`#ker φ(ℝ)` times the integral of `dx' / √Ψ₂Sq₂(x')` over the abscissas `x'` with
`Ψ₂Sq₂(x') > 0` of the affine points of the image `φ(W₁(ℝ))`. -/
theorem ofReal_abs_mul_realPeriodLIntegral_eq_card_ker_mul_setLIntegral (φ : Isogeny W₁ W₂)
    {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    ENNReal.ofReal |c| * W₁.realPeriodLIntegral =
      Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
        ∫⁻ y in {y | 0 < W₂.Ψ₂Sq.eval y ∧
            ∃ P ∈ (Hom.ofIsogeny φ).pointMapHom.range, P ≠ 0 ∧ P.xCoord = y},
          ENNReal.ofReal (√(W₂.Ψ₂Sq.eval y))⁻¹ := by
  set A := {y | 0 < W₂.Ψ₂Sq.eval y}
  set B := {y | 0 < W₂.Ψ₂Sq.eval y ∧
    ∃ P ∈ (Hom.ofIsogeny φ).pointMapHom.range, P ≠ 0 ∧ P.xCoord = y}
  set n := Nat.card (Hom.ofIsogeny φ).pointMapHom.ker
  have hA : MeasurableSet A := measurableSet_lt measurable_const W₂.Ψ₂Sq.continuous.measurable
  have hB := measurableSet_setOf_xCoord_mem_range φ
  have hg : Measurable fun y ↦ ENNReal.ofReal (√(W₂.Ψ₂Sq.eval y))⁻¹ :=
    W₂.Ψ₂Sq.continuous.measurable.sqrt.inv.ennreal_ofReal
  rw [ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard φ hc,
    ← lintegral_const_mul _ hg]
  calc _ = ∫⁻ y in A, B.indicator (fun y ↦ n * ENNReal.ofReal (√(W₂.Ψ₂Sq.eval y))⁻¹) y :=
        setLIntegral_congr_fun_ae hA ?_
    _ = _ := by
      rw [lintegral_indicator hB, Measure.restrict_restrict hB,
        inter_eq_self_of_subset_left fun y (hy : y ∈ B) ↦ hy.1]
  filter_upwards [volume.ae_ne 0] with y hy0 hy
  rw [encard_inter_preimage_eq_indicator φ hy0 hy]
  by_cases hyB : y ∈ B
  · rw [indicator_of_mem hyB, indicator_of_mem hyB, ENat.toENNReal_coe]
  · rw [indicator_of_notMem hyB, indicator_of_notMem hyB, ENat.toENNReal_zero, zero_mul]

/-- **The real period under an isogeny that is onto on real points.** Let `φ : W₁ → W₂` be an
isogeny over `ℝ` with `φ^*ω₂ = c ω₁`. If `φ` maps `W₁(ℝ)` onto `W₂(ℝ)`, then
`|c| Ω(W₁) = #ker φ(ℝ) · Ω(W₂)`. -/
theorem abs_mul_realPeriod_eq_card_ker_mul_of_surjective (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    (hφ : Function.Surjective (Hom.ofIsogeny φ).pointMap) :
    |c| * W₁.realPeriod = Nat.card (Hom.ofIsogeny φ).pointMapHom.ker * W₂.realPeriod := by
  refine abs_mul_realPeriod_eq_of_ae_encard_eq φ hc ?_
  filter_upwards [volume.ae_ne 0] with y hy0 hy
  obtain ⟨y', h⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq hy.le
  rw [inter_preimage_eq_setOf φ hy0]
  have he := encard_setOf_eval_div_eq_xCoord_of_mem_range φ
    ((Point.neg_some_ne_some_iff_pos_eval_Ψ₂Sq h).mpr hy)
    ((hφ (.some y y' h)).imp fun Q hQ ↦ (Hom.pointMapHom_apply _ Q).trans hQ)
  rwa [Point.xCoord_some] at he

end Fibres

section Image

variable {φ : Isogeny W₁ W₂} {c : ℝ}

/-- Off the poles, `c² D⁴ Ψ₂Sq₂(N / D) = w² Ψ₂Sq₁`, so the sign of `Ψ₂Sq₁` controls that of
`Ψ₂Sq₂(N / D)`. -/
private theorem nonneg_eval_Ψ₂Sq_div
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {x : ℝ} (hD : φ.xRatFunc.denom.eval x ≠ 0) (hx : 0 ≤ W₁.Ψ₂Sq.eval x) :
    0 ≤ W₂.Ψ₂Sq.eval (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) := by
  have h := eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq hc hD
  have hc0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hpos : 0 < c ^ 2 * φ.xRatFunc.denom.eval x ^ 4 := by positivity
  exact (mul_nonneg_iff_of_pos_left hpos).mp (h ▸ mul_nonneg (sq_nonneg _) hx)

/-- Off the poles, where `w` or `Ψ₂Sq₁` vanishes, so does `Ψ₂Sq₂(N / D)`. -/
private theorem eval_Ψ₂Sq_div_eq_zero
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {x : ℝ} (hD : φ.xRatFunc.denom.eval x ≠ 0)
    (hx : (wronskian φ.xRatFunc.denom φ.xRatFunc.num).eval x * W₁.Ψ₂Sq.eval x = 0) :
    W₂.Ψ₂Sq.eval (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) = 0 := by
  have h := eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq hc hD
  have hc0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  rw [sq, mul_assoc, hx, mul_zero] at h
  simpa [hc0, hD] using h.symm

/-- Where `|N / D| → ∞` along a filter on which eventually `D ≠ 0` and `Ψ₂Sq₁ ≥ 0`, in fact
`N / D → ∞`: its values are abscissas of real points of `W₂`, which are bounded below. -/
private theorem tendsto_eval_div_atTop_of_tendsto_abs
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {l : Filter ℝ}
    (h : Tendsto (fun x ↦ |φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x|) l atTop)
    (hl : ∀ᶠ x in l, φ.xRatFunc.denom.eval x ≠ 0 ∧ 0 ≤ W₁.Ψ₂Sq.eval x) :
    Tendsto (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) l atTop := by
  obtain ⟨m, hm⟩ := bddBelow_setOf_nonneg_eval_Ψ₂Sq (W := W₂)
  refine tendsto_atTop.mpr fun b ↦ ((h.eventually_ge_atTop (|m| + |b| + 1)).and hl).mono ?_
  rintro x ⟨h₁, hD, hx⟩
  have h₂ := hm (nonneg_eval_Ψ₂Sq_div hc hD hx)
  rcases abs_cases (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) with ⟨h₃, -⟩ | ⟨h₃, -⟩
  · linarith [le_abs_self b, abs_nonneg m]
  · linarith [neg_abs_le m, abs_nonneg b]

variable (φ) in
/-- Beyond some `p`, `D` has no roots and `Ψ₂Sq₁ > 0`; at `p`, `Ψ₂Sq₁ ≥ 0` and `D` or `Ψ₂Sq₁`
vanishes. So `p` is the larger of the largest root of `Ψ₂Sq₁` and the largest pole of `N / D`. -/
private theorem exists_forall_lt_eval_denom_ne_zero_and_pos :
    ∃ p, 0 ≤ W₁.Ψ₂Sq.eval p ∧ (φ.xRatFunc.denom.eval p = 0 ∨ W₁.Ψ₂Sq.eval p = 0) ∧
      ∀ ⦃x⦄, p < x → φ.xRatFunc.denom.eval x ≠ 0 ∧ 0 < W₁.Ψ₂Sq.eval x := by
  -- `p` is the largest `x` with `D(x) = 0` or `Ψ₂Sq₁(x) ≤ 0`
  set Z := {x | φ.xRatFunc.denom.eval x = 0 ∨ W₁.Ψ₂Sq.eval x ≤ 0}
  obtain ⟨e, he, hpos⟩ := exists_isRoot_Ψ₂Sq_and_forall_lt_pos_eval W₁
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (Polynomial.eventually_atTop_not_isRoot _ φ.xRatFunc.denom_ne_zero)
  have heZ : e ∈ Z := Or.inr he.eq_zero.le
  have hZb : BddAbove Z := ⟨max e M, fun x hx ↦ le_of_not_gt fun h ↦ by
    rcases hx with hx | hx
    · exact hM x (le_of_max_le_right h.le) hx
    · exact (hpos (lt_of_le_of_lt (le_max_left e M) h)).not_ge hx⟩
  have hZc : IsClosed Z := (isClosed_eq φ.xRatFunc.denom.continuous continuous_const).union
    (isClosed_le W₁.Ψ₂Sq.continuous continuous_const)
  have hgt : ∀ ⦃x⦄, sSup Z < x → φ.xRatFunc.denom.eval x ≠ 0 ∧ 0 < W₁.Ψ₂Sq.eval x :=
    fun x hx ↦ by
      have : x ∉ Z := fun h ↦ (le_csSup hZb h).not_gt hx
      simp only [Z, mem_ofPred_eq, not_or, not_le] at this
      exact this
  have hp0 : 0 ≤ W₁.Ψ₂Sq.eval (sSup Z) := by
    rcases (le_csSup hZb heZ).eq_or_lt with h | h
    · exact h ▸ he.eq_zero.ge
    · exact (hpos h).le
  refine ⟨sSup Z, hp0, ?_, hgt⟩
  exact (hZc.csSup_mem ⟨e, heZ⟩ hZb).imp_right hp0.antisymm'

variable (φ) in
/-- `N / D → ∞` at `∞`: the degree of `N` exceeds that of `D`. -/
private theorem tendsto_eval_div_atTop
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    Tendsto (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) atTop atTop := by
  obtain ⟨p, -, -, hgt⟩ := exists_forall_lt_eval_denom_ne_zero_and_pos φ
  refine tendsto_eval_div_atTop_of_tendsto_abs hc
    (abs_div_tendsto_atTop_atTop_of_degree_gt _ _
      (degree_lt_degree (natDegree_denom_lt_natDegree_num_xRatFunc φ)) φ.xRatFunc.denom_ne_zero)
    ((eventually_gt_atTop p).mono fun x hx ↦ ⟨(hgt hx).1, (hgt hx).2.le⟩)

/-- At a pole `p` of `N / D` beyond which `D ≠ 0` and `Ψ₂Sq₁ > 0`, the function `N / D` tends to
`∞` on both sides of `(p, ∞)`, so it has a minimum there. At the minimum its derivative `w / D²`
vanishes, so `Ψ₂Sq₂(N / D) = 0` there, and the minimum is at most the largest root `e` of
`Ψ₂Sq₂`. -/
private theorem exists_lt_eval_div_le_of_eval_denom_eq_zero
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {e : ℝ} (hpos : ∀ ⦃y⦄, e < y → 0 < W₂.Ψ₂Sq.eval y) {p : ℝ}
    (hp : φ.xRatFunc.denom.eval p = 0)
    (hgt : ∀ ⦃x⦄, p < x → φ.xRatFunc.denom.eval x ≠ 0 ∧ 0 < W₁.Ψ₂Sq.eval x) :
    ∃ x₀, p < x₀ ∧ φ.xRatFunc.num.eval x₀ / φ.xRatFunc.denom.eval x₀ ≤ e := by
  set r := fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x
  have hcont : ContinuousOn r (Ioi p) := fun x hx ↦
    (hasDerivAt_eval_div_eval (hgt hx).1).continuousAt.continuousWithinAt
  -- `N(p) ≠ 0`, as `N` and `D` are coprime, so `|N / D| → ∞` at `p`
  have hNp : φ.xRatFunc.num.eval p ≠ 0 := fun hN ↦ by
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom φ.xRatFunc
    simpa [hN, hp] using congrArg (eval p) hab
  have hD : Tendsto (fun x ↦ |φ.xRatFunc.denom.eval x|) (𝓝[>] p) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa [hp] using
      (φ.xRatFunc.denom.continuous.abs.tendsto p).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun x hx ↦ abs_pos.mpr (hgt hx).1⟩
  have hpole : Tendsto r (𝓝[>] p) atTop := by
    refine tendsto_eval_div_atTop_of_tendsto_abs hc ?_
      (eventually_nhdsWithin_of_forall fun x hx ↦ ⟨(hgt hx).1, (hgt hx).2.le⟩)
    simpa [abs_div, div_eq_mul_inv] using
      (((φ.xRatFunc.num.continuous.abs.tendsto p).mono_left nhdsWithin_le_nhds).pos_mul_atTop
        (abs_pos.mpr hNp) (tendsto_inv_nhdsGT_zero.comp hD))
  -- a local minimum of `r` on `(a, b)`, where `p < a < p + 1 < b` and `r(a), r(b) > r(p + 1)`
  obtain ⟨a, ha, hpa⟩ := ((hpole.eventually_gt_atTop (r (p + 1))).and
    (Ioo_mem_nhdsGT (by linarith : p < p + 1))).exists
  obtain ⟨b, hb, hpb⟩ := ((tendsto_eval_div_atTop φ hc |>.eventually_gt_atTop (r (p + 1))).and
    (eventually_gt_atTop (p + 1))).exists
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isLocalMin_mem_open Ioo_subset_Icc_self
    (hcont.mono fun x hx ↦ hpa.1.trans_le hx.1) ⟨hpa.2.le, hpb.le⟩
    (fun z hz ↦ by
      rcases hz with ⟨⟨h₁, h₂⟩, h₃⟩
      rcases h₁.eq_or_lt with rfl | h₁
      · exact ha
      rcases h₂.eq_or_lt with rfl | h₂
      · exact hb
      exact absurd ⟨h₁, h₂⟩ h₃) isOpen_Ioo
  have hpx₀ : p < x₀ := hpa.1.trans hx₀.1
  have hw := hmin.hasDerivAt_eq_zero (hasDerivAt_eval_div_eval (hgt hpx₀).1)
  rw [div_eq_zero_iff, or_iff_left (pow_ne_zero 2 (hgt hpx₀).1)] at hw
  refine ⟨x₀, hpx₀, le_of_not_gt fun h ↦ (hpos h).ne' ?_⟩
  exact eval_Ψ₂Sq_div_eq_zero hc (hgt hpx₀).1 (by rw [hw, zero_mul])

/-- **The intermediate value argument.** Every `y` at least the largest root `e` of `Ψ₂Sq₂` is
`N(x) / D(x)` for some `x` with `D(x) ≠ 0` and `Ψ₂Sq₁(x) ≥ 0`. -/
private theorem exists_eval_div_eq
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {e : ℝ} (hpos : ∀ ⦃y⦄, e < y → 0 < W₂.Ψ₂Sq.eval y) {y : ℝ} (hy : e ≤ y) :
    ∃ x, 0 ≤ W₁.Ψ₂Sq.eval x ∧ φ.xRatFunc.denom.eval x ≠ 0 ∧
      φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x = y := by
  obtain ⟨p, hp0, hpZ, hgt⟩ := exists_forall_lt_eval_denom_ne_zero_and_pos φ
  -- a point `x₀ ≥ p` off the poles at which `N / D` is at most `e`
  obtain ⟨x₀, hpx₀, hD₀, hx₀⟩ : ∃ x₀, p ≤ x₀ ∧ φ.xRatFunc.denom.eval x₀ ≠ 0 ∧
      φ.xRatFunc.num.eval x₀ / φ.xRatFunc.denom.eval x₀ ≤ e := by
    by_cases hDp : φ.xRatFunc.denom.eval p = 0
    · obtain ⟨x₀, h₁, h₂⟩ := exists_lt_eval_div_le_of_eval_denom_eq_zero hc hpos hDp hgt
      exact ⟨x₀, h₁.le, (hgt h₁).1, h₂⟩
    · refine ⟨p, le_rfl, hDp, le_of_not_gt fun h ↦ (hpos h).ne' ?_⟩
      exact eval_Ψ₂Sq_div_eq_zero hc hDp (by rw [hpZ.resolve_left hDp, mul_zero])
  have hD (x : ℝ) (hx : x₀ ≤ x) : φ.xRatFunc.denom.eval x ≠ 0 :=
    hx.eq_or_lt.elim (· ▸ hD₀) fun h ↦ (hgt (hpx₀.trans_lt h)).1
  -- the intermediate value theorem on `[x₀, M]`, where `N(M) / D(M) ≥ y`
  obtain ⟨M, hM, hxM⟩ := ((tendsto_eval_div_atTop φ hc |>.eventually_ge_atTop y).and
    (eventually_ge_atTop x₀)).exists
  obtain ⟨x, hx, hrx⟩ := intermediate_value_Icc hxM
    (fun x hx ↦ (hasDerivAt_eval_div_eval (hD x hx.1)).continuousAt.continuousWithinAt)
    ⟨hx₀.trans hy, hM⟩
  refine ⟨x, ?_, hD x hx.1, hrx⟩
  rcases (hpx₀.trans hx.1).eq_or_lt with h | h
  · exact h ▸ hp0
  · exact (hgt h).2.le

variable (φ) in
/-- **The image of `φ` contains every real point beyond the largest root of `Ψ₂Sq₂`.** If
`Ψ₂Sq₂ > 0` on `(e, ∞)`, every affine real point `P` of `W₂` with `x(P) ≥ e` is the image under
`φ` of a real point of `W₁`. -/
theorem mem_range_pointMapHom_of_le_xCoord {e : ℝ} (hpos : ∀ ⦃y⦄, e < y → 0 < W₂.Ψ₂Sq.eval y)
    {P : W₂.Point} (hP : P ≠ 0) (he : e ≤ P.xCoord) : P ∈ (Hom.ofIsogeny φ).pointMapHom.range := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨x, hx, hD, hr⟩ := exists_eval_div_eq hc hpos he
  obtain ⟨y, h⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq hx
  have h0 : (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0 :=
    (pointMap_ofIsogeny_some_eq_zero_iff h).not.mpr hD
  rcases Point.eq_or_eq_neg_of_xCoord_eq h0 hP ((xCoord_pointMap_ofIsogeny_some h hD).trans hr)
    with he | he
  · exact ⟨_, (Hom.pointMapHom_apply _ _).trans he⟩
  · exact ⟨-.some x y h, by rw [map_neg, Hom.pointMapHom_apply, he, neg_neg]⟩

variable (φ) in
/-- With three real roots `e₁ < e₂ < e` of `Ψ₂Sq₂`, translating by the point `T` of order two over
`e₁` carries every affine real point `P` with `x(P) < e`, which lies over `[e₁, e₂]`, into the
image of `φ`: `x(P + T) - e₁ = (e₁ - e₂)(e₁ - e) / (x(P) - e₁) ≥ e - e₁`. -/
private theorem add_mem_range_pointMapHom_of_xCoord_lt {e₁ e₂ e : ℝ} (h₁₂ : e₁ < e₂)
    (h₂ : e₂ < e)
    (hfac : W₂.Ψ₂Sq = C 4 * (X - C e₁) * (X - C e₂) * (X - C e)) {t : ℝ}
    (hT : W₂.Nonsingular e₁ t) (hψ : W₂.polynomialY.evalEval e₁ t = 0) {P : W₂.Point}
    (hP : P ≠ 0) (hx : P.xCoord < e) :
    P + .some e₁ t hT ∈ (Hom.ofIsogeny φ).pointMapHom.range := by
  have hpos : ∀ ⦃y⦄, e < y → 0 < W₂.Ψ₂Sq.eval y := fun y hy ↦
    (W₂.pos_eval_Ψ₂Sq_iff_of_eq_prod_three_roots h₁₂ h₂ hfac y).mpr (Or.inr hy)
  obtain ⟨x, y, h, rfl⟩ := Point.exists_eq_some_of_ne_zero hP
  rw [Point.xCoord_some] at hx
  -- `x` lies in `[e₁, e₂]`, as `Ψ₂Sq₂(x) ≥ 0`
  have hΨ : 0 ≤ 4 * (x - e₁) * (x - e₂) * (x - e) := by
    simpa [hfac] using exists_equation_iff_nonneg_eval_Ψ₂Sq.mp ⟨y, h.1⟩
  have h₁ : e₁ ≤ x := le_of_not_gt fun h ↦ by
    nlinarith [mul_pos (mul_pos (sub_pos.2 h) (by linarith : (0 : ℝ) < e₂ - x)) (sub_pos.2 hx)]
  have hx₂ : x ≤ e₂ := le_of_not_gt fun h ↦ by
    nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < x - e₁) (sub_pos.2 h)) (sub_pos.2 hx)]
  rcases h₁.eq_or_lt with rfl | h₁
  · -- over `e₁` the point is `T` itself, and `T + T = 0`
    obtain rfl := Y_eq_of_evalEval_polynomialY_eq_zero hT.1 hψ h.1
    rw [(Point.some_add_self_eq_zero_iff hT).mpr hψ]
    exact zero_mem _
  have hne : x ≠ e₁ := h₁.ne'
  have hc := W₂.neg_evalEval_polynomialX_eq_of_Ψ₂Sq_eq two_ne_zero hfac
    (by rwa [WeierstrassCurve.ψ₂])
  have key := Point.xCoord_add_sub_mul_sub hT hψ h hne
  rw [hc] at key
  refine mem_range_pointMapHom_of_le_xCoord φ hpos (fun h0 ↦ hne ?_) ?_
  · -- `P + T = 0` would make `P = -T = T`
    rw [add_eq_zero_iff_eq_neg, ← (neg_eq_iff_add_eq_zero.mpr
      ((Point.some_add_self_eq_zero_iff hT).mpr hψ))] at h0
    simpa using congrArg Point.xCoord h0
  · nlinarith [mul_pos (sub_pos.2 h₁) (by linarith : (0 : ℝ) < e - e₁)]

end Image

section Index

/-- When `φ` is onto the real points, the index is one. -/
private theorem abs_mul_realPeriod_mul_index_eq_of_forall_mem (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    (h : ∀ P, P ∈ (Hom.ofIsogeny φ).pointMapHom.range) :
    |c| * W₁.realPeriod * (Hom.ofIsogeny φ).pointMapHom.range.index =
      Nat.card (Hom.ofIsogeny φ).pointMapHom.ker * W₂.realPeriod := by
  rw [AddSubgroup.index_eq_one.mpr (eq_top_iff.mpr fun P _ ↦ h P), Nat.cast_one, mul_one]
  exact abs_mul_realPeriod_eq_card_ker_mul_of_surjective φ hc fun P ↦
    (h P).imp fun Q hQ ↦ (Hom.pointMapHom_apply _ Q).symm.trans hQ

/-- With three real roots `e₁ < e₂ < e` of `Ψ₂Sq₂`, if the point `T` of order two over `e₁` is not
in the image of `φ`, the abscissas `x'` with `Ψ₂Sq₂(x') > 0` of the affine points of the image are
exactly `(e, ∞)`: a point of the image over `(e₁, e₂)` would put `T` in the image. -/
private theorem setOf_xCoord_mem_range_eq_Ioi (φ : Isogeny W₁ W₂) {e₁ e₂ e : ℝ} (h₁₂ : e₁ < e₂)
    (h₂ : e₂ < e) (hfac : W₂.Ψ₂Sq = C 4 * (X - C e₁) * (X - C e₂) * (X - C e)) {t : ℝ}
    (hT : W₂.Nonsingular e₁ t) (hψ : W₂.polynomialY.evalEval e₁ t = 0)
    (hTH : .some e₁ t hT ∉ (Hom.ofIsogeny φ).pointMapHom.range) :
    {y | 0 < W₂.Ψ₂Sq.eval y ∧
      ∃ P ∈ (Hom.ofIsogeny φ).pointMapHom.range, P ≠ 0 ∧ P.xCoord = y} = Ioi e := by
  have hpos : ∀ ⦃y⦄, e < y → 0 < W₂.Ψ₂Sq.eval y := fun y hy ↦
    (W₂.pos_eval_Ψ₂Sq_iff_of_eq_prod_three_roots h₁₂ h₂ hfac y).mpr (Or.inr hy)
  ext y
  refine ⟨fun ⟨hy, P, hPH, hP, hPy⟩ ↦ mem_Ioi.mpr (lt_of_not_ge fun hle ↦ hTH ?_), fun hy ↦ ?_⟩
  · have hlt : P.xCoord < e := hPy ▸ hle.lt_of_ne fun h ↦ by
      rw [h] at hy
      exact (hy.trans_eq (by simp [hfac])).false
    simpa using sub_mem (add_mem_range_pointMapHom_of_xCoord_lt φ h₁₂ h₂ hfac hT hψ hP hlt) hPH
  · obtain ⟨y', h⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq (hpos hy).le
    refine ⟨hpos hy, _, mem_range_pointMapHom_of_le_xCoord φ hpos (Point.some_ne_zero h) ?_,
      Point.some_ne_zero h, Point.xCoord_some h⟩
    rw [Point.xCoord_some]
    exact (mem_Ioi.mp hy).le

/-- **The real period under an isogeny.** Let `φ : W₁ → W₂` be an isogeny over `ℝ` with
`φ^*ω₂ = c ω₁`. Then `|c| Ω(W₁) · [W₂(ℝ) : φ(W₁(ℝ))] = #ker φ(ℝ) · Ω(W₂)`, the index being that of
the image of `φ` on real points. -/
theorem abs_mul_realPeriod_mul_index_eq_card_ker_mul (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    |c| * W₁.realPeriod * (Hom.ofIsogeny φ).pointMapHom.range.index =
      Nat.card (Hom.ofIsogeny φ).pointMapHom.ker * W₂.realPeriod := by
  set H := (Hom.ofIsogeny φ).pointMapHom.range
  obtain ⟨e, he, hpos⟩ := exists_isRoot_Ψ₂Sq_and_forall_lt_pos_eval W₂
  have hH (P : W₂.Point) (hP : P ≠ 0) (hle : e ≤ P.xCoord) : P ∈ H :=
    mem_range_pointMapHom_of_le_xCoord φ hpos hP hle
  by_cases hx : ∃ x₀ < e, 0 ≤ W₂.Ψ₂Sq.eval x₀
  swap
  · -- every real point other than `O` lies over `[e, ∞)`
    refine abs_mul_realPeriod_mul_index_eq_of_forall_mem φ hc fun P ↦ ?_
    rcases eq_or_ne P 0 with rfl | hP
    · exact zero_mem H
    obtain ⟨x, y, h, rfl⟩ := Point.exists_eq_some_of_ne_zero hP
    refine hH _ hP (le_of_not_gt fun hlt ↦ hx ⟨x, ?_,
      exists_equation_iff_nonneg_eval_Ψ₂Sq.mp ⟨y, h.1⟩⟩)
    rwa [Point.xCoord_some] at hlt
  obtain ⟨x₀, hx₀, h₀⟩ := hx
  obtain ⟨e₁, e₂, h₁₂, h₂, hfac⟩ := exists_Ψ₂Sq_eq_prod_three_roots he hpos hx₀ h₀
  -- the point `T` of order two over `e₁`; a point `P` off the image has `P + T` in it
  obtain ⟨t, hT⟩ := exists_nonsingular_of_nonneg_eval_Ψ₂Sq (W := W₂) (x := e₁) (by simp [hfac])
  have hψ : W₂.polynomialY.evalEval e₁ t = 0 := by
    simpa [hfac, WeierstrassCurve.ψ₂] using W₂.evalEval_ψ₂_sq hT.1
  have hnot (P : W₂.Point) (hP : P ∉ H) : P + .some e₁ t hT ∈ H := by
    have hP0 : P ≠ 0 := fun h ↦ hP (h ▸ zero_mem H)
    exact add_mem_range_pointMapHom_of_xCoord_lt φ h₁₂ h₂ hfac hT hψ hP0
      (lt_of_not_ge fun hle ↦ hP (hH P hP0 hle))
  by_cases hTH : .some e₁ t hT ∈ H
  · refine abs_mul_realPeriod_mul_index_eq_of_forall_mem φ hc fun P ↦ by_contra fun hP ↦ hP ?_
    simpa only [add_sub_cancel_right] using sub_mem (hnot P hP) hTH
  -- otherwise the image has index two, and its abscissas `(e, ∞)` carry half of the period
  have hidx : H.index = 2 := AddSubgroup.index_eq_two_iff.mpr ⟨.some e₁ t hT, fun P ↦ by
    by_cases hP : P ∈ H
    · exact Or.inr ⟨hP, fun h ↦ hTH (by simpa using sub_mem h hP)⟩
    · exact Or.inl ⟨hnot P hP, hP⟩⟩
  have hI₁ := congrArg ENNReal.toReal
    (ofReal_abs_mul_realPeriodLIntegral_eq_card_ker_mul_setLIntegral φ hc)
  have hI₂ := congrArg ENNReal.toReal
    (W₂.realPeriodLIntegral_eq_two_mul_setLIntegral_Ioi h₁₂ h₂ hfac)
  rw [setOf_xCoord_mem_range_eq_Ioi φ h₁₂ h₂ hfac hT hψ hTH, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg c), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hI₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hI₂
  rw [hidx, WeierstrassCurve.realPeriod_def, WeierstrassCurve.realPeriod_def, hI₂]
  push_cast
  linear_combination 4 * hI₁

end Index

end TauCeti.Isogeny
