/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Wronskian
public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod
-- Proof-only: the quotient rule, and the derivative of a polynomial function.
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
-- Proof-only: the real points over an abscissa, and the finite kernel of an isogeny on points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Real
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
-- Proof-only: the image of an open set under `N / D` is σ-compact, hence measurable, and the
-- integrand `1 / √Ψ₂Sq` is measurable.
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Topology.Algebra.Polynomial

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

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.5.
-/

public section

open MeasureTheory Polynomial Set WeierstrassCurve.Affine
open scoped ENNReal

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
  · convert HasDerivAt.div (φ.xRatFunc.num.hasDerivAt x) (φ.xRatFunc.denom.hasDerivAt x) hD
      using 1
    rw [oddPart, wronskian]
    simp only [eval_sub, eval_mul]
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
    (ne_zero_of_pullbackDifferential_eq_smul φ hc) (countable_exceptional φ hc)
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
  refine W₁.abs_mul_realPeriod_eq_of_ae_encard_eq (ne_zero_of_pullbackDifferential_eq_smul φ hc)
    (countable_exceptional φ hc)
    (s := oddPart φ c)
    (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) hn <;>
  · simp only [mem_union, mem_ofPred_eq, IsRoot.def, not_or] at hx
    have := substitution_hypotheses φ hc hx.1 hx.2
    tauto

section Fibres

/-- Over each `x` with `Ψ₂Sq(x) > 0`, an elliptic curve over `ℝ` has a real point. -/
private theorem exists_nonsingular {W : WeierstrassCurve.Affine ℝ} [W.IsElliptic] {x : ℝ}
    (hx : 0 < W.Ψ₂Sq.eval x) : ∃ y, W.Nonsingular x y :=
  let ⟨y, h⟩ := exists_equation_iff_nonneg_eval_Ψ₂Sq.mpr hx.le
  ⟨y, equation_iff_nonsingular.mp h⟩

/-- A real point over an `x` with `Ψ₂Sq(x) > 0` is not of order two. -/
private theorem neg_some_ne_some {W : WeierstrassCurve.Affine ℝ} {x y : ℝ} (h : W.Nonsingular x y)
    (hx : 0 < W.Ψ₂Sq.eval x) : -Point.some x y h ≠ .some x y h :=
  Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq.mpr
    ⟨Point.some_ne_zero h, (Point.xCoord_some h).symm ▸ hx⟩

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
  obtain ⟨y, h⟩ := exists_nonsingular hx
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
  rw [encard, ← ENat.card_eq_coe_natCard,
    show (Hom.ofIsogeny φ).pointMap = (Hom.ofIsogeny φ).pointMapHom from
      funext fun Q ↦ (Hom.pointMapHom_apply _ Q).symm]
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
    · obtain ⟨y', h⟩ := exists_nonsingular hx
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
  obtain ⟨y', h⟩ := exists_nonsingular hy
  have hP := neg_some_ne_some h hy
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
  obtain ⟨y', h⟩ := exists_nonsingular hy
  rw [inter_preimage_eq_setOf φ hy0]
  have he := encard_setOf_eval_div_eq_xCoord_of_mem_range φ (neg_some_ne_some h hy)
    ((hφ (.some y y' h)).imp fun Q hQ ↦ (Hom.pointMapHom_apply _ Q).trans hQ)
  rwa [Point.xCoord_some] at he

end Fibres

end TauCeti.Isogeny
