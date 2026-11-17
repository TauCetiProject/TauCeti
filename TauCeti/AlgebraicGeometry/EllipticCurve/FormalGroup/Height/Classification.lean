/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.RingTheory.FormalGroup.ZSMul
-- Proof-only: `charP_of_injective_algebraMap` to transfer characteristic to `AlgebraicClosure K`.
import Mathlib.Algebra.CharP.Algebra
-- Proof-only: `Polynomial.degree_quadratic` for roots of monic quadratics over `AlgebraicClosure`.
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
-- Proof-only: `nilradical_eq_zero` and `nilradical_eq_sInf` for reduction to prime quotients.
import Mathlib.RingTheory.Nilpotent.Lemmas
-- Proof-only: singular point existence and translation to the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
-- Proof-only: height and formal group law of `y² + a₁xy = x³`.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
-- Proof-only: invariance of formal-group height and order under Weierstrass variable changes.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
-- Proof-only: the formal series of `[n]` is `(formalGroup W).zsmulSeries n`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.MulByInt
-- Proof-only: the order of an isogeny's formal series is its inseparable degree.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Order
-- Proof-only: `deg [n] = n²`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
-- Proof-only: ordinarity and supersingularity via the separable degree of `[p]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
-- Proof-only: `PowerSeries.order_map_of_injective`.
import TauCeti.RingTheory.PowerSeries.Order

/-!
# Classification of formal-group heights of Weierstrass curves

This file classifies the height of the formal group `Ê` of every Weierstrass curve
`W : WeierstrassCurve K`, smooth or singular, over any field `K`, and establishes the sharp
multiplication-series order bounds over reduced commutative rings.

For an elliptic curve `W` over a field `K`, multiplication by `n ≠ 0` induces the formal-group
multiplication series `[n]_Ê` (`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`), whose
power-series order equals the inseparable degree of the isogeny `[n]`
(`TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`).
In prime characteristic `p`, `[p]` has degree `p²`, and its separable degree is `p` when `W` is
ordinary and `1` when `W` is supersingular. Consequently `[p]_Ê` has order `p` in the ordinary case
(height `1`) and order `p²` in the supersingular case (height `2`). Combining this with the
height-one criterion (`WeierstrassCurve.height_formalGroup_eq_one_iff`) gives the Hasse-invariant
characterization of ordinarity and supersingularity in every characteristic.

For a singular Weierstrass curve (`Δ = 0`) over a field, passing to the algebraic closure,
translating the singular point to the origin, and shearing one tangent line to `y = 0` transforms
`W` into a model `y² + a₁xy = x³` with `a₁⁴ = c₄`. Since the order of `[m]_Ê` and the height of
`Ê` are invariant under field extensions and changes of variables, a nodal curve
(`Δ = 0`, `c₄ ≠ 0`) has multiplicative formal group (order of `[m]_Ê` at most `m ≤ m²`, and height
`1` in prime characteristic), while a cuspidal curve (`Δ = 0`, `c₄ = 0`) has additive formal group
(`[m]_Ê = 0` whenever `(m : K) = 0`, and height `⊤`). Reducing modulo prime ideals carries the
order bound `order ([m]_Ê) ≤ m²` (for `c₄ ≠ 0 ∨ Δ ≠ 0`) and the vanishing `[m]_Ê = 0` (for
`Δ = 0`, `c₄ = 0`, `m = 0`) to every reduced commutative ring.

In particular, in characteristic `p`, the formal group of every Weierstrass curve has height `1`,
`2`, or `⊤`; for every `p ≠ 0` with `(p : K) = 0`, the height is infinite exactly when
`c₄ = 0 ∧ Δ = 0`, and in prime characteristic `p` it is at most `2` exactly when
`c₄ ≠ 0 ∨ Δ ≠ 0`.

## Main results

* `WeierstrassCurve.order_zsmulSeries_formalGroup_eq_inseparableDegree` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup_eq_inseparableDegree`: for an elliptic curve and
  nonzero `n`, the order of `[n]_Ê` equals the inseparable degree of the isogeny `[n]`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one` and
  `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: an elliptic curve in
  characteristic `p` is ordinary exactly when `Ê` has height `1`, and supersingular exactly when
  `Ê` has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the formal group of an elliptic curve in prime
  characteristic `p` has height `1` or `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero` and
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`: an elliptic curve in
  characteristic `p` is ordinary (resp. supersingular) exactly when the coefficient of `Tᵖ⁻¹` in
  its invariant differential is nonzero (resp. zero).
* `WeierstrassCurve.order_nsmulSeries_formalGroup_le_sq`: over any reduced commutative ring, if
  `m ≠ 0` and `c₄ ≠ 0 ∨ Δ ≠ 0`, then `[m]_Ê` has order at most `m²`.
* `WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero`: over any reduced
  commutative ring, if `Δ = 0`, `c₄ = 0`, and `(m : R) = 0`, then `[m]_Ê = 0`.
* `WeierstrassCurve.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero` and
  `WeierstrassCurve.height_formalGroup_ne_top`: for `p ≠ 0`, any smooth or nodal Weierstrass curve
  (in particular any elliptic curve) has finite formal-group height.
* `WeierstrassCurve.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero` and
  `WeierstrassCurve.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero`: a nodal Weierstrass
  curve in prime characteristic has height `1`, and a cuspidal Weierstrass curve with `(p : K) = 0`
  has height `⊤`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_or_eq_top`,
  `WeierstrassCurve.height_formalGroup_eq_top_iff`, and
  `WeierstrassCurve.height_formalGroup_le_two_iff`: complete classification of formal-group heights
  of arbitrary Weierstrass curves over a field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7, V.3 and V.4.
* N. M. Katz, *p-adic properties of modular schemes and modular forms*, in *Modular functions of
  one variable III*, Lecture Notes in Math. 350, Springer (1973), Chapter 2.
-/

public section

namespace WeierstrassCurve

/-- Every monic quadratic polynomial over an algebraically closed field has a root. -/
private theorem exists_root_quadratic {L : Type*} [Field L] [IsAlgClosed L] (b c : L) :
    ∃ r : L, r ^ 2 + b * r + c = 0 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : L) * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c)
    (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  exact ⟨r, by simpa [Polynomial.IsRoot.def] using hr⟩

section Elliptic

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- For an elliptic curve `W` and `n ≠ 0`, the power-series order of `[n]_Ê` equals the
inseparable degree of the multiplication-by-`n` isogeny. -/
theorem order_zsmulSeries_formalGroup_eq_inseparableDegree [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero W hn,
    TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree]

/-- For an elliptic curve `W` and `m ≠ 0`, the power-series order of `[m]_Ê` equals the
inseparable degree of the multiplication-by-`m` isogeny. -/
theorem order_nsmulSeries_formalGroup_eq_inseparableDegree [W.IsElliptic] {m : ℕ} (hm : m ≠ 0) :
    ((formalGroup W).nsmulSeries m).order =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
        (mod_cast hm : (m : ℤ) ≠ 0)).inseparableDegree := by
  rw [← FormalGroup.zsmulSeries_natCast, order_zsmulSeries_formalGroup_eq_inseparableDegree]

/-- Every elliptic curve has a nonzero geometric point, so it is ordinary at `0`. -/
private theorem isOrdinary_zero [W.IsElliptic] : W.IsOrdinary 0 := by
  classical
  set W' := W.baseChange (AlgebraicClosure K)
  have : W'.IsElliptic := inferInstanceAs (W.map _).IsElliptic
  obtain ⟨y, hy⟩ := exists_root_quadratic W'.a₃ (-W'.a₆)
  have heq : W'.toAffine.Equation 0 y := by
    rw [Affine.equation_iff]
    linear_combination hy
  exact isOrdinary_iff_exists.mpr
    ⟨.some 0 y (W'.toAffine.equation_iff_nonsingular.mp heq), zero_nsmul _, by simp⟩

variable {p : ℕ}

/-- **Ordinary curves have formal-group height one**: in prime characteristic `p`, an elliptic
curve is ordinary exactly when its formal group has height `1` (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one [W.IsElliptic] [hp : Fact p.Prime] [CharP K p] :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  rw [isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p W hp.out,
    ← Nat.cast_one, FormalGroup.height_eq_natCast_iff,
    order_nsmulSeries_formalGroup_eq_inseparableDegree W hp.out.ne_zero,
    ENat.natCast_inj, pow_one]
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
    (mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)
  have hmul : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq]
  exact ⟨fun h ↦ mul_left_cancel₀ hp.out.ne_zero (h ▸ hmul),
    fun h ↦ mul_right_cancel₀ hp.out.ne_zero (h ▸ hmul)⟩

/-- **Supersingular curves have formal-group height two**: in prime characteristic `p`, an elliptic
curve is supersingular exactly when its formal group has height `2` (Silverman V.3.1). -/
theorem isSupersingular_iff_height_formalGroup_eq_two [W.IsElliptic] [hp : Fact p.Prime]
    [CharP K p] : W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  rw [isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p W,
    ← Nat.cast_two, FormalGroup.height_eq_natCast_iff,
    order_nsmulSeries_formalGroup_eq_inseparableDegree W hp.out.ne_zero, ENat.natCast_inj]
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
    (mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)
  have hmul : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, one_mul] at hmul
    exact hmul
  · rw [h] at hmul
    exact mul_right_cancel₀ (pow_ne_zero 2 hp.out.ne_zero) (by rwa [one_mul])

/-- **Height dichotomy for elliptic curves**: over a field of prime characteristic `p`, the formal
group of an elliptic curve has height `1` or `2` (Silverman IV.7.4). -/
theorem height_formalGroup_eq_one_or_eq_two [W.IsElliptic] [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsOrdinary p
  · exact Or.inl ((isOrdinary_iff_height_formalGroup_eq_one W).mp h)
  · exact Or.inr ((isSupersingular_iff_height_formalGroup_eq_two W).mp (not_isOrdinary.mp h))

/-- **The height-two bound for elliptic curves**: over a field of prime characteristic `p`, the
formal group of an elliptic curve has height at most `2`. -/
theorem height_formalGroup_le_two [W.IsElliptic] [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p ≤ 2 := by
  rcases height_formalGroup_eq_one_or_eq_two W with h | h <;> simp [h]

/-- **The Hasse invariant criterion for ordinarity**: over a field of characteristic `p`, an
elliptic curve is ordinary exactly when the coefficient of `Tᵖ⁻¹` in its invariant differential is
nonzero. -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero [W.IsElliptic] [CharP K p] :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [isOrdinary_iff_height_formalGroup_eq_one, height_formalGroup_eq_one_iff]
  · simp [W.isOrdinary_zero]

/-- **The Hasse invariant criterion for supersingularity**: over a field of characteristic `p`, an
elliptic curve is supersingular exactly when the coefficient of `Tᵖ⁻¹` in its invariant
differential vanishes. -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero [W.IsElliptic] [CharP K p] :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_ne_iff]

end Elliptic

section Singular

/-- Every singular Weierstrass curve over an algebraically closed field is equivalent under a
variable change to a curve `y² + a₁xy = x³` with `a₁⁴ = c₄`. -/
private theorem exists_variableChange_singular_normalForm {L : Type*} [Field L] [IsAlgClosed L]
    (W : WeierstrassCurve L) (hΔ : W.Δ = 0) :
    ∃ C : VariableChange L,
      (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 ∧ (C • W).a₄ = 0 ∧ (C • W).a₆ = 0 ∧
        (C • W).a₁ ^ 4 = W.c₄ := by
  obtain ⟨x₀, y₀, hsing⟩ := W.toAffine.exists_isSingular_of_Δ_eq_zero hΔ
  let C₁ : VariableChange L := ⟨1, x₀, 0, y₀⟩
  set W₁ := C₁ • W with hW₁
  have hsing₁ : W₁.toAffine.IsSingular 0 0 :=
    (Affine.isSingular_iff_variableChange W.toAffine x₀ y₀).mp hsing
  obtain ⟨h₆, h₄, h₃⟩ := (Affine.isSingular_zero W₁.toAffine).mp hsing₁
  obtain ⟨α, hα⟩ := exists_root_quadratic W₁.a₁ (-W₁.a₂)
  let C₂ : VariableChange L := ⟨1, 0, α, 0⟩
  have ha₂ : ((C₂ * C₁) • W).a₂ = 0 := by
    rw [mul_smul, ← hW₁, variableChange_a₂]
    simp only [C₂, inv_one, Units.val_one, one_pow, one_mul, mul_zero, add_zero]
    linear_combination -hα
  have ha₃ : ((C₂ * C₁) • W).a₃ = 0 := by
    rw [mul_smul, ← hW₁]
    simp [C₂, variableChange_a₃, h₃]
  have ha₄ : ((C₂ * C₁) • W).a₄ = 0 := by
    rw [mul_smul, ← hW₁]
    simp [C₂, variableChange_a₄, h₃, h₄]
  have ha₆ : ((C₂ * C₁) • W).a₆ = 0 := by
    rw [mul_smul, ← hW₁]
    simp [C₂, variableChange_a₆, h₆]
  refine ⟨C₂ * C₁, ha₂, ha₃, ha₄, ha₆, ?_⟩
  calc ((C₂ * C₁) • W).a₁ ^ 4 = ((C₂ * C₁) • W).c₄ := by
        simp only [c₄, b₂, b₄, ha₂, ha₃, ha₄]
        ring
    _ = W.c₄ := by
        rw [mul_smul, variableChange_c₄, variableChange_c₄]
        simp [C₁, C₂]

/-- Field-level order bound: for a smooth or nodal Weierstrass curve over a field and `m ≠ 0`,
`[m]_Ê` has order at most `m²`. -/
private theorem order_nsmulSeries_formalGroup_le_sq_field {K : Type*} [Field K]
    (W : WeierstrassCurve K) {m : ℕ} (hm : m ≠ 0) (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    ((formalGroup W).nsmulSeries m).order ≤ (m ^ 2 : ℕ) := by
  by_cases hΔ : W.Δ = 0
  · have hc₄ : W.c₄ ≠ 0 := h.resolve_right (not_not.mpr hΔ)
    let ι := algebraMap K (AlgebraicClosure K)
    obtain ⟨C, h₂, h₃, h₄, h₆, h₁⟩ :=
      exists_variableChange_singular_normalForm (W.map ι) (by simp [hΔ])
    have ha₁ : (C • W.map ι).a₁ ≠ 0 := fun h0 ↦ hc₄ (ι.injective (by
      rw [map_zero, ← map_c₄, ← h₁, h0, zero_pow (by decide)]))
    have hord : ((formalGroup W).nsmulSeries m).order =
        ((FormalGroup.𝔾ₘ : FormalGroup (AlgebraicClosure K)).nsmulSeries m).order := by
      rw [← PowerSeries.order_map_of_injective ι.injective, FormalGroup.map_nsmulSeries,
        ← map_formalGroup, ← VariableChange.formalCoordinate_smul_formalGroup C (W.map ι),
        ← (FormalGroup.smulIso (C.formalCoordinate (W.map ι)) _).order_nsmulSeries_eq m,
        formalGroup_eq_homothety_smul_𝔾ₘ (Units.mk0 _ ha₁) rfl h₂ h₃ h₄ h₆,
        ← (FormalGroup.smulIso _ FormalGroup.𝔾ₘ).order_nsmulSeries_eq m]
    rw [hord]
    have hcoeff : PowerSeries.coeff m
        ((FormalGroup.𝔾ₘ : FormalGroup (AlgebraicClosure K)).nsmulSeries m) = 1 := by
      rw [FormalGroup.nsmulSeries_𝔾ₘ, map_sub, add_comm, add_pow]
      simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_one, hm]
    exact (PowerSeries.order_le m (by rw [hcoeff]; exact one_ne_zero)).trans
      (by exact_mod_cast Nat.le_self_pow (by decide) m)
  · have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    rw [W.order_nsmulSeries_formalGroup_eq_inseparableDegree hm, Nat.cast_le]
    set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine (mod_cast hm : (m : ℤ) ≠ 0)
    have hmul : φ.separableDegree * φ.inseparableDegree = m ^ 2 := by
      rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
        Int.natAbs_natCast]
    have hsep : 1 ≤ φ.separableDegree := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
      rw [h0, zero_mul] at hmul
      exact pow_ne_zero 2 hm hmul.symm
    calc φ.inseparableDegree = 1 * φ.inseparableDegree := (one_mul _).symm
      _ ≤ φ.separableDegree * φ.inseparableDegree := Nat.mul_le_mul_right _ hsep
      _ = m ^ 2 := hmul

/-- Field-level vanishing at a cusp: if `Δ = 0`, `c₄ = 0`, and `(m : K) = 0`, then `[m]_Ê = 0`. -/
private theorem nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero_field {K : Type*}
    [Field K] (W : WeierstrassCurve K) {m : ℕ} (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) (hm : (m : K) = 0) :
    (formalGroup W).nsmulSeries m = 0 := by
  let ι := algebraMap K (AlgebraicClosure K)
  obtain ⟨C, h₂, h₃, h₄, h₆, h₁⟩ :=
    exists_variableChange_singular_normalForm (W.map ι) (by simp [hΔ])
  have ha₁ : (C • W.map ι).a₁ = 0 := by simpa [hc₄] using h₁
  have hm' : (m : AlgebraicClosure K) = 0 := by rw [← map_natCast ι, hm, map_zero]
  rw [← PowerSeries.order_eq_top, ← PowerSeries.order_map_of_injective ι.injective,
    FormalGroup.map_nsmulSeries, ← map_formalGroup,
    ← VariableChange.formalCoordinate_smul_formalGroup C (W.map ι),
    ← (FormalGroup.smulIso (C.formalCoordinate (W.map ι)) _).order_nsmulSeries_eq m,
    formalGroup_eq_𝔾ₐ ha₁ h₂ h₃ h₄ h₆, FormalGroup.nsmulSeries_𝔾ₐ,
    ← map_natCast PowerSeries.C, hm', map_zero, zero_mul, PowerSeries.order_zero]

/-- **Order bound for `[m]_Ê` over reduced rings**: for any smooth or nodal Weierstrass curve over
a reduced commutative ring (`c₄ ≠ 0 ∨ Δ ≠ 0`) and any `m ≠ 0`, the multiplication-by-`m` series
has order at most `m²`. -/
theorem order_nsmulSeries_formalGroup_le_sq {R : Type*} [CommRing R] [IsReduced R]
    (W : WeierstrassCurve R) {m : ℕ} (hm : m ≠ 0) (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    ((formalGroup W).nsmulSeries m).order ≤ (m ^ 2 : ℕ) := by
  have hex : ∃ P : Ideal R, P.IsPrime ∧ (W.c₄ ∉ P ∨ W.Δ ∉ P) := by
    by_contra hall
    push Not at hall
    have hmem (x : R) (hx : ∀ P : Ideal R, P.IsPrime → x ∈ P) : x = 0 := by
      have : x ∈ nilradical R := by
        rw [nilradical_eq_sInf]
        exact Ideal.mem_sInf.mpr fun P hP ↦ hx P hP
      rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact h.elim (fun hc₄ ↦ hc₄ (hmem _ fun P hP ↦ (hall P hP).1))
      (fun hΔ ↦ hΔ (hmem _ fun P hP ↦ (hall P hP).2))
  obtain ⟨P, hP, hPmem⟩ := hex
  let _ : P.IsPrime := hP
  let f : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hf_ne {x : R} (hx : x ∉ P) : f x ≠ 0 := by
    intro h0
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P)) (by simpa [f] using h0)
  have hmap : (W.map f).c₄ ≠ 0 ∨ (W.map f).Δ ≠ 0 :=
    hPmem.imp (fun hc₄ ↦ by rw [map_c₄]; exact hf_ne hc₄) (fun hΔ ↦ by rw [map_Δ]; exact hf_ne hΔ)
  calc ((formalGroup W).nsmulSeries m).order
      ≤ (PowerSeries.map f ((formalGroup W).nsmulSeries m)).order := PowerSeries.le_order_map f
    _ = ((formalGroup (W.map f)).nsmulSeries m).order := by
        rw [FormalGroup.map_nsmulSeries, ← map_formalGroup]
    _ ≤ (m ^ 2 : ℕ) := order_nsmulSeries_formalGroup_le_sq_field (W.map f) hm hmap

/-- **Vanishing of `[m]_Ê` at a cusp over reduced rings**: over a reduced commutative ring, if
`Δ = 0`, `c₄ = 0`, and `(m : R) = 0`, then `[m]_Ê = 0`. -/
theorem nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero {R : Type*} [CommRing R]
    [IsReduced R] (W : WeierstrassCurve R) {m : ℕ} (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0)
    (hm : (m : R) = 0) : (formalGroup W).nsmulSeries m = 0 := by
  ext k
  rw [map_zero]
  suffices PowerSeries.coeff k ((formalGroup W).nsmulSeries m) ∈ nilradical R by
    rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro P hP
  let _ : P.IsPrime := hP
  let f : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hz := nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero_field (W.map f)
    (by simp [hΔ]) (by simp [hc₄]) (by rw [← map_natCast f, hm, map_zero])
  have hk : f (PowerSeries.coeff k ((formalGroup W).nsmulSeries m)) = 0 := by
    rw [← FormalGroup.coeff_nsmulSeries_map, ← map_formalGroup, hz, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P)) (by simpa [f] using hk))

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {p : ℕ}

/-- Over any field and for any `p ≠ 0`, a smooth or nodal Weierstrass curve (`c₄ ≠ 0 ∨ Δ ≠ 0`) has
finite formal-group height. -/
theorem height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero (hp : p ≠ 0)
    (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) : (formalGroup W).height p ≠ ⊤ := by
  rw [ne_eq, FormalGroup.height_eq_top_iff]
  intro h0
  have hord := W.order_nsmulSeries_formalGroup_le_sq hp h
  simp [h0] at hord

/-- Over any field and for any `p ≠ 0`, the formal group of an elliptic curve has finite height. -/
theorem height_formalGroup_ne_top [W.IsElliptic] (hp : p ≠ 0) :
    (formalGroup W).height p ≠ ⊤ :=
  W.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero hp (Or.inr W.isUnit_Δ.ne_zero)

/-- **Nodal curves have formal-group height one**: over a field of prime characteristic `p`, a
singular Weierstrass curve with `c₄ ≠ 0` has formal group of height `1`. -/
theorem height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero [Fact p.Prime] [CharP K p]
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) : (formalGroup W).height p = 1 := by
  let ι := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_algebraMap ι.injective p
  obtain ⟨C, h₂, h₃, h₄, h₆, h₁⟩ :=
    exists_variableChange_singular_normalForm (W.map ι) (by simp [hΔ])
  have ha₁ : (C • W.map ι).a₁ ≠ 0 := fun h0 ↦ hc₄ (ι.injective (by
    rw [map_zero, ← map_c₄, ← h₁, h0, zero_pow (by decide)]))
  rw [← FormalGroup.height_map (formalGroup W) ι p, ← map_formalGroup,
    ← VariableChange.height_formalGroup_variableChange C]
  exact height_formalGroup_eq_one ha₁ h₂ h₃ h₄ h₆

/-- **Cuspidal curves have infinite formal-group height**: over a field with `(p : K) = 0`, a
singular Weierstrass curve with `c₄ = 0` has formal group of height `⊤`. -/
theorem height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0)
    (hp : (p : K) = 0) : (formalGroup W).height p = ⊤ :=
  ((formalGroup W).height_eq_top_iff).mpr
    (W.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ hp)

/-- **Complete height trichotomy for Weierstrass curves**: over a field of characteristic `p`, the
formal group of any Weierstrass curve has height `1`, `2`, or `⊤`. -/
theorem height_formalGroup_eq_one_or_eq_two_or_eq_top [CharP K p] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ∨ (formalGroup W).height p = ⊤ := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    by_cases hΔ : W.Δ = 0
    · by_cases hc₄ : W.c₄ = 0
      · exact Or.inr (Or.inr
          (W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ (CharP.cast_eq_zero K p)))
      · exact Or.inl (W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ hc₄)
    · have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      rcases W.height_formalGroup_eq_one_or_eq_two with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (((formalGroup W).height_eq_top_iff).mpr (by simp)))

/-- Over a field with `p ≠ 0` and `(p : K) = 0`, the formal group of a Weierstrass curve has
infinite height exactly when the curve is cuspidal (`c₄ = 0` and `Δ = 0`). -/
theorem height_formalGroup_eq_top_iff (hp : p ≠ 0) (hpK : (p : K) = 0) :
    (formalGroup W).height p = ⊤ ↔ W.c₄ = 0 ∧ W.Δ = 0 := by
  refine ⟨fun htop ↦ ?_, fun ⟨hc₄, hΔ⟩ ↦
    W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ hpK⟩
  by_contra h
  rw [not_and_or] at h
  exact W.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero hp h htop

/-- **Height-two locus for Weierstrass curves**: over a field of prime characteristic `p`, the
formal group of a Weierstrass curve has height at most `2` exactly when it is smooth or nodal
(`c₄ ≠ 0 ∨ Δ ≠ 0`). -/
theorem height_formalGroup_le_two_iff [hp : Fact p.Prime] [CharP K p] :
    (formalGroup W).height p ≤ 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  rw [← not_and_or, ← W.height_formalGroup_eq_top_iff hp.out.ne_zero (CharP.cast_eq_zero K p)]
  refine ⟨fun hle htop ↦ by simp [htop] at hle, fun hntop ↦ ?_⟩
  rcases W.height_formalGroup_eq_one_or_eq_two_or_eq_top with h | h | h
  · simp [h]
  · simp [h]
  · exact absurd h hntop

end Singular

end WeierstrassCurve
