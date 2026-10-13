/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
public import Mathlib.RingTheory.Henselian
-- Proof-only: the sum of two points with singular reduction at a nonsplit node.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.IndexTwo
-- Proof-only: the points with singular reduction when the reduction is singular at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
-- Proof-only: an anisotropic binary quadratic form over a finite field takes every value.
import TauCeti.FieldTheory.Finite.BinaryQuadratic
-- Proof-only: solutions and the discriminant under a translation.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange
-- Proof-only: index two from the sums of points outside a subgroup.
import TauCeti.GroupTheory.Index.Two
-- Proof-only: Hensel's lemma for a polynomial that is not monic.
import TauCeti.RingTheory.Henselian.Basic
-- Proof-only: a double root of the tangent quadratic over a perfect residue field.
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Points with singular reduction at a nonsplit node of even order

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪` and residue field
`k`, and let `W` be an elliptic curve over `F` with an integral model `W_O` over `O` whose reduction
is a node at the origin with no rational tangent direction: `a₃, a₄, a₆ ∈ 𝔪` and the tangent
quadratic `T² + a₁ T − a₂` has no root in `k`. The points with nonsingular reduction form the
subgroup `E₀(F)` of `W(F)` (`WeierstrassCurve.Affine.nonsingularReduction`), whose index divides
`2` (`WeierstrassCurve.Affine.index_nonsingularReduction_dvd_two_of_tangentQuadratic_no_roots`).
For a discrete valuation, on a minimal equation, this is nonsplit multiplicative reduction of type
`Iₙ` with `n = ord(Δ)`, and Tate's algorithm reports the local index `c_v = gcd(2, n)`
(Silverman, *Advanced Topics*, IV.9, Table 4.1). When `n` is odd every point has nonsingular
reduction (`WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_not_splits`). This file proves
the even case: when `Δ` is a unit times a square, `O` is Henselian and `k` is finite, some point
has singular reduction, so `[E(F) : E₀(F)] = 2`.

The point is found in three steps, carried out over the Henselian local ring `O` itself
(`WeierstrassCurve.exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots`).

* **Centring.** The singular point of the reduction lifts to a critical point `(r, t) ∈ 𝔪²` of the
  Weierstrass polynomial, and translating it to the origin makes `a₃ = a₄ = 0`. The two conditions
  combine to `6 r² + b₂ r + b₄ = 0`, a quadratic with unit linear coefficient `b₂`, which Hensel's
  lemma solves; then `t` is read off from either condition, as `2` or `a₁` is a unit. On the
  centred equation `y² + a₁ x y = x³ + a₂ x² + a₆` one has `Δ = −a₆ (b₂³ + 432 a₆)`, so `a₆` and
  `Δ` differ by a unit.
* **The residue conic.** Write `Δ` as a unit times `z²`, so that `a₆ = z² A` with `A` a unit.
  Along `(x, y) = (z X, z Y)` the centred equation divided by `z²` is
  `Y² + a₁ X Y − a₂ X² − z X³ = A`, whose reduction is the conic `Y² + a₁ X Y − a₂ X² = A`. Its
  quadratic part is anisotropic, and over a finite field it takes every value
  (`FiniteField.exists_sq_add_mul_mul_sub_mul_sq_eq`), so the conic has a point.
* **Lifting.** The residue conic is smooth, since the discriminant `b₂` of its quadratic part is a
  unit, so one of the partial derivatives is a unit at the point, and Hensel's lemma in that
  variable lifts it to a solution `(X, Y)` over `O`. The solution `(z X, z Y)` of the centred
  equation has both coordinates in `𝔪`, and so does the corresponding point of `W`, which therefore
  has singular reduction.

The finiteness of `k` is used only to find a point on the residue conic, which over a general
residue field need not exist.

## Main results

* `WeierstrassCurve.exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots`: over a
  Henselian local ring with finite residue field, an equation whose reduction is a nonsplit node
  at the origin, with `Δ` a unit times a square, has a solution in `𝔪 × 𝔪`. This is a converse of
  `WeierstrassCurve.exists_associated_sq_Δ_of_isSingular`.
* `WeierstrassCurve.Affine.exists_notMem_nonsingularReduction_of_tangentQuadratic_no_roots`: at a
  nonsplit node with `Δ` a unit times a square, over a Henselian valuation ring with finite residue
  field, some point has singular reduction.
* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_two_of_tangentQuadratic_no_roots`: in the
  same situation, `[E(F) : E₀(F)] = 2`.
* `Affine.index_nonsingularReduction_eq_two_of_isTateTerminal_I_of_tangentQuadratic_no_roots`:
  when Tate's algorithm stops with the symbol `I₂ₘ` and the tangent quadratic has no root, that
  is at nonsplit multiplicative reduction of even type, `[E(F) : E₀(F)] = 2`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve

/-- **Centring at a singular point of the reduction.** Over a Henselian local ring, if `a₃` and
`a₄` lie in the maximal ideal and `b₂` is a unit, then for some `r, t ∈ 𝔪` the translation
`x ↦ x + r`, `y ↦ y + t` makes `a₃ = a₄ = 0`: `(r, t)` is a critical point of the Weierstrass
polynomial. -/
private theorem exists_translate_a₃_eq_zero_and_a₄_eq_zero {R : Type*} [CommRing R]
    [HenselianLocalRing R] (W : WeierstrassCurve R) (h₃ : W.a₃ ∈ maximalIdeal R)
    (h₄ : W.a₄ ∈ maximalIdeal R) (hb₂ : IsUnit W.b₂) :
    ∃ r t : R, r ∈ maximalIdeal R ∧ t ∈ maximalIdeal R ∧
      (VariableChange.mk 1 r 0 t • W).a₃ = 0 ∧ (VariableChange.mk 1 r 0 t • W).a₄ = 0 := by
  simp only [variableChange_a₃, variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul]
  -- `a₁` times the first condition plus `2` times the second is `6 r² + b₂ r + b₄ = 0`
  have hb₄ : W.b₄ ∈ maximalIdeal R := by
    rw [b₄]
    exact add_mem ((maximalIdeal R).mul_mem_left _ h₄) ((maximalIdeal R).mul_mem_left _ h₃)
  obtain ⟨r, hr, hr𝔪⟩ := TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal
    (C 6 * X ^ 2 + C W.b₂ * X + C W.b₄) (a₀ := 0) (by simpa using hb₄) (by simpa using hb₂)
  have hr' : 6 * r ^ 2 + W.b₂ * r + W.b₄ = 0 := by simpa using hr.eq_zero
  rw [b₂, b₄] at hr'
  rw [sub_zero] at hr𝔪
  by_cases h2 : IsUnit (2 : R)
  · -- solve the first condition for `t`
    obtain ⟨i, hi⟩ := h2.exists_right_inv
    have e₃ : W.a₃ + W.a₁ * r + 2 * (-(W.a₃ + W.a₁ * r) * i) = 0 := by
      linear_combination (-(W.a₃ + W.a₁ * r)) * hi
    refine ⟨r, -(W.a₃ + W.a₁ * r) * i, hr𝔪, (maximalIdeal R).mul_mem_right _ (neg_mem
      (add_mem h₃ ((maximalIdeal R).mul_mem_left _ hr𝔪))), by linear_combination e₃, ?_⟩
    refine h2.mul_right_eq_zero.1 ?_
    linear_combination hr' - W.a₁ * e₃
  · -- `2 ∈ 𝔪`, so `a₁² ≡ b₂` is a unit; solve the second condition for `t`
    have h2𝔪 : (2 : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h2
    have ha₁ : IsUnit W.a₁ := by
      have hsq : W.a₁ ^ 2 = W.b₂ - 2 * (2 * W.a₂) := by rw [b₂]; ring
      rw [← residue_ne_zero_iff_isUnit] at hb₂ ⊢
      refine fun h0 ↦ hb₂ ?_
      have := congrArg (residue R) hsq
      rw [map_pow, h0, map_sub, (residue_eq_zero_iff _).2
        ((maximalIdeal R).mul_mem_right _ h2𝔪)] at this
      simpa using this.symm
    obtain ⟨j, hj⟩ := ha₁.exists_right_inv
    have e₄ : W.a₄ + 2 * W.a₂ * r - W.a₁ * ((W.a₄ + 2 * W.a₂ * r + 3 * r ^ 2) * j) +
        3 * r ^ 2 = 0 := by
      linear_combination (-(W.a₄ + 2 * W.a₂ * r + 3 * r ^ 2)) * hj
    refine ⟨r, (W.a₄ + 2 * W.a₂ * r + 3 * r ^ 2) * j, hr𝔪, (maximalIdeal R).mul_mem_right _
      (add_mem (add_mem h₄ ((maximalIdeal R).mul_mem_left _ hr𝔪))
        ((maximalIdeal R).mul_mem_left _ (Ideal.pow_mem_of_mem _ hr𝔪 2 two_pos))), ?_,
      by linear_combination e₄⟩
    refine ha₁.mul_right_eq_zero.1 ?_
    linear_combination hr' - 2 * e₄

/-- **Lifting a point of the residue conic.** Over a Henselian local ring, let `b₂ = a₁² + 4 a₂`
and `A` be units and `z ∈ 𝔪`. A solution modulo `𝔪` of `Y² + a₁ X Y − a₂ X² − z X³ = A` lifts to
a solution: the reduction is a smooth conic, so a partial derivative is a unit at the solution. -/
private theorem exists_conic_eq {R : Type*} [CommRing R] [HenselianLocalRing R]
    {a₁ a₂ z A X₀ Y₀ : R} (hb₂ : IsUnit (a₁ ^ 2 + 4 * a₂)) (hz : z ∈ maximalIdeal R)
    (hA : IsUnit A) (h₀ : Y₀ ^ 2 + a₁ * X₀ * Y₀ - a₂ * X₀ ^ 2 - z * X₀ ^ 3 - A ∈ maximalIdeal R) :
    ∃ X Y : R, Y ^ 2 + a₁ * X * Y - a₂ * X ^ 2 - z * X ^ 3 - A = 0 := by
  by_cases hY : IsUnit (2 * Y₀ + a₁ * X₀)
  · -- Hensel's lemma in `Y`
    obtain ⟨Y, hY', -⟩ := TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal
      (X ^ 2 + C (a₁ * X₀) * X - C (a₂ * X₀ ^ 2 + z * X₀ ^ 3 + A)) (a₀ := Y₀)
      (by convert h₀ using 1; simp; ring) (by convert hY using 1; simp [derivative_pow])
    exact ⟨X₀, Y, by linear_combination (by simpa using hY'.eq_zero :
      Y ^ 2 + a₁ * X₀ * Y - (a₂ * X₀ ^ 2 + z * X₀ ^ 3 + A) = 0)⟩
  · -- otherwise `∂/∂X` is a unit, since both partials in `𝔪` would force `X₀, Y₀, A ∈ 𝔪`
    have hX : IsUnit (-3 * z * X₀ ^ 2 - 2 * a₂ * X₀ + a₁ * Y₀) := by
      by_contra hX
      have h𝔪Y := (mem_maximalIdeal _).2 hY
      have h𝔪X := (mem_maximalIdeal _).2 hX
      have hzX : z * X₀ ^ 2 ∈ maximalIdeal R := (maximalIdeal R).mul_mem_right _ hz
      have hX₀ : X₀ ∈ maximalIdeal R := by
        refine (Ideal.unit_mul_mem_iff_mem _ hb₂).1 ?_
        rw [show (a₁ ^ 2 + 4 * a₂) * X₀ = a₁ * (2 * Y₀ + a₁ * X₀) -
            2 * (-3 * z * X₀ ^ 2 - 2 * a₂ * X₀ + a₁ * Y₀) - 6 * (z * X₀ ^ 2) by ring]
        exact sub_mem (sub_mem ((maximalIdeal R).mul_mem_left _ h𝔪Y)
          ((maximalIdeal R).mul_mem_left _ h𝔪X)) ((maximalIdeal R).mul_mem_left _ hzX)
      have hY₀ : Y₀ ∈ maximalIdeal R := by
        refine (Ideal.unit_mul_mem_iff_mem _ hb₂).1 ?_
        rw [show (a₁ ^ 2 + 4 * a₂) * Y₀ = 2 * a₂ * (2 * Y₀ + a₁ * X₀) +
            a₁ * (-3 * z * X₀ ^ 2 - 2 * a₂ * X₀ + a₁ * Y₀) + 3 * a₁ * (z * X₀ ^ 2) by ring]
        exact add_mem (add_mem ((maximalIdeal R).mul_mem_left _ h𝔪Y)
          ((maximalIdeal R).mul_mem_left _ h𝔪X)) ((maximalIdeal R).mul_mem_left _ hzX)
      refine (mem_maximalIdeal _).1 ?_ hA
      rw [show A = Y₀ * Y₀ + a₁ * X₀ * Y₀ - a₂ * X₀ * X₀ - z * X₀ ^ 3 -
          (Y₀ ^ 2 + a₁ * X₀ * Y₀ - a₂ * X₀ ^ 2 - z * X₀ ^ 3 - A) by ring]
      exact sub_mem (sub_mem (sub_mem (add_mem ((maximalIdeal R).mul_mem_left _ hY₀)
        ((maximalIdeal R).mul_mem_right _ (((maximalIdeal R).mul_mem_left _ hX₀))))
        ((maximalIdeal R).mul_mem_left _ hX₀)) ((maximalIdeal R).mul_mem_right _ hz)) h₀
    obtain ⟨X', hX', -⟩ := TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal
      (-C z * X ^ 3 - C a₂ * X ^ 2 + C (a₁ * Y₀) * X + C (Y₀ ^ 2 - A)) (a₀ := X₀)
      (by convert h₀ using 1; simp; ring) (by convert hX using 1; simp [derivative_pow]; ring)
    exact ⟨X', Y₀, by linear_combination (by simpa using hX'.eq_zero :
      -(z * X' ^ 3) - a₂ * X' ^ 2 + a₁ * Y₀ * X' + (Y₀ ^ 2 - A) = 0)⟩

/-- **A centred nonsplit node of even order has a solution reducing to it.** This is
`WeierstrassCurve.exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots` for an equation
with `a₃ = a₄ = 0` and `b₂` a unit. Then `Δ = −a₆ (b₂³ + 432 a₆)`, so `a₆ = z² A` with `A` a unit,
and the solution is `(z X, z Y)` for a solution `(X, Y)` of `Y² + a₁ X Y − a₂ X² − z X³ = A`,
lifted from a point of the residue conic `Y² + a₁ X Y − a₂ X² = A`. -/
private theorem exists_equation_mem_maximalIdeal_of_a₃_eq_zero_of_a₄_eq_zero {R : Type*}
    [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)] (W : WeierstrassCurve R)
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ ∈ maximalIdeal R) (hb₂ : IsUnit W.b₂)
    (hroot : ∀ t : ResidueField R, t ^ 2 + residue R W.a₁ * t - residue R W.a₂ ≠ 0) {z : R}
    (hΔ : Associated (z ^ 2) W.Δ) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ W.toAffine.Equation x y := by
  -- with `a₃ = a₄ = 0`, one has `b₄ = 0`, `b₆ = 4 a₆` and `b₈ = b₂ a₆`
  have hΔ' : W.Δ = -W.a₆ * (W.b₂ ^ 3 + 432 * W.a₆) := by
    simp only [Δ, b₂, b₄, b₆, b₈, h₃, h₄]
    ring
  have hw : IsUnit (W.b₂ ^ 3 + 432 * W.a₆) := by
    rw [← residue_ne_zero_iff_isUnit]
    simpa [(residue_eq_zero_iff _).2 h₆] using (residue_ne_zero_iff_isUnit _).2 hb₂
  -- so `a₆ = z² A` with `A` a unit, and `z ∈ 𝔪`
  obtain ⟨u, hu⟩ := hΔ
  set A : R := -(u * ↑hw.unit⁻¹)
  have hA : W.a₆ = z ^ 2 * A := by
    linear_combination (↑hw.unit⁻¹ : R) * (hu.trans hΔ') - W.a₆ * hw.mul_val_inv
  have hz : z ∈ maximalIdeal R := by
    refine (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 <|
      (Ideal.mul_unit_mem_iff_mem _ u.isUnit).1 ?_
    rw [hu, hΔ']
    exact (maximalIdeal R).mul_mem_right _ (neg_mem h₆)
  -- the residue conic `Y² + a₁ X Y − a₂ X² = A` has a point, which lifts
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_sq_add_mul_mul_sub_mul_sq_eq hroot (residue R A)
  obtain ⟨X₀, rfl⟩ := residue_surjective x
  obtain ⟨Y₀, rfl⟩ := residue_surjective y
  obtain ⟨X, Y, hXY⟩ := exists_conic_eq (A := A) (X₀ := X₀) (Y₀ := Y₀) (by rwa [← b₂]) hz
    (u.isUnit.mul hw.unit⁻¹.isUnit).neg (by
      refine (residue_eq_zero_iff _).1 ?_
      simp only [map_sub, map_add, map_mul, map_pow, (residue_eq_zero_iff _).2 hz]
      linear_combination hxy)
  refine ⟨z * X, z * Y, (maximalIdeal R).mul_mem_right _ hz, (maximalIdeal R).mul_mem_right _ hz,
    ?_⟩
  rw [Affine.equation_iff]
  linear_combination z ^ 2 * hXY + z * Y * h₃ - z * X * h₄ - hA

/-- **A nonsplit node of even order has a solution reducing to it.** Over a Henselian local ring
with finite residue field, let the reduction of `W` be singular at the origin, `a₃, a₄, a₆ ∈ 𝔪`,
with a tangent quadratic `T² + a₁ T − a₂` that has no root in the residue field, so that the
singular point is a node without rational tangent directions. If `Δ` is a unit times a square,
then some solution `(x, y)` of `W` has `x, y ∈ 𝔪`. This is a converse, for the normal form at the
origin, of `WeierstrassCurve.exists_associated_sq_Δ_of_isSingular`. -/
theorem exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots {R : Type*} [CommRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)] (W : WeierstrassCurve R)
    (h₃ : W.a₃ ∈ maximalIdeal R) (h₄ : W.a₄ ∈ maximalIdeal R) (h₆ : W.a₆ ∈ maximalIdeal R)
    (hroot : ∀ t : ResidueField R, t ^ 2 + residue R W.a₁ * t - residue R W.a₂ ≠ 0) {z : R}
    (hΔ : Associated (z ^ 2) W.Δ) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ W.toAffine.Equation x y := by
  have h0 {a : R} (ha : a ∈ maximalIdeal R) : residue R a = 0 := (residue_eq_zero_iff _).2 ha
  -- `b₂` is a unit, since otherwise the tangent quadratic has a double root in the perfect
  -- residue field
  have hb₂ : IsUnit W.b₂ := by
    by_contra hb
    obtain ⟨s, -, hs⟩ :=
      TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
        (a := W.a₁) (b := W.a₂) (by simpa only [b₂] using (mem_maximalIdeal _).2 hb)
    refine hroot (residue R s) ?_
    have hs0 := h0 hs
    simp only [map_sub, map_mul, map_pow] at hs0
    linear_combination -hs0
  -- translate the critical point `(r, t)` to the origin, which keeps the residues of `a₁`, `a₂`,
  -- `a₆` and `b₂`, and solve the centred equation
  obtain ⟨r, t, hr, ht, h₃', h₄'⟩ := W.exists_translate_a₃_eq_zero_and_a₄_eq_zero h₃ h₄ hb₂
  obtain ⟨x, y, hx, hy, hE⟩ :=
    (VariableChange.mk 1 r 0 t • W).exists_equation_mem_maximalIdeal_of_a₃_eq_zero_of_a₄_eq_zero
      h₃' h₄' ((residue_eq_zero_iff _).1 (by simp [variableChange_a₆, h0 hr, h0 ht, h0 h₆]))
      (by
        rw [← residue_ne_zero_iff_isUnit]
        simpa [variableChange_b₂, h0 hr] using (residue_ne_zero_iff_isUnit _).2 hb₂)
      (fun s ↦ by
        have ha₂ : residue R (VariableChange.mk 1 r 0 t • W).a₂ = residue R W.a₂ := by
          simp [variableChange_a₂, h0 hr]
        simpa [variableChange_a₁, ha₂] using hroot s)
      (by rwa [variableChange_translate_Δ])
  refine ⟨x + r, y + t, add_mem hx hr, add_mem hy ht, ?_⟩
  simpa using (Affine.variableChange_equation W (VariableChange.mk 1 r 0 t) x y).2 hE

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

/-- **At a nonsplit node with `Δ` a unit times a square, some point has singular reduction**, when
the valuation ring is Henselian, for instance complete, and its residue field is finite. Here the
reduction of the integral model is singular at the origin, `a₃, a₄, a₆ ∈ 𝔪`, and its tangent
quadratic `T² + a₁ T − a₂` has no root in the residue field. For a discrete valuation, on a minimal
equation, this is nonsplit multiplicative reduction of type `Iₙ` with `n` even. -/
theorem exists_notMem_nonsingularReduction_of_tangentQuadratic_no_roots
    [HenselianLocalRing v.valuationSubring] [Finite (ResidueField v.valuationSubring)]
    [W.IsElliptic]
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0)
    {z : v.valuationSubring} (hΔ : Associated (z ^ 2) (integralModel v.valuationSubring W).Δ) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v := by
  obtain ⟨x, y, hx, hy, hE⟩ :=
    exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots _ h₃ h₄ h₆ hroot hΔ
  have hF : W.Nonsingular x y :=
    W.equation_iff_nonsingular.1 ((equation_integralModel_iff v).1 hE)
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ hF).2
    ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 hx,
      (Valuation.mem_maximalIdeal_iff (v := v)).1 hy⟩⟩

/-- **At a nonsplit node with `Δ` a unit times a square, `[E(F) : E₀(F)] = 2`**, when the valuation
ring is Henselian, for instance complete, and its residue field is finite. Here the reduction of
the integral model is singular at the origin, `a₃, a₄, a₆ ∈ 𝔪`, and its tangent quadratic
`T² + a₁ T − a₂` has no root in the residue field. For a discrete valuation, on a minimal equation,
this is nonsplit multiplicative reduction of type `Iₙ` with `n` even, where Tate's algorithm reports
the local index `2`. -/
theorem index_nonsingularReduction_eq_two_of_tangentQuadratic_no_roots
    [HenselianLocalRing v.valuationSubring] [Finite (ResidueField v.valuationSubring)]
    [W.IsElliptic]
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0)
    {z : v.valuationSubring} (hΔ : Associated (z ^ 2) (integralModel v.valuationSubring W).Δ) :
    (W.nonsingularReduction v).index = 2 := by
  obtain ⟨P, hP⟩ :=
    exists_notMem_nonsingularReduction_of_tangentQuadratic_no_roots v h₃ h₄ h₆ hroot hΔ
  exact AddSubgroup.index_eq_two_of_add_mem
    (fun _ _ ↦ add_mem_nonsingularReduction_of_tangentQuadratic_no_roots v h₃ h₄ h₆ hroot) hP

/-- **At nonsplit multiplicative reduction of even type `I₂ₘ`, `[E(F) : E₀(F)] = 2`**, when the
valuation ring is Henselian, for instance complete, and its residue field is finite. This is the
local index `c_v = 2` that Tate's algorithm reports there. Here `ϖ` generates the maximal ideal of
the valuation ring, Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with
the symbol `I₂ₘ` (`ϖ ∣ a₃`, `ϖ ∣ a₄`, `ϖ ∣ a₆`, `ϖ ∤ b₂` and `ϖ²ᵐ ∥ Δ`), and the tangent quadratic
`T² + a₁ T − a₂` has no root in the residue field. -/
theorem index_nonsingularReduction_eq_two_of_isTateTerminal_I_of_tangentQuadratic_no_roots
    [HenselianLocalRing v.valuationSubring] [Finite (ResidueField v.valuationSubring)]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {m : ℕ}
    (hm : m ≠ 0) (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.I (2 * m)))
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0) :
    (W.nonsingularReduction v).index = 2 := by
  set Wo := integralModel v.valuationSubring W
  have key (a : v.valuationSubring) : a ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ a := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h
  obtain ⟨h₃, h₄, h₆, -, ⟨c, hc⟩, hn⟩ := isTateTerminal_I_add_one.1 h
  -- `Δ = ϖ^(2k + 2) c` with `c` a unit, since `ϖ^(2k + 3) ∤ Δ`
  have hcu : IsUnit c := by
    by_contra hcu
    obtain ⟨d, rfl⟩ := (key c).1 ((mem_maximalIdeal _).2 hcu)
    exact hn ⟨d, by rw [hc]; ring⟩
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.2 fun h0 ↦ hn <| by
    rw [← integralModel_Δ_eq v.valuationSubring W,
      map_eq_zero_iff _ (IsFractionRing.injective v.valuationSubring F)] at h0
    rw [h0]
    exact dvd_zero _⟩
  exact index_nonsingularReduction_eq_two_of_tangentQuadratic_no_roots v ((key _).2 h₃)
    ((key _).2 h₄) ((key _).2 h₆) hroot (z := ϖ ^ (k + 1))
    ⟨hcu.unit, by rw [hcu.unit_spec, hc]; ring⟩

end Affine

end WeierstrassCurve
