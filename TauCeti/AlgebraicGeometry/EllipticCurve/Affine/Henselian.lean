/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ComputeDegree
-- Proof-only: finite-field norms supply points on the residue conic.
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.Algebra.QuadraticAlgebra.NormTrace
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot
-- Proof-only: Hensel's lemma for a polynomial that is not monic.
import TauCeti.RingTheory.Henselian.Basic

/-!
# Hensel's lemma for Weierstrass equations

Let `R` be a Henselian local ring with residue field `k`, and let `W` be a Weierstrass curve over
`R`. Every nonsingular point of the reduced curve `W_k = W ⊗ k` is the residue of a nonsingular
point of `W`. This is Hensel's lemma applied to the Weierstrass equation in whichever variable has
a nonvanishing partial derivative at the point of `W_k`.

The singular point of `W_k` lifts too, when it is a node at the origin: if `a₃, a₄ ∈ 𝔪` and `b₂` is
a unit, then the two partial derivatives of the Weierstrass polynomial vanish at some `(r, t) ∈ 𝔪²`,
and the translation `x ↦ x + r`, `y ↦ y + t` makes `a₃ = a₄ = 0`. The two conditions combine to
`6 r² + b₂ r + b₄ = 0`, a quadratic with unit linear coefficient `b₂`, which Hensel's lemma solves;
then `t` is read off from either condition, as `2` or `a₁` is a unit.

For a finite residue field and a nonsplit tangent quadratic, a discriminant that is a unit times
a square gives a solution with both coordinates in the maximal ideal. The centred case reduces
to a residue conic, whose points are obtained from surjectivity of the finite-field norm; the
general case follows by the translation above.

## Main results

* `WeierstrassCurve.Affine.exists_nonsingular_residue_eq`: over a Henselian local ring, every
  nonsingular point of the reduced curve is the residue of a nonsingular point.
* `WeierstrassCurve.exists_translate_a₃_eq_zero_and_a₄_eq_zero`: over a Henselian local ring, if
  `a₃, a₄ ∈ 𝔪` and `b₂` is a unit, a translation by an element of `𝔪²` makes `a₃ = a₄ = 0`.

* `WeierstrassCurve.exists_equation_mem_maximalIdeal_of_a₃_eq_zero_of_a₄_eq_zero`: the centred
  nonsplit equation with even discriminant order has a solution in the maximal ideal.
* `WeierstrassCurve.exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots`: the same
  lifting result for the uncentred equation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [HenselianLocalRing R] {W : Affine R}

/-- **Nonsingular points lift along a Henselian local ring.** Over a Henselian local ring `R`, every
nonsingular point of the reduction of a Weierstrass curve `W` to the residue field is the residue
of a nonsingular point of `W`. -/
theorem exists_nonsingular_residue_eq {x₀ y₀ : R}
    (h : (W.map (residue R)).Nonsingular (residue R x₀) (residue R y₀)) :
    ∃ x y : R, W.Nonsingular x y ∧ residue R x = residue R x₀ ∧ residue R y = residue R y₀ := by
  -- a solution over `R` whose residues are `(res x₀, res y₀)` is nonsingular over `R`, since one
  -- of its partial derivatives has nonzero residue
  have hns {x y : R} (he : W.Equation x y) (hx : residue R x = residue R x₀)
      (hy : residue R y = residue R y₀) : W.Nonsingular x y := by
    rw [← hx, ← hy] at h
    simp only [Nonsingular, map_polynomialX, map_polynomialY, map_mapRingHom_evalEval] at h
    exact ⟨he, h.2.imp (fun hr h0 ↦ hr (by rw [h0, map_zero]))
      (fun hr h0 ↦ hr (by rw [h0, map_zero]))⟩
  rw [nonsingular_iff'] at h
  obtain ⟨he, hX | hY⟩ := h
  · -- lift the `x`-coordinate as a simple root of the monic cubic `W(X, y₀)`, up to sign
    rw [equation_iff'] at he
    set g : R[X] := X ^ 3 + C W.a₂ * X ^ 2 + C (W.a₄ - W.a₁ * y₀) * X +
      C (W.a₆ - y₀ ^ 2 - W.a₃ * y₀) with hg
    have hgm : g.Monic := by rw [hg]; monicity!
    obtain ⟨x, hx, hxx₀⟩ := HenselianLocalRing.is_henselian g hgm x₀
      (by
        rw [← residue_eq_zero_iff, ← neg_eq_zero, ← he]
        simp [hg]
        ring)
      (by
        rw [← residue_ne_zero_iff_isUnit, ← neg_ne_zero]
        convert hX using 1
        simp [hg, derivative_pow, map_ofNat]
        ring)
    have hres : residue R x = residue R x₀ := by
      rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine ⟨x, y₀, hns ?_ hres rfl, hres, rfl⟩
    rw [equation_iff', ← neg_eq_zero, ← hx.eq_zero]
    simp [hg]
    ring
  · -- lift the `y`-coordinate as a simple root of the monic quadratic `W(x₀, Y)`
    rw [equation_iff'] at he
    set f : R[X] := X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X -
      C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hf
    have hfm : f.Monic := by rw [hf]; monicity!
    obtain ⟨y, hy, hyy₀⟩ := HenselianLocalRing.is_henselian f hfm y₀
      (by
        rw [← residue_eq_zero_iff, ← he]
        simp [hf]
        ring)
      (by
        rw [← residue_ne_zero_iff_isUnit]
        convert hY using 1
        simp [hf, derivative_pow, map_ofNat]
        ring)
    have hres : residue R y = residue R y₀ := by
      rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine ⟨x₀, y, hns ?_ rfl hres, rfl, hres⟩
    rw [equation_iff', ← hy.eq_zero]
    simp [hf]
    ring

end WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- **Centring at a singular point of the reduction.** Over a Henselian local ring, if `a₃` and
`a₄` lie in the maximal ideal and `b₂` is a unit, then for some `r, t ∈ 𝔪` the translation
`x ↦ x + r`, `y ↦ y + t` makes `a₃ = a₄ = 0`: `(r, t)` is a critical point of the Weierstrass
polynomial. -/
theorem exists_translate_a₃_eq_zero_and_a₄_eq_zero {R : Type*} [CommRing R]
    [HenselianLocalRing R] (W : WeierstrassCurve R) (h₃ : W.a₃ ∈ maximalIdeal R)
    (h₄ : W.a₄ ∈ maximalIdeal R) (hb₂ : IsUnit W.b₂) :
    ∃ r t : R, r ∈ maximalIdeal R ∧ t ∈ maximalIdeal R ∧
      (VariableChange.mk 1 r 0 t • W).a₃ = 0 ∧ (VariableChange.mk 1 r 0 t • W).a₄ = 0 := by
  have h0 {a : R} (ha : a ∈ maximalIdeal R) : residue R a = 0 := (residue_eq_zero_iff _).2 ha
  simp only [variableChange_a₃, variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul]
  -- `a₁` times the first condition plus `2` times the second is `6 r² + b₂ r + b₄ = 0`
  have hb₄ : W.b₄ ∈ maximalIdeal R := (residue_eq_zero_iff _).1 (by simp [b₄, h0 h₃, h0 h₄])
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
    refine ⟨r, -(W.a₃ + W.a₁ * r) * i, hr𝔪,
      (residue_eq_zero_iff _).1 (by simp [h0 h₃, h0 hr𝔪]), by linear_combination e₃, ?_⟩
    refine h2.mul_right_eq_zero.1 ?_
    linear_combination hr' - W.a₁ * e₃
  · -- `2 ∈ 𝔪`, so `a₁² ≡ b₂` is a unit; solve the second condition for `t`
    have h2𝔪 : (2 : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h2
    have ha₁ : IsUnit W.a₁ := by
      have hsq : W.a₁ ^ 2 = W.b₂ - 2 * (2 * W.a₂) := by rw [b₂]; ring
      rw [← residue_ne_zero_iff_isUnit] at hb₂ ⊢
      refine fun ha0 ↦ hb₂ ?_
      have := congrArg (residue R) hsq
      rw [map_pow, ha0, map_sub, h0 ((maximalIdeal R).mul_mem_right _ h2𝔪)] at this
      simpa using this.symm
    obtain ⟨j, hj⟩ := ha₁.exists_right_inv
    have e₄ : W.a₄ + 2 * W.a₂ * r - W.a₁ * ((W.a₄ + 2 * W.a₂ * r + 3 * r ^ 2) * j) +
        3 * r ^ 2 = 0 := by
      linear_combination (-(W.a₄ + 2 * W.a₂ * r + 3 * r ^ 2)) * hj
    refine ⟨r, (W.a₄ + 2 * W.a₂ * r + 3 * r ^ 2) * j, hr𝔪,
      (residue_eq_zero_iff _).1 (by simp [h0 h₄, h0 hr𝔪]), ?_, by linear_combination e₄⟩
    refine ha₁.mul_right_eq_zero.1 ?_
    linear_combination hr' - 2 * e₄

/-- Over a Henselian local ring with finite residue field, suppose `a₃ = a₄ = 0`, `a₆ ∈ 𝔪`,
`b₂` is a unit, and the tangent quadratic has no residue-field root. If the discriminant is
associated to a square, the Weierstrass equation has a solution with both coordinates in `𝔪`. -/
theorem exists_equation_mem_maximalIdeal_of_a₃_eq_zero_of_a₄_eq_zero {R : Type*}
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
  -- the residue conic `Y² + a₁ X Y − a₂ X² = A` has a point, given by the norm of the quadratic
  -- extension of the residue field generated by a root of `T² − a₁ T − a₂`, and it lifts
  have : Fact (∀ r : ResidueField R, r ^ 2 ≠ residue R W.a₂ + residue R W.a₁ * r) :=
    ⟨fun r hr ↦ hroot (-r) (by linear_combination hr)⟩
  have : Finite (QuadraticAlgebra (ResidueField R) (residue R W.a₂) (residue R W.a₁)) :=
    Module.finite_of_finite (ResidueField R)
  -- The algebra structure is pinned to the quadratic algebra's own: instance search would build one
  -- through `ResidueField.algebraOfIsIntegral`, which is not reducibly the same.
  obtain ⟨q, hq⟩ := @FiniteField.norm_surjective (ResidueField R)
    (QuadraticAlgebra (ResidueField R) (residue R W.a₂) (residue R W.a₁)) _ _
    QuadraticAlgebra.instAlgebra _ (residue R A)
  rw [QuadraticAlgebra.algebraNorm_eq_norm, QuadraticAlgebra.norm_def] at hq
  obtain ⟨X₀, hX₀⟩ := residue_surjective q.im
  obtain ⟨Y₀, hY₀⟩ := residue_surjective q.re
  obtain ⟨X, Y, hXY⟩ := TauCeti.HenselianLocalRing.exists_conic_eq
    (A := A) (X₀ := X₀) (Y₀ := Y₀) (by rwa [← b₂]) hz
    (u.isUnit.mul hw.unit⁻¹.isUnit).neg (by
      refine (residue_eq_zero_iff _).1 ?_
      simp only [map_sub, map_add, map_mul, map_pow, (residue_eq_zero_iff _).2 hz, hX₀, hY₀]
      linear_combination hq)
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

end WeierstrassCurve

end
