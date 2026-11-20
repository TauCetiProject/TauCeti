/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Classification
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.SquareRoot

/-!
# Quadratic twists by a character of the absolute Galois group

Let `K` be a field of characteristic other than `2`, and `Gal(Kᵃˡᵍ/K)` its absolute Galois group
with the Krull topology (Mathlib's `Field.absoluteGaloisGroup K` is this group by definition). A
continuous character `η : Gal(Kᵃˡᵍ/K) → ℤˣ` is the quadratic character of `K(√d)/K` for a unit
`d`, read off from the action `g √d = η(g) √d` on a square root of `d`. The quadratic twist of a
Weierstrass curve `W` by `η` is then the twist `W.quadraticTwistOf 0 (-d)` by the trace `0` and
norm `-d` of `√d`, which is the classical twist by `4d`, and `4d` differs from `d` by a square.
`W.IsQuadraticTwistBy E η` says that `E` is isomorphic over `K` to this twist, for some unit `d`
and square root `√d` on which `η` describes the Galois action.

When `j(W) ∉ {0, 1728}` the twists of `W` are its quadratic twists, and the twisting character is
determined by the twist. This file proves that an elliptic curve `E` over `K` is a quadratic twist
of `W` by a character exactly when `j(E) = j(W)` (`exists_isQuadraticTwistBy_iff_j_eq`), and that
the character is then unique (`existsUnique_isQuadraticTwistBy`). Uniqueness comes from the
invariants: if `E` is isomorphic to the twists by `d` and by `d'`, comparing `c₄` and `c₆`, which
are nonzero, gives `d' / d = w²` for some `w ∈ K`, so `√d'` and `w √d` agree up to sign and the two
characters coincide.

The trivial character gives exactly the curves isomorphic to `W` over `K`
(`isQuadraticTwistBy_one_iff`). Applied to a Tate curve, this presents a curve with nonintegral
`j`-invariant over a nonarchimedean field as the twist of a Tate curve by a unique character.

## Main definitions

* `WeierstrassCurve.IsQuadraticTwistBy`: `E` is the quadratic twist of `W` by the character `η`.

## Main results

* `WeierstrassCurve.isQuadraticTwistBy_one_iff`: the twist by the trivial character is `W` itself,
  up to isomorphism over `K`.
* `WeierstrassCurve.exists_isQuadraticTwistBy_iff_j_eq`: for `j(W) ∉ {0, 1728}`, an elliptic
  curve is a quadratic twist of `W` by some character exactly when it has the `j`-invariant of `W`.
* `WeierstrassCurve.IsQuadraticTwistBy.unique`: for `j(W) ∉ {0, 1728}`, the twisting character of
  an elliptic curve is unique.
* `WeierstrassCurve.existsUnique_isQuadraticTwistBy`: for `j(W) ∉ {0, 1728}`, an elliptic curve
  with the `j`-invariant of `W` is the twist of `W` by exactly one character.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.2 and X.5
* B. Mazur and K. Rubin, *Selmer companion curves*, Trans. Amer. Math. Soc. 367 (2015), §2
-/

public section

namespace WeierstrassCurve

variable {K : Type*} [Field K]

/-- **`E` is the quadratic twist of `W` by the character `η`.** There are a unit `d` of `K` and a
square root `a` of `d` in the algebraic closure on which every `g` acts by `g a = η(g) • a`, such
that `E` is isomorphic over `K` to the twist of `W` by the parameters `(0, -d)`, the trace and
norm of `a`.

In characteristic `2` the twist by `(0, -d)` is singular, so no elliptic curve is a twist in this
sense. -/
def IsQuadraticTwistBy (W E : WeierstrassCurve K) (η : Gal(AlgebraicClosure K/K) →ₜ* ℤˣ) :
    Prop :=
  ∃ (d : Kˣ) (a : AlgebraicClosure K), a ^ 2 = algebraMap K (AlgebraicClosure K) d ∧
    (∀ g : Gal(AlgebraicClosure K/K), g a = (η g : ℤ) • a) ∧
    ∃ C : VariableChange K, C • W.quadraticTwistOf 0 (-(d : K)) = E

/-- **The twist by the trivial character is the trivial twist.** In characteristic other than
`2`, a Weierstrass curve is the quadratic twist of `W` by the trivial character exactly when it is
isomorphic to `W` over `K`. -/
theorem isQuadraticTwistBy_one_iff {W E : WeierstrassCurve K} (h2 : (2 : K) ≠ 0) :
    W.IsQuadraticTwistBy E 1 ↔ ∃ C : VariableChange K, C • W = E := by
  refine ⟨fun ⟨d, a, ha, hη, C, hC⟩ ↦ ?_, fun ⟨C, hC⟩ ↦ ?_⟩
  · -- a square root of `d` fixed by every automorphism is `c ∈ K`, so `d = c²` is a square
    obtain ⟨c, rfl⟩ := TauCeti.mem_range_algebraMap_of_sq_eq_of_forall_apply_eq ha h2
      fun g ↦ by simpa using hη g
    have hd : (d : K) = c ^ 2 := (algebraMap K (AlgebraicClosure K)).injective (by
      rw [map_pow]
      exact ha.symm)
    have hc : c ≠ 0 := by
      rintro rfl
      exact d.ne_zero (by simp [hd])
    -- the twist by `(0, -c²)` is the twist by the split quadratic `(x + c)(x - c)`
    obtain ⟨C₁, hC₁⟩ := W.exists_smul_eq_quadraticTwistOf_add_mul (-c) c
      (isUnit_iff_ne_zero.mpr (by rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero h2 hc))
    refine ⟨C * C₁, ?_⟩
    rw [mul_smul, hC₁, ← hC, hd, neg_add_cancel, neg_mul, ← sq]
  · -- the twist by `(0, -1)` is the twist by the split quadratic `(x + 1)(x - 1)`
    obtain ⟨C₁, hC₁⟩ := W.exists_smul_eq_quadraticTwistOf_add_mul (-1) 1
      (isUnit_iff_ne_zero.mpr (by rwa [sub_neg_eq_add, one_add_one_eq_two]))
    refine ⟨1, 1, by simp, fun g ↦ by simp, C * C₁⁻¹, ?_⟩
    rw [mul_smul, Units.val_one,
      show W.quadraticTwistOf 0 (-1) = W.quadraticTwistOf (-1 + 1) (-1 * 1) by norm_num, ← hC₁,
      inv_smul_smul, hC]

variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- An elliptic curve with the `j`-invariant of `W`, where `j(W) ∉ {0, 1728}`, is isomorphic over
`K` to the twist of `W` by the parameters `(t, n)` with nonzero discriminant `t² - 4n`. -/
private theorem exists_smul_quadraticTwistOf_eq_of_j_eq (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728)
    (E : WeierstrassCurve K) [E.IsElliptic] (hj : E.j = W.j) :
    ∃ t n : K, t ^ 2 - 4 * n ≠ 0 ∧ ∃ C : VariableChange K, C • W.quadraticTwistOf t n = E := by
  rcases W.exists_smul_eq_or_exists_smul_eq_quadraticTwist_of_j_eq (Ω := SeparableClosure K)
    hj₀ hj₁₇₂₈ E hj with ⟨C, hC⟩ | ⟨L, _, C, hC⟩
  · exact ⟨1, 0, by norm_num, C⁻¹, by rw [quadraticTwistOf_one_zero, ← hC, inv_smul_smul]⟩
  · obtain ⟨θ, -, hθ⟩ := W.exists_quadraticTwist_eq L
    rw [hθ] at hC
    refine ⟨_, _, ?_, C⁻¹, by rw [← hC, inv_smul_smul]⟩
    -- the twist is isomorphic to the elliptic curve `E`, so its discriminant is a unit
    have : (W.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)).IsElliptic := by
      rw [← hC]
      infer_instance
    exact ((W.isElliptic_quadraticTwistOf_iff _ _).mp this).1.ne_zero

omit [W.IsElliptic] in
/-- In characteristic other than `2`, the twist by parameters `(t, n)` with nonzero discriminant
`D = t² - 4n` is the twist by `(0, -D / 4)`, completing the square. -/
private theorem exists_smul_quadraticTwistOf_zero_eq {t n : K} (h2 : (2 : K) ≠ 0) :
    ∃ C : VariableChange K,
      C • W.quadraticTwistOf 0 (-((t ^ 2 - 4 * n) / 4)) = W.quadraticTwistOf t n := by
  have h4 : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using h2
  obtain ⟨C, hC⟩ := W.exists_smul_quadraticTwistOf_eq t n (a := 1) (-(t / 2)) isUnit_one
  refine ⟨C⁻¹, ?_⟩
  rw [inv_smul_eq_iff, hC]
  congr 1 <;> field_simp <;> ring

variable {W} in
/-- The `j`-invariant of an elliptic quadratic twist is that of `W`. -/
theorem IsQuadraticTwistBy.j_eq {E : WeierstrassCurve K} [E.IsElliptic]
    {η : Gal(AlgebraicClosure K/K) →ₜ* ℤˣ} (h : W.IsQuadraticTwistBy E η) : E.j = W.j := by
  obtain ⟨d, a, -, -, C, rfl⟩ := h
  have : (W.quadraticTwistOf 0 (-(d : K))).IsElliptic := by
    rw [← inv_smul_smul C (W.quadraticTwistOf 0 _)]
    infer_instance
  simp_rw [variableChange_j]
  exact W.j_quadraticTwistOf _ _ this

/-- If `E` is isomorphic to the twists of `W` by `(0, -d)` and by `(0, -d')`, and
`j(W) ∉ {0, 1728}`, then `d' / d` is a square in `K`: compare `c₄` and `c₆`, which are nonzero. -/
private theorem exists_eq_sq_mul_of_smul_quadraticTwistOf (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728)
    {d d' : K} (hd : d ≠ 0) (h2 : (2 : K) ≠ 0) {C : VariableChange K}
    (hC : C • W.quadraticTwistOf 0 (-d) = W.quadraticTwistOf 0 (-d')) :
    ∃ w : K, d' = w ^ 2 * d := by
  have hc₄ : W.c₄ ≠ 0 := fun h ↦ hj₀ (W.j_eq_zero h)
  have hΔ : W.Δ ≠ 0 := by
    rw [← coe_Δ']
    exact W.Δ'.ne_zero
  have hc₆ : W.c₆ ≠ 0 := fun h ↦ hj₁₇₂₈ (by
    rw [j_eq, inv_mul_eq_iff_eq_mul₀ hΔ]
    linear_combination -W.c_relation + W.c₆ * h)
  have h₄ := congrArg c₄ hC
  have h₆ := congrArg c₆ hC
  simp only [variableChange_c₄, variableChange_c₆, c₄_quadraticTwistOf,
    c₆_quadraticTwistOf] at h₄ h₆
  refine ⟨((C.u⁻¹ : Kˣ) : K), ?_⟩
  -- with `x = 4d'`, `y = 4d` and `z = u⁻¹`: `x² = z⁴y²` and `x³ = z⁶y³`, so `x = z²y`
  set z : K := ((C.u⁻¹ : Kˣ) : K)
  have h₄' : (4 * d') ^ 2 = z ^ 4 * (4 * d) ^ 2 := mul_right_cancel₀ hc₄ (by linear_combination -h₄)
  have h₆' : (4 * d') ^ 3 = z ^ 6 * (4 * d) ^ 3 := mul_right_cancel₀ hc₆ (by linear_combination -h₆)
  have h4 : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using h2
  have hs : z ^ 2 * (4 * d) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (Units.ne_zero _)) (mul_ne_zero h4 hd)
  have hx2 : (4 * d') ^ 2 = (z ^ 2 * (4 * d)) ^ 2 := by rw [h₄']; ring
  have hx : (4 * d' - z ^ 2 * (4 * d)) * (4 * d') ^ 2 = 0 := by
    linear_combination h₆' - z ^ 2 * (4 * d) * hx2
  have hx' := sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (hx2 ▸ pow_ne_zero 2 hs))
  exact mul_left_cancel₀ h4 (by linear_combination hx')

variable {W} in
/-- **Uniqueness of the twisting character.** If `j(W) ∉ {0, 1728}`, an elliptic curve is the
quadratic twist of `W` by at most one character. -/
theorem IsQuadraticTwistBy.unique (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728) {E : WeierstrassCurve K}
    [E.IsElliptic] {η η' : Gal(AlgebraicClosure K/K) →ₜ* ℤˣ} (h : W.IsQuadraticTwistBy E η)
    (h' : W.IsQuadraticTwistBy E η') : η = η' := by
  obtain ⟨d, a, ha, hη, C, hC⟩ := h
  obtain ⟨d', a', ha', hη', C', hC'⟩ := h'
  -- the twist is isomorphic to the elliptic curve `E`, so `4d` is a unit and `2 ≠ 0`
  have hell : (W.quadraticTwistOf 0 (-(d : K))).IsElliptic := by
    rw [← inv_smul_smul C (W.quadraticTwistOf 0 _), hC]
    infer_instance
  have h4d := ((W.isElliptic_quadraticTwistOf_iff _ _).mp hell).1.ne_zero
  have h2 : (2 : K) ≠ 0 := fun h ↦ h4d (by linear_combination 2 * (d : K) * h)
  obtain ⟨w, hw⟩ := W.exists_eq_sq_mul_of_smul_quadraticTwistOf hj₀ hj₁₇₂₈ d.ne_zero h2
    (C := C'⁻¹ * C) (by rw [mul_smul, hC, ← hC', inv_smul_smul])
  -- `a'` and `w a` are square roots of `d'`, so they agree up to sign
  have hsq : a' ^ 2 = (algebraMap K (AlgebraicClosure K) w * a) ^ 2 := by
    rw [ha', mul_pow, ha, ← map_pow, ← map_mul, hw]
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    exact d'.ne_zero (by simpa using ha'.symm)
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
    exact (map_ne_zero _).mpr h2
  have hηa' (g : Gal(AlgebraicClosure K/K)) : g a' = (η g : ℤ) • a' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e <;>
      simp only [e, map_mul, map_neg, AlgEquiv.commutes, hη g, smul_neg, mul_smul_comm]
  exact TauCeti.ContinuousMonoidHom.eq_of_apply_eq_zsmul ha'0 h2' hηa' hη'

/-- **Twists by a character are the curves with the same `j`-invariant.** In characteristic other
than `2`, when `j(W) ∉ {0, 1728}`, an elliptic curve is the quadratic twist of `W` by some
continuous character of the absolute Galois group exactly when it has the `j`-invariant of `W`. -/
theorem exists_isQuadraticTwistBy_iff_j_eq (h2 : (2 : K) ≠ 0) (hj₀ : W.j ≠ 0)
    (hj₁₇₂₈ : W.j ≠ 1728) (E : WeierstrassCurve K) [E.IsElliptic] :
    (∃ η : Gal(AlgebraicClosure K/K) →ₜ* ℤˣ, W.IsQuadraticTwistBy E η) ↔ E.j = W.j := by
  refine ⟨fun ⟨η, h⟩ ↦ h.j_eq, fun hj ↦ ?_⟩
  obtain ⟨t, n, hD, C, hC⟩ := W.exists_smul_quadraticTwistOf_eq_of_j_eq hj₀ hj₁₇₂₈ E hj
  obtain ⟨C', hC'⟩ := W.exists_smul_quadraticTwistOf_zero_eq (t := t) (n := n) h2
  have h4 : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using h2
  set d : Kˣ := Units.mk0 ((t ^ 2 - 4 * n) / 4) (div_ne_zero hD h4)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) d) two_pos
  obtain ⟨η, hη⟩ := TauCeti.exists_continuousMonoidHom_apply_eq_zsmul_of_sq_eq ha
  exact ⟨η, d, a, ha, hη, C * C', by rw [mul_smul, Units.val_mk0, hC', hC]⟩

/-- **The twisting character is unique.** In characteristic other than `2`, when
`j(W) ∉ {0, 1728}`, an elliptic curve with the `j`-invariant of `W` is the quadratic twist of `W`
by exactly one continuous character of the absolute Galois group. -/
theorem existsUnique_isQuadraticTwistBy (h2 : (2 : K) ≠ 0) (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728)
    (E : WeierstrassCurve K) [E.IsElliptic] (hj : E.j = W.j) :
    ∃! η : Gal(AlgebraicClosure K/K) →ₜ* ℤˣ, W.IsQuadraticTwistBy E η :=
  let ⟨η, hη⟩ := (W.exists_isQuadraticTwistBy_iff_j_eq h2 hj₀ hj₁₇₂₈ E).mpr hj
  ⟨η, hη, fun _ hη' ↦ hη'.unique hj₀ hj₁₇₂₈ hη⟩

end WeierstrassCurve
