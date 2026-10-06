/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
-- Proof-only: an extension of an algebraically closed field adds no torsion.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.AlgClosed
-- Proof-only: over an algebraically closed field, torsion is read off the roots of `ΨSqₙ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Roots

/-!
# Supersingular and ordinary Weierstrass curves

An elliptic curve `E` over a field `K` of characteristic `p > 0` is **supersingular** when it has
no nonzero geometric point of order `p`, that is `E[p](AlgebraicClosure K) = O`, and **ordinary**
otherwise (Silverman V.3.1). The definition here is this geometric one, read over Mathlib's
`AlgebraicClosure K`, and it makes sense over an arbitrary field of characteristic `p`, where there
is in general no trace of Frobenius.

The geometric points must be taken over an *algebraic* closure, not a separable one. Over an
imperfect field an ordinary curve can have all of its nonzero `p`-torsion purely inseparable over
`K`: over `𝔽₂(t)` the curve `y² + xy = x³ + t` has `j = 1 / t ≠ 0`, so it is ordinary, but its
only nonzero `2`-torsion point is `(0, √t)`, which does not lie over the separable closure. A
separable-closure definition would call this curve supersingular, and would make supersingularity
change under the purely inseparable extension `𝔽₂(√t) / 𝔽₂(t)`.

With the algebraic closure, the choice of closure does not matter: an extension of an
algebraically closed field adds no torsion
(`WeierstrassCurve.torsionBy_baseChange_eq_bot_iff_of_isAlgClosed`), so the `p`-torsion may be
read over any algebraically closed extension of `K`. It follows that supersingularity is invariant
under every field extension `L / K`, algebraic or not.

In characteristic `2` and `3` supersingularity is decided by the `j`-invariant. There the
polynomial whose roots are the abscissae of the nonzero `p`-torsion is `a₁²x² + a₃²`,
respectively `(b₂x³ + b₈)²`, and on an elliptic curve it is a nonzero constant exactly when `j = 0`.

## Main definitions

* `WeierstrassCurve.IsSupersingular`: `W` has no nonzero `p`-torsion point over
  `AlgebraicClosure K`.
* `WeierstrassCurve.IsOrdinary`: `W` is not supersingular.

## Main results

* `WeierstrassCurve.isSupersingular_iff_of_isAlgClosed`: the `p`-torsion may be read over any
  algebraically closed extension of `K`.
* `WeierstrassCurve.isSupersingular_baseChange_iff`: supersingularity is invariant under an
  arbitrary field extension.
* `WeierstrassCurve.isSupersingular_variableChange_iff`: it is invariant under changes of
  variables.
* `WeierstrassCurve.isSupersingular_iff_forall_pow`: a supersingular curve has no nonzero
  `p ^ r`-torsion over `AlgebraicClosure K` for any `r`.
* `WeierstrassCurve.isSupersingular_two_iff_j_eq_zero` and
  `WeierstrassCurve.isSupersingular_three_iff_j_eq_zero`: in characteristic `2` and `3`, an elliptic
  curve is supersingular exactly when `j = 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.3.1, V.4.1 and
  Appendix A.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]

open scoped Classical in
/-- **A supersingular Weierstrass curve at `p`**: the curve has no nonzero point of order dividing
`p` over the algebraic closure of `K`. For an elliptic curve over a field of characteristic `p > 0`
this is supersingularity in the sense of Silverman V.3.1. -/
def IsSupersingular (p : ℕ) (W : WeierstrassCurve K) : Prop :=
  AddSubgroup.torsionBy (W.baseChange (AlgebraicClosure K)).toAffine.Point p = ⊥

/-- **An ordinary Weierstrass curve at `p`**: the curve is not supersingular at `p`, so it has a
nonzero `p`-torsion point over the algebraic closure of `K`. -/
def IsOrdinary (p : ℕ) (W : WeierstrassCurve K) : Prop :=
  ¬W.IsSupersingular p

variable {p : ℕ} {W : WeierstrassCurve K}

/-- A curve that is not supersingular is ordinary. -/
@[simp]
theorem not_isSupersingular : ¬W.IsSupersingular p ↔ W.IsOrdinary p :=
  Iff.rfl

/-- A curve that is not ordinary is supersingular. -/
@[simp]
theorem not_isOrdinary : ¬W.IsOrdinary p ↔ W.IsSupersingular p :=
  not_not

open scoped Classical in
/-- Supersingularity unfolded: every `p`-torsion point over `AlgebraicClosure K` is zero. -/
theorem isSupersingular_iff_forall :
    W.IsSupersingular p ↔
      ∀ P : (W.baseChange (AlgebraicClosure K)).toAffine.Point, p • P = 0 → P = 0 := by
  simp only [IsSupersingular, AddSubgroup.eq_bot_iff_forall, AddSubgroup.torsionBy.nsmul_iff]

open scoped Classical in
/-- An ordinary curve has a nonzero `p`-torsion point over `AlgebraicClosure K`. -/
theorem isOrdinary_iff_exists :
    W.IsOrdinary p ↔
      ∃ P : (W.baseChange (AlgebraicClosure K)).toAffine.Point, p • P = 0 ∧ P ≠ 0 := by
  simp [IsOrdinary, isSupersingular_iff_forall]

open scoped Classical in
/-- **A supersingular curve has no geometric `p`-power torsion**: if
`E[p](AlgebraicClosure K) = O` then `E[p ^ r](AlgebraicClosure K) = O` for every `r`. -/
theorem isSupersingular_iff_forall_pow :
    W.IsSupersingular p ↔
      ∀ r : ℕ, AddSubgroup.torsionBy (W.baseChange (AlgebraicClosure K)).toAffine.Point
        ((p : ℤ) ^ r) = ⊥ := by
  refine ⟨fun h r ↦ ?_, fun h ↦ by simpa [IsSupersingular] using h 1⟩
  rw [isSupersingular_iff_forall] at h
  simp only [← Nat.cast_pow, AddSubgroup.eq_bot_iff_forall, AddSubgroup.torsionBy.nsmul_iff]
  induction r with
  | zero => simp
  | succ r ih => exact fun P hP ↦ h P (ih (p • P) (by rwa [smul_smul, ← pow_succ]))

section Elliptic

variable [W.IsElliptic]

/-- **Supersingularity may be read over any algebraically closed extension** `Ω` of `K`: the
`p`-torsion of `W` over `Ω` is trivial exactly when it is over `AlgebraicClosure K`, since
`AlgebraicClosure K` embeds into `Ω` and an extension of an algebraically closed field adds no
torsion. -/
theorem isSupersingular_iff_of_isAlgClosed (hp : p ≠ 0) (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] [DecidableEq Ω] :
    W.IsSupersingular p ↔ AddSubgroup.torsionBy (W.baseChange Ω).toAffine.Point p = ⊥ := by
  classical
  -- Mathlib's ellipticity instance is stated for `W.map f`, which `W.baseChange A` unfolds to.
  have : (W.baseChange (AlgebraicClosure K)).IsElliptic := inferInstanceAs (W.map _).IsElliptic
  let ι : AlgebraicClosure K →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) Ω := ι.toRingHom.toAlgebra
  -- `(W⁄A)⁄B` is `(W⁄A).map (algebraMap A B)` by definition, and `map_baseChange` collapses
  -- that map along the tower `K → A → B`.
  have hbc : (W.baseChange (AlgebraicClosure K)).baseChange Ω = W.baseChange Ω :=
    map_baseChange W (IsScalarTower.toAlgHom K (AlgebraicClosure K) Ω)
  rw [IsSupersingular, ← torsionBy_baseChange_eq_bot_iff_of_isAlgClosed
    (W.baseChange (AlgebraicClosure K)) (Ω := Ω) (Nat.cast_ne_zero.mpr hp), hbc]

/-- **Supersingularity is invariant under field extension**: for an arbitrary extension `L / K`,
not necessarily algebraic, `W` is supersingular exactly when its base change to `L` is. -/
theorem isSupersingular_baseChange_iff (hp : p ≠ 0) (L : Type*) [Field L] [Algebra K L] :
    (W.baseChange L).IsSupersingular p ↔ W.IsSupersingular p := by
  classical
  have : (W.baseChange L).IsElliptic := inferInstanceAs (W.map _).IsElliptic
  -- As above, `map_baseChange` collapses the double base change along `K → L → AlgebraicClosure L`.
  have hbc : (W.baseChange L).baseChange (AlgebraicClosure L) = W.baseChange (AlgebraicClosure L) :=
    map_baseChange W (IsScalarTower.toAlgHom K L (AlgebraicClosure L))
  rw [isSupersingular_iff_of_isAlgClosed hp (AlgebraicClosure L),
    W.isSupersingular_iff_of_isAlgClosed hp (AlgebraicClosure L), hbc]

/-- **Ordinarity is invariant under field extension.** -/
theorem isOrdinary_baseChange_iff (hp : p ≠ 0) (L : Type*) [Field L] [Algebra K L] :
    (W.baseChange L).IsOrdinary p ↔ W.IsOrdinary p :=
  (isSupersingular_baseChange_iff hp L).not

end Elliptic

/-- **Supersingularity is invariant under a change of variables**: isomorphic Weierstrass curves
have isomorphic point groups over `AlgebraicClosure K`. -/
theorem isSupersingular_variableChange_iff (C : VariableChange K) :
    (C • W).IsSupersingular p ↔ W.IsSupersingular p := by
  classical
  let e := W.pointEquivVariableChange (AlgebraicClosure K) C
  simp only [isSupersingular_iff_forall]
  refine ⟨fun h P hP ↦ ?_, fun h P hP ↦ e.injective ?_⟩
  · rw [← e.apply_symm_apply P, h (e.symm P) (by rw [← map_nsmul, hP, map_zero]), map_zero]
  · rw [h (e P) (by rw [← map_nsmul, hP, map_zero]), map_zero]

/-- **Ordinarity is invariant under a change of variables.** -/
theorem isOrdinary_variableChange_iff (C : VariableChange K) :
    (C • W).IsOrdinary p ↔ W.IsOrdinary p :=
  (isSupersingular_variableChange_iff C).not

/-! ### Characteristic two and three -/

section AlgClosed

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] (V : WeierstrassCurve F)
  [V.IsElliptic]

/-- In characteristic `2` the `2`-torsion of an elliptic curve over an algebraically closed field
is trivial exactly when `a₁ = 0`: then `ΨSq₂ = a₃²` is a nonzero constant, and otherwise
`x = a₃ / a₁` is a root of `ΨSq₂ = a₁² x² + a₃²`. -/
private theorem torsionBy_two_eq_bot_iff [CharP F 2] :
    AddSubgroup.torsionBy V.toAffine.Point 2 = ⊥ ↔ V.a₁ = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have heval (x : F) : (V.ΨSq 2).eval x = V.a₁ ^ 2 * x ^ 2 + V.a₃ ^ 2 := by
    rw [ΨSq_two, Ψ₂Sq, ← b₂_of_char_two, ← b₆_of_char_two]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination (2 * x ^ 3 + V.b₄ * x) * h2
  rw [torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero]
  simp only [heval]
  refine ⟨fun h ↦ by_contra fun ha ↦ h (V.a₃ / V.a₁) ?_, fun ha x ↦ ?_⟩
  · field_simp
    linear_combination V.a₃ ^ 2 * h2
  · have hΔ := V.isUnit_Δ.ne_zero
    rw [Δ_of_char_two, ha] at hΔ
    simpa [ha] using hΔ

/-- In characteristic `3` the `3`-torsion of an elliptic curve over an algebraically closed field
is trivial exactly when `b₂ = 0`: there `ψ₃ = b₂ x³ + b₈`, whose constant term `b₈` cannot vanish
together with `b₂`, and which has a root as soon as `b₂ ≠ 0`. -/
private theorem torsionBy_three_eq_bot_iff [CharP F 3] :
    AddSubgroup.torsionBy V.toAffine.Point 3 = ⊥ ↔ V.b₂ = 0 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have heval (x : F) : (V.ΨSq 3).eval x = (V.b₂ * x ^ 3 + V.b₈) ^ 2 := by
    rw [ΨSq_three, Ψ₃]
    simp only [eval_pow, eval_add, eval_mul, eval_C, eval_X, eval_ofNat]
    linear_combination (x ^ 4 + V.b₄ * x ^ 2 + V.b₆ * x) *
      (3 * x ^ 4 + 2 * V.b₂ * x ^ 3 + 3 * V.b₄ * x ^ 2 + 3 * V.b₆ * x + 2 * V.b₈) * h3
  rw [torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero]
  simp only [heval, ne_eq, pow_eq_zero_iff two_ne_zero]
  refine ⟨fun h ↦ by_contra fun hb ↦ ?_, fun hb x hx ↦ ?_⟩
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-V.b₈ / V.b₂) three_pos
    exact h z (by rw [hz]; field_simp; ring)
  · rw [hb, zero_mul, zero_add] at hx
    have hb₄ : V.b₄ = 0 := by
      have := V.b_relation_of_char_three
      rw [hx, hb, zero_mul, zero_sub, zero_eq_neg] at this
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact V.isUnit_Δ.ne_zero (by rw [Δ_of_char_three, hb, hb₄]; ring)

end AlgClosed

variable [W.IsElliptic]

/-- **In characteristic `2` an elliptic curve is supersingular exactly when `j = 0`**, equivalently
`a₁ = 0` (`WeierstrassCurve.j_eq_zero_iff_of_char_two`). -/
theorem isSupersingular_two_iff_j_eq_zero [CharP K 2] : W.IsSupersingular 2 ↔ W.j = 0 := by
  classical
  have : (W.baseChange (AlgebraicClosure K)).IsElliptic := inferInstanceAs (W.map _).IsElliptic
  have hj : (W.baseChange (AlgebraicClosure K)).j = algebraMap K _ W.j := W.map_j _
  rw [IsSupersingular, Nat.cast_ofNat, torsionBy_two_eq_bot_iff, ← j_eq_zero_iff_of_char_two, hj,
    FaithfulSMul.algebraMap_eq_zero_iff]

/-- **In characteristic `3` an elliptic curve is supersingular exactly when `j = 0`**, equivalently
`b₂ = 0` (`WeierstrassCurve.j_eq_zero_iff_of_char_three`). -/
theorem isSupersingular_three_iff_j_eq_zero [CharP K 3] : W.IsSupersingular 3 ↔ W.j = 0 := by
  classical
  have : (W.baseChange (AlgebraicClosure K)).IsElliptic := inferInstanceAs (W.map _).IsElliptic
  have hj : (W.baseChange (AlgebraicClosure K)).j = algebraMap K _ W.j := W.map_j _
  rw [IsSupersingular, Nat.cast_ofNat, torsionBy_three_eq_bot_iff, ← j_eq_zero_iff_of_char_three,
    hj, FaithfulSMul.algebraMap_eq_zero_iff]

end WeierstrassCurve

end
