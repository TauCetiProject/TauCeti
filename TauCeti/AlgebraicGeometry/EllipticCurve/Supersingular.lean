/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
-- Proof-only: torsion is transported along an additive equivalence.
import TauCeti.Algebra.Module.Torsion.Basic
-- Proof-only: an extension of an algebraically closed field adds no torsion.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.AlgClosed
-- Proof-only: over an algebraically closed field, the `2`- and `3`-torsion in characteristic `2`
-- and `3`, read off the roots of `ΨSqₙ`.
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
* `WeierstrassCurve.isSupersingular_iff_j_eq_zero_of_char_two` and
  `WeierstrassCurve.isSupersingular_iff_j_eq_zero_of_char_three`: in characteristic `2` and `3`,
  an elliptic curve is supersingular exactly when `j = 0`.
* `WeierstrassCurve.isOrdinary_iff_j_ne_zero_of_char_two` and
  `WeierstrassCurve.isOrdinary_iff_j_ne_zero_of_char_three`: in characteristic `2` and `3`, an
  elliptic curve is ordinary exactly when `j ≠ 0`.

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
  -- `A[n] = ⊥` says that `n` is a regular scalar on `A`, and powers of regular scalars are regular.
  have key (n : ℤ) :
      AddSubgroup.torsionBy (W.baseChange (AlgebraicClosure K)).toAffine.Point n = ⊥ ↔
        IsSMulRegular (W.baseChange (AlgebraicClosure K)).toAffine.Point n := by
    rw [isSMulRegular_iff_torsionBy_eq_bot, ← Submodule.toAddSubgroup_inj,
      Submodule.bot_toAddSubgroup]
  simp only [IsSupersingular, key]
  exact ⟨fun h r ↦ h.pow r, fun h ↦ by simpa using h 1⟩

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
@[simp]
theorem isSupersingular_variableChange_iff (C : VariableChange K) :
    (C • W).IsSupersingular p ↔ W.IsSupersingular p := by
  classical
  rw [IsSupersingular, IsSupersingular, ← not_iff_not, ← ne_eq, ← ne_eq,
    ← AddSubgroup.nontrivial_iff_ne_bot, ← AddSubgroup.nontrivial_iff_ne_bot]
  exact ((W.pointEquivVariableChange _ C).torsionByCongr p).toEquiv.nontrivial_congr

/-- **Ordinarity is invariant under a change of variables.** -/
@[simp]
theorem isOrdinary_variableChange_iff (C : VariableChange K) :
    (C • W).IsOrdinary p ↔ W.IsOrdinary p :=
  (isSupersingular_variableChange_iff C).not

/-! ### Characteristic two and three -/

variable [W.IsElliptic]

/-- **In characteristic `2` an elliptic curve is supersingular exactly when `j = 0`**, equivalently
`a₁ = 0` (`WeierstrassCurve.j_eq_zero_iff_of_char_two`). -/
theorem isSupersingular_iff_j_eq_zero_of_char_two [CharP K 2] : W.IsSupersingular 2 ↔ W.j = 0 := by
  classical
  have : (W.baseChange (AlgebraicClosure K)).IsElliptic := inferInstanceAs (W.map _).IsElliptic
  have hj : (W.baseChange (AlgebraicClosure K)).j = algebraMap K _ W.j := W.map_j _
  rw [IsSupersingular, Nat.cast_ofNat, torsionBy_two_eq_bot_iff_of_char_two,
    ← j_eq_zero_iff_of_char_two, hj, FaithfulSMul.algebraMap_eq_zero_iff]

/-- **In characteristic `3` an elliptic curve is supersingular exactly when `j = 0`**, equivalently
`b₂ = 0` (`WeierstrassCurve.j_eq_zero_iff_of_char_three`). -/
theorem isSupersingular_iff_j_eq_zero_of_char_three [CharP K 3] :
    W.IsSupersingular 3 ↔ W.j = 0 := by
  classical
  have : (W.baseChange (AlgebraicClosure K)).IsElliptic := inferInstanceAs (W.map _).IsElliptic
  have hj : (W.baseChange (AlgebraicClosure K)).j = algebraMap K _ W.j := W.map_j _
  rw [IsSupersingular, Nat.cast_ofNat, torsionBy_three_eq_bot_iff_of_char_three,
    ← j_eq_zero_iff_of_char_three, hj, FaithfulSMul.algebraMap_eq_zero_iff]

/-- **In characteristic `2` an elliptic curve is ordinary exactly when `j ≠ 0`.** -/
theorem isOrdinary_iff_j_ne_zero_of_char_two [CharP K 2] : W.IsOrdinary 2 ↔ W.j ≠ 0 :=
  isSupersingular_iff_j_eq_zero_of_char_two.not

/-- **In characteristic `3` an elliptic curve is ordinary exactly when `j ≠ 0`.** -/
theorem isOrdinary_iff_j_ne_zero_of_char_three [CharP K 3] : W.IsOrdinary 3 ↔ W.j ≠ 0 :=
  isSupersingular_iff_j_eq_zero_of_char_three.not

end WeierstrassCurve

end
