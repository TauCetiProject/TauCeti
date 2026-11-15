/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Equation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic

/-!
# The Vélu isogeny `W → W / Φ`

Let `W` be an elliptic curve over a field `F` and `Φ` a finite subgroup of `W(F)`. Vélu's
coordinates `X = veluX W Φ` and `Y = veluY W Φ` satisfy the Weierstrass equation of the quotient
curve `veluCurve W Φ` and generate the field fixed by the translations in `Φ`
(`Isogeny/Velu/Equation.lean`). This file packages the embedding of function fields sending the
generic point of `W / Φ` to `(X, Y)` as an isogeny

`veluIsogeny W Φ : W → W / Φ`,

and proves that it is the quotient map by `Φ`, in every characteristic, including when the
characteristic divides `#Φ`:

* it has degree `#Φ` and is separable, its function-field extension being the Galois extension
  `F(W) / F(W) ^ Φ`;
* its kernel is `Φ`;
* an isogeny `ψ` out of `W` factors through it, by a unique isogeny, exactly when `Φ ⊆ ker ψ`.

Moreover the quotient curve is **elliptic**. Since `Φ` is killed by `n = #Φ`, multiplication by
`n` factors through the Vélu isogeny, so `W / Φ` is the source of an isogeny to the elliptic
curve `W`, and such a source is elliptic (`TauCeti.Isogeny.isElliptic`). No coefficient of
`veluCurve W Φ` is computed for this.

## Main definitions

* `WeierstrassCurve.Affine.veluIsogeny`: the isogeny `W → W / Φ` given by Vélu's coordinates.

## Main results

* `WeierstrassCurve.Affine.fieldPullback_veluIsogeny_genericX` and
  `WeierstrassCurve.Affine.fieldPullback_veluIsogeny_genericY`: it pulls the coordinates of
  `W / Φ` back to Vélu's coordinates.
* `WeierstrassCurve.Affine.fieldRange_fieldPullback_veluIsogeny`: it pulls the function field
  of `W / Φ` back to the translation fixed field.
* `WeierstrassCurve.Affine.degree_veluIsogeny`: it has degree `#Φ`.
* `WeierstrassCurve.Affine.isSeparable_veluIsogeny`: it is separable.
* `WeierstrassCurve.Affine.ker_veluIsogeny`: its kernel is `Φ`.
* `WeierstrassCurve.Affine.existsUnique_comp_veluIsogeny_eq_iff_le_ker`: the universal property
  of the quotient.
* `WeierstrassCurve.Affine.isElliptic_veluCurve`: the quotient curve is elliptic.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A 273 (1971),
  238–241.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.11, III.4.12 and
  III.4.13.
* S. Galbraith, *Mathematics of Public Key Cryptography*, §25.1.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
  (Φ : AddSubgroup (W⁄F).toAffine.Point) [Finite Φ]

/-- **The Vélu isogeny** `W → W / Φ`: the coordinate pullback sending the coordinates of the
quotient curve `veluCurve W Φ` to Vélu's coordinates `veluX W Φ` and `veluY W Φ`. -/
noncomputable def veluIsogeny : Isogeny W (veluCurve W Φ).toAffine where
  pullback := (functionFieldLift (equation_veluX_veluY W Φ) (transcendental_veluX W Φ)).comp
    (IsScalarTower.toAlgHom F _ _)
  mapsInfinity := by
    refine CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace _
      (algebraMap F[X] (veluCurve W Φ).toAffine.CoordinateRing Polynomial.X) ?_
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply,
      ← genericX_eq_algebraMap, functionFieldLift_genericX, infinityPlace_veluX,
      ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

/-- The function-field pullback of the Vélu isogeny is the embedding of `F(W / Φ)` at Vélu's
coordinates. -/
theorem fieldPullback_veluIsogeny :
    (veluIsogeny W Φ).fieldPullback =
      functionFieldLift (equation_veluX_veluY W Φ) (transcendental_veluX W Φ) :=
  ((veluIsogeny W Φ).fieldPullback_unique _ fun _ ↦ rfl).symm

/-- The Vélu isogeny pulls the `x`-coordinate of `W / Φ` back to Vélu's `x`-coordinate. -/
@[simp]
theorem fieldPullback_veluIsogeny_genericX :
    (veluIsogeny W Φ).fieldPullback (veluCurve W Φ).toAffine.genericX = veluX W Φ := by
  rw [fieldPullback_veluIsogeny, functionFieldLift_genericX]

/-- The Vélu isogeny pulls the `y`-coordinate of `W / Φ` back to Vélu's `y`-coordinate. -/
@[simp]
theorem fieldPullback_veluIsogeny_genericY :
    (veluIsogeny W Φ).fieldPullback (veluCurve W Φ).toAffine.genericY = veluY W Φ := by
  rw [fieldPullback_veluIsogeny, functionFieldLift_genericY]

/-- **The Vélu isogeny pulls `F(W / Φ)` back to the translation fixed field** `F(W) ^ Φ`. -/
@[simp]
theorem fieldRange_fieldPullback_veluIsogeny :
    (veluIsogeny W Φ).fieldPullback.fieldRange = translationFixedField W Φ := by
  rw [fieldPullback_veluIsogeny, fieldRange_functionFieldLift_veluCurve]

/-- **The Vélu isogeny has degree `#Φ`**, in every characteristic. -/
@[simp]
theorem degree_veluIsogeny : (veluIsogeny W Φ).degree = Nat.card Φ := by
  rw [Isogeny.degree_def, fieldRange_fieldPullback_veluIsogeny, finrank_translationFixedField]

/-- **The Vélu isogeny is separable**, even when the characteristic divides `#Φ`: `F(W)` is
Galois over the translation fixed field. -/
instance isSeparable_veluIsogeny :
    Algebra.IsSeparable (veluIsogeny W Φ).fieldPullback.fieldRange W.FunctionField := by
  rw [fieldRange_fieldPullback_veluIsogeny]
  infer_instance

/-- **The kernel of the Vélu isogeny is `Φ`.** -/
@[simp]
theorem ker_veluIsogeny : (veluIsogeny W Φ).ker = Φ := by
  rw [Isogeny.ker_def, fieldRange_fieldPullback_veluIsogeny,
    translationFixingSubgroup_translationFixedField]

/-- **The universal property of the quotient by `Φ`** (Silverman III.4.11): an isogeny `ψ` out of
`W` factors as `χ ∘ veluIsogeny W Φ`, for a unique isogeny `χ` out of `W / Φ`, exactly when its
kernel contains `Φ`. -/
theorem existsUnique_comp_veluIsogeny_eq_iff_le_ker {W' : Affine F} (ψ : Isogeny W W') :
    (∃! χ : Isogeny (veluCurve W Φ).toAffine W', χ.comp (veluIsogeny W Φ) = ψ) ↔ Φ ≤ ψ.ker := by
  rw [Isogeny.existsUnique_comp_eq_iff_ker_le (by simp), ker_veluIsogeny]

/-- **The quotient curve `W / Φ` is elliptic**, over every field and in every characteristic. -/
instance isElliptic_veluCurve : (veluCurve W Φ).IsElliptic := by
  have hn : ((Nat.card Φ : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hle : Φ ≤ (Isogeny.mulByIntIsogenyOfNeZero W hn).ker := fun P hP ↦ by
    rw [Isogeny.mem_ker_mulByIntIsogenyOfNeZero_iff, natCast_zsmul]
    exact congrArg Subtype.val (card_nsmul_eq_zero' (G := Φ) (x := ⟨P, hP⟩))
  obtain ⟨χ, -, -⟩ := (existsUnique_comp_veluIsogeny_eq_iff_le_ker W Φ _).mpr hle
  exact χ.isElliptic

end WeierstrassCurve.Affine

end
