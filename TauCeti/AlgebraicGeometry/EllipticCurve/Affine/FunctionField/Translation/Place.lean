/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois

/-!
# Translations move the places of points

Let `W` be an elliptic curve over a field `F`. The automorphism group of `F(W)` over `F` acts on
the places of `F(W)` (`TauCeti.Place.instMulActionAlgEquiv`), and the translation `τ_P^*` is such
an automorphism. It moves the place of a point `Q` to the place of `Q - P`: the function
`τ_P^* f` takes at `Q` the value `f` takes at `Q + P`, and the place `σ • v` is the one at which
`σ f` behaves as `f` does at `v`. Through the equivariance of principal divisors
(`TauCeti.Divisor.principal_smul`) this computes the divisor of a translated function from the
divisor of the function, which is what the divisor calculus of the Weil pairing needs.

The proof reads the place of a point off the reduction of the generic point
(`WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`). An `F`-automorphism `σ`
carries the kernel of reduction at `w` onto the kernel of reduction at `σ • w`, so reducing
`σ A` at `σ • w` is reducing `A` at `w`; and `τ_P^*` carries the generic point to its translate
by `P`.

## Main results

* `WeierstrassCurve.Affine.map_mem_polePoints_smul_iff` and
  `WeierstrassCurve.Affine.reductionOfDegreeEqOne_smul_map`: an automorphism of `K / F` carries
  reduction at a place `w` to reduction at `σ • w`.
* `WeierstrassCurve.Affine.translation_smul_pointEquivDegreeOnePlace`: `τ_P^*` carries the
  place of `Q` to the place of `Q - P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3, III.8.
-/

public section

open TauCeti

namespace WeierstrassCurve.Affine

section Automorphism

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : Affine F)
  [W.IsElliptic]

/-- **An automorphism carries the kernel of reduction at `w` onto that at `σ • w`**: the
`x`-coordinate of `σ A` has a pole at `σ • w` exactly when that of `A` has one at `w`. -/
-- not `@[simp]`: `mem_polePoints_iff` is, and it unfolds the membership on the left-hand side
-- first, so this lemma would never fire. Apply it, or `rw` with it.
theorem map_mem_polePoints_smul_iff (σ : K ≃ₐ[F] K) (w : Place F K)
    (A : (W⁄K).toAffine.Point) :
    Point.map (σ : K →ₐ[F] K) A ∈ polePoints W (σ • w) ↔ A ∈ polePoints W w := by
  rw [mem_polePoints_iff, mem_polePoints_iff, map_eq_zero_iff _ (Point.map_injective _),
    Point.xCoord_map, AlgEquiv.coe_toAlgHom, Place.valuation_smul_apply]

variable [DecidableEq F]

/-- **Reduction commutes with automorphisms**: reducing `σ A` at `σ • w` is reducing `A` at `w`,
for a place `w` of degree one and an automorphism `σ` of `K / F`. -/
@[simp]
theorem reductionOfDegreeEqOne_smul_map (σ : K ≃ₐ[F] K) {w : Place F K} (hw : w.degree = 1)
    (A : (W⁄K).toAffine.Point) :
    reductionOfDegreeEqOne W ((Place.degree_smul σ w).trans hw) (Point.map (σ : K →ₐ[F] K) A) =
      reductionOfDegreeEqOne W hw A := by
  rw [reductionOfDegreeEqOne_eq_iff, ← Point.map_baseChange (σ : K →ₐ[F] K), ← map_sub,
    map_mem_polePoints_smul_iff]
  exact sub_reductionOfDegreeEqOne_mem_polePoints W hw A

end Automorphism

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- **The translation by `P` carries the place of `Q` to the place of `Q - P`**: `τ_P^* f` has
at `Q` the behaviour of `f` at `Q + P`. -/
@[simp]
theorem translation_smul_pointEquivDegreeOnePlace (P Q : W.Point) :
    translation W (Point.equivBaseChangeSelf W P) • (pointEquivDegreeOnePlace W Q).1 =
      (pointEquivDegreeOnePlace W (Q - P)).1 := by
  set σ := translation W (Point.equivBaseChangeSelf W P)
  set v := pointEquivDegreeOnePlace W Q
  -- `σ • v` is the place of some point `R`, read off the reduction of the generic point
  have hdeg : (σ • v.1).degree = 1 := (Place.degree_smul σ v.1).trans v.2
  set R := (pointEquivDegreeOnePlace W).symm ⟨σ • v.1, hdeg⟩ with hR
  have hRv : (pointEquivDegreeOnePlace W R).1 = σ • v.1 := by
    rw [hR, Equiv.apply_symm_apply]
  suffices R = Q - P by rw [← this, hRv]
  apply (Point.equivBaseChangeSelf W).injective
  -- the generic point is the image under `σ` of its translate by `-P`
  have hgen : genericPoint W = Point.map (σ : W.FunctionField →ₐ[F] W.FunctionField)
      (translatedGenericPoint W (-Point.equivBaseChangeSelf W P)) := by
    rw [map_translation_translatedGenericPoint, neg_add_cancel,
      translatedGenericPoint_zero]
  -- the reduction depends on the place only, not on the proof that it has degree one
  have hred : ∀ {w₁ w₂ : Place F W.FunctionField} (h : w₁ = w₂) (h₁ : w₁.degree = 1)
      (h₂ : w₂.degree = 1), reductionOfDegreeEqOne W h₁ = reductionOfDegreeEqOne W h₂ := by
    rintro _ _ rfl _ _
    rfl
  rw [← reductionOfDegreeEqOne_genericPoint W R, hred hRv _ hdeg, hgen,
    reductionOfDegreeEqOne_smul_map W σ v.2, translatedGenericPoint_def, map_add,
    reductionOfDegreeEqOne_genericPoint, reductionOfDegreeEqOne_baseChange, map_sub,
    sub_eq_add_neg]

end WeierstrassCurve.Affine

end
