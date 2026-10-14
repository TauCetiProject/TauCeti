/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Equation

/-!
# Galois descent of Vélu's quotient curve

Let `W` be an elliptic curve over `F`, let `K/F` be a field extension, and let `Φ` be a finite
subgroup of `W(K)`. Vélu's construction produces the quotient curve `veluCurve W_K Φ` over `K`,
the unique Weierstrass curve whose equation is satisfied by Vélu's coordinates
`X = x + ∑_{Q ∈ Φ, Q ≠ O} (x ∘ τ_Q - x(Q))` and `Y = y + ∑_{Q ∈ Φ, Q ≠ O} (y ∘ τ_Q - y(Q))`.

The coefficients of the quotient curve are symmetric in the points of `Φ`. This file makes that
precise through the Galois action. An `F`-automorphism `σ` of `K` acts on the function field of
`W_K` fixing `x` and `y`, and it conjugates translation by `Q` into translation by `σ Q`. If `σ`
maps `Φ` into itself, it therefore only permutes the terms of the sums defining `X` and `Y`, so
it fixes Vélu's coordinates. Applying `σ` to the equation they satisfy, uniqueness of the
quotient curve shows that `σ` fixes its coefficients. When `K/F` is Galois, possibly infinite,
for instance a separable closure of `F`, a subgroup `Φ` stable under the whole Galois group thus
has a quotient curve defined over `F`.

The subgroup `Φ` is typed as in `WeierstrassCurve.Affine.veluCurve`, inside the points of
`(W⁄K)⁄K`. The Galois action is stated on the points of `W⁄K` and transported along
`WeierstrassCurve.Affine.Point.equivBaseChangeSelf`.

## Main results

* `WeierstrassCurve.functionFieldGaloisAction_veluX` and
  `WeierstrassCurve.functionFieldGaloisAction_veluY`: an automorphism of `K/F` mapping `Φ` into
  itself fixes Vélu's coordinates.
* `WeierstrassCurve.map_veluCurve`: such an automorphism fixes the coefficients of the quotient
  curve.
* `WeierstrassCurve.exists_baseChange_eq_veluCurve`: for a Galois extension `K/F` and a
  Galois-stable finite subgroup `Φ` of `W(K)`, the quotient curve `veluCurve W_K Φ` is the base
  change of a Weierstrass curve over `F`.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A 273 (1971),
  238–241.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.12 and III.4.13.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  (W : WeierstrassCurve F)
  (Φ : AddSubgroup ((W⁄K)⁄K).toAffine.Point) [Finite Φ]

attribute [local instance] Fintype.ofFinite

/-- The Galois conjugate of a point of `(W⁄K)⁄K`, computed on `W⁄K` through
`equivBaseChangeSelf`. -/
private noncomputable def conjPoint (σ : K ≃ₐ[F] K) (Q : ((W⁄K)⁄K).toAffine.Point) :
    ((W⁄K)⁄K).toAffine.Point :=
  Affine.Point.equivBaseChangeSelf _
    (Multiplicative.toAdd (W.pointGaloisAction σ) ((Affine.Point.equivBaseChangeSelf _).symm Q))

private theorem xCoord_conjPoint (σ : K ≃ₐ[F] K) (Q : ((W⁄K)⁄K).toAffine.Point) :
    Affine.Point.xCoord (conjPoint W σ Q) = σ (Affine.Point.xCoord Q) := by
  simp [conjPoint]

private theorem yCoord_conjPoint (σ : K ≃ₐ[F] K) (Q : ((W⁄K)⁄K).toAffine.Point) :
    Affine.Point.yCoord (conjPoint W σ Q) = σ (Affine.Point.yCoord Q) := by
  simp [conjPoint]

variable {W Φ} in
/-- If `σ` maps `Φ` into itself, Galois conjugation permutes the terms of a sum over `Φ`. -/
private theorem sum_conjPoint {M : Type*} [AddCommMonoid M] {σ : K ≃ₐ[F] K}
    (hΦ : ∀ P : (W⁄K).toAffine.Point, Affine.Point.equivBaseChangeSelf _ P ∈ Φ →
      Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ)
    (h : ((W⁄K)⁄K).toAffine.Point → M) :
    ∑ Q : Φ, h (conjPoint W σ Q) = ∑ Q : Φ, h Q := by
  let f : Φ → Φ := fun Q ↦ ⟨conjPoint W σ Q, hΦ _ (by simp)⟩
  have hf : f.Bijective := Finite.injective_iff_bijective.mp fun Q₁ Q₂ hQ ↦
    Subtype.ext <| (Affine.Point.equivBaseChangeSelf _).symm.injective <|
      (Multiplicative.toAdd (W.pointGaloisAction σ)).injective <|
        (Affine.Point.equivBaseChangeSelf _).injective (congrArg Subtype.val hQ)
  exact hf.sum_comp fun Q ↦ h Q

variable [W.IsElliptic]

/-- The Galois action intertwines translation by any point of `(W⁄K)⁄K` with translation by its
conjugate. -/
private theorem functionFieldGaloisAction_translation_conjPoint (σ : K ≃ₐ[F] K)
    (Q : ((W⁄K)⁄K).toAffine.Point) (z : (W⁄K).toAffine.FunctionField) :
    functionFieldGaloisAction W σ (Affine.translation (W⁄K).toAffine Q z) =
      Affine.translation (W⁄K).toAffine (conjPoint W σ Q) (functionFieldGaloisAction W σ z) := by
  rw [conjPoint, ← functionFieldGaloisAction_translation, AddEquiv.apply_symm_apply]

/-- **An automorphism of `K/F` mapping `Φ` into itself fixes Vélu's `x`-coordinate.** -/
theorem functionFieldGaloisAction_veluX {σ : K ≃ₐ[F] K}
    (hΦ : ∀ P : (W⁄K).toAffine.Point, Affine.Point.equivBaseChangeSelf _ P ∈ Φ →
      Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ) :
    functionFieldGaloisAction W σ (Affine.veluX (W⁄K).toAffine Φ) =
      Affine.veluX (W⁄K).toAffine Φ := by
  rw [Affine.veluX_def, map_sub, map_sum, functionFieldGaloisAction_algebraMap, map_sum]
  simp only [functionFieldGaloisAction_translation_conjPoint, functionFieldGaloisAction_genericX,
    ← xCoord_conjPoint]
  rw [sum_conjPoint hΦ fun Q ↦ Affine.translation (W⁄K).toAffine Q (W⁄K).toAffine.genericX,
    sum_conjPoint hΦ Affine.Point.xCoord]

/-- **An automorphism of `K/F` mapping `Φ` into itself fixes Vélu's `y`-coordinate.** -/
theorem functionFieldGaloisAction_veluY {σ : K ≃ₐ[F] K}
    (hΦ : ∀ P : (W⁄K).toAffine.Point, Affine.Point.equivBaseChangeSelf _ P ∈ Φ →
      Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ) :
    functionFieldGaloisAction W σ (Affine.veluY (W⁄K).toAffine Φ) =
      Affine.veluY (W⁄K).toAffine Φ := by
  rw [Affine.veluY_def, map_sub, map_sum, functionFieldGaloisAction_algebraMap, map_sum]
  simp only [functionFieldGaloisAction_translation_conjPoint, functionFieldGaloisAction_genericY,
    ← yCoord_conjPoint]
  rw [sum_conjPoint hΦ fun Q ↦ Affine.translation (W⁄K).toAffine Q (W⁄K).toAffine.genericY,
    sum_conjPoint hΦ Affine.Point.yCoord]

/-- **An automorphism of `K/F` mapping `Φ` into itself fixes the coefficients of the quotient
curve** `veluCurve W_K Φ`. -/
theorem map_veluCurve {σ : K ≃ₐ[F] K}
    (hΦ : ∀ P : (W⁄K).toAffine.Point, Affine.Point.equivBaseChangeSelf _ P ∈ Φ →
      Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ) :
    (Affine.veluCurve (W⁄K).toAffine Φ).map (σ : K →+* K) = Affine.veluCurve (W⁄K).toAffine Φ := by
  apply Affine.eq_veluCurve_of_equation
  have h := (Affine.equation_veluX_veluY (W⁄K).toAffine Φ).map
    (functionFieldGaloisAction W σ).toRingHom
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, functionFieldGaloisAction_veluX W Φ hΦ,
    functionFieldGaloisAction_veluY W Φ hΦ] at h
  -- `σ` on the function field restricts to `σ` on constants, so mapping the base change of the
  -- quotient curve along it is the base change of the curve mapped along `σ`.
  have hmap : ((Affine.veluCurve (W⁄K).toAffine Φ).map (σ : K →+* K)).baseChange
        (W⁄K).toAffine.FunctionField =
      ((Affine.veluCurve (W⁄K).toAffine Φ).baseChange (W⁄K).toAffine.FunctionField).map
        (functionFieldGaloisAction W σ : (W⁄K).toAffine.FunctionField →+* _) := by
    generalize Affine.veluCurve (W⁄K).toAffine Φ = V
    have hσ : (algebraMap K (W⁄K).toAffine.FunctionField).comp (σ : K →+* K) =
        (functionFieldGaloisAction W σ : (W⁄K).toAffine.FunctionField →+* _).comp
          (algebraMap K (W⁄K).toAffine.FunctionField) :=
      RingHom.ext fun a ↦ (functionFieldGaloisAction_algebraMap W σ a).symm
    -- Both sides are `V.map` of a composite: `baseChange` is `map (algebraMap _ _)` by its
    -- definition, which Mathlib states no unfolding lemma for, and `map_map` holds by `rfl`.
    -- Unfolding `baseChange` with `simp` also unfolds it inside the function field's type.
    exact congrArg V.map hσ
  rwa [hmap]

/-- **Galois descent of Vélu's quotient curve.** For a Galois extension `K/F`, possibly infinite,
and a finite subgroup `Φ` of `W(K)` stable under every automorphism of `K/F`, the quotient curve
`veluCurve W_K Φ` is the base change of a Weierstrass curve over `F`. -/
theorem exists_baseChange_eq_veluCurve [IsGalois F K]
    (hΦ : ∀ σ : K ≃ₐ[F] K, ∀ P : (W⁄K).toAffine.Point, Affine.Point.equivBaseChangeSelf _ P ∈ Φ →
      Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ) :
    ∃ V : WeierstrassCurve F, V⁄K = Affine.veluCurve (W⁄K).toAffine Φ :=
  (mem_range_baseChange_iff_fixed _).mpr fun σ ↦ map_veluCurve W Φ (hΦ σ)

end WeierstrassCurve

end
