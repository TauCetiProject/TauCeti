/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.SingularPointCount
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The `q`-power map on the nonsingular points of a nodal cubic

Let `W` be a Weierstrass model over a finite field `F` with `q` elements which is singular with a
node, that is `Δ = 0` and `c₄ ≠ 0`. Its Frobenius trace `a_q = q + 1 - #W(F)` is `1` when the
node is split and `-1` when it is not (`WeierstrassCurve.frobeniusTrace_eq_one_of_splits`,
`WeierstrassCurve.frobeniusTrace_eq_neg_one_of_not_splits`). This file shows that over every
extension `K` of `F` the `q`-power map `Fr` on the coordinates of the nonsingular points is
multiplication by `a_q q`:

`Fr P = (a_q q) • P`.

This is the singular counterpart of the relation `Fr (Fr P) = a_q • Fr P - q • P` satisfied on an
elliptic curve (`TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom`). At multiplicative
reduction it computes the action of a Frobenius element on the points with nonsingular reduction,
and through it the sign `a_q` that distinguishes split from nonsplit multiplicative reduction.

The node lies at a point `(x₀, y₀)` of `F²`, and its tangent slopes are the roots `α`,
`-a₁ - α` of `T² + a₁ T - (3 x₀ + a₂)`, whose product with `c₄` is the node polynomial
(`WeierstrassCurve.nodePolynomial_eq_of_isSingular`). Over a field containing `α`, the parameter
`s = (y - y₀ - α (x - x₀)) / (y - y₀ + (a₁ + α) (x - x₀))` identifies the nonsingular points
with the multiplicative group (`WeierstrassCurve.Affine.Point.nodeAddEquiv`). At a split node
`α` lies in `F`, so `Fr` fixes it and raises `s` to the `q`-th power. At a nonsplit node `α` does
not lie in `F`, so `Fr` exchanges the two slopes, and it sends `s` to `s ^ (-q)`.

## Main results

* `WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_eq_zsmul`: the `q`-power map on the points of
  a nodal cubic over an extension of `F` is multiplication by `a_q q`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.5, V.2 and VII.5.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine.Point

universe u

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F}

/-- The `q`-power map at a node with tangent slope `α`, read on the parameter of
`WeierstrassCurve.Affine.Point.nodeAddEquiv`: if `Fr` fixes the node and the slope, it acts as
`q`, and if it fixes the node and exchanges the two slopes, it acts as `-q`. -/
private theorem map_frobeniusAlgHom_eq_zsmul_of_isSingular {K : Type*} [Field K] [Algebra F K]
    [DecidableEq K] {x₀ y₀ α : K} (h : (W⁄K).toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + (W⁄K).a₁ * α - (3 * x₀ + (W⁄K).a₂) = 0) (hn : 2 * α + (W⁄K).a₁ ≠ 0)
    (hx₀ : x₀ ^ Fintype.card F = x₀) (hy₀ : y₀ ^ Fintype.card F = y₀) {ε : ℤ}
    (hε : ε = 1 ∧ α ^ Fintype.card F = α ∨ ε = -1 ∧ α ^ Fintype.card F = -(W⁄K).a₁ - α)
    (P : (W⁄K).toAffine.Point) :
    map (FiniteField.frobeniusAlgHom F K) P = (ε * Fintype.card F) • P := by
  set e := nodeAddEquiv h hα hn
  apply e.injective
  rw [map_zsmul]
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← zero_def, _root_.map_zero, _root_.map_zero, smul_zero]
  -- the coefficients of `W⁄K` come from `F`, so the `q`-power map fixes them
  have ha₁ : (W⁄K).a₁ ^ Fintype.card F = (W⁄K).a₁ := by
    simp only [WeierstrassCurve.baseChange, map_a₁]
    rw [← map_pow, FiniteField.pow_card]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_zsmul, map_some, val_toMul_nodeAddEquiv_some, Units.val_zpow_eq_zpow_val, zpow_mul,
    zpow_natCast, val_toMul_nodeAddEquiv_some]
  simp only [FiniteField.frobeniusAlgHom_apply]
  -- the `q`-th power of the parameter of `(x, y)`, with the `q`-power map moved inside
  have hq : ((y - y₀ - α * (x - x₀)) / (y - y₀ + ((W⁄K).a₁ + α) * (x - x₀))) ^
      Fintype.card F = (y ^ Fintype.card F - y₀ - α ^ Fintype.card F * (x ^ Fintype.card F - x₀)) /
        (y ^ Fintype.card F - y₀ +
          ((W⁄K).a₁ + α ^ Fintype.card F) * (x ^ Fintype.card F - x₀)) := by
    have := map_div₀ (FiniteField.frobeniusAlgHom F K) (y - y₀ - α * (x - x₀))
      (y - y₀ + ((W⁄K).a₁ + α) * (x - x₀))
    simpa only [map_sub, map_add, map_mul, FiniteField.frobeniusAlgHom_apply, hx₀, hy₀, ha₁]
      using this
  rcases hε with ⟨rfl, hαq⟩ | ⟨rfl, hαq⟩
  · rw [zpow_one, hq, hαq]
  · rw [zpow_neg_one, inv_pow, hq, hαq, inv_div]
    congr 1 <;> ring

/-- **The `q`-power map on the points of a nodal cubic is multiplication by `a_q q`.** Let `W` be
a Weierstrass model over a finite field `F` with `q` elements which has a node, that is `Δ = 0`
and `c₄ ≠ 0`, and let `a_q = q + 1 - #W(F)` be its Frobenius trace, `1` at a split node and `-1`
at a nonsplit node. Over every extension `K` of `F`, the map `Fr` raising the coordinates of the
nonsingular points to the `q`-th power satisfies `Fr P = (a_q q) • P`. -/
theorem map_frobeniusAlgHom_eq_zsmul (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) {K : Type u} [Field K]
    [Algebra F K] [DecidableEq K] (P : (W⁄K).toAffine.Point) :
    map (FiniteField.frobeniusAlgHom F K) P = (W.frobeniusTrace * Nat.card F) • P := by
  classical
  obtain ⟨x₀, y₀, h⟩ := exists_isSingular_of_Δ_eq_zero W.toAffine hΔ
  -- the node polynomial splits exactly when the tangent quadratic has a root in `F`
  have hsplit : W.nodePolynomial.Splits ↔ ∃ t, 1 * t ^ 2 + W.a₁ * t + -(3 * x₀ + W.a₂) = 0 := by
    rw [W.nodePolynomial_eq_of_isSingular h,
      splits_mul_iff_right (C_ne_zero.2 hc₄) (Splits.C _),
      splits_quadratic_iff_exists_root one_ne_zero]
  have hK {L : Type u} [Field L] [Algebra F L] (t : F) : (algebraMap F L t) ^ Fintype.card F =
      algebraMap F L t := by
    rw [← map_pow, FiniteField.pow_card]
  have hsing (L : Type u) [Field L] [Algebra F L] :
      (W⁄L).toAffine.IsSingular (algebraMap F L x₀) (algebraMap F L y₀) := by
    simpa using h.baseChange (Algebra.ofId F L)
  -- `c₄ = (2 α + a₁) ^ 4` for a tangent slope `α`, so the two slopes are distinct
  have hnode (L : Type u) [Field L] [Algebra F L] {α : L}
      (hα : α ^ 2 + (W⁄L).a₁ * α - (3 * algebraMap F L x₀ + (W⁄L).a₂) = 0) :
      2 * α + (W⁄L).a₁ ≠ 0 := fun h0 ↦ hc₄ <| by
    have := Affine.c₄_eq_of_isSingular (hsing L) hα
    rw [h0] at this
    simpa [WeierstrassCurve.baseChange] using this
  by_cases hs : W.nodePolynomial.Splits
  · -- at a split node a tangent slope `t` lies in `F`, and `Fr` fixes it
    obtain ⟨t, ht⟩ := hsplit.1 hs
    have hα : algebraMap F K t ^ 2 + (W⁄K).a₁ * algebraMap F K t -
        (3 * algebraMap F K x₀ + (W⁄K).a₂) = 0 := by
      have := congrArg (algebraMap F K) ht
      simp only [_root_.map_add, _root_.map_mul, _root_.map_pow, _root_.map_neg, map_ofNat,
        one_mul, _root_.map_zero] at this
      simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂]
      linear_combination this
    rw [frobeniusTrace_eq_one_of_splits W hΔ hc₄ hs, Nat.card_eq_fintype_card]
    exact map_frobeniusAlgHom_eq_zsmul_of_isSingular (hsing K) hα (hnode K hα) (hK x₀) (hK y₀)
      (.inl ⟨rfl, hK t⟩) P
  · -- at a nonsplit node the tangent slopes lie in an algebraic closure `L` of `K` but not in
    -- `F`, so `Fr` exchanges them; the statement over `K` is read off the one over `L`
    rw [frobeniusTrace_eq_neg_one_of_not_splits W hΔ hs, Nat.card_eq_fintype_card]
    let L := AlgebraicClosure K
    let ι := IsScalarTower.toAlgHom F K L
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
      (C 1 * X ^ 2 + C (W⁄L).a₁ * X + C (-(3 * algebraMap F L x₀ + (W⁄L).a₂)))
      (by rw [degree_quadratic one_ne_zero]; decide)
    replace hα : α ^ 2 + (W⁄L).a₁ * α - (3 * algebraMap F L x₀ + (W⁄L).a₂) = 0 := by
      simpa [sub_eq_add_neg] using hα
    have hαq : α ^ Fintype.card F = -(W⁄L).a₁ - α := by
      have ha₁ : (W⁄L).a₁ = algebraMap F L W.a₁ := by simp [WeierstrassCurve.baseChange]
      have ha₂ : (W⁄L).a₂ = algebraMap F L W.a₂ := by simp [WeierstrassCurve.baseChange]
      have := TauCeti.FiniteField.pow_card_eq_neg_sub_of_not_exists_root
        (b := W.a₁) (c := -(3 * x₀ + W.a₂)) (L := L) (α := α)
        (fun ⟨t, ht⟩ ↦ hs (hsplit.2 ⟨t, by linear_combination ht⟩))
        (by
          simp only [_root_.map_neg, _root_.map_add, _root_.map_mul, map_ofNat, ← ha₁, ← ha₂]
          linear_combination hα)
      rwa [← ha₁] at this
    have hL := map_frobeniusAlgHom_eq_zsmul_of_isSingular (hsing L) hα (hnode L hα) (hK x₀) (hK y₀)
      (.inr ⟨rfl, hαq⟩) (map ι P)
    -- `ι` commutes with the `q`-power maps and is injective on points
    apply map_injective ι
    rw [map_zsmul, map_map, ι.frobeniusAlgHom_comm, ← map_map, hL]

end WeierstrassCurve.Affine.Point

end
