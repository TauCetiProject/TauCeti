/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.FunctionField.Elliptic.NormalForm

/-!
# Nonsingularity of the Weierstrass equation of a genus-one function field

Let `x` and `y` be Weierstrass coordinates at a place `P` of degree one of a function field
`F / k`: they have pole divisors `2P` and `3P` and satisfy the equation of a Weierstrass curve
`W` over `k`.  This file shows that `W` has no singular point over `k` unless `F` has genus
zero; over a perfect field this makes `W` an elliptic curve.

The argument is the classical one.  If `(x₀, y₀) ∈ k²` is a singular point of `W`, then the
Taylor expansion of the Weierstrass equation at it reads `Y² + a₁XY = X³ + (3x₀ + a₂)X²` for
`X = x - x₀` and `Y = y - y₀`.  Dividing by `X²` shows that the slope `z = Y / X` satisfies
`X = z² + a₁z - (3x₀ + a₂)` and `Y = zX`, so `x` and `y` lie in `k(z)`.  Since `x` and `y`
generate `F`, so does `z`, and `F` has genus zero.

Over a perfect field a singular Weierstrass curve always has a rational singular point
(`WeierstrassCurve.Affine.exists_isSingular_of_Δ_eq_zero`), so the Weierstrass curve of a
genus-one function field is elliptic.  Over an imperfect field a singular point need not be
rational (for `y² = x³ + t` over `𝔽₂(t)` it is `(0, √t)`), and the argument gives no information
there.  For two of the normal forms, nonsingularity has a form that needs no perfectness: the
cubic of `Y² = X³ + a₂X² + a₄X + a₆` is squarefree, because a double root of it is a rational
singular point, and `a₆ ≠ 0` in `Y² + XY = X³ + a₂X² + a₆`, because otherwise the origin is
singular.

## Main results

* `TauCeti.Place.IsWeierstrassCoordinates.adjoin_div_eq_top_of_isSingular`: at a rational
  singular point `(x₀, y₀)` of `W`, the slope `(y - y₀) / (x - x₀)` generates `F`.
* `TauCeti.Place.IsWeierstrassCoordinates.genus_eq_zero_of_isSingular`: so `F` has genus zero.
* `TauCeti.Place.IsWeierstrassCoordinates.isElliptic`: over a perfect field, the Weierstrass
  curve of a function field of nonzero genus is elliptic.
* `TauCeti.Place.IsWeierstrassCoordinates.squarefree_of_isCharNeTwoNF` and
  `TauCeti.Place.IsWeierstrassCoordinates.a₆_ne_zero_of_isCharTwoJNeZeroNF`: the
  nonsingularity conditions of the normal forms `Y² = X³ + a₂X² + a₄X + a₆` and
  `Y² + XY = X³ + a₂X² + a₆`, over an arbitrary field.
* `TauCeti.Place.exists_isWeierstrassCoordinates_isElliptic_of_genus_eq_one`: over a perfect
  exact constant field, a genus-one function field has Weierstrass coordinates for an elliptic
  curve at every place of degree one.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 6.1.2.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer, 2009,
  Proposition III.1.4.
-/

public section

namespace TauCeti

open AlgebraicGeometry WeierstrassCurve _root_.Polynomial

open scoped _root_.IntermediateField

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place.IsWeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : P.IsWeierstrassCoordinates W x y)
include h

/-- **At a rational singular point the slope generates the function field**: if `(x₀, y₀)` is
a singular point of `W` over `k`, then `F = k(z)` for `z = (y - y₀) / (x - x₀)`. -/
theorem adjoin_div_eq_top_of_isSingular (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) :
    k⟮(y - algebraMap k F y₀) / (x - algebraMap k F x₀)⟯ = ⊤ := by
  set X := x - algebraMap k F x₀ with hXdef
  set z := (y - algebraMap k F y₀) / X
  have hX0 : X ≠ 0 := sub_ne_zero.mpr fun hx ↦
    h.transcendental_x (hx ▸ isAlgebraic_algebraMap x₀)
  have hY : y - algebraMap k F y₀ = z * X := (div_mul_cancel₀ _ hX0).symm
  -- The equation expanded at the singular point, divided by `X²`, gives
  -- `X = z² + a₁z - (3x₀ + a₂)`; together with `y - y₀ = zX` this puts `x` and `y` in `k(z)`.
  have hXz : X = z ^ 2 + algebraMap k F W.a₁ * z - algebraMap k F (3 * x₀ + W.a₂) := by
    have key := (Affine.equation_iff_of_isSingular (hs.map (algebraMap k F)) x y).mp h.equation
    simp only [Affine.map, map_a₁, map_a₂, ← map_ofNat (algebraMap k F) 3, ← map_mul,
      ← map_add] at key
    rw [← hXdef, hY] at key
    have : X ^ 2 * (X - (z ^ 2 + algebraMap k F W.a₁ * z - algebraMap k F (3 * x₀ + W.a₂))) =
        0 := by
      linear_combination -key
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hX0))
  set K := k⟮z⟯
  have hz : z ∈ K := IntermediateField.mem_adjoin_simple_self k z
  have hXK : X ∈ K := by
    rw [hXz]
    exact K.sub_mem (K.add_mem (pow_mem hz 2) (K.mul_mem (K.algebraMap_mem _) hz))
      (K.algebraMap_mem _)
  have hxK : x ∈ K := by
    have hx : x = X + algebraMap k F x₀ := (sub_add_cancel x _).symm
    rw [hx]
    exact K.add_mem hXK (K.algebraMap_mem x₀)
  have hyK : y ∈ K := by
    have hy : y = z * X + algebraMap k F y₀ := eq_add_of_sub_eq hY
    rw [hy]
    exact K.add_mem (K.mul_mem hz hXK) (K.algebraMap_mem y₀)
  rw [eq_top_iff, ← h.adjoin_eq_top hF hP, IntermediateField.adjoin_le_iff]
  exact Set.insert_subset_iff.mpr ⟨hxK, Set.singleton_subset_iff.mpr hyK⟩

/-- **A Weierstrass equation with a rational singular point defines a rational function
field**: if `W` has a singular point over `k`, then `F` has genus zero. -/
theorem genus_eq_zero_of_isSingular (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) : genus k F = 0 := by
  set z := (y - algebraMap k F y₀) / (x - algebraMap k F x₀)
  have htop : k⟮z⟯ = ⊤ := h.adjoin_div_eq_top_of_isSingular hF hP hs
  -- `x` lies in `k(z)`, so `z` is transcendental together with `x`.
  refine genus_eq_zero_of_adjoin_eq_top (fun hz ↦ h.transcendental_x ?_) htop
  have := IntermediateField.isAlgebraic_adjoin_simple hz.isIntegral
  have hx : x ∈ k⟮z⟯ := htop ▸ IntermediateField.mem_top
  exact (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : k⟮z⟯)).algHom k⟮z⟯.val

/-- **The Weierstrass curve of a function field of nonzero genus is elliptic**, over a perfect
field. -/
theorem isElliptic [PerfectField k] (hF : IsFunctionField k F) (hP : P.degree = 1)
    (hg : genus k F ≠ 0) : W.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  -- Over a perfect field a vanishing discriminant produces a rational singular point.
  intro hΔ
  obtain ⟨x₀, y₀, hs⟩ := Affine.exists_isSingular_of_Δ_eq_zero W.toAffine hΔ
  exact hg (h.genus_eq_zero_of_isSingular hF hP hs)

/-- **The nonsingularity condition of the normal form `Y² = X³ + a₂X² + a₄X + a₆`**: for a
function field of nonzero genus the cubic is squarefree, over an arbitrary field. -/
theorem squarefree_of_isCharNeTwoNF [W.IsCharNeTwoNF] (hF : IsFunctionField k F)
    (hP : P.degree = 1) (hg : genus k F ≠ 0) :
    Squarefree (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : k[X]) := by
  set f : k[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ with hfdef
  have hf3 : f.natDegree = 3 := by rw [hfdef]; compute_degree!
  have hf0 : f ≠ 0 := by rintro hf; simp [hf] at hf3
  -- A non-unit `g` with `g² ∣ f` has degree one, so it has a root `a`, and `(X - a)² ∣ f`.
  intro g hg2
  by_contra hgu
  have hg0 : g ≠ 0 := by rintro rfl; simp [hf0] at hg2
  have hdeg : g.natDegree = 1 := by
    have := natDegree_le_of_dvd hg2 hf0
    rw [natDegree_mul hg0 hg0, hf3] at this
    have h1 : g.natDegree ≠ 0 := fun h0 ↦ hgu <| by
      rw [natDegree_eq_zero] at h0
      obtain ⟨c, rfl⟩ := h0
      exact isUnit_C.mpr (Ne.isUnit (by rintro rfl; simp at hg0))
    omega
  obtain ⟨a, ha⟩ :=
    exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hdeg)
  obtain ⟨q, hq⟩ : (X - C a) ^ 2 ∣ f := by
    rw [sq]
    exact (mul_dvd_mul (dvd_iff_isRoot.mpr ha) (dvd_iff_isRoot.mpr ha)).trans hg2
  have h0 : a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆ = 0 := by
    have hfa : f.eval a = a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆ := by simp [hfdef]
    rw [← hfa]
    simp [hq]
  have h1 : 3 * a ^ 2 + 2 * W.a₂ * a + W.a₄ = 0 := by
    have hf'a : (derivative f).eval a = 3 * a ^ 2 + 2 * W.a₂ * a + W.a₄ := by
      simp [hfdef]; ring
    rw [← hf'a]
    simp [hq, derivative_mul, derivative_pow]
  -- The double root `a` makes `(a, 0)` a rational singular point.
  refine hg (h.genus_eq_zero_of_isSingular hF hP (x₀ := a) (y₀ := 0) ?_)
  rw [Affine.isSingular_iff', Affine.equation_iff, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  refine ⟨by linear_combination -h0, by linear_combination -h1, by ring⟩

/-- **The nonsingularity condition of the normal form `Y² + XY = X³ + a₂X² + a₆`**: for a
function field of nonzero genus, `a₆ ≠ 0`, over an arbitrary field. -/
theorem a₆_ne_zero_of_isCharTwoJNeZeroNF [W.IsCharTwoJNeZeroNF] (hF : IsFunctionField k F)
    (hP : P.degree = 1) (hg : genus k F ≠ 0) : W.a₆ ≠ 0 := fun h₆ ↦
  -- If `a₆ = 0`, the origin is a singular point.
  hg (h.genus_eq_zero_of_isSingular hF hP ((Affine.isSingular_zero _).mpr
    ⟨h₆, a₄_of_isCharTwoJNeZeroNF W, a₃_of_isCharTwoJNeZeroNF W⟩))

end Place.IsWeierstrassCoordinates

namespace Place

/-- **Nonsingular Weierstrass coordinates** (Stichtenoth, Proposition 6.1.2): over a perfect
exact constant field, at every place of degree one of a genus-one function field there are
Weierstrass coordinates for an elliptic curve. -/
theorem exists_isWeierstrassCoordinates_isElliptic_of_genus_eq_one [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1)
    {P : Place k F} (hP : P.degree = 1) :
    ∃ (W : WeierstrassCurve k) (x y : F), W.IsElliptic ∧ P.IsWeierstrassCoordinates W x y := by
  obtain ⟨W, x, y, h⟩ := P.exists_isWeierstrassCoordinates_of_genus_eq_one hF hex hg hP
  exact ⟨W, x, y, h.isElliptic hF hP (by omega), h⟩

end Place

/-- An elliptic function field over a perfect exact constant field has a place of degree one with
Weierstrass coordinates for an elliptic curve. -/
theorem IsEllipticFunctionField.exists_isWeierstrassCoordinates_isElliptic [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (he : IsEllipticFunctionField k F) :
    ∃ (P : Place k F) (W : WeierstrassCurve k) (x y : F),
      P.degree = 1 ∧ W.IsElliptic ∧ P.IsWeierstrassCoordinates W x y := by
  obtain ⟨P, hP⟩ := he.exists_place_degree_eq_one hF hex
  obtain ⟨W, x, y, hW, h⟩ :=
    P.exists_isWeierstrassCoordinates_isElliptic_of_genus_eq_one hF hex he.genus_eq_one hP
  exact ⟨P, W, x, y, hP, hW, h⟩

end TauCeti
