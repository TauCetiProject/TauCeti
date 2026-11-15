/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.DegreeOneReduction
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Basic
-- Proof-only: a nontrivial valuation bounded by `1` on a Dedekind domain is adic up to equivalence.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# The reduction of the generic point

Let `W` be an elliptic curve over a field `F`. The generic point `(genericX, genericY)` is a
point of `W` over its own function field `F(W)`, and every point `P` of `W` has a place of
`F(W)`, of degree one (`WeierstrassCurve.Affine.pointEquivDegreeOnePlace`). At that place the
generic point **reduces to `P`**.

In the language of `Affine/Point/DegreeOneReduction.lean`, this is the statement that
`reductionOfDegreeEqOne` of the generic point at the place of `P` is `P`
(`WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`). Any `F`-algebra map `τ` out of
`F(W)` carries the generic point to the tautological point of `τ`, and this identity is what the
reduction of such points is computed from: an isogeny's action on points in particular.

Transporting a point along a homomorphism of fields `f : F →+* K` is compatible with places: the
place of the transported point restricts along `FunctionField.map W f` to the place of the point
(`WeierstrassCurve.Affine.isEquiv_comap_pointPlace_map`), so reduction at the two places can be
compared.

## Main results

* `WeierstrassCurve.Affine.valuation_pointPlace_genericX_sub_lt_one` and
  `WeierstrassCurve.Affine.valuation_pointPlace_genericY_sub_lt_one`: `x - a` and `y - b` vanish
  at the place of `(a, b)`.
* `WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`: the generic point reduces to `P`
  at the place of `P`.
* `WeierstrassCurve.Affine.isEquiv_comap_pointPlace_map`: the place of a point transported along
  a field homomorphism `f` restricts along `FunctionField.map W f` to the place of the point.
* `WeierstrassCurve.Affine.valuation_pointPlace_functionFieldMap_sub_lt_one`: at the diagonal
  place of `genericPoint` on `W⁄F(W)`, `FunctionField.map W (algebraMap F F(W))` agrees with
  `algebraMap F(W) _` to first order.
* `WeierstrassCurve.Affine.map_mem_polePoints_smul_iff` and
  `WeierstrassCurve.Affine.reductionOfDegreeEqOne_smul_map`: reduction commutes with field
  automorphisms and their action on places.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1, VII.2.1.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : Affine F) [W.IsElliptic]

/-- **`x - a` vanishes at the place of `(a, b)`**: the class of `X - a` lies in the point ideal. -/
theorem valuation_pointPlace_genericX_sub_lt_one {x y : F} (h : W.Equation x y) :
    (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)).valuation
      (genericX W - algebraMap F W.FunctionField x) < 1 := by
  rw [← algebraMap_XClass, Place.valuation_ofPrime_algebraMap_lt_one_iff,
    CoordinateRing.pointPlace_asIdeal]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- **`y - b` vanishes at the place of `(a, b)`**: the class of `Y - b` lies in the point ideal. -/
theorem valuation_pointPlace_genericY_sub_lt_one {x y : F} (h : W.Equation x y) :
    (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)).valuation
      (genericY W - algebraMap F W.FunctionField y) < 1 := by
  rw [← algebraMap_YClass, Place.valuation_ofPrime_algebraMap_lt_one_iff,
    CoordinateRing.pointPlace_asIdeal]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

section BaseChange

variable {K : Type*} [Field K] (f : F →+* K)

open IsDedekindDomain in
/-- **The place of a transported point restricts to the place of the point**: along the embedding
`FunctionField.map W f : F(W) → K(W)`, the valuation of the place of `(f a, f b)` restricts to one
equivalent to the valuation of the place of `(a, b)`. The restriction is bounded by `1` on the
coordinate ring of `W` and vanishes on `x - a` and `y - b`, so its centre is the ideal of
`(a, b)`. -/
theorem isEquiv_comap_pointPlace_map {x y : F} (h : W.Equation x y) :
    (((Place.ofPrime K (W.map f).FunctionField (CoordinateRing.pointPlace
      ((W.map_equation f.injective x y).mpr h))).valuation).comap
        (FunctionField.map W f)).IsEquiv
      (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)).valuation := by
  set u := ((Place.ofPrime K (W.map f).FunctionField (CoordinateRing.pointPlace
      ((W.map_equation f.injective x y).mpr h))).valuation).comap (FunctionField.map W f) with hu
  -- `x - a` and `y - b` vanish at the place of the transported point
  have hx : u (genericX W - algebraMap F W.FunctionField x) < 1 := by
    rw [hu, Valuation.comap_apply, map_sub, FunctionField.map_genericX,
      FunctionField.map_algebraMap]
    exact valuation_pointPlace_genericX_sub_lt_one _ _
  have hy : u (genericY W - algebraMap F W.FunctionField y) < 1 := by
    rw [hu, Valuation.comap_apply, map_sub, FunctionField.map_genericY,
      FunctionField.map_algebraMap]
    exact valuation_pointPlace_genericY_sub_lt_one _ _
  have : u.IsNontrivial := ⟨⟨_, (Valuation.ne_zero_iff u).mpr
    (sub_ne_zero.mpr (genericX_ne_algebraMap W x)), hx.ne⟩⟩
  have hR (r : W.CoordinateRing) : u (algebraMap W.CoordinateRing W.FunctionField r) ≤ 1 := by
    rw [hu, Valuation.comap_apply, FunctionField.map_algebraMap_coordinateRing,
      Place.valuation_ofPrime]
    exact HeightOneSpectrum.valuation_le_one _ _
  obtain ⟨𝔭, he, hmem⟩ :=
    Valuation.exists_heightOneSpectrum_isEquiv_of_le_one W.CoordinateRing u hR
  -- the centre of `u` contains, hence is, the maximal ideal of `(a, b)`
  have h𝔭 : 𝔭 = CoordinateRing.pointPlace h := by
    refine HeightOneSpectrum.ext (((CoordinateRing.pointPlace h).isMaximal.eq_of_le
      𝔭.isPrime.ne_top ?_).symm)
    rw [CoordinateRing.pointPlace_asIdeal, CoordinateRing.XYIdeal, Ideal.span_le]
    rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, hmem]
    · rwa [algebraMap_XClass]
    · rwa [algebraMap_YClass]
  rw [Place.valuation_ofPrime, ← h𝔭]
  exact he.symm

/-- On `F[genericX, genericY] ⊆ F(W)`, the second-factor embedding `FunctionField.map` is
bounded by `1` and agrees with `algebraMap` to first order at the diagonal place. -/
private theorem valuation_pointPlace_functionFieldMap_sub_lt_one_of_mem_adjoin
    (heq : (W.map (algebraMap F W.FunctionField)).Equation W.genericX W.genericY)
    {a : W.FunctionField} (ha : a ∈ Algebra.adjoin F {W.genericX, W.genericY}) :
    let L := W.FunctionField
    let ι := algebraMap F L
    let v := (Place.ofPrime L (W.map ι).FunctionField (CoordinateRing.pointPlace heq)).valuation
    v (FunctionField.map W ι a) ≤ 1 ∧ v (FunctionField.map W ι a - algebraMap L _ a) < 1 := by
  set L := W.FunctionField
  set ι := algebraMap F L
  set v := (Place.ofPrime L (W.map ι).FunctionField (CoordinateRing.pointPlace heq)).valuation
  set w := FunctionField.map W ι
  set c := algebraMap L (W.map ι).FunctionField
  have hc_le (b : L) : v (c b) ≤ 1 := Valuation.IsTrivialOn.valuation_algebraMap_le_one v b
  have hgen_le (b : L) (hlt : v (w b - c b) < 1) : v (w b) ≤ 1 ∧ v (w b - c b) < 1 := by
    have hsplit : w b = (w b - c b) + c b := by ring
    exact ⟨hsplit ▸ (v.map_add _ _).trans (max_le hlt.le (hc_le _)), hlt⟩
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
  · rintro b (rfl | rfl)
    · refine hgen_le _ ?_
      have hwX : w W.genericX = (W.map ι).genericX := FunctionField.map_genericX W ι
      rw [hwX]
      exact valuation_pointPlace_genericX_sub_lt_one (W.map ι) heq
    · refine hgen_le _ ?_
      have hwY : w W.genericY = (W.map ι).genericY := FunctionField.map_genericY W ι
      rw [hwY]
      exact valuation_pointPlace_genericY_sub_lt_one (W.map ι) heq
  · intro k
    have hk : w (algebraMap F L k) = c (algebraMap F L k) := FunctionField.map_algebraMap W ι k
    exact ⟨hk ▸ hc_le _, by rw [hk, sub_self, Valuation.map_zero]; exact zero_lt_one⟩
  · intro x y _ _ hx hy
    refine ⟨by rw [map_add]; exact (v.map_add _ _).trans (max_le hx.1 hy.1), ?_⟩
    rw [map_add, map_add, add_sub_add_comm]
    exact (v.map_add _ _).trans_lt (max_lt hx.2 hy.2)
  · intro x y _ _ hx hy
    refine ⟨by rw [map_mul, Valuation.map_mul]; exact mul_le_one' hx.1 hy.1, ?_⟩
    have hmul_sub : w x * w y - c x * c y = (w x - c x) * w y + c x * (w y - c y) := by ring
    rw [map_mul, map_mul, hmul_sub]
    refine (v.map_add _ _).trans_lt (max_lt ?_ ?_)
    · rw [Valuation.map_mul]; exact Left.mul_lt_one_of_lt_of_le hx.2 hy.1
    · rw [Valuation.map_mul]; exact Right.mul_lt_one_of_le_of_lt (hc_le x) hy.2

/-- **At the diagonal place of `W.genericPoint` on `W⁄F(W)`, the second-factor embedding
`FunctionField.map W (algebraMap F F(W))` agrees with `algebraMap F(W) _` to first order on every
element of `F(W)`.** -/
theorem valuation_pointPlace_functionFieldMap_sub_lt_one
    (heq : (W.map (algebraMap F W.FunctionField)).Equation W.genericX W.genericY)
    (z : W.FunctionField) :
    (Place.ofPrime W.FunctionField (W.map (algebraMap F W.FunctionField)).FunctionField
      (CoordinateRing.pointPlace heq)).valuation
        (FunctionField.map W (algebraMap F W.FunctionField) z -
          algebraMap W.FunctionField _ z) < 1 := by
  obtain ⟨r, s, hs_mem, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  set L := W.FunctionField
  set ι := algebraMap F L
  set v := (Place.ofPrime L (W.map ι).FunctionField (CoordinateRing.pointPlace heq)).valuation
  set w := FunctionField.map W ι
  set c := algebraMap L (W.map ι).FunctionField
  set r' : L := algebraMap W.CoordinateRing L r
  set s' : L := algebraMap W.CoordinateRing L s
  have hr := valuation_pointPlace_functionFieldMap_sub_lt_one_of_mem_adjoin W heq
    (algebraMap_mem_adjoin_genericX_genericY W r)
  have hs := valuation_pointPlace_functionFieldMap_sub_lt_one_of_mem_adjoin W heq
    (algebraMap_mem_adjoin_genericX_genericY W s)
  have hs0 : s' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs_mem
  have hcs : v (c s') = 1 := Valuation.IsTrivialOn.eq_one (v := v) s' hs0
  have hws : v (w s') = 1 := by
    have hsplit : w s' = (w s' - c s') + c s' := by ring
    rw [hsplit, v.map_add_eq_of_lt_right (hs.2.trans_eq hcs.symm), hcs]
  have hws0 : w s' ≠ 0 := fun h ↦ by simp [h] at hws
  have hcs0 : c s' ≠ 0 := (map_ne_zero_iff c c.injective).mpr hs0
  have hquot : w (r' / s') - c (r' / s') =
      ((w r' - c r') * c s' - c r' * (w s' - c s')) / (w s' * c s') := by
    rw [map_div₀, map_div₀]; field_simp [hws0, hcs0]; ring
  rw [hquot, map_div₀, Valuation.map_mul, hws, hcs, mul_one, div_one]
  refine (v.map_sub _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_mul, hcs, mul_one]; exact hr.2
  · rw [Valuation.map_mul]
    exact Right.mul_lt_one_of_le_of_lt
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one v r') hs.2

end BaseChange

section Automorphism

variable {K : Type*} [Field K] [Algebra F K] [DecidableEq K]

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

variable [DecidableEq F]

/-- **The generic point reduces to `P` at the place of `P`.** -/
@[simp]
theorem reductionOfDegreeEqOne_genericPoint (P : W.Point) :
    reductionOfDegreeEqOne W (W.pointEquivDegreeOnePlace P).2 (genericPoint W) =
      Point.equivBaseChangeSelf W P := by
  rw [reductionOfDegreeEqOne_eq_iff]
  rcases P with _ | ⟨x, y, h⟩
  · rw [coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def, map_zero, map_zero, sub_zero,
      mem_polePoints_iff, xCoord_genericPoint, Place.valuation_infinity, genericX_eq_algebraMap]
    exact Or.inr (one_lt_infinityPlace_X W)
  · rw [Point.equivBaseChangeSelf_some W h, genericPoint_eq_some,
      some_sub_baseChange_mem_polePoints_iff, coe_pointEquivDegreeOnePlace_some]
    exact ⟨valuation_pointPlace_genericX_sub_lt_one W h.1,
      valuation_pointPlace_genericY_sub_lt_one W h.1⟩

end WeierstrassCurve.Affine

end
