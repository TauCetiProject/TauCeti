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
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
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
compared. Along `ι : F → F(W)`, the function-field embedding `FunctionField.map W ι` and the scalar
embedding `algebraMap F(W) (F(W))(W)` agree to first order at the place of `W.genericPoint`
(`WeierstrassCurve.Affine.valuation_pointPlace_genericX_genericY_map_sub_algebraMap_lt_one`).

## Main results

* `WeierstrassCurve.Affine.valuation_pointPlace_genericX_sub_lt_one` and
  `WeierstrassCurve.Affine.valuation_pointPlace_genericY_sub_lt_one`: `x - a` and `y - b` vanish
  at the place of `(a, b)`.
* `WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`: the generic point reduces to `P`
  at the place of `P`.
* `WeierstrassCurve.Affine.isEquiv_comap_pointPlace_map`: the place of a point transported along
  a field homomorphism `f` restricts along `FunctionField.map W f` to the place of the point.
* `WeierstrassCurve.Affine.valuation_pointPlace_genericX_genericY_map_sub_algebraMap_lt_one`:
  `FunctionField.map W ι` and `algebraMap F(W) (F(W))(W)` agree modulo the place of
  `W.genericPoint`.
* `WeierstrassCurve.Affine.map_mem_polePoints_smul_iff` and
  `WeierstrassCurve.Affine.reductionOfDegreeEqOne_smul_map`: reduction commutes with field
  automorphisms and their action on places.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1, VII.2.1.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve.Affine

/-- For a valuation `v` on `L` trivial on `E`, the elements of `E` where a ring homomorphism
`μ : E →+* L` (agreeing with `algebraMap E L` on `F`) agrees with `algebraMap E L` modulo `v < 1`
form an intermediate field of `E / F`. -/
private def eqModValuationIntermediateField {F E L Γ : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) [v.IsTrivialOn E] (μ : E →+* L)
    (hμ : ∀ c : F, μ (algebraMap F E c) = algebraMap E L (algebraMap F E c)) :
    IntermediateField F E where
  carrier := {x : E | v (μ x - algebraMap E L x) < 1}
  algebraMap_mem' c := by
    rw [Set.mem_ofPred_eq, hμ, sub_self, map_zero]
    exact zero_lt_one
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq, _root_.map_add, _root_.map_add, add_sub_add_comm]
    exact v.map_add_lt hx hy
  mul_mem' {x y} hx hy := by
    have hμx : v (μ x) ≤ 1 := by
      have hκ : v (algebraMap E L x) ≤ 1 := Valuation.IsTrivialOn.valuation_algebraMap_le_one v x
      simpa only [sub_add_cancel] using
        (v.map_add (μ x - algebraMap E L x) (algebraMap E L x)).trans (max_le hx.le hκ)
    have hmul : μ x * μ y - algebraMap E L x * algebraMap E L y =
        (μ x - algebraMap E L x) * algebraMap E L y + μ x * (μ y - algebraMap E L y) := by ring
    rw [Set.mem_ofPred_eq, map_mul, map_mul, hmul]
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hx (Valuation.IsTrivialOn.valuation_algebraMap_le_one v y)
    · rw [map_mul]
      exact mul_lt_of_le_one_of_lt hμx hy
  inv_mem' x hx := by
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hx' : v (μ x - algebraMap E L x) < 1 := hx
    have hκx : v (algebraMap E L x) = 1 := Valuation.IsTrivialOn.eq_one (v := v) x hx0
    have hμx : v (μ x) = 1 := by
      simpa only [sub_add_cancel, hκx] using
        Valuation.map_add_eq_of_lt_right v (hx'.trans_eq hκx.symm)
    have hμx0 : μ x ≠ 0 := (map_ne_zero_iff μ μ.injective).mpr hx0
    have hκx0 : algebraMap E L x ≠ 0 :=
      (map_ne_zero_iff (algebraMap E L) (algebraMap E L).injective).mpr hx0
    rw [Set.mem_ofPred_eq, map_inv₀, map_inv₀, inv_sub_inv hμx0 hκx0, map_div₀, map_mul,
      hμx, hκx, mul_one, div_one, ← neg_sub, Valuation.map_neg]
    exact hx'

@[simp]
private theorem mem_eqModValuationIntermediateField {F E L Γ : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) [v.IsTrivialOn E] (μ : E →+* L)
    (hμ : ∀ c : F, μ (algebraMap F E c) = algebraMap E L (algebraMap F E c)) {x : E} :
    x ∈ eqModValuationIntermediateField v μ hμ ↔ v (μ x - algebraMap E L x) < 1 :=
  Iff.rfl

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

/-- **Along `ι : F → F(W)`, the function-field embedding `FunctionField.map W ι` and the scalar
embedding `algebraMap F(W) (F(W))(W)` agree to first order at the place of `W.genericPoint`.** -/
theorem valuation_pointPlace_genericX_genericY_map_sub_algebraMap_lt_one
    (z : W.FunctionField) :
    (Place.ofPrime W.FunctionField (W.map (algebraMap F W.FunctionField)).FunctionField
      (CoordinateRing.pointPlace (W := W.map (algebraMap F W.FunctionField))
        W.equation_genericX_genericY)).valuation
        (FunctionField.map W (algebraMap F W.FunctionField) z -
          algebraMap W.FunctionField (W.map (algebraMap F W.FunctionField)).FunctionField z) <
      1 := by
  let ι := algebraMap F W.FunctionField
  let v := (Place.ofPrime W.FunctionField (W.map ι).FunctionField
    (CoordinateRing.pointPlace (W := W.map ι) W.equation_genericX_genericY)).valuation
  let S := eqModValuationIntermediateField v (FunctionField.map W ι)
    (fun c ↦ FunctionField.map_algebraMap W ι c)
  have hX : W.genericX ∈ S := by
    rw [mem_eqModValuationIntermediateField, FunctionField.map_genericX]
    exact valuation_pointPlace_genericX_sub_lt_one (W.map ι) W.equation_genericX_genericY
  have hY : W.genericY ∈ S := by
    rw [mem_eqModValuationIntermediateField, FunctionField.map_genericY]
    exact valuation_pointPlace_genericY_sub_lt_one (W.map ι) W.equation_genericX_genericY
  have htop : S = ⊤ :=
    top_unique (W.adjoin_genericX_genericY_eq_top ▸
      IntermediateField.adjoin_le_iff.mpr (Set.pair_subset hX hY))
  exact (mem_eqModValuationIntermediateField v _ _).mp (htop ▸ IntermediateField.mem_top)

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
