/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
-- Proof-only: a Frobenius element raises residues to the `q`-th power and keeps poles.
import TauCeti.RingTheory.Valuation.FrobeniusElement
-- Proof-only: transport of points along an equality of curves keeps their coordinates.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
-- Proof-only: reduction is injective on torsion prime to the residue characteristic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
-- Proof-only: the `q`-power map on points is a root of `X² - a_q X + q`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Charpoly
-- Proof-only: the `q`-power map on the points of a nodal cubic is multiplication by `a_q q`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Frobenius.Node

/-!
# Reduction turns a Frobenius element into the `q`-power map

Let `W` be a Weierstrass curve over a field `K`, and let `L` be an extension of `K` with a
valuation `v`, valuation ring `O` and residue field `k`, over which `W` has an integral model.
Reduction of points is a homomorphism `E₀(L) →+ W_k,ns(k)` from the points with nonsingular
reduction to the nonsingular points of the reduced curve
(`WeierstrassCurve.Affine.nonsingularReductionHom`); at good reduction `E₀(L)` is all of `W(L)`
and this is `WeierstrassCurve.Affine.Point.reductionHom`.

Suppose that the reduced curve is the base change to `k` of a curve `C` over a finite subfield `F`
of `k` with `q` elements, as the reduction of a curve over a local field is the base change of its
reduction over the smaller residue field. Let `τ` be a `K`-algebra endomorphism of `L` which is a
**Frobenius element** for `v`: `v (τ x - x ^ q) < 1` for every `x` in `O`, so that `τ` acts on
`k` as the `q`-power map. Then `τ` preserves `E₀(L)`, and reduction carries `τ` to the `q`-power
map on the coordinates of the points of `C` over `k`:

`red (τ P) = Fr (red P)`.

This is how the Galois action of a Frobenius element on the points with nonsingular reduction is
computed on the reduced curve. At good reduction the `q`-power map satisfies
`Fr² - a_q Fr + q = 0` (`TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom`); when `C` is a
nodal cubic, as at multiplicative reduction, it is multiplication by `a_q q`, with `a_q = ±1`
(`WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_eq_zsmul`).

Over the fraction field `L` of a Dedekind domain, at a height-one prime `u`, these give relations
on the torsion of order prime to `u` with nonsingular reduction, where `a_q` is the Frobenius trace
of `C`: `τ (τ P) = a_q • τ P - q • P` at good reduction, and `τ P = (a_q q) • P` at a node. In
each case the difference of the two sides reduces to the point at infinity and is killed by an
integer prime to `u`, and reduction is injective on such torsion
(`WeierstrassCurve.Affine.Point.eq_zero_of_nonsingularReductionHom_eq_zero_of_nsmul_eq_zero`).

## Main results

* `WeierstrassCurve.Affine.Point.map_mem_nonsingularReduction`: a Frobenius element for `v`
  preserves the points with nonsingular reduction.
* `WeierstrassCurve.Affine.Point.cast_nonsingularReductionHom_map_eq_map_frobeniusAlgHom` and,
  at good reduction, `WeierstrassCurve.Affine.Point.cast_reductionHom_map_eq_map_frobeniusAlgHom`:
  reduction carries a Frobenius element for `v` to the `q`-power map on the points of the reduced
  curve.
* `WeierstrassCurve.Affine.Point.map_map_eq_of_nsmul_eq_zero`: over the fraction field of a
  Dedekind domain, an endomorphism acting on the residues at a prime `u` of good reduction as the
  `q`-power map satisfies `τ (τ P) = a_q • τ P - q • P` on the torsion of order prime to `u`.
* `WeierstrassCurve.Affine.Point.map_eq_zsmul_of_nsmul_eq_zero`: at a prime `u` where the
  reduction is a node, such an endomorphism satisfies `τ P = (a_q q) • P` on the torsion of order
  prime to `u` with nonsingular reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.3.1, VII.2, VII.3.1 and
  VII.7.
-/

public section

open IsLocalRing

namespace WeierstrassCurve.Affine.Point

variable {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) {W : WeierstrassCurve K} [IsIntegral v.valuationSubring (W⁄L)]
  [DecidableEq L] [DecidableEq (ResidueField v.valuationSubring)]
  {F : Type*} [Field F] [Fintype F] [Algebra F (ResidueField v.valuationSubring)]
  {C : WeierstrassCurve F}

omit [DecidableEq (ResidueField v.valuationSubring)] in
/-- **A Frobenius element preserves nonsingular reduction.** Let the reduced curve of `W` at `v`
be the base change of a curve `C` over a finite field `F` with `q` elements, and let `τ` be a
`K`-algebra endomorphism of `L` with `v (τ x - x ^ q) < 1` for every `x` in the valuation ring.
If `P` lies in `E₀(L)`, so does `τ P`: the reduction of `τ P` is the image of the reduction of `P`
under the `q`-power map, which preserves the nonsingular points of `C`. -/
theorem map_mem_nonsingularReduction
    (hC : (integralModel v.valuationSubring (W⁄L)).map (residue v.valuationSubring) =
      C.baseChange (ResidueField v.valuationSubring))
    {τ : L →ₐ[K] L} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ Fintype.card F) < 1)
    {P : (W⁄L).toAffine.Point} (hP : P ∈ (W⁄L).toAffine.nonsingularReduction v) :
    map τ P ∈ (W⁄L).toAffine.nonsingularReduction v := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (W⁄L).toAffine.nonsingularReduction v |>.zero_mem
  rw [map_some]
  by_cases hx : v x ≤ 1
  · obtain ⟨hτx, hx'⟩ := v.exists_le_one_and_residue_eq_pow hτ hx
    obtain ⟨hτy, hy'⟩ := v.exists_le_one_and_residue_eq_pow hτ
      (valuation_y_le_one_of_valuation_x_le_one v h.left hx)
    rw [some_mem_nonsingularReduction_iff v h hx] at hP
    rw [some_mem_nonsingularReduction_iff v _ hτx, hx', hy', hC]
    rw [hC] at hP
    -- the `q`-power map is an injective `F`-algebra map of the residue field fixing `C`
    simpa only [FiniteField.frobeniusAlgHom_apply] using
      (C.toAffine.baseChange_nonsingular
        (FiniteField.frobeniusAlgHom F (ResidueField v.valuationSubring)).injective _ _).mpr hP
  · exact mem_nonsingularReduction_of_one_lt v
      (by rw [xCoord_some]; exact v.one_lt_map_of_one_lt Fintype.card_ne_zero hτ (not_le.mp hx))

/-- **Reduction carries a Frobenius element to the `q`-power map.** Let the reduced curve of `W`
at the valuation `v` of `L` be the base change of a curve `C` over a finite field `F` with `q`
elements, and let `τ` be a `K`-algebra endomorphism of `L` with `v (τ x - x ^ q) < 1` for every
`x` in the valuation ring. Then for every point `P` with nonsingular reduction, the reduction of
`τ P` is the image of the reduction of `P` under the `q`-power map
`FiniteField.frobeniusAlgHom` on the coordinates of the nonsingular points of `C`. -/
theorem cast_nonsingularReductionHom_map_eq_map_frobeniusAlgHom
    (hC : (integralModel v.valuationSubring (W⁄L)).map (residue v.valuationSubring) =
      C.baseChange (ResidueField v.valuationSubring))
    {τ : L →ₐ[K] L} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ Fintype.card F) < 1)
    (P : (W⁄L).toAffine.nonsingularReduction v) :
    AddEquiv.cast (M := fun V ↦ V.toAffine.Point) hC
        ((W⁄L).toAffine.nonsingularReductionHom v
          ⟨map τ P, map_mem_nonsingularReduction v hC hτ P.2⟩) =
      map (FiniteField.frobeniusAlgHom F _)
        (AddEquiv.cast (M := fun V ↦ V.toAffine.Point) hC
          ((W⁄L).toAffine.nonsingularReductionHom v P)) := by
  obtain ⟨_ | ⟨x, y, h⟩, hP⟩ := P
  · have e₁ : (⟨map τ .zero, map_mem_nonsingularReduction v hC hτ hP⟩ :
        (W⁄L).toAffine.nonsingularReduction v) = 0 := Subtype.ext (map_zero τ)
    have e₂ : (⟨.zero, hP⟩ : (W⁄L).toAffine.nonsingularReduction v) = 0 := rfl
    rw [e₁, e₂]
    simp only [_root_.map_zero]
  by_cases hx : v x ≤ 1
  · obtain ⟨hτx, hx'⟩ := v.exists_le_one_and_residue_eq_pow hτ hx
    obtain ⟨hτy, hy'⟩ := v.exists_le_one_and_residue_eq_pow hτ
      (valuation_y_le_one_of_valuation_x_le_one v h.left hx)
    have hτh := (W.toAffine.baseChange_nonsingular τ.injective x y).mpr h
    have hP' := (some_mem_nonsingularReduction_iff v h hx).mp hP
    have hτP' := (some_mem_nonsingularReduction_iff v hτh hτx).mp
      (map_mem_nonsingularReduction v hC hτ hP)
    simp only [map_some]
    rw [nonsingularReductionHom_some_of_valuation_le_one v hτh hτx hτP',
      nonsingularReductionHom_some_of_valuation_le_one v h hx hP', AddEquiv.cast_apply,
      AddEquiv.cast_apply, cast_some hC, cast_some hC, map_some]
    simp only [FiniteField.frobeniusAlgHom_apply, hx', hy']
  · -- a point with a pole reduces to the point at infinity, and so does its image under `τ`
    have hx₁ : 1 < v x := not_le.mp hx
    have hτx := v.one_lt_map_of_one_lt Fintype.card_ne_zero hτ hx₁
    have e₁ : (W⁄L).toAffine.nonsingularReductionHom v
        ⟨map τ (some x y h), map_mem_nonsingularReduction v hC hτ hP⟩ = 0 :=
      (nonsingularReductionHom_eq_zero_iff v _).mpr
        (.inr (by simpa [map_some, xCoord_some] using hτx))
    have e₂ : (W⁄L).toAffine.nonsingularReductionHom v ⟨some x y h, hP⟩ = 0 :=
      (nonsingularReductionHom_eq_zero_iff v _).mpr (.inr (by simpa [xCoord_some] using hx₁))
    rw [e₁, e₂]
    simp only [_root_.map_zero]

/-- **Reduction carries a Frobenius element to the `q`-power map**, at good reduction. Let `W` have
good reduction at the valuation `v` of `L`, with reduced curve the base change of a curve `C` over
a finite field `F` with `q` elements, and let `τ` be a `K`-algebra endomorphism of `L` with
`v (τ x - x ^ q) < 1` for every `x` in the valuation ring. Then the reduction of `τ P` is the image
of the reduction of `P` under the `q`-power map `FiniteField.frobeniusAlgHom` on the coordinates
of the points of `C`. -/
theorem cast_reductionHom_map_eq_map_frobeniusAlgHom
    [(integralModel v.valuationSubring (W⁄L)).IsElliptic]
    (hC : (integralModel v.valuationSubring (W⁄L)).map (residue v.valuationSubring) =
      C.baseChange (ResidueField v.valuationSubring))
    {τ : L →ₐ[K] L} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ Fintype.card F) < 1)
    (P : (W⁄L).toAffine.Point) :
    AddEquiv.cast (M := fun V ↦ V.toAffine.Point) hC (reductionHom v (map τ P)) =
      map (FiniteField.frobeniusAlgHom F _)
        (AddEquiv.cast (M := fun V ↦ V.toAffine.Point) hC (reductionHom v P)) := by
  rw [reductionHom_apply v P (by simp), reductionHom_apply v _ (by simp)]
  exact cast_nonsingularReductionHom_map_eq_map_frobeniusAlgHom v hC hτ ⟨P, by simp⟩

end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

section Dedekind

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [Algebra A L] [IsFractionRing A L] (u : HeightOneSpectrum A)
  {W : WeierstrassCurve K} [IsIntegral (u.valuation L).valuationSubring (W⁄L)] [DecidableEq L]
  {F : Type*} [Field F] [Fintype F] [Algebra F (ResidueField (u.valuation L).valuationSubring)]
  {C : WeierstrassCurve F}

/-- **A Frobenius element satisfies `X² - a_q X + q` on prime-to-`u` torsion at good reduction.**
Let `W` have good reduction at a height-one prime `u` of a Dedekind domain with fraction field `L`,
with reduced curve the base change of a curve `C` over a finite field `F` with `q` elements, and
let `τ` be a `K`-algebra endomorphism of `L` acting on the residues at `u` as the `q`-power map.
If `n • P = 0` for a point `P` of `W(L)` and an integer `n ∉ u`, then
`τ (τ P) = a_q • τ P - q • P`, where `a_q` is the Frobenius trace of `C`. -/
theorem Affine.Point.map_map_eq_of_nsmul_eq_zero
    [(integralModel (u.valuation L).valuationSubring (W⁄L)).IsElliptic]
    (hC : (integralModel (u.valuation L).valuationSubring (W⁄L)).map
      (residue (u.valuation L).valuationSubring) =
        C.baseChange (ResidueField (u.valuation L).valuationSubring))
    {τ : L →ₐ[K] L}
    (hτ : ∀ x, u.valuation L x ≤ 1 → u.valuation L (τ x - x ^ Fintype.card F) < 1) {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) {P : (W⁄L).toAffine.Point} (hP : n • P = 0) :
    Affine.Point.map τ (Affine.Point.map τ P) =
      C.frobeniusTrace • Affine.Point.map τ P - Nat.card F • P := by
  classical
  -- `C` is elliptic, its base change being the reduction of `W`
  have : C.IsElliptic := by
    have hΔ := ((integralModel (u.valuation L).valuationSubring (W⁄L)).map
      (residue (u.valuation L).valuationSubring)).isUnit_Δ
    rw [hC, WeierstrassCurve.baseChange, map_Δ] at hΔ
    exact ⟨isUnit_iff_ne_zero.mpr fun h0 ↦ not_isUnit_zero (by rwa [h0, _root_.map_zero] at hΔ)⟩
  -- `τ (τ P) - a_q • τ P + q • P` reduces to `Fr (Fr P') - a_q • Fr P' + q • P' = 0`, where
  -- `P'` is the reduction of `P` and `Fr` is the `q`-power map, and is killed by `n`
  set e := AddEquiv.cast
    (M := fun V : WeierstrassCurve (ResidueField (u.valuation L).valuationSubring) ↦
      V.toAffine.Point) hC
  have hred (Q : (W⁄L).toAffine.Point) :=
    Affine.Point.cast_reductionHom_map_eq_map_frobeniusAlgHom (u.valuation L) hC hτ Q
  rw [← sub_eq_zero]
  refine Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u hn ?_ ?_
  · apply e.injective
    rw [map_sub, map_sub, map_sub, map_sub, map_zsmul, map_zsmul, map_nsmul, map_nsmul, hred, hred,
      TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom, _root_.map_zero]
    exact sub_self _
  · rw [nsmul_sub, nsmul_sub, ← map_nsmul, ← map_nsmul, smul_comm n, ← map_nsmul, smul_comm n, hP]
    simp

/-- **A Frobenius element acts as `a_q q` at a node.** Let a height-one prime `u` of a Dedekind
domain with fraction field `L` reduce the elliptic curve `W` to the base change of a nodal cubic
`C` over a finite field `F` with `q` elements, whose Frobenius trace `a_q` is `1` or `-1` as the
node is split or not, and let `τ` be a `K`-algebra endomorphism of `L` acting on the residues at `u`
as the `q`-power map. If `P` has nonsingular reduction at `u` and `n • P = 0` for an integer
`n ∉ u`, then `τ P = (a_q q) • P`. -/
theorem Affine.Point.map_eq_zsmul_of_nsmul_eq_zero [W.IsElliptic]
    (hC : (integralModel (u.valuation L).valuationSubring (W⁄L)).map
      (residue (u.valuation L).valuationSubring) =
        C.baseChange (ResidueField (u.valuation L).valuationSubring))
    (hΔ : C.Δ = 0) (hc₄ : C.c₄ ≠ 0) {τ : L →ₐ[K] L}
    (hτ : ∀ x, u.valuation L x ≤ 1 → u.valuation L (τ x - x ^ Fintype.card F) < 1) {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) {P : (W⁄L).toAffine.Point}
    (hP₀ : P ∈ (W⁄L).toAffine.nonsingularReduction (u.valuation L)) (hP : n • P = 0) :
    Affine.Point.map τ P = (C.frobeniusTrace * Nat.card F) • P := by
  classical
  -- `τ P - (a_q q) • P` has nonsingular reduction, reduces to `Fr P' - (a_q q) • P' = 0`, where
  -- `P'` is the reduction of `P` and `Fr` is the `q`-power map, and is killed by `n`
  set E₀ := (W⁄L).toAffine.nonsingularReduction (u.valuation L)
  set Q : E₀ := ⟨P, hP₀⟩
  set D : E₀ := ⟨Affine.Point.map τ P,
    Affine.Point.map_mem_nonsingularReduction (u.valuation L) hC hτ hP₀⟩ -
      (C.frobeniusTrace * Nat.card F) • Q
  have hD : D = 0 := by
    refine Affine.Point.eq_zero_of_nonsingularReductionHom_eq_zero_of_nsmul_eq_zero u hn ?_ ?_
    · apply (AddEquiv.cast (M := fun V : WeierstrassCurve
        (ResidueField (u.valuation L).valuationSubring) ↦ V.toAffine.Point) hC).injective
      rw [map_sub, map_sub, map_zsmul, map_zsmul,
        Affine.Point.cast_nonsingularReductionHom_map_eq_map_frobeniusAlgHom _ hC hτ Q,
        Affine.Point.map_frobeniusAlgHom_eq_zsmul hΔ hc₄, sub_self, _root_.map_zero]
    · rw [AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, nsmul_sub, ← map_nsmul, smul_comm n, hP]
      simp
  exact sub_eq_zero.1 (congrArg Subtype.val hD)

end Dedekind


end WeierstrassCurve
