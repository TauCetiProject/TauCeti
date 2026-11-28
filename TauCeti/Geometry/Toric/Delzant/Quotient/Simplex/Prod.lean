/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Hirzebruch
public import TauCeti.Geometry.Toric.Delzant.Quotient.Naturality
public import TauCeti.Geometry.Toric.Delzant.Quotient.Prod
public import TauCeti.Geometry.Toric.Delzant.Quotient.Simplex.Symplectic
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.Geometry.Manifold.Diffeomorph.Prod

/-!
# Delzant quotients of products of simplices

Let `Δ_a ⊆ (ℝⁿ)*` and `Δ_b ⊆ (ℝᵐ)*` be the standard simplices of sizes `a, b > 0`. The Delzant
quotient of `Δ_a` is `(ℂPⁿ, 2π a ω_FS)` (`TauCeti.Toric.DelzantQuotient.simplexDiffeomorph`), and
the Delzant quotient of a product of polytopes is the symplectic product of the Delzant quotients
(`TauCeti.Toric.IsDelzant.delzantQuotientProdDiffeomorph`). Together they identify the Delzant
quotient of the product presentation of `Δ_a × Δ_b` with

`(ℂPⁿ × ℂPᵐ, 2π a ω_FS ⊕ 2π b ω_FS)`

(`TauCeti.Toric.DelzantQuotient.simplexProdDiffeomorph`,
`TauCeti.Toric.DelzantQuotient.mpullback_simplexProdDiffeomorph_prod`), with the moment map
`([w], [w']) ↦ ((a |w_(k + 1)|²)_k, (b |w'_(l + 1)|²)_l)` for unit vectors `w` and `w'`.

**Products of two-spheres.** For `n = m = 1` the product `[0, a] × [0, b]` of two intervals is
the rectangle, presented in the lattice `ℤ²` as the Hirzebruch trapezoid with `k = 0`
(`TauCeti.Toric.hirzebruchNormal 0`, `TauCeti.Toric.hirzebruchSupport a b`): the normals
`(1, 0)`, `(0, 1)`, `(0, -1)`, `(-1, 0)` with support constants `0`, `0`, `-b`, `-a`. Listing
these facets as those of the two intervals, `(1, 0)` and `(-1, 0)` for the first and `(0, 1)` and
`(0, -1)` for the second, and splitting `ℤ²` as `ℤ × ℤ`, matches this presentation with the
product presentation of `Δ_a × Δ_b`: the two have the same level and the same kernel torus after
relabelling the coordinates of `ℂ⁴`. So the Delzant quotient of the rectangle, the toric
`S² × S²`, is `(ℂP¹ × ℂP¹, 2π a ω_FS ⊕ 2π b ω_FS)`
(`TauCeti.Toric.DelzantQuotient.rectangleDiffeomorph`,
`TauCeti.Toric.DelzantQuotient.mpullback_rectangleDiffeomorph_prod`), with moment map
`([w], [w']) ↦ (a |w₁|², b |w'₁|²)` (`reducedMomentMap_rectangleDiffeomorph_symm_mk_apply_zero`,
`reducedMomentMap_rectangleDiffeomorph_symm_mk_apply_one`). Its symplectic volume
`(2π)² a b` is the case `k = 0` of
`TauCeti.Toric.liouvilleMeasure_univ_delzantQuotientSymplecticForm_hirzebruch`.

## Main definitions

* `TauCeti.Toric.DelzantQuotient.simplexProdDiffeomorph`: the diffeomorphism of the Delzant
  quotient of `Δ_a × Δ_b` with `ℂPⁿ × ℂPᵐ`.
* `TauCeti.Toric.DelzantQuotient.rectangleDiffeomorph`: the diffeomorphism of the Delzant
  quotient of the rectangle `[0, a] × [0, b]` with `ℂP¹ × ℂP¹`.

## Main results

* `TauCeti.Toric.DelzantQuotient.mpullback_simplexProdDiffeomorph_prod`,
  `TauCeti.Toric.DelzantQuotient.isSymplectomorphism_simplexProdDiffeomorph`: the Delzant quotient
  of `Δ_a × Δ_b` is `(ℂPⁿ × ℂPᵐ, 2π a ω_FS ⊕ 2π b ω_FS)`.
* `TauCeti.Toric.DelzantQuotient.mpullback_rectangleDiffeomorph_prod`,
  `TauCeti.Toric.DelzantQuotient.isSymplectomorphism_rectangleDiffeomorph`: the Delzant quotient
  of the rectangle is `(ℂP¹ × ℂP¹, 2π a ω_FS ⊕ 2π b ω_FS)`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28–29 (Delzant's construction and its examples).
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Metric Module Real
open scoped Manifold ContDiff

namespace TauCeti.Toric

namespace DelzantQuotient

/-! ### Products of simplices -/

section SimplexProd

variable (n m : ℕ) [NeZero n] [NeZero m] {a b : ℝ}

/-- **The Delzant quotient of a product of simplices is `ℂPⁿ × ℂPᵐ` as a smooth manifold.** For
`a, b > 0`, the Delzant quotient of the product presentation of the simplices `Δ_a ⊆ (ℝⁿ)*` and
`Δ_b ⊆ (ℝᵐ)*` is diffeomorphic to `ℂPⁿ × ℂPᵐ`, by the product of `simplexDiffeomorph` on the two
factors composed with the identification `delzantQuotientProdDiffeomorph` of the Delzant quotient
of a product with the product of the Delzant quotients. -/
def simplexProdDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
      (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    DelzantQuotient (((Int.castAddHom ℝ).compLeft (Fin n)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin m)))
        (prodNormal (simplexNormal (Fin n)) (simplexNormal (Fin m)))
        (Sum.elim (simplexSupport a) (simplexSupport b)) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra (((Int.castAddHom ℝ).compLeft (Fin n)).prodMap
          ((Int.castAddHom ℝ).compLeft (Fin m)))
          (prodNormal (simplexNormal (Fin n)) (simplexNormal (Fin m))))
        (Fin (Fintype.card (Option (Fin n) ⊕ Option (Fin m)) +
          finrank ℝ ((Fin n → ℝ) × (Fin m → ℝ))) → ℝ)),
      𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, Fin m → ℂ)⟯
      ComplexProjectiveSpace n × ComplexProjectiveSpace m :=
  letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  letI := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
  letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
    (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
      ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  haveI := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
  haveI := (isDelzant_simplex hb).isManifold_delzantQuotient (isIntegralLattice_intCast m)
  ((isDelzant_simplex ha).delzantQuotientProdDiffeomorph (isDelzant_simplex hb)
    (isIntegralLattice_intCast n) (isIntegralLattice_intCast m)).trans
      ((simplexDiffeomorph n ha).prodCongrOfModels (simplexDiffeomorph m hb))

/-- `simplexProdDiffeomorph` is the product of `simplexDiffeomorph` on the two factors, composed
with the identification `prodHomeomorph` of the Delzant quotient of a product with the product of
the Delzant quotients. -/
@[simp]
theorem coe_simplexProdDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    letI := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    ⇑(simplexProdDiffeomorph n m ha hb) =
      Prod.map (simplexDiffeomorph n ha) (simplexDiffeomorph m hb) ∘
        prodHomeomorph ((Int.castAddHom ℝ).compLeft (Fin n)) ((Int.castAddHom ℝ).compLeft (Fin m))
          (simplexNormal (Fin n)) (simplexNormal (Fin m)) (simplexSupport a)
          (simplexSupport b) := by
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
      (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  rw [simplexProdDiffeomorph, Diffeomorph.coe_trans, Diffeomorph.coe_prodCongrOfModels,
    IsDelzant.coe_delzantQuotientProdDiffeomorph]

/-- The inverse of `simplexProdDiffeomorph` is the product of the inverses of
`simplexDiffeomorph`, followed by the inverse of `prodHomeomorph`. -/
@[simp]
theorem coe_simplexProdDiffeomorph_symm (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    letI := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    ⇑(simplexProdDiffeomorph n m ha hb).symm =
      (prodHomeomorph ((Int.castAddHom ℝ).compLeft (Fin n)) ((Int.castAddHom ℝ).compLeft (Fin m))
          (simplexNormal (Fin n)) (simplexNormal (Fin m)) (simplexSupport a)
          (simplexSupport b)).symm ∘
        Prod.map (simplexDiffeomorph n ha).symm (simplexDiffeomorph m hb).symm := by
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
      (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  rw [simplexProdDiffeomorph, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    Diffeomorph.prodCongrOfModels_symm, Diffeomorph.coe_prodCongrOfModels,
    IsDelzant.coe_delzantQuotientProdDiffeomorph_symm]

/-- **The Delzant quotient of a product of simplices is `(ℂPⁿ × ℂPᵐ, 2π a ω_FS ⊕ 2π b ω_FS)`.**
The diffeomorphism `simplexProdDiffeomorph` pulls the product of `2π a` times the Fubini–Study form
of `ℂPⁿ` and `2π b` times that of `ℂPᵐ` back to the reduced symplectic form of the Delzant quotient
of `Δ_a × Δ_b`. -/
theorem mpullback_simplexProdDiffeomorph_prod (ha : 0 < a) (hb : 0 < b) :
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    haveI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).isManifold_delzantQuotient
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    SmoothForm.mpullback (simplexProdDiffeomorph n m ha hb)
        (simplexProdDiffeomorph n m ha hb).contMDiff
        (SmoothTwoForm.prod ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm n)
          ((2 * π * b) • ComplexProjectiveSpace.fubiniStudyForm m)) =
      IsDelzant.delzantQuotientSymplecticForm ((isDelzant_simplex ha).prod
        (isIntegralLattice_intCast n).injective (isIntegralLattice_intCast m).injective
          (isDelzant_simplex hb))
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m)) := by
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  have := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
  have := (isDelzant_simplex hb).isManifold_delzantQuotient (isIntegralLattice_intCast m)
  have := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).isManifold_delzantQuotient
    ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  -- Pull back in two steps: along the product of the two `simplexDiffeomorph`, then along the
  -- identification of the Delzant quotient of the product with the product of Delzant quotients.
  have hcomp : ⇑(simplexProdDiffeomorph n m ha hb) =
      Prod.map (simplexDiffeomorph n ha) (simplexDiffeomorph m hb) ∘
        ⇑((isDelzant_simplex ha).delzantQuotientProdDiffeomorph (isDelzant_simplex hb)
          (isIntegralLattice_intCast n) (isIntegralLattice_intCast m)) := by
    rw [coe_simplexProdDiffeomorph, IsDelzant.coe_delzantQuotientProdDiffeomorph]
  have hprod := SmoothTwoForm.mpullback_prodMap_prod (simplexDiffeomorph n ha).contMDiff
    (simplexDiffeomorph m hb).contMDiff ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm n)
    ((2 * π * b) • ComplexProjectiveSpace.fubiniStudyForm m)
  rw [mpullback_simplexDiffeomorph_smul_fubiniStudyForm,
    mpullback_simplexDiffeomorph_smul_fubiniStudyForm] at hprod
  rw [← IsDelzant.mpullback_delzantQuotientProdDiffeomorph_prod, ← hprod,
    SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ hcomp _

/-- **The Delzant quotient of a product of simplices is symplectomorphic to
`(ℂPⁿ × ℂPᵐ, 2π a ω_FS ⊕ 2π b ω_FS)`**, by `simplexProdDiffeomorph`. -/
theorem isSymplectomorphism_simplexProdDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    haveI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).isManifold_delzantQuotient
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    SmoothTwoForm.IsSymplectomorphism
      (IsDelzant.delzantQuotientSymplecticForm ((isDelzant_simplex ha).prod
        (isIntegralLattice_intCast n).injective (isIntegralLattice_intCast m).injective
          (isDelzant_simplex hb))
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m)))
      (SmoothTwoForm.prod ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm n)
        ((2 * π * b) • ComplexProjectiveSpace.fubiniStudyForm m))
      (simplexProdDiffeomorph n m ha hb) :=
  letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
    (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
      ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  haveI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
    (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).isManifold_delzantQuotient
      ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
  SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.2
    (mpullback_simplexProdDiffeomorph_prod n m ha hb)

/-- **The moment map of `ℂPⁿ × ℂPᵐ`, first factor.** Under `simplexProdDiffeomorph`, the reduced
moment map of the Delzant quotient of `Δ_a × Δ_b` sends the point `([w], [w'])` of
`ℂPⁿ × ℂPᵐ`, for unit vectors `w` and `w'`, to a covector whose coordinate along the `k`-th basis
vector of `ℝⁿ` is `a |w_(k + 1)|²`. -/
theorem reducedMomentMap_simplexProdDiffeomorph_symm_mk_apply_fst (ha : 0 < a) (hb : 0 < b)
    (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (w' : sphere (0 : EuclideanSpace ℂ (Fin (m + 1))) 1) (k : Fin n) :
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    reducedMomentMap (i := ((Int.castAddHom ℝ).compLeft (Fin n)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin m)))
        (u := prodNormal (simplexNormal (Fin n)) (simplexNormal (Fin m)))
        (c := Sum.elim (simplexSupport a) (simplexSupport b))
        (surjective_linearCombination_prodNormal surjective_linearCombination_simplexNormal
          surjective_linearCombination_simplexNormal)
        ((simplexProdDiffeomorph n m ha hb).symm
          (ComplexProjectiveSpace.mk n w, ComplexProjectiveSpace.mk m w')) (Pi.single k 1, 0) =
      a * ‖(w : EuclideanSpace ℂ (Fin (n + 1))) k.succ‖ ^ 2 := by
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
  -- The inverse of `simplexProdDiffeomorph` is, by definition, the product of the inverses of
  -- `simplexDiffeomorph` followed by the inverse of `prodHomeomorph`.
  have h := DFunLike.congr_fun (reducedMomentMap_prodHomeomorph_symm
    (surjective_linearCombination_simplexNormal (κ := Fin n))
    (surjective_linearCombination_simplexNormal (κ := Fin m))
    ((simplexDiffeomorph n ha).symm (ComplexProjectiveSpace.mk n w),
      (simplexDiffeomorph m hb).symm (ComplexProjectiveSpace.mk m w'))) (Pi.single k 1, 0)
  rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero,
    reducedMomentMap_simplexDiffeomorph_symm_mk_apply] at h
  rw [coe_simplexProdDiffeomorph_symm, Function.comp_apply, Prod.map_apply]
  exact h

/-- **The moment map of `ℂPⁿ × ℂPᵐ`, second factor.** Under `simplexProdDiffeomorph`, the reduced
moment map of the Delzant quotient of `Δ_a × Δ_b` sends the point `([w], [w'])` of
`ℂPⁿ × ℂPᵐ`, for unit vectors `w` and `w'`, to a covector whose coordinate along the `l`-th basis
vector of `ℝᵐ` is `b |w'_(l + 1)|²`. -/
theorem reducedMomentMap_simplexProdDiffeomorph_symm_mk_apply_snd (ha : 0 < a) (hb : 0 < b)
    (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (w' : sphere (0 : EuclideanSpace ℂ (Fin (m + 1))) 1) (l : Fin m) :
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast n).injective
        (isIntegralLattice_intCast m).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
        ((isIntegralLattice_intCast n).prod (isIntegralLattice_intCast m))
    reducedMomentMap (i := ((Int.castAddHom ℝ).compLeft (Fin n)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin m)))
        (u := prodNormal (simplexNormal (Fin n)) (simplexNormal (Fin m)))
        (c := Sum.elim (simplexSupport a) (simplexSupport b))
        (surjective_linearCombination_prodNormal surjective_linearCombination_simplexNormal
          surjective_linearCombination_simplexNormal)
        ((simplexProdDiffeomorph n m ha hb).symm
          (ComplexProjectiveSpace.mk n w, ComplexProjectiveSpace.mk m w')) (0, Pi.single l 1) =
      b * ‖(w' : EuclideanSpace ℂ (Fin (m + 1))) l.succ‖ ^ 2 := by
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex hb).delzantQuotientChartedSpace (isIntegralLattice_intCast m)
  -- The inverse of `simplexProdDiffeomorph` is, by definition, the product of the inverses of
  -- `simplexDiffeomorph` followed by the inverse of `prodHomeomorph`.
  have h := DFunLike.congr_fun (reducedMomentMap_prodHomeomorph_symm
    (surjective_linearCombination_simplexNormal (κ := Fin n))
    (surjective_linearCombination_simplexNormal (κ := Fin m))
    ((simplexDiffeomorph n ha).symm (ComplexProjectiveSpace.mk n w),
      (simplexDiffeomorph m hb).symm (ComplexProjectiveSpace.mk m w'))) (0, Pi.single l 1)
  rw [ContinuousLinearMap.coprod_apply, map_zero, zero_add,
    reducedMomentMap_simplexDiffeomorph_symm_mk_apply] at h
  rw [coe_simplexProdDiffeomorph_symm, Function.comp_apply, Prod.map_apply]
  exact h

end SimplexProd

/-! ### The rectangle -/

section Rectangle

variable {a b : ℝ}

/-- The facets `(1, 0)`, `(0, 1)`, `(0, -1)`, `(-1, 0)` of the rectangle, listed as the facets
`some 0` and `none` of the first interval and of the second. -/
def rectangleFacetEquiv : Fin 4 ≃ Option (Fin 1) ⊕ Option (Fin 1) where
  toFun := ![.inl (some 0), .inr (some 0), .inr none, .inl none]
  invFun
    | .inl (some _) => 0
    | .inr (some _) => 1
    | .inr none => 2
    | .inl none => 3
  left_inv := by decide
  right_inv := by decide

theorem coe_rectangleFacetEquiv :
    ⇑rectangleFacetEquiv = ![.inl (some 0), .inr (some 0), .inr none, .inl none] := (rfl)

@[simp] theorem rectangleFacetEquiv_zero : rectangleFacetEquiv 0 = .inl (some 0) := (rfl)

@[simp] theorem rectangleFacetEquiv_one : rectangleFacetEquiv 1 = .inr (some 0) := (rfl)

@[simp] theorem rectangleFacetEquiv_two : rectangleFacetEquiv 2 = .inr none := (rfl)

@[simp] theorem rectangleFacetEquiv_three : rectangleFacetEquiv 3 = .inl none := (rfl)

@[simp] theorem rectangleFacetEquiv_symm_inl_some (i : Fin 1) :
    rectangleFacetEquiv.symm (.inl (some i)) = 0 := (rfl)

@[simp] theorem rectangleFacetEquiv_symm_inr_some (i : Fin 1) :
    rectangleFacetEquiv.symm (.inr (some i)) = 1 := (rfl)

@[simp] theorem rectangleFacetEquiv_symm_inr_none : rectangleFacetEquiv.symm (.inr none) = 2 :=
  (rfl)

@[simp] theorem rectangleFacetEquiv_symm_inl_none : rectangleFacetEquiv.symm (.inl none) = 3 :=
  (rfl)

/-- The splitting `ℤ² = ℤ × ℤ` of the lattice of the rectangle. -/
private def rectangleLatticeMap (v : Fin 2 → ℤ) : (Fin 1 → ℤ) × (Fin 1 → ℤ) :=
  (fun _ ↦ v 0, fun _ ↦ v 1)

/-- The splitting `ℝ² = ℝ × ℝ`. -/
private def rectangleLinearMap : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (LinearMap.pi fun _ ↦ LinearMap.proj 0).prod (LinearMap.pi fun _ ↦ LinearMap.proj 1)

private theorem surjective_rectangleLatticeMap : Function.Surjective rectangleLatticeMap :=
  fun p ↦ ⟨![p.1 0, p.2 0], by
    ext k <;> fin_cases k <;> rfl⟩

private theorem injective_rectangleLinearMap : Function.Injective rectangleLinearMap := by
  intro y y' h
  ext k
  fin_cases k
  · exact congrFun (congrArg Prod.fst h) 0
  · exact congrFun (congrArg Prod.snd h) 0

private theorem rectangleLinearMap_intCast (v : Fin 2 → ℤ) :
    rectangleLinearMap ((Int.castAddHom ℝ).compLeft (Fin 2) v) =
      ((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap ((Int.castAddHom ℝ).compLeft (Fin 1))
        (rectangleLatticeMap v) := by
  ext k <;> fin_cases k <;> rfl

/-- Listed along `rectangleFacetEquiv`, the normals of the product of two intervals are the
normals of the rectangle, split along `ℤ² = ℤ × ℤ`. -/
private theorem prodNormal_comp_rectangleFacetEquiv :
    prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1)) ∘ rectangleFacetEquiv =
      fun j ↦ rectangleLatticeMap (hirzebruchNormal 0 j) := by
  funext j
  fin_cases j <;> ext k <;> fin_cases k <;>
    simp [rectangleLatticeMap, hirzebruchNormal_def]

/-- Listed along `rectangleFacetEquiv`, the support constants of the product of two intervals are
those of the rectangle. -/
private theorem sumElim_simplexSupport_comp_rectangleFacetEquiv :
    Sum.elim (simplexSupport a) (simplexSupport b) ∘ rectangleFacetEquiv =
      hirzebruchSupport a b := by
  funext j
  fin_cases j <;> simp [hirzebruchSupport_def]

/-- The levels of the rectangle and of the product of two intervals correspond along
`rectangleFacetEquiv`. -/
theorem prodMap_piLpCongrLeft_mem_delzantLevel_rectangle_iff
    (x : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    Prod.map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ rectangleFacetEquiv)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ rectangleFacetEquiv) x ∈
        delzantLevel (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
          ((Int.castAddHom ℝ).compLeft (Fin 1)))
          (prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1)))
          (Sum.elim (simplexSupport a) (simplexSupport b)) ↔
      x ∈ delzantLevel ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 0)
        (hirzebruchSupport a b) := by
  rw [prodMap_piLpCongrLeft_mem_delzantLevel_iff, prodNormal_comp_rectangleFacetEquiv,
    sumElim_simplexSupport_comp_rectangleFacetEquiv,
    delzantLevel_comp_left injective_rectangleLinearMap rectangleLinearMap_intCast]

/-- The kernel tori of the rectangle and of the product of two intervals correspond along
`rectangleFacetEquiv`. -/
theorem comp_symm_mem_ker_facetTorusHom_rectangle_iff (θ : Fin 4 → AddCircle (2 * π)) :
    θ ∘ rectangleFacetEquiv.symm ∈ (facetTorusHom (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1)))
        (prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1))) (2 * π)).ker ↔
      θ ∈ (facetTorusHom ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 0) (2 * π)).ker
        := by
  rw [AddMonoidHom.mem_ker, ← facetTorusHom_comp_equiv, ← AddMonoidHom.mem_ker,
    prodNormal_comp_rectangleFacetEquiv, ker_facetTorusHom_comp_left surjective_rectangleLatticeMap
      injective_rectangleLinearMap rectangleLinearMap_intCast]

/-- The change of presentation `DelzantQuotient.congr` along `rectangleFacetEquiv`, from the
Delzant quotient of the rectangle to that of the product of two intervals, as a diffeomorphism. -/
private def rectangleCongrDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
      (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
      ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
    DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 0)
        (hirzebruchSupport a b) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 0))
        (Fin (Fintype.card (Fin 4) + finrank ℝ (Fin 2 → ℝ)) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
          ((Int.castAddHom ℝ).compLeft (Fin 1)))
          (prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1))))
        (Fin (Fintype.card (Option (Fin 1) ⊕ Option (Fin 1)) +
          finrank ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ))) → ℝ))⟯
      DelzantQuotient (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1)))
        (prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1)))
        (Sum.elim (simplexSupport a) (simplexSupport b)) :=
  IsDelzant.delzantQuotientCongrDiffeomorph ((isDelzant_simplex ha).prod
      (isIntegralLattice_intCast 1).injective (isIntegralLattice_intCast 1).injective
        (isDelzant_simplex hb))
    (isDelzant_rectangle ha hb) ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
    (isIntegralLattice_intCast 2) rectangleFacetEquiv
    prodMap_piLpCongrLeft_mem_delzantLevel_rectangle_iff
    comp_symm_mem_ker_facetTorusHom_rectangle_iff

/-- **The Delzant quotient of the rectangle is `ℂP¹ × ℂP¹` as a smooth manifold.** For `a, b > 0`,
the Delzant quotient of the rectangle `[0, a] × [0, b]`, presented in `ℤ²` as the Hirzebruch
trapezoid with `k = 0`, is diffeomorphic to `ℂP¹ × ℂP¹`. The moment map becomes
`([w], [w']) ↦ (a |w₁|², b |w'₁|²)`, so the facets `{x(e₁) = 0}` and `{x(e₁) = a}` are where the
homogeneous coordinate `1`, respectively `0`, of the first factor vanishes, and likewise for
`x(e₂)` and the second factor. -/
def rectangleDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 0)
        (hirzebruchSupport a b) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 0))
        (Fin (Fintype.card (Fin 4) + finrank ℝ (Fin 2 → ℝ)) → ℝ)),
      𝓘(ℝ, Fin 1 → ℂ).prod 𝓘(ℝ, Fin 1 → ℂ)⟯
      ComplexProjectiveSpace 1 × ComplexProjectiveSpace 1 :=
  letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
  letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
    (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
  (rectangleCongrDiffeomorph ha hb).trans (simplexProdDiffeomorph 1 1 ha hb)

/-- `rectangleDiffeomorph` is the change of presentation `DelzantQuotient.congr` along
`rectangleFacetEquiv`, from the rectangle to the product of two intervals, followed by
`simplexProdDiffeomorph`. -/
@[simp]
theorem coe_rectangleDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
      (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
      ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
    ⇑(rectangleDiffeomorph ha hb) = simplexProdDiffeomorph 1 1 ha hb ∘
      DelzantQuotient.congr rectangleFacetEquiv prodMap_piLpCongrLeft_mem_delzantLevel_rectangle_iff
        comp_symm_mem_ker_facetTorusHom_rectangle_iff := by
  let _ := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
      (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
  rw [rectangleDiffeomorph, Diffeomorph.coe_trans, rectangleCongrDiffeomorph,
    IsDelzant.coe_delzantQuotientCongrDiffeomorph]

/-- The inverse of `rectangleDiffeomorph` is the inverse of `simplexProdDiffeomorph`, followed by
the inverse of the change of presentation `DelzantQuotient.congr` along `rectangleFacetEquiv`. -/
@[simp]
theorem coe_rectangleDiffeomorph_symm (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
      (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
      ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
    ⇑(rectangleDiffeomorph ha hb).symm =
      (DelzantQuotient.congr rectangleFacetEquiv
        prodMap_piLpCongrLeft_mem_delzantLevel_rectangle_iff
        comp_symm_mem_ker_facetTorusHom_rectangle_iff).symm ∘
        (simplexProdDiffeomorph 1 1 ha hb).symm := by
  let _ := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
      (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
  rw [rectangleDiffeomorph, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    rectangleCongrDiffeomorph, IsDelzant.coe_delzantQuotientCongrDiffeomorph_symm]

/-- **The Delzant quotient of the rectangle is `(ℂP¹ × ℂP¹, 2π a ω_FS ⊕ 2π b ω_FS)`.** The
diffeomorphism `rectangleDiffeomorph` pulls the product of `2π a` and `2π b` times the
Fubini–Study form of `ℂP¹` back to the reduced symplectic form of the Delzant quotient of the
rectangle `[0, a] × [0, b]`. -/
theorem mpullback_rectangleDiffeomorph_prod (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    haveI := (isDelzant_rectangle ha hb).isManifold_delzantQuotient (isIntegralLattice_intCast 2)
    SmoothForm.mpullback (rectangleDiffeomorph ha hb) (rectangleDiffeomorph ha hb).contMDiff
        (SmoothTwoForm.prod ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm 1)
          ((2 * π * b) • ComplexProjectiveSpace.fubiniStudyForm 1)) =
      (isDelzant_rectangle ha hb).delzantQuotientSymplecticForm (isIntegralLattice_intCast 2) := by
  let _ := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
    (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
  have := (isDelzant_rectangle ha hb).isManifold_delzantQuotient (isIntegralLattice_intCast 2)
  have := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
      (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).isManifold_delzantQuotient
    ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
  -- Pull back in two steps: along `simplexProdDiffeomorph`, then along the change of
  -- presentation from the rectangle to the product of two intervals.
  have hcomp : ⇑(rectangleDiffeomorph ha hb) =
      ⇑(simplexProdDiffeomorph 1 1 ha hb) ∘ ⇑(rectangleCongrDiffeomorph ha hb) :=
    Diffeomorph.coe_trans _ _
  have hcongr : SmoothForm.mpullback (rectangleCongrDiffeomorph ha hb)
      (rectangleCongrDiffeomorph ha hb).contMDiff
      (IsDelzant.delzantQuotientSymplecticForm ((isDelzant_simplex ha).prod
        (isIntegralLattice_intCast 1).injective (isIntegralLattice_intCast 1).injective
          (isDelzant_simplex hb))
        ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))) =
      (isDelzant_rectangle ha hb).delzantQuotientSymplecticForm (isIntegralLattice_intCast 2) :=
    IsDelzant.mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm _ _ _ _ _ _ _
  rw [← hcongr, ← mpullback_simplexProdDiffeomorph_prod 1 1 ha hb, SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ hcomp _

/-- **The Delzant quotient of the rectangle is symplectomorphic to
`(ℂP¹ × ℂP¹, 2π a ω_FS ⊕ 2π b ω_FS)`**, by `rectangleDiffeomorph`. -/
theorem isSymplectomorphism_rectangleDiffeomorph (ha : 0 < a) (hb : 0 < b) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    haveI := (isDelzant_rectangle ha hb).isManifold_delzantQuotient (isIntegralLattice_intCast 2)
    SmoothTwoForm.IsSymplectomorphism
      ((isDelzant_rectangle ha hb).delzantQuotientSymplecticForm (isIntegralLattice_intCast 2))
      (SmoothTwoForm.prod ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm 1)
        ((2 * π * b) • ComplexProjectiveSpace.fubiniStudyForm 1))
      (rectangleDiffeomorph ha hb) :=
  letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
  haveI := (isDelzant_rectangle ha hb).isManifold_delzantQuotient (isIntegralLattice_intCast 2)
  SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.2
    (mpullback_rectangleDiffeomorph_prod ha hb)

/-- The first two facet normals of the rectangle, `(1, 0)` and `(0, 1)`, are the standard basis
vectors of `ℝ²`. -/
private theorem intCast_hirzebruchNormal_zero_castSucc_castSucc (j : Fin 2) :
    (Int.castAddHom ℝ).compLeft (Fin 2) (hirzebruchNormal 0 j.castSucc.castSucc) =
      Pi.single j 1 := by
  ext k
  fin_cases j <;> fin_cases k <;> simp [hirzebruchNormal_def]

/-- The moment map coordinate of the rectangle along the `j`-th basis vector of `ℝ²` at
`(rectangleDiffeomorph ha hb).symm p` agrees with the coordinate of the product of two intervals
at `(simplexProdDiffeomorph 1 1 ha hb).symm p` along the matching facet normal: both facets have
support constant `0`. -/
private theorem reducedMomentMap_rectangleDiffeomorph_symm_apply_single (ha : 0 < a)
    (hb : 0 < b) (hβ : Function.Surjective (Fintype.linearCombination ℝ
      fun j ↦ (Int.castAddHom ℝ).compLeft (Fin 2) (hirzebruchNormal 0 j)))
    (p : ComplexProjectiveSpace 1 × ComplexProjectiveSpace 1) (j : Fin 2) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    letI := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
        (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
      ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
    reducedMomentMap hβ ((rectangleDiffeomorph ha hb).symm p) (Pi.single j 1) =
      reducedMomentMap (i := ((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
          ((Int.castAddHom ℝ).compLeft (Fin 1)))
          (u := prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1)))
          (c := Sum.elim (simplexSupport a) (simplexSupport b))
          (surjective_linearCombination_prodNormal surjective_linearCombination_simplexNormal
            surjective_linearCombination_simplexNormal)
          ((simplexProdDiffeomorph 1 1 ha hb).symm p)
          ((((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap ((Int.castAddHom ℝ).compLeft (Fin 1)))
            (prodNormal (simplexNormal (Fin 1)) (simplexNormal (Fin 1))
              (rectangleFacetEquiv j.castSucc.castSucc))) := by
  let _ := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
  let _ := ((isDelzant_simplex ha).prod (isIntegralLattice_intCast 1).injective
        (isIntegralLattice_intCast 1).injective (isDelzant_simplex hb)).delzantQuotientChartedSpace
    ((isIntegralLattice_intCast 1).prod (isIntegralLattice_intCast 1))
  have h := reducedMomentMap_congr_apply_sub rectangleFacetEquiv
    prodMap_piLpCongrLeft_mem_delzantLevel_rectangle_iff
    comp_symm_mem_ker_facetTorusHom_rectangle_iff
    (surjective_linearCombination_prodNormal surjective_linearCombination_simplexNormal
      surjective_linearCombination_simplexNormal) hβ ((rectangleDiffeomorph ha hb).symm p)
    j.castSucc.castSucc
  have hq : DelzantQuotient.congr rectangleFacetEquiv
      prodMap_piLpCongrLeft_mem_delzantLevel_rectangle_iff
      comp_symm_mem_ker_facetTorusHom_rectangle_iff ((rectangleDiffeomorph ha hb).symm p) =
      (simplexProdDiffeomorph 1 1 ha hb).symm p := by
    rw [coe_rectangleDiffeomorph_symm, Function.comp_apply, Homeomorph.apply_symm_apply]
  rw [hq, intCast_hirzebruchNormal_zero_castSucc_castSucc] at h
  fin_cases j <;> simpa [hirzebruchSupport_def] using h.symm

/-- **The moment map of `ℂP¹ × ℂP¹`, first coordinate.** Under `rectangleDiffeomorph`, the reduced
moment map of the Delzant quotient of the rectangle `[0, a] × [0, b]` sends the point
`([w], [w'])`, for unit vectors `w` and `w'` of `ℂ²`, to a covector with first coordinate
`x(e₁) = a |w₁|²`. -/
theorem reducedMomentMap_rectangleDiffeomorph_symm_mk_apply_zero (ha : 0 < a) (hb : 0 < b)
    (hβ : Function.Surjective (Fintype.linearCombination ℝ
      fun j ↦ (Int.castAddHom ℝ).compLeft (Fin 2) (hirzebruchNormal 0 j)))
    (w w' : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    reducedMomentMap hβ ((rectangleDiffeomorph ha hb).symm
        (ComplexProjectiveSpace.mk 1 w, ComplexProjectiveSpace.mk 1 w')) (Pi.single 0 1) =
      a * ‖(w : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2 := by
  rw [reducedMomentMap_rectangleDiffeomorph_symm_apply_single]
  simpa using reducedMomentMap_simplexProdDiffeomorph_symm_mk_apply_fst 1 1 ha hb w w' 0

/-- **The moment map of `ℂP¹ × ℂP¹`, second coordinate.** Under `rectangleDiffeomorph`, the
reduced moment map of the Delzant quotient of the rectangle `[0, a] × [0, b]` sends the point
`([w], [w'])`, for unit vectors `w` and `w'` of `ℂ²`, to a covector with second coordinate
`x(e₂) = b |w'₁|²`. -/
theorem reducedMomentMap_rectangleDiffeomorph_symm_mk_apply_one (ha : 0 < a) (hb : 0 < b)
    (hβ : Function.Surjective (Fintype.linearCombination ℝ
      fun j ↦ (Int.castAddHom ℝ).compLeft (Fin 2) (hirzebruchNormal 0 j)))
    (w w' : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    letI := (isDelzant_rectangle ha hb).delzantQuotientChartedSpace (isIntegralLattice_intCast 2)
    reducedMomentMap hβ ((rectangleDiffeomorph ha hb).symm
        (ComplexProjectiveSpace.mk 1 w, ComplexProjectiveSpace.mk 1 w')) (Pi.single 1 1) =
      b * ‖(w' : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2 := by
  rw [reducedMomentMap_rectangleDiffeomorph_symm_apply_single]
  simpa using reducedMomentMap_simplexProdDiffeomorph_symm_mk_apply_snd 1 1 ha hb w w' 0

end Rectangle

end DelzantQuotient

end TauCeti.Toric
