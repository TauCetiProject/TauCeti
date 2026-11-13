/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Galois

/-!
# Detecting the action on Tate-curve torsion

A chosen `n`-th root `u` of the Tate parameter, together with the `n`-th roots of unity,
generates all `n`-torsion under uniformization. Consequently a continuous coefficient
endomorphism acts trivially on the entire torsion group if and only if it fixes both
`μ_n` and `u`. More generally, its action is determined by its restriction to `μ_n` and
its value on `u`.

When the roots of unity are fixed, the displacement of every torsion point is its
exponent times the displacement of the chosen division point. This turns Kummer
characters into the action on the whole torsion group, rather than just one point;
in particular it gives the triviality test needed to study wild inertia at
multiplicative reduction. No primitive root, torsion basis, algebraicity, or discrete
valuation is required.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
-/

public noncomputable section

namespace TauCeti

open Function WeierstrassCurve WeierstrassCurve.Affine
open scoped AddSubgroup

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] [DecidableEq L] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℕ)
  (u : Lˣ) (hu : u ^ n = Units.map (algebraMap K L : K →* L) q)

/-- For any representative `a` of its exponent, a Tate torsion point is a root-of-unity
point plus `a` times the chosen division point. -/
theorem exists_tateRootsOfUnityHom_add_zsmul_tateDivisionPoint
    (P : (((tateCurveAt q hq)⁄L).toAffine.Point)[(n : ℤ)])
    (a : ℤ) (ha : tateTorsionExponent L q hq n P = (a : QuotSMulTop (n : ℤ) ℤ)) :
    ∃ ζ : Additive (rootsOfUnity n L),
      P = tateRootsOfUnityHom L q hq n ζ + a • tateDivisionPoint q hq n u hu := by
  have hz : tateTorsionExponent L q hq n (P - a • tateDivisionPoint q hq n u hu) = 0 := by
    simp [ha]
  obtain ⟨ζ, hζ⟩ := (exact_tateRootsOfUnityHom_tateTorsionExponent L q hq n _).mp hz
  exact ⟨ζ, sub_eq_iff_eq_add.mp hζ.symm⟩

include hu in
/-- Two continuous coefficient endomorphisms induce the same action on Tate `n`-torsion
if they agree on the `n`-th roots of unity and on a chosen `n`-th root of the parameter. -/
theorem torsionByMap_tateCurveAt_eq_of_rootsOfUnity_eq
    (σ τ : L →ₐ[K] L) (hσ : Continuous σ) (hτ : Continuous τ)
    (hζ : ∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = restrictRootsOfUnity τ n ζ)
    (huστ : Units.map (σ : L →* L) u = Units.map (τ : L →* L) u) :
    torsionByMap (n : ℤ) (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap =
      torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap := by
  ext P
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (tateTorsionExponent L q hq n P)
  obtain ⟨ζ, rfl⟩ := exists_tateRootsOfUnityHom_add_zsmul_tateDivisionPoint q hq n u hu P a ha.symm
  have hroot : torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
      (tateRootsOfUnityHom L q hq n ζ) =
        torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap
          (tateRootsOfUnityHom L q hq n ζ) := by
    obtain ⟨ζ, rfl⟩ := Additive.ofMul.surjective ζ
    simp only [torsionByMap_tateRootsOfUnityHom q hq n σ hσ,
      torsionByMap_tateRootsOfUnityHom q hq n τ hτ, hζ]
  have hdivision : torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
      (tateDivisionPoint q hq n u hu) =
        torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap
          (tateDivisionPoint q hq n u hu) := by
    apply Subtype.ext
    simp only [coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap,
      coe_tateDivisionPoint, map_tateUnitHom q hq σ hσ, map_tateUnitHom q hq τ hτ, huστ]
  simp only [map_add, map_zsmul, hroot, hdivision]

/-- If roots of unity are fixed, the displacement of any torsion point with exponent `[a]`
is `a` times the displacement of a chosen division point. -/
theorem torsionByMap_tateCurveAt_sub_eq_zsmul
    (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (hζ : ∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = ζ)
    (P : (((tateCurveAt q hq)⁄L).toAffine.Point)[(n : ℤ)])
    (a : ℤ) (ha : tateTorsionExponent L q hq n P = (a : QuotSMulTop (n : ℤ) ℤ)) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap P - P =
      a • (torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
        (tateDivisionPoint q hq n u hu) - tateDivisionPoint q hq n u hu) := by
  obtain ⟨ζ, rfl⟩ := exists_tateRootsOfUnityHom_add_zsmul_tateDivisionPoint q hq n u hu P a ha
  have hroot : torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
      (tateRootsOfUnityHom L q hq n ζ) = tateRootsOfUnityHom L q hq n ζ := by
    obtain ⟨ζ, rfl⟩ := Additive.ofMul.surjective ζ
    rw [torsionByMap_tateRootsOfUnityHom q hq n σ hσ, hζ]
  simp only [map_add, map_zsmul, hroot, smul_sub]
  abel

include hu in
/-- A continuous coefficient endomorphism fixes all Tate `n`-torsion exactly when it fixes
the roots of unity and a chosen `n`-th root of the parameter. This detects triviality of
the entire action, not only of its action on the exponent quotient. -/
theorem torsionByMap_tateCurveAt_eq_id_iff
    (σ : L →ₐ[K] L) (hσ : Continuous σ) :
    torsionByMap (n : ℤ) (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap =
        LinearMap.id ↔
      (∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = ζ) ∧
        Units.map (σ : L →* L) u = u := by
  have hn : n ≠ 0 := by
    intro hn
    have hnorm := congrArg (fun v : Lˣ ↦ ‖(v : L)‖) hu
    have hq1 : ‖(q : K)‖ = 1 := by simpa [hn] using hnorm.symm
    exact hq.ne hq1
  constructor
  · intro h
    refine ⟨fun ζ ↦ ?_, ?_⟩
    · have he := LinearMap.congr_fun h (tateRootsOfUnityHom L q hq n (.ofMul ζ))
      rw [torsionByMap_tateRootsOfUnityHom q hq n σ hσ, LinearMap.id_apply] at he
      exact Additive.ofMul.injective ((tateRootsOfUnityHom_injective L q hq n hn) he)
    · exact (torsionByMap_tateDivisionPoint_eq_self_iff q hq n σ hσ u hu).mp
        (LinearMap.congr_fun h _)
  · rintro ⟨hζ, huσ⟩
    apply LinearMap.ext
    intro P
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (tateTorsionExponent L q hq n P)
    have h := torsionByMap_tateCurveAt_sub_eq_zsmul q hq n u hu σ hσ hζ P a ha.symm
    have hdivision := (torsionByMap_tateDivisionPoint_eq_self_iff q hq n σ hσ u hu).mpr huσ
    rw [hdivision, sub_self, smul_zero] at h
    exact sub_eq_zero.mp h

end TauCeti
