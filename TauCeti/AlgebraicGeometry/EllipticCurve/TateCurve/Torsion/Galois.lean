/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois

/-!
# Galois action on Tate-curve torsion

For a Tate curve with parameter `q`, the exponent quotient of its `n`-torsion is fixed by
continuous automorphisms of the coefficient extension. Consequently every displacement
`σ(P) - P` lies in the roots-of-unity subgroup. If `σ` also fixes the `n`-th roots of unity,
then `(σ - 1)² = 0` on `E_q[n]`. Fixing all `ℓ`-power roots of unity gives the same
basis-free identity on the `ℓ`-adic Tate module.

A chosen `n`-th root `u` of `q` gives a torsion point of exponent one. Its displacement is
exactly the root-of-unity point with parameter `σ(u)/u`; for `n ≠ 0`, this displacement
vanishes exactly when `σ(u) = u`. These formulas describe the finite-level extension of the
trivial character by the cyclotomic character, used in the inertia calculation at split
multiplicative reduction. They hold over complete ultrametric extensions, without assuming
that every exponent class is represented or that all roots of unity are rational.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
-/

public section

noncomputable section

namespace TauCeti

open Function WeierstrassCurve WeierstrassCurve.Affine
open scoped AddSubgroup

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] [DecidableEq L] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℕ)

/-- Every displacement of a Tate torsion point under a continuous algebra endomorphism belongs
to the roots-of-unity image. No surjectivity assumption on the exponent map is needed. -/
theorem sub_mem_range_tateRootsOfUnityHom (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (P : (((tateCurveAt q hq)⁄L).toAffine.Point)[(n : ℤ)]) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap P - P ∈
      (tateRootsOfUnityHom L q hq n).range := by
  apply (exact_tateRootsOfUnityHom_tateTorsionExponent L q hq n _).mp
  rw [map_sub, tateTorsionExponent_torsionByMap q hq n σ hσ, sub_self]

/-- A continuous algebra endomorphism fixing the `n`-th roots of unity acts unipotently of index
at most two on Tate-curve `n`-torsion. This is an identity of endomorphisms, not a choice of a
torsion basis. -/
theorem torsionByMap_tateCurveAt_sub_id_sq_eq_zero (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (hζ : ∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = ζ) :
    (torsionByMap (n : ℤ)
      (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap -
        LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro P
  obtain ⟨ζ, hP⟩ := sub_mem_range_tateRootsOfUnityHom q hq n σ hσ P
  obtain ⟨ζ, rfl⟩ := Additive.ofMul.surjective ζ
  have hfix := torsionByMap_tateRootsOfUnityHom q hq n σ hσ ζ
  rw [hζ ζ] at hfix
  simp only [pow_two, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply, ← hP, hfix, sub_self]

/-- The displacement of a chosen division point is the root-of-unity point with parameter
`σ(u)/u`. The equation `σ(u) = ζ u` specifies this root without choosing a generator of `μ_n`. -/
theorem torsionByMap_tateDivisionPoint_sub (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (u : Lˣ) (hu : u ^ n = Units.map (algebraMap K L : K →* L) q)
    (ζ : rootsOfUnity n L)
    (hζ : Units.map (σ : L →* L) u = (ζ : Lˣ) * u) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
        (tateDivisionPoint q hq n u hu) - tateDivisionPoint q hq n u hu =
      tateRootsOfUnityHom L q hq n (.ofMul ζ) := by
  apply Subtype.ext
  simp only [AddSubgroupClass.coe_sub, coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap,
    coe_tateDivisionPoint, coe_tateRootsOfUnityHom]
  rw [map_tateUnitHom q hq σ hσ, hζ, ofMul_mul, map_add, add_sub_cancel_right,
    toMul_ofMul]

/-- The division point represented by an `n`-th root `u` of `q` is fixed exactly when `u` is
fixed. Thus nontrivial Kummer action gives nontrivial action on Tate torsion. -/
theorem torsionByMap_tateDivisionPoint_eq_self_iff
    (σ : L →ₐ[K] L) (hσ : Continuous σ) (u : Lˣ)
    (hu : u ^ n = Units.map (algebraMap K L : K →* L) q) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
        (tateDivisionPoint q hq n u hu) = tateDivisionPoint q hq n u hu ↔
      Units.map (σ : L →* L) u = u := by
  have hn : n ≠ 0 := by
    intro hn
    have hqL : ‖((Units.map (algebraMap K L : K →* L) q : Lˣ) : L)‖ < 1 := by
      simpa using hq
    have hq1 : Units.map (algebraMap K L : K →* L) q = 1 := by simpa [hn] using hu.symm
    simp [hq1] at hqL
  have hroot : Units.map (σ : L →* L) u / u ∈ rootsOfUnity n L := by
    have hqσ : Units.map (σ : L →* L)
        (Units.map (algebraMap K L : K →* L) q) =
          Units.map (algebraMap K L : K →* L) q := by
      ext
      exact σ.commutes (q : K)
    rw [mem_rootsOfUnity, div_pow, ← map_pow, hu, hqσ, div_self']
  let ζ : rootsOfUnity n L := ⟨_, hroot⟩
  have h := torsionByMap_tateDivisionPoint_sub q hq n σ hσ u hu ζ (div_mul_cancel _ _).symm
  have hzero : tateRootsOfUnityHom L q hq n (.ofMul ζ) = 0 ↔ ζ = 1 := by
    rw [← map_zero (tateRootsOfUnityHom L q hq n),
      (tateRootsOfUnityHom_injective L q hq n hn).eq_iff, ofMul_eq_zero]
  rw [← sub_eq_zero, h, hzero]
  simp only [ζ, Subgroup.mk_eq_one, div_eq_one]

/-- Fixing all `ℓ`-power roots of unity makes the action on the Tate module of a Tate curve
unipotent of index at most two. No basis, discreteness of the valuation, or algebraicity of the
complete extension is required. -/
theorem tateModuleGaloisRepresentation_tateCurveAt_sub_one_sq_eq_zero (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : L ≃ₐ[K] L) (hσ : Continuous σ)
    (hζ : ∀ k, ∀ ζ : rootsOfUnity (ℓ ^ k) L,
      restrictRootsOfUnity σ.toAlgHom (ℓ ^ k) ζ = ζ) :
    ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply TateModule.ext
  intro k
  have hproj (y : TateModule ℓ ((tateCurveAt q hq)⁄L).toAffine.Point) :
      TateModule.proj k (((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ - 1) y) =
        torsionByMap ((ℓ ^ k : ℕ) : ℤ)
          (Point.map σ.toAlgHom).toIntLinearMap (TateModule.proj k y) - TateModule.proj k y := by
    apply Subtype.ext
    simp only [LinearMap.sub_apply, one_apply_eq_self, map_sub,
      AddSubgroupClass.coe_sub, coe_proj_tateModuleGaloisRepresentation,
      coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap]
  have h := LinearMap.congr_fun
    (torsionByMap_tateCurveAt_sub_id_sq_eq_zero q hq (ℓ ^ k) σ.toAlgHom hσ (hζ k))
    (TateModule.proj k x)
  simp only [pow_two, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply] at h
  simpa only [pow_two, mul_apply_eq_comp, hproj, LinearMap.zero_apply, map_zero] using h

end TauCeti
