/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Galois
public import TauCeti.RingTheory.RootsOfUnity.PadicTateTwist

/-!
# The cyclotomic submodule of a Tate curve

Tate uniformization embeds the Tate twist `ℤ_ℓ(1)` in the Tate module of a Tate curve.
Its image consists exactly of the compatible torsion points with zero exponent at every
finite level. The embedding intertwines the Galois actions, and every Galois displacement
lies in its image: the action on the quotient is trivial. When the coefficient extension
contains all `ℓ`-power roots of unity, the image has rank one.

These statements describe the cyclotomic part of the Tate representation without choosing
a compatible system of roots of the Tate parameter. They are the filtration used to compute
inertia invariants at split multiplicative reduction. No algebraicity or discreteness
hypothesis is imposed on the complete normed extension.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
-/

public noncomputable section

namespace TauCeti

open Function WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (L : Type*) [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] [DecidableEq L] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- The cyclotomic embedding into the Tate module of a Tate curve, induced by uniformization
on unit representatives. -/
def tateCyclotomicMap : PadicTateTwist ℓ L →ₗ[ℤ_[ℓ]]
    TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point) :=
  TateModule.mapLinearMap (tateUnitHom L q hq)

/-- The cyclotomic map at a torsion level is the roots-of-unity inclusion. -/
@[simp]
theorem proj_tateCyclotomicMap (x : PadicTateTwist ℓ L) (n : ℕ) :
    TateModule.proj n (tateCyclotomicMap L q hq ℓ x) =
      tateRootsOfUnityHom L q hq (ℓ ^ n) (PadicTateTwist.proj n x) := by
  apply Subtype.ext
  simp only [tateCyclotomicMap, TateModule.mapLinearMap_apply, TateModule.proj_map,
    TateModule.levelMap_apply, coe_tateRootsOfUnityHom, PadicTateTwist.coe_proj,
    ofMul_toMul]

omit [Fact ℓ.Prime] in
/-- On unit torsion, uniformization is the roots-of-unity inclusion. -/
@[simp]
theorem levelMap_tateUnitHom (n : ℕ) (ζ : Additive (rootsOfUnity (ℓ ^ n) L)) :
    TateModule.levelMap (tateUnitHom L q hq) n
        ((PadicTateTwist.levelAddEquivRootsOfUnity n).symm ζ) =
      tateRootsOfUnityHom L q hq (ℓ ^ n) ζ := by
  apply Subtype.ext
  simp only [TateModule.levelMap_apply, PadicTateTwist.coe_levelAddEquivRootsOfUnity_symm,
    coe_tateRootsOfUnityHom]

private theorem tateUnitHom_levelMap_injective (n : ℕ) :
    Injective (TateModule.levelMap (p := ℓ) (tateUnitHom L q hq) n) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (PadicTateTwist.levelAddEquivRootsOfUnity n).symm.surjective x
  obtain ⟨y, rfl⟩ := (PadicTateTwist.levelAddEquivRootsOfUnity n).symm.surjective y
  rw [levelMap_tateUnitHom, levelMap_tateUnitHom] at hxy
  exact congrArg (PadicTateTwist.levelAddEquivRootsOfUnity n).symm
    (tateRootsOfUnityHom_injective L q hq (ℓ ^ n)
      (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero) hxy)

/-- The cyclotomic map is injective, even when the extension lacks some roots of unity. -/
theorem tateCyclotomicMap_injective : Injective (tateCyclotomicMap L q hq ℓ) := by
  intro x y h
  apply TateModule.map_injective _ (tateUnitHom_levelMap_injective L q hq ℓ)
  simpa only [tateCyclotomicMap, TateModule.mapLinearMap_apply] using h

/-- A Tate-module point belongs to the cyclotomic submodule exactly when every finite-level
exponent is zero. This does not require roots of the Tate parameter in the extension. -/
theorem mem_range_tateCyclotomicMap_iff
    (x : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point)) :
    x ∈ LinearMap.range (tateCyclotomicMap L q hq ℓ) ↔
      ∀ n, tateTorsionExponent L q hq (ℓ ^ n) (TateModule.proj n x) = 0 := by
  simp only [LinearMap.mem_range, tateCyclotomicMap, TateModule.mapLinearMap_apply]
  have h := TateModule.mem_range_map_iff (tateUnitHom L q hq)
    (tateUnitHom_levelMap_injective L q hq ℓ) x
  simp only [AddMonoidHom.mem_range] at h
  refine h.trans (forall_congr' fun n ↦ ?_)
  rw [exact_tateRootsOfUnityHom_tateTorsionExponent L q hq (ℓ ^ n) (TateModule.proj n x)]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨ζ, rfl⟩ := (PadicTateTwist.levelAddEquivRootsOfUnity n).symm.surjective y
    exact ⟨ζ, (levelMap_tateUnitHom L q hq ℓ n ζ).symm.trans hy⟩
  · rintro ⟨ζ, hζ⟩
    exact ⟨(PadicTateTwist.levelAddEquivRootsOfUnity n).symm ζ,
      (levelMap_tateUnitHom L q hq ℓ n ζ).trans hζ⟩

/-- With all `ℓ`-power roots of unity present, the cyclotomic submodule has rank one. -/
theorem finrank_range_tateCyclotomicMap [∀ n, HasEnoughRootsOfUnity L (ℓ ^ n)] :
    Module.finrank ℤ_[ℓ] (LinearMap.range (tateCyclotomicMap L q hq ℓ)) = 1 := by
  rw [LinearMap.finrank_range_of_inj (tateCyclotomicMap_injective L q hq ℓ),
    PadicTateTwist.finrank]

variable {L}

/-- The cyclotomic embedding intertwines the roots-of-unity and elliptic-curve Galois actions
for every continuous algebra automorphism of the complete extension. -/
theorem tateCyclotomicMap_galoisRepresentation (σ : L ≃ₐ[K] L) (hσ : Continuous σ)
    (x : PadicTateTwist ℓ L) :
    tateCyclotomicMap L q hq ℓ (PadicTateTwist.galoisRepresentation σ x) =
      (tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ
        (tateCyclotomicMap L q hq ℓ x) := by
  apply TateModule.ext
  intro n
  apply Subtype.ext
  simp only [proj_tateCyclotomicMap, coe_tateRootsOfUnityHom,
    coe_proj_tateModuleGaloisRepresentation]
  rw [map_tateUnitHom q hq σ.toAlgHom hσ]
  congr 2
  apply Units.ext
  simpa only [PadicTateTwist.coe_proj, Units.coe_map, AlgEquiv.coe_toAlgHom,
    AlgHom.coe_toMonoidHom] using
    PadicTateTwist.coe_tateModuleProj_galoisRepresentation σ x n

/-- Every Galois displacement lies in the cyclotomic submodule, so the induced action on the
quotient by this submodule is trivial. -/
theorem galois_sub_mem_range_tateCyclotomicMap (σ : L ≃ₐ[K] L) (hσ : Continuous σ)
    (x : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point)) :
    (tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ x - x ∈
      LinearMap.range (tateCyclotomicMap L q hq ℓ) := by
  rw [mem_range_tateCyclotomicMap_iff]
  intro n
  have heq : TateModule.proj n
      ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ x) =
      torsionByMap ((ℓ ^ n : ℕ) : ℤ) (Point.map σ.toAlgHom).toIntLinearMap
        (TateModule.proj n x) := by
    apply Subtype.ext
    simp only [coe_proj_tateModuleGaloisRepresentation, coe_torsionByMap_apply,
      AddMonoidHom.coe_toIntLinearMap]
  rw [map_sub, heq, map_sub, tateTorsionExponent_torsionByMap q hq (ℓ ^ n) σ.toAlgHom hσ,
    sub_self]

end TauCeti
