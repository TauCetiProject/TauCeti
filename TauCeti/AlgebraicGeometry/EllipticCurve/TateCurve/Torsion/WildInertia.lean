/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Basic
public import TauCeti.NumberTheory.LocalField.WildInertia

/-!
# Wild inertia on Tate-curve torsion

Over a nonarchimedean local field, absolute wild inertia acts trivially on the prime-to-residue-
characteristic torsion of a Tate curve in every finite normal extension. No root of the Tate
parameter is required in the extension: a unit representative of a torsion point has an `n`-th
power which is an integer power of the parameter, so wild inertia fixes that representative.

The proof equips the finite extension with the spectral norm. The algebraic closure is used
only for the absolute Galois action and need not be complete or normed.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
* J.-P. Serre, *Corps Locaux*, Chapter IV, §2.
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine _root_.ValuativeRel
open scoped _root_.AddSubgroup

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [Normal K L]
  [DecidableEq L]
  (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℕ)

/-- Absolute wild inertia fixes every Tate `n`-torsion point in a finite normal extension
when the residue characteristic does not divide `n`. In particular this applies at every
`ℓ`-power level for `ℓ` different from the residue characteristic. -/
theorem torsionByMap_tateCurveAt_eq_id_of_mem_wildInertiaSubgroup
    (hn : ¬ ringChar 𝓀[K] ∣ n) (σ : Gal(AlgebraicClosure K/K))
    (hσ : σ ∈ wildInertiaSubgroup K) :
    torsionByMap (n : ℤ)
      (Point.map (W' := (tateCurveAt q hq).toAffine)
        (AlgEquiv.restrictNormal σ L).toAlgHom).toIntLinearMap = LinearMap.id := by
  let _ := spectralNorm.normedField K L
  let _ := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hcont : Continuous (AlgEquiv.restrictNormal σ L) :=
    (AlgEquiv.restrictNormal σ L).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  apply LinearMap.ext
  intro P
  obtain ⟨v, hv⟩ := tateUnitHom_surjective L q hq (P : ((tateCurveAt q hq)⁄L).toAffine.Point)
  obtain ⟨v, rfl⟩ := Additive.ofMul.surjective v
  have hzero : tateUnitHom L q hq (.ofMul (v ^ n)) = 0 := by
    rw [ofMul_pow, map_nsmul, hv]
    exact (AddSubgroup.torsionBy.nsmul_iff.mp P.property)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp ((tateUnitHom_eq_zero_iff L q hq _).mp hzero)
  have hpow : (v : L) ^ n = algebraMap K L (q ^ a : Kˣ) := by
    simpa using congrArg (fun w : Lˣ ↦ (w : L)) ha.symm
  have hfix : Units.map ((AlgEquiv.restrictNormal σ L).toAlgHom : L →* L) v = v := by
    apply Units.ext
    apply Subtype.ext
    rw [Units.coe_map, AlgHom.coe_toMonoidHom, AlgEquiv.coe_toAlgHom,
      AlgEquiv.restrictNormal_apply]
    apply (mem_wildInertiaSubgroup_iff_pow_eq.mp hσ) n hn (q ^ a)
    exact_mod_cast congrArg L.val hpow
  apply Subtype.ext
  simp only [coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply,
    ← hv, map_tateUnitHom q hq (AlgEquiv.restrictNormal σ L).toAlgHom hcont, hfix]

end TauCeti
