/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Galois
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Completion
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Arithmetic inertia acts unipotently on Tate-curve torsion

For a Tate curve over a nonarchimedean local field `K`, every element of arithmetic inertia
satisfies `(σ - 1)² = 0` on torsion of order prime to the residue characteristic, and on the
corresponding Tate modules. These are statements about points over the algebraic closure,
not a conditional statement about an automorphism of an unspecified complete extension.

The uniformization is used over the completion of the algebraic closure. The spectral norm
makes each arithmetic automorphism continuous there; inertia fixes the prime-to-residue-
characteristic roots of unity even after completion. Injectivity of the point map then brings
the identity back to the algebraic closure. This supplies the unipotence input for the inertia
representation at split multiplicative reduction, without choosing a basis of torsion.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
-/

public noncomputable section

open UniformSpace ValuativeRel WeierstrassCurve WeierstrassCurve.Affine
open scoped AddSubgroup

namespace TauCeti

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DecidableEq (AlgebraicClosure K)]
  (q : Kˣ) (hq : ‖(q : K)‖ < 1)

/-- An element of arithmetic inertia has square-zero displacement on every prime-to-residue-
characteristic torsion point of a Tate curve over the algebraic closure. -/
theorem map_tateCurveAt_sub_sq_eq_zero_of_mem_inertiaSubgroup {m : ℕ}
    (hm : m.Coprime (ringChar 𝓀[K])) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K)
    {P : ((tateCurveAt q hq)⁄(AlgebraicClosure K)).toAffine.Point} (hP : m • P = 0) :
    Point.map σ.toAlgHom (Point.map σ.toAlgHom P - P) -
      (Point.map σ.toAlgHom P - P) = 0 := by
  classical
  let : NontriviallyNormedField K :=
    .ofNormNeOne ⟨(q : K), q.ne_zero, hq.ne⟩
  let : NormedField (AlgebraicClosure K) := spectralNorm.normedField K _
  let : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K _
  let C := Completion (AlgebraicClosure K)
  let : IsUltrametricDist C := .of_normedAlgebra K
  let ι := IsScalarTower.toAlgHom K (AlgebraicClosure K) C
  let τ := Completion.mapAlgEquiv σ σ.isometry_of_isAlgebraic.continuous
    σ.symm.isometry_of_isAlgebraic.continuous
  have hτ : Continuous τ := Completion.continuous_mapAlgEquiv _ _ _
  have hroots (ζ : rootsOfUnity m C) : restrictRootsOfUnity τ.toAlgHom m ζ = ζ := by
    apply rootsOfUnity.coe_injective
    exact apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one_completion hσ hm
      (congrArg Units.val ((mem_rootsOfUnity m (ζ : Cˣ)).mp ζ.2))
  have hcomm (Q : ((tateCurveAt q hq)⁄(AlgebraicClosure K)).toAffine.Point) :
      Point.map τ.toAlgHom (Point.map ι Q) = Point.map ι (Point.map σ.toAlgHom Q) := by
    have heq : τ.toAlgHom.comp ι = ι.comp σ.toAlgHom := by
      ext x
      -- The scalar-tower map is the canonical embedding into the completion.
      simp only [AlgHom.comp_apply, ι, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom,
        τ, C, Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
        Completion.mapAlgEquiv_coe]
    rw [Point.map_map, Point.map_map, heq]
  have hQ : m • Point.map ι P = 0 := by rw [← map_nsmul, hP, map_zero]
  have h := congrArg Subtype.val <| LinearMap.congr_fun
    (torsionByMap_tateCurveAt_sub_id_sq_eq_zero q hq m τ.toAlgHom hτ hroots)
    ⟨Point.map ι P, AddSubgroup.torsionBy.nsmul_iff.mpr hQ⟩
  apply Point.map_injective (f := ι)
  simpa only [pow_two, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply, coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap,
    AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero, map_sub, hcomm, map_zero] using h

/-- Arithmetic inertia acts unipotently of index at most two on the prime-to-residue-
characteristic Tate module of a Tate curve. The representation is the native one over the
algebraic closure. -/
theorem tateModuleGaloisRepresentation_tateCurveAt_sub_one_sq_eq_zero_of_mem_inertiaSubgroup
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (ringChar 𝓀[K]))
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply TateModule.ext
  intro n
  apply Subtype.ext
  simpa only [pow_two, mul_apply_eq_comp, LinearMap.sub_apply, one_apply_eq_self,
    map_sub, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero,
    coe_proj_tateModuleGaloisRepresentation, LinearMap.zero_apply, map_zero] using
    map_tateCurveAt_sub_sq_eq_zero_of_mem_inertiaSubgroup q hq (hℓ.pow_left n) hσ
      (AddSubgroup.torsionBy.nsmul_iff.mp (TateModule.proj n x).2)

end TauCeti
