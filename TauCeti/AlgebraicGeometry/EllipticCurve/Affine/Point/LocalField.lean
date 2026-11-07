/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
public import Mathlib.NumberTheory.LocalField.Basic
import TauCeti.NumberTheory.LocalField.AdicCompletion
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Torsion lifting over a local field

Over a nonarchimedean local field, reduction identifies the prime-to-residue-characteristic
torsion of the subgroup with nonsingular reduction with that of the reduced nonsingular locus.
This applies to bad reduction as well as good reduction, and in particular lifts torsion on a
split node to the original local field, not merely to a separately constructed completion.

The formal kernel is uniquely divisible by integers invertible in the residue field. Correcting
an arbitrary nonsingular lift by a point in that kernel produces its unique torsion lift.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VII.2.1 and VII.3.1.
-/

public section

open ValuativeRel IsLocalRing IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]

section Division

variable (W : Affine K) [IsIntegral 𝒪[K] W] [W.IsElliptic]

/-- Division by a residue-field unit preserves the points reducing to infinity. -/
private theorem exists_nsmul_eq_of_pole {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0)
    {P : W.toAffine.Point} (hP : P = 0 ∨ 1 < valuation K P.xCoord) :
    ∃ Q : W.toAffine.Point, (Q = 0 ∨ 1 < valuation K Q.xCoord) ∧ n • Q = P := by
  classical
  let u := TauCeti.maximalPrime K
  let L := u.adicCompletion K
  let O := u.adicCompletionIntegers K
  let i := algebraMap K L
  let f : W.toAffine.Point →+ (W.map i).toAffine.Point :=
    AddMonoidHom.mk' (Point.mapAlong i i.injective) (Point.mapAlong_add i i.injective)
  have hf : Function.Bijective f := ⟨Point.mapAlong_injective i i.injective,
    Point.mapAlong_surjective i i.injective
      (TauCeti.bijective_algebraMap_adicCompletion_maximalPrime K).2⟩
  have hf_apply (Q : W.toAffine.Point) : f Q = Point.mapAlong i i.injective Q := (rfl)
  have hx (Q : W.toAffine.Point) : Valued.v (f Q).xCoord = u.valuation K Q.xCoord := by
    cases Q with
    | zero => simp only [← Point.zero_def, map_zero, Point.xCoord_zero]
    | some x y h =>
      rw [hf_apply, Point.mapAlong_some, Point.xCoord_some, Point.xCoord_some]
      exact u.valuedAdicCompletion_eq_valuation' x
  have hint : IsIntegral O (W.map i) := IsIntegral.baseChange
    ((IsScalarTower.algebraMap_eq 𝒪[K] O L).symm.trans
      (IsScalarTower.algebraMap_eq 𝒪[K] K L)) W
  have hdivide (V : WeierstrassCurve L) [IsIntegral O V] [V.IsElliptic]
      (R : V.toAffine.Point) (hR : R = 0 ∨ 1 < Valued.v R.xCoord) :
      ∃ S : V.toAffine.Point, (S = 0 ∨ 1 < Valued.v S.xCoord) ∧ n • S = R := by
    obtain ⟨C, rfl⟩ := (inferInstance : IsIntegral O V).integral
    have hR' : R ∈ C.kerReduction u := by
      rw [mem_kerReduction_iff, Point.reduction_eq_zero_iff]
      exact hR
    obtain ⟨S, hS⟩ := (C.nsmul_kerReduction_bijective u
      (TauCeti.natCast_notMem_maximalPrime (L := K) hn)).2 ⟨R, hR'⟩
    refine ⟨S, ?_, congrArg Subtype.val hS⟩
    exact (Point.reduction_eq_zero_iff _ _).mp ((C.mem_kerReduction_iff u).mp S.2)
  obtain ⟨S, hS, hnS⟩ := hdivide (W.map i) (f P) (hP.imp
    (fun h ↦ by rw [h, map_zero]) (fun h ↦ by
      rw [hx]
      exact (TauCeti.isEquiv_valuation_maximalPrime K).one_lt_iff_one_lt.mpr h))
  obtain ⟨Q, rfl⟩ := hf.2 S
  refine ⟨Q, ?_, hf.1 ?_⟩
  · exact hS.imp (fun h ↦ hf.1 (h.trans (map_zero _).symm)) (fun h ↦ by
      rw [hx] at h
      exact (TauCeti.isEquiv_valuation_maximalPrime K).one_lt_iff_one_lt.mp h)
  · rw [map_nsmul, hnS]

end Division

variable (W : Affine K) [IsIntegral (valuation K).valuationSubring W] [W.IsElliptic]

-- The integer subring 𝒪[K] and the valuation subring have definitionally equal carriers;
-- only their bundled subring structures differ.
local instance : HenselianLocalRing (valuation K).valuationSubring :=
  inferInstanceAs (HenselianLocalRing 𝒪[K])

variable [DecidableEq (ResidueField (valuation K).valuationSubring)]

/-- Multiplication by an integer nonzero in the residue field is bijective on the kernel of
nonsingular reduction over a nonarchimedean local field. -/
theorem nsmul_ker_nonsingularReductionHom_bijective {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0) :
    Function.Bijective
      (fun P : (W.toAffine.nonsingularReductionHom (valuation K)).ker ↦ n • P) := by
  classical
  let ρ := W.toAffine.nonsingularReductionHom (valuation K)
  have hzero (P : W.toAffine.nonsingularReduction (valuation K)) (hP : ρ P = 0)
      (hnP : n • P = 0) : P = 0 := by
    apply Subtype.ext
    by_contra hP0
    have hpole := ((nonsingularReductionHom_eq_zero_iff (valuation K) P).mp hP).resolve_left hP0
    have : IsIntegral ((TauCeti.maximalPrime K).valuation K).valuationSubring W := by
      rw [TauCeti.valuationSubring_valuation_maximalPrime]
      infer_instance
    have hle := Point.valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero
      (TauCeti.maximalPrime K) (TauCeti.natCast_notMem_maximalPrime (L := K) hn) hP0
      (congrArg Subtype.val hnP)
    exact hpole.not_ge ((TauCeti.isEquiv_valuation_maximalPrime K).le_one_iff_le_one.mp hle.1)
  constructor
  · intro P Q h
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply hzero
    · simp only [AddSubgroup.coe_sub, map_sub]
      have hP : ρ P = 0 := P.2
      have hQ : ρ Q = 0 := Q.2
      rw [hP, hQ, sub_self]
    · simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_sub,
        ZeroMemClass.coe_zero, nsmul_sub] using congrArg Subtype.val (sub_eq_zero.mpr h)
  · intro P
    -- Use the same carrier identification as for the Henselian instance above.
    let : IsIntegral 𝒪[K] W :=
      inferInstanceAs (IsIntegral (valuation K).valuationSubring W)
    obtain ⟨Q, hQ, hnQ⟩ := exists_nsmul_eq_of_pole W hn
      ((nonsingularReductionHom_eq_zero_iff (valuation K) P.val).mp P.2)
    have hQ₀ : Q ∈ W.toAffine.nonsingularReduction (valuation K) := hQ.elim
      (fun h ↦ h ▸ (W.toAffine.nonsingularReduction (valuation K)).zero_mem)
      (mem_nonsingularReduction_of_one_lt (valuation K))
    have hρQ : ρ ⟨Q, hQ₀⟩ = 0 := (nonsingularReductionHom_eq_zero_iff _ _).mpr hQ
    exact ⟨⟨⟨Q, hQ₀⟩, hρQ⟩, Subtype.ext (Subtype.ext hnQ)⟩

/-- Every reduced nonsingular point killed by an integer invertible in the residue field has a
unique lift killed by that integer and having nonsingular reduction, over the original local
field. No minimality or good-reduction hypothesis is required. -/
theorem existsUnique_nonsingularReduction_torsion_lift_of_localField {n : ℕ}
    (hn : (n : 𝓀[K]) ≠ 0)
    (Q : ((integralModel (valuation K).valuationSubring W.toAffine).map
      (residue (valuation K).valuationSubring)).toAffine.Point) (hQ : n • Q = 0) :
    ∃! P : W.toAffine.nonsingularReduction (valuation K),
      n • P = 0 ∧ W.toAffine.nonsingularReductionHom (valuation K) P = Q := by
  let ρ := W.toAffine.nonsingularReductionHom (valuation K)
  have hker : Function.Bijective (fun P : ρ.ker ↦ (n : ℤ) • P) := by
    simpa only [natCast_zsmul] using nsmul_ker_nonsingularReductionHom_bijective W hn
  -- The additive and ℤ-linear kernels have definitionally equal carriers.
  simpa only [natCast_zsmul, AddMonoidHom.coe_toIntLinearMap] using
    TauCeti.existsUnique_torsion_lift_of_bijective_ker_smul (n : ℤ) ρ.toIntLinearMap
      (nonsingularReductionHom_surjective (valuation K)) hker
      Q (by simpa only [natCast_zsmul] using hQ)

/-- Reduction identifies the prime-to-residue-characteristic torsion of the subgroup with
nonsingular reduction over a local field with the torsion of its reduced nonsingular locus. -/
noncomputable def torsionNonsingularReductionAddEquivOfLocalField {n : ℕ}
    (hn : (n : 𝓀[K]) ≠ 0) :
    Submodule.torsionBy ℤ (W.toAffine.nonsingularReduction (valuation K)) (n : ℤ) ≃+
      Submodule.torsionBy ℤ
        ((integralModel (valuation K).valuationSubring W.toAffine).map
          (residue (valuation K).valuationSubring)).toAffine.Point (n : ℤ) := by
  let ρ := W.toAffine.nonsingularReductionHom (valuation K)
  have hker : Function.Bijective (fun P : ρ.ker ↦ (n : ℤ) • P) := by
    simpa only [natCast_zsmul] using nsmul_ker_nonsingularReductionHom_bijective W hn
  -- The additive and ℤ-linear kernels have definitionally equal carriers.
  exact AddEquiv.ofBijective (TauCeti.torsionByMap (n : ℤ) ρ.toIntLinearMap).toAddMonoidHom
    (TauCeti.bijective_torsionByMap_of_bijective_ker_smul (n : ℤ) ρ.toIntLinearMap
      (nonsingularReductionHom_surjective (valuation K))
      hker)

/-- The local-field torsion equivalence sends a point to its reduction. -/
@[simp]
theorem coe_torsionNonsingularReductionAddEquivOfLocalField_apply {n : ℕ}
    (hn : (n : 𝓀[K]) ≠ 0)
    (P : Submodule.torsionBy ℤ (W.toAffine.nonsingularReduction (valuation K)) (n : ℤ)) :
    (W.torsionNonsingularReductionAddEquivOfLocalField hn P :
      ((integralModel (valuation K).valuationSubring W.toAffine).map
        (residue (valuation K).valuationSubring)).toAffine.Point) =
      W.toAffine.nonsingularReductionHom (valuation K) P :=
  TauCeti.coe_torsionByMap_apply _ _ _

/-- The inverse local-field torsion equivalence lifts a point to one with that reduction. -/
@[simp]
theorem nonsingularReductionHom_torsionNonsingularReductionAddEquivOfLocalField_symm {n : ℕ}
    (hn : (n : 𝓀[K]) ≠ 0)
    (Q : Submodule.torsionBy ℤ
      ((integralModel (valuation K).valuationSubring W.toAffine).map
        (residue (valuation K).valuationSubring)).toAffine.Point (n : ℤ)) :
    W.toAffine.nonsingularReductionHom (valuation K)
      ((W.torsionNonsingularReductionAddEquivOfLocalField hn).symm Q :
        W.toAffine.nonsingularReduction (valuation K)) = Q := by
  have h := congrArg Subtype.val
    ((W.torsionNonsingularReductionAddEquivOfLocalField hn).apply_symm_apply Q)
  simpa only [coe_torsionNonsingularReductionAddEquivOfLocalField_apply] using h

end WeierstrassCurve.Affine
