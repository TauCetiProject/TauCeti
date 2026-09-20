/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Generated.Preserves
public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Generators
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Tensor invariance for the short-root type-G2 carrier over the prime field

The four numbered simple root subgroups and the weight torus of the short-root type-`G₂` carrier
over `𝔽₃` preserve the type-`G₂` cross product and fix the invariant dual form by congruence.
Both statements are equations between matrices, so they pass from the generators to the whole
generated subgroup of points, and hence to the universal point of the carrier's coordinate Hopf
algebra.

This is what the special isogeny of characteristic three needs: the matrix `Matrix.g2SpecialIsogeny`
of signed two-by-two minors is multiplicative exactly on matrices preserving both tensors.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.preservesG2Cross_of_mem_points` and
  `TauCeti.G2ShortRoot.PrimeField.preservesDualForm_of_mem_points`: every matrix-valued point of
  the carrier preserves both tensors.
* `TauCeti.G2ShortRoot.PrimeField.preservesG2Cross_carrierGenericMatrix` and
  `TauCeti.G2ShortRoot.PrimeField.preservesDualForm_carrierGenericMatrix`: the universal point
  does too.

## References

* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix WithConv
open scoped TensorProduct
open scoped CategoryTheory.MonObj

namespace TauCeti.G2ShortRoot.PrimeField

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

universe v

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

private noncomputable def crossOperatorPrime : Fin 7 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  fun a => (crossOperator a).map (Int.cast : ℤ → ZMod 3)

private noncomputable def invariantDualFormPrime : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  invariantDualForm.map (Int.cast : ℤ → ZMod 3)

private theorem map_algebraMap_crossOperatorPrime (a : Fin 7) :
    (crossOperatorPrime a).map (algebraMap (ZMod 3) A) =
      (crossOperator a).map (Int.cast : ℤ → A) := by
  rw [crossOperatorPrime, Matrix.map_map]
  exact congrArg _ (funext fun z => map_intCast (algebraMap (ZMod 3) A) z)

private theorem map_algebraMap_invariantDualFormPrime :
    invariantDualFormPrime.map (algebraMap (ZMod 3) A) =
      invariantDualForm.map (Int.cast : ℤ → A) := by
  rw [invariantDualFormPrime, Matrix.map_map]
  exact congrArg _ (funext fun z => map_intCast (algebraMap (ZMod 3) A) z)

private theorem preserves_crossOperatorPrime_iff (g : Matrix (Fin 7) (Fin 7) A) :
    ConstantMultiplication.Preserves (ZMod 3) 7 crossOperatorPrime g ↔ PreservesG2Cross g := by
  constructor
  · intro h
    rw [ConstantMultiplication.preserves_def] at h
    rw [preservesG2Cross_def]
    intro k
    simpa only [ConstantMultiplication.imageStructureMatrix_def,
      map_algebraMap_crossOperatorPrime] using h k
  · intro h
    rw [preservesG2Cross_def] at h
    rw [ConstantMultiplication.preserves_def]
    intro k
    simpa only [ConstantMultiplication.imageStructureMatrix_def,
      map_algebraMap_crossOperatorPrime] using h k

/-- The generic matrix of `GL₇` pushed along the coordinate map of a numbered simple root
subgroup is the matrix of a root-subgroup point at a universal parameter. -/
theorem exists_map_genericMatrix_generator_inl (k : Fin 2 ⊕ Fin 2) :
    ∃ u : Multiplicative (AdditiveGroup.coordinateHopfAlgebra (ZMod 3)),
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
          (generator (.inl k)).hom.toAlgHom =
        ((rootSubgroupPoints k
          (AdditiveGroup.coordinateHopfAlgebra (ZMod 3)) u :
          _root_.Matrix.GeneralLinearGroup (Fin 7)
            (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) :
          Matrix (Fin 7) (Fin 7) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) := by
  set B : CommAlgCat (ZMod 3) :=
    CommAlgCat.of (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3)) with hB
  set q : HopfAlgebra.points (R := ZMod 3)
      (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3)) B :=
    toConv (AlgHom.id (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) with hq
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inl k))).app B q =
      toConv (generator (.inl k)).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, hq, WithConv.ofConv_toConv, AlgHom.id_comp]
  refine ⟨AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) q, ?_⟩
  rw [coe_rootSubgroupPoints_gaPointsMulEquiv, hid,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    TauCeti.GeneralLinear.pointsMulEquiv_apply]

/-- The generic matrix of `GL₇` pushed along the coordinate map of the weight torus is the
matrix of a torus point at universal coordinates. -/
theorem exists_map_genericMatrix_generator_inr :
    ∃ s : Fin 2 → ((DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (Fin 2))).obj)ˣ,
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
          (generator (.inr ())).hom.toAlgHom =
        ((weightTorusPoints
          ((DiagonalizableGroup.coordinateRing (ZMod 3)
            (SplitTorus.characterGroup (Fin 2))).obj) s :
          _root_.Matrix.GeneralLinearGroup (Fin 7)
            ((DiagonalizableGroup.coordinateRing (ZMod 3)
              (SplitTorus.characterGroup (Fin 2))).obj)) :
          Matrix (Fin 7) (Fin 7) ((DiagonalizableGroup.coordinateRing (ZMod 3)
            (SplitTorus.characterGroup (Fin 2))).obj)) := by
  set B : CommAlgCat (ZMod 3) :=
    CommAlgCat.of (ZMod 3) ((DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (Fin 2))).obj) with hB
  set q : HopfAlgebra.points (R := ZMod 3)
      (H := (DiagonalizableGroup.coordinateRing (ZMod 3)
        (SplitTorus.characterGroup (Fin 2))).obj) B :=
    toConv (AlgHom.id (ZMod 3) ((DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (Fin 2))).obj)) with hq
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inr ()))).app B q =
      toConv (generator (.inr ())).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, hq, WithConv.ofConv_toConv, AlgHom.id_comp]
  refine ⟨SplitTorus.pointsMulEquiv q, ?_⟩
  rw [coe_weightTorusPoints_pointsMulEquiv, hid,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    TauCeti.GeneralLinear.pointsMulEquiv_apply]

/-- The matrix of the point at parameter `t` of the root subgroup numbered `inl 0`. -/
theorem coe_rootSubgroupPoints_inl_zero (t : A) :
    ((rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      1 + t • (raisingMatrix 0).map (Int.cast : ℤ → A) + t ^ 2 • Matrix.single 2 4 1 := by
  rw [coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inl_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raisingMatrix, Matrix.single, mul_comm]

/-- The matrix of the point at parameter `t` of the root subgroup numbered `inl 1`. -/
theorem coe_rootSubgroupPoints_inl_one (t : A) :
    ((rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      1 + t • (raisingMatrix 1).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inl_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raisingMatrix]

/-- The matrix of the point at parameter `t` of the root subgroup numbered `inr 0`. -/
theorem coe_rootSubgroupPoints_inr_zero (t : A) :
    ((rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      1 + t • (loweringMatrix 0).map (Int.cast : ℤ → A) + t ^ 2 • Matrix.single 4 2 1 := by
  rw [coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inr_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loweringMatrix, Matrix.single, mul_comm]

/-- The matrix of the point at parameter `t` of the root subgroup numbered `inr 1`. -/
theorem coe_rootSubgroupPoints_inr_one (t : A) :
    ((rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      1 + t • (loweringMatrix 1).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inr_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loweringMatrix]

private theorem preservesG2Cross_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (t : A) :
    PreservesG2Cross
      (((rootSubgroupPoints k A (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) := by
  rcases k with i | i
  · fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta]
      rw [coe_rootSubgroupPoints_inl_zero]
      exact
        preservesG2Cross_one_add_smul_raisingMatrix_zero_add_sq_smul_single t
    · simp only [Fin.isValue, Fin.mk_one]
      rw [coe_rootSubgroupPoints_inl_one]
      exact preservesG2Cross_one_add_smul_raisingMatrix_one t
  · fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta]
      rw [coe_rootSubgroupPoints_inr_zero]
      exact
        preservesG2Cross_one_add_smul_loweringMatrix_zero_add_sq_smul_single t
    · simp only [Fin.isValue, Fin.mk_one]
      rw [coe_rootSubgroupPoints_inr_one]
      exact preservesG2Cross_one_add_smul_loweringMatrix_one t

private theorem preservesDualForm_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (t : A) :
    let g := ((rootSubgroupPoints k A (Multiplicative.ofAdd t) :
      _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)
    g * invariantDualForm.map (Int.cast : ℤ → A) * gᵀ =
      invariantDualForm.map (Int.cast : ℤ → A) := by
  rcases k with i | i
  · fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta]
      rw [coe_rootSubgroupPoints_inl_zero]
      exact
        one_add_smul_raisingMatrix_zero_add_sq_smul_single_mul_invariantDualForm_mul_transpose t
    · simp only [Fin.isValue, Fin.mk_one]
      rw [coe_rootSubgroupPoints_inl_one]
      exact one_add_smul_raisingMatrix_one_mul_invariantDualForm_mul_transpose t
  · fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta]
      rw [coe_rootSubgroupPoints_inr_zero]
      exact
        one_add_smul_loweringMatrix_zero_add_sq_smul_single_mul_invariantDualForm_mul_transpose t
    · simp only [Fin.isValue, Fin.mk_one]
      rw [coe_rootSubgroupPoints_inr_one]
      exact one_add_smul_loweringMatrix_one_mul_invariantDualForm_mul_transpose t

/-- Every point of the short-root type-`G₂` carrier preserves the invariant cross product. -/
theorem preservesG2Cross_of_mem_points {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ points A) :
    PreservesG2Cross ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) := by
  rw [← preserves_crossOperatorPrime_iff]
  refine TauCeti.GeneralLinear.preserves_of_mem_generatedPointsSubgroup 7 generator
    crossOperatorPrime (fun j => ?_) A (points_def A ▸ hg)
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
    obtain ⟨t, rfl⟩ : ∃ t, Multiplicative.ofAdd t = u := ⟨Multiplicative.toAdd u, rfl⟩
    rw [hu, preserves_crossOperatorPrime_iff]
    exact preservesG2Cross_rootSubgroupPoints k t
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    rw [hs, preserves_crossOperatorPrime_iff,
      coe_weightTorusPoints, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal]
    exact preservesG2Cross_diagonal_torusCharacter s

/-- Every point of the short-root type-`G₂` carrier fixes the invariant dual form by
congruence. -/
theorem preservesDualForm_of_mem_points {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ points A) :
    ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
        invariantDualForm.map (Int.cast : ℤ → A) *
        ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → A) := by
  have key := TauCeti.GeneralLinear.mul_mul_transpose_of_mem_generatedPointsSubgroup 7 generator
    invariantDualFormPrime (fun j => ?_) A (points_def A ▸ hg)
  · rwa [map_algebraMap_invariantDualFormPrime] at key
  · rcases j with k | ⟨⟩
    · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
      obtain ⟨t, rfl⟩ : ∃ t, Multiplicative.ofAdd t = u := ⟨Multiplicative.toAdd u, rfl⟩
      rw [hu, map_algebraMap_invariantDualFormPrime]
      exact preservesDualForm_rootSubgroupPoints k t
    · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
      rw [hs, map_algebraMap_invariantDualFormPrime,
        coe_weightTorusPoints, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal]
      exact diagonal_torusCharacter_mul_invariantDualForm_mul_transpose s

/-- Preserving the type-`G₂` cross product is inherited by the image of a matrix under an
algebra map. -/
theorem preservesG2Cross_map {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 3) S] [Algebra (ZMod 3) T] (f : S →ₐ[ZMod 3] T)
    {M : Matrix (Fin 7) (Fin 7) S} (h : PreservesG2Cross M) :
    PreservesG2Cross (M.map f) := by
  rw [← preserves_crossOperatorPrime_iff] at h ⊢
  exact ConstantMultiplication.Preserves.map (ZMod 3) 7 crossOperatorPrime h f

/-- Fixing the invariant dual form by congruence is inherited by the image of a matrix under a
ring homomorphism. -/
theorem preservesDualForm_map {S T : Type*} [Ring S] [Ring T] (f : S →+* T)
    {M : Matrix (Fin 7) (Fin 7) S}
    (h : M * invariantDualForm.map (Int.cast : ℤ → S) * Mᵀ =
      invariantDualForm.map (Int.cast : ℤ → S)) :
    M.map f * invariantDualForm.map (Int.cast : ℤ → T) * (M.map f)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → T) := by
  have hform : (invariantDualForm.map (Int.cast : ℤ → S)).map (f : S → T) =
      invariantDualForm.map (Int.cast : ℤ → T) := by
    rw [Matrix.map_map]
    exact congrArg _ (funext fun z => map_intCast f z)
  have himg := congrArg (fun N : Matrix (Fin 7) (Fin 7) S => N.map (f : S →+* T)) h
  simp only [Matrix.map_mul, Matrix.transpose_map] at himg
  rwa [hform] at himg

private theorem coe_universalPoint :
    ((TauCeti.GeneralLinear.pointToGeneralLinear 7 (toConv carrierQuotient.hom.toAlgHom) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) carrierAlgebra) :
      Matrix (Fin 7) (Fin 7) carrierAlgebra) = carrierGenericMatrix := by
  rw [carrierGenericMatrix_def,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]

private theorem universalPoint_mem_points :
    TauCeti.GeneralLinear.pointToGeneralLinear 7 (toConv carrierQuotient.hom.toAlgHom) ∈
      points carrierAlgebra := by
  rw [points_eq_hopfIdealPointsSubgroup,
    TauCeti.GeneralLinear.pointToGeneralLinear_mem_hopfIdealPointsSubgroup_iff_toIdeal_le_ker]
  -- `carrierQuotient` is an abbreviation for this quotient map; exposing that stable
  -- presentation lets the quotient-kernel theorem apply without unfolding unrelated coercions.
  simpa only [definingIdeal_def] using
    (show (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker carrierQuotient.hom.toAlgHom.toRingHom by
      rw [show carrierQuotient = CommHopfAlgCat.mkQuotient
        (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
        (CommHopfAlgCat.commonKernelHopfIdeal generator) from rfl,
        CommHopfAlgCat.mkQuotient_ker])

/-- The universal point of the carrier preserves the invariant cross product. -/
theorem preservesG2Cross_carrierGenericMatrix : PreservesG2Cross carrierGenericMatrix := by
  rw [← coe_universalPoint]
  exact preservesG2Cross_of_mem_points universalPoint_mem_points

/-- The universal point of the carrier fixes the invariant dual form by congruence. -/
theorem preservesDualForm_carrierGenericMatrix :
    carrierGenericMatrix * invariantDualForm.map (Int.cast : ℤ → carrierAlgebra) *
        carrierGenericMatrixᵀ = invariantDualForm.map (Int.cast : ℤ → carrierAlgebra) := by
  rw [← coe_universalPoint]
  exact preservesDualForm_of_mem_points universalPoint_mem_points

end TauCeti.G2ShortRoot.PrimeField
