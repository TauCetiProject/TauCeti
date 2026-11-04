/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.AllDifferentials
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Adjoint weights at every root of the short-root F₄ carrier

Every selected root differential of the carrier generated over 𝔽₂ has the corresponding
integral torus character. Thus all forty-eight roots of the named F₄ datum occur in its
adjoint representation, including both root lengths in characteristic two. Characters are
not reduced modulo two: the argument uses the universal point of the weight torus.

These are lower bounds on the root spaces, not an assertion that they are one-dimensional
or exhaust the nonzero adjoint weights. No identification with an independently constructed
pinned group is made.

The root-curve coefficient calculation uses `PrimeField.Root.AllDifferentials`, and the
weight-space interpretation uses `HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open WithConv

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

local notation "R" => ZMod 2
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator
local notation "root" => f4Root

/-- The weight torus scales every selected root differential by its integral root character,
over arbitrary commutative coefficient algebras. -/
theorem weightTorusPoints_conj_tangentMatrix_rootDerivationAt
    (B : Type*) [CommRing B] [Algebra R B] (k : Fin F4.numRoots) (s : Fin 4 → Bˣ) :
    (weightTorusPoints B s : Matrix.GeneralLinearGroup (Fin 26) B) *
        GeneralLinear.tangentMatrix 26 (HopfIdeal.quotientLieHom J (rootDerivationAt B k)) *
        ((weightTorusPoints B s : Matrix.GeneralLinearGroup (Fin 26) B)⁻¹ :
          Matrix.GeneralLinearGroup (Fin 26) B) =
      (torusCharacter s (root k) : B) •
        GeneralLinear.tangentMatrix 26 (HopfIdeal.quotientLieHom J (rootDerivationAt B k)) := by
  let s' := fun i ↦ Units.map (Polynomial.C : B →+* Polynomial B).toMonoidHom (s i)
  have h := congrArg (fun g : points (Polynomial B) ↦
      ((g : Matrix.GeneralLinearGroup (Fin 26) (Polynomial B)) :
        Matrix (Fin 26) (Fin 26) (Polynomial B)))
    (weightTorusPoints_conj_rootSubgroupPointsAt k (Polynomial B) s'
      (Multiplicative.ofAdd Polynomial.X))
  have hT' : pointsMap (Polynomial.CAlgHom : B →ₐ[ZMod 2] Polynomial B)
      (weightTorusPoints B s) = weightTorusPoints (Polynomial B) s' :=
    pointsMap_weightTorusPoints _ s
  have hT := coe_coe_pointsMap (Polynomial.CAlgHom : B →ₐ[R] Polynomial B)
    (weightTorusPoints B s)
  have hTinv := coe_coe_pointsMap (Polynomial.CAlgHom : B →ₐ[R] Polynomial B)
    ((weightTorusPoints B s)⁻¹)
  simp only [map_inv, hT', Subgroup.coe_inv,
    funext (@Polynomial.CAlgHom_apply (ZMod 2) B _ _ _)] at hT hTinv
  have hχ : (torusCharacter s' (root k) : Polynomial B) =
      Polynomial.C (torusCharacter s (root k) : B) := by
    exact congrArg Units.val (map_torusCharacter Polynomial.C s (root k)).symm
  rw [simplyConnectedRootDatum_F4, f4SimplyConnectedRootDatum_root] at h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, toAdd_ofAdd] at h
  rw [hT, hTinv] at h
  -- The named datum has rank definitionally four; `erw` retypes its root embedding.
  erw [hχ] at h
  have hc := congrArg (fun M : Matrix (Fin 26) (Fin 26) (Polynomial B) ↦
    M.map (fun p ↦ p.coeff 1)) h
  rw [Matrix.map_coeff_mul_map_C, Matrix.map_coeff_map_C_mul] at hc
  have hc1 := map_coeff_one_rootSubgroupPointsAt B k 1
  simp only [map_one, one_mul, one_smul] at hc1
  -- As above, `erw` retypes the named datum's `Fin F4.rank` character as `Fin 4`.
  erw [hc1, map_coeff_one_rootSubgroupPointsAt] at hc
  exact hc

/-- Every selected root differential lies in the adjoint weight space of that root's
integral character. -/
theorem rootDerivationAt_mem_adjointWeightSpace (k : Fin F4.numRoots) :
    (Derivation.cotangentLinearEquiv (B := R)).symm (rootDerivationAt R k) ∈
      Derivation.adjointWeightSpace
        (CommHopfAlgCat.commonKernelLift generator (.inr ())).hom
        (SplitTorus.weightCharacter (root k)) := by
  rw [mem_adjointWeightSpace_iff]
  intro a b hab
  let K := MonoidAlgebra R (Multiplicative (Fin 4 →₀ ℤ))
  let s : Fin 4 → Kˣ := SplitTorus.pointsMulEquiv (toConv (AlgHom.id R K))
  have hχ (μ : Fin 4 → ℤ) : (torusCharacter s μ : K) =
      MonoidAlgebra.single (SplitTorus.weightCharacter μ) 1 := by
    rw [← SplitTorus.charOfPoint_weightCharacter,
      DiagonalizableGroup.charOfPoint_apply_coe, ofConv_toConv, AlgHom.id_apply]
  have hmap : GeneralLinear.tangentMatrix 26
      (HopfIdeal.quotientLieHom J (rootDerivationAt K k)) =
      (tangentMatrix ((Derivation.cotangentLinearEquiv (B := R)).symm
        (rootDerivationAt R k))).map (algebraMap R K) := by
    rw [← mapValue_rootDerivationAt (Algebra.ofId R K) k,
      HopfIdeal.quotientLieHom_mapValue, GeneralLinear.tangentMatrix_mapValue,
      tangentMatrix_apply, LinearEquiv.apply_symm_apply]
    ext a b
    simp only [Matrix.map_apply, Algebra.ofId_apply]
  have h := weightTorusPoints_conj_tangentMatrix_rootDerivationAt K k s
  rw [hmap, coe_weightTorusPoints, F4ShortRoot.coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, ← map_inv, diagGL_coe,
    diagGL_coe] at h
  have he := congrFun (congrFun h a) b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
    Pi.inv_apply, Matrix.smul_apply, smul_eq_mul] at he
  have he' :
      (torusCharacter s (f4ShortRootWeight a - f4ShortRootWeight b) : K) *
          algebraMap R K (tangentMatrix ((Derivation.cotangentLinearEquiv (B := R)).symm
            (rootDerivationAt R k)) a b) =
        (torusCharacter s (root k) : K) *
          algebraMap R K (tangentMatrix ((Derivation.cotangentLinearEquiv (B := R)).symm
            (rootDerivationAt R k)) a b) := by
    rw [torusCharacter_sub, div_eq_mul_inv, Units.val_mul, mul_right_comm]
    exact he
  simp only [hχ] at he'
  dsimp only [K] at he'
  simp only [MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, MonoidAlgebra.single_mul_single,
    one_mul, mul_one] at he'
  by_contra hne
  exact hab (MonoidAlgebra.single_left_injective hne he')

/-- All forty-eight roots occur as nontrivial adjoint weights of the short-root carrier
over 𝔽₂. This asserts occurrence, not exhaustion or root-space dimension. -/
theorem weightCharacter_root_mem_nontrivialAdjointWeights (k : Fin F4.numRoots) :
    SplitTorus.weightCharacter (root k) ∈ Derivation.nontrivialAdjointWeights
      (CommHopfAlgCat.commonKernelLift generator (.inr ())).hom := by
  apply Derivation.mem_nontrivialAdjointWeights.mpr
  refine ⟨SplitTorus.weightCharacter_eq_one_iff.not.mpr ?_, ?_⟩
  · simpa only [f4SimplyConnectedRootDatum_root] using (f4SimplyConnectedRootDatum.ne_zero k)
  · intro hbot
    have hv := rootDerivationAt_mem_adjointWeightSpace k
    rw [hbot, Submodule.mem_bot] at hv
    exact rootDerivationAt_ne_zero R k
      ((Derivation.cotangentLinearEquiv (B := R)).symm.map_eq_zero_iff.mp hv)

end

end TauCeti.F4ShortRoot.PrimeField
