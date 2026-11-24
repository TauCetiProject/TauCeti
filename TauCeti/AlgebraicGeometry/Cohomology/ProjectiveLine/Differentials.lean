/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.NegativeTwist

/-!
# The normalized trace on projective-line differentials

For every commutative ring `R`, the standard coordinates identify `H¹(ℙ¹_R, Ω)` with `R`.
The Mayer–Vietoris class of `dt/t` maps to `1`. This uses the signed comparison
`Ω ≅ 𝒪(-2)` and the explicit cohomology computation for negative twists.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite Polynomial

namespace TauCeti.AlgebraicGeometry.projectiveLine

noncomputable section

universe u

variable (R : Type u) [CommRing R]

open _root_.AlgebraicGeometry.Scheme.Modules _root_.TauCeti.AlgebraicGeometry.Scheme.Modules

/-- The coordinate-normalized identification `H¹(ℙ¹_R, Ω) ≃ R`.
Its inverse sends `1` to the Mayer–Vietoris class of `dt/t`. -/
def cohomologyOneDifferentialsLinearEquiv :
    Cohomology ((projectiveLine R).relativeDifferentials R) 1 ≃ₗ[R] R :=
  cohomologyBaseLinearEquivOfIso R (relativeDifferentialsIsoTwistingSheaf R) 1 ≪≫ₗ
    cohomologyOneTwistingSheafLinearEquiv R 0 ≪≫ₗ
      TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R (Fin 2 → R)

private abbrev overlap : (projectiveLine R).Opens :=
  Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R 0) ⊓
    Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R 1)

/-- The differential `dt/t` on the overlap of the two standard charts, where `t = X₁/X₀`. -/
def logDifferential : Γ((projectiveLine R).relativeDifferentials R,
    Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R 0) ⊓
      Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R 1)) :=
  (projectiveLine R).presheaf.map (homOfLE (show overlap R ≤ _ from inf_le_right)).op
    (affineCoordinate R 1) •
    ((projectiveLine R).universalDerivation R).d
      ((projectiveLine R).presheaf.map (homOfLE (show overlap R ≤ _ from inf_le_left)).op
        (affineCoordinate R 0))

/-- The logarithmic differential is the inverse chart coordinate times the differential
of the first coordinate. -/
lemma logDifferential_def :
    let U₀ := Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R 0)
    let U₁ := Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R 1)
    logDifferential R =
      (projectiveLine R).presheaf.map (homOfLE (show U₀ ⊓ U₁ ≤ U₁ from inf_le_right)).op
          (affineCoordinate R 1) •
        ((projectiveLine R).universalDerivation R).d
          ((projectiveLine R).presheaf.map (homOfLE (show U₀ ⊓ U₁ ≤ U₀ from inf_le_left)).op
            (affineCoordinate R 0)) :=
  (rfl)

private def twistOverlapOne :
    Γ(Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), overlap R) :=
  let c := (TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R (Fin 2 → R)).symm (1 : R)
  Proj.twistingSheaf.const (i := 2) (j := 0) (by norm_num) c.val
    ((coord R 0 * coord R 1) ^ 1) c.property (coord_mul_coord_pow_mem R 1) _
    (inf_le_basicOpen_coord_mul_coord_pow R)

private lemma twistOverlapOne_eq : twistOverlapOne R =
    (projectiveLine R).presheaf.map (homOfLE (show overlap R ≤ _ from inf_le_right)).op
    (affineCoordinate R 1) •
      Proj.twistingSheaf.chartGenerator (-2) (coord R 0) (coord_mem R 0) (overlap R)
        inf_le_left := by
  apply Proj.twistingSheaf.ext
  intro x
  let := x.val.isPrime
  erw [twistOverlapOne, Proj.twistingSheaf.const_apply, Proj.twistingSheaf.smul_apply,
    val_res_affineCoordinate, Proj.twistingSheaf.chartGenerator_apply]
  simp only [TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleZeroEquiv_symm_apply,
    map_one]
  norm_num only
  rw [Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  -- At this point the localization relation has reduced to the following polynomial
  -- identity; the type annotation selects the original symmetric algebra.
  change (coord R 1 * coord R 0 ^ 2) * 1 =
    (coord R 0 * coord R 1) ^ 1 * (coord R 0 * coord R 0 ^ 0)
  ring

private lemma differentialIsoTwist_inv_twistOverlapOne :
    (relativeDifferentialsIsoTwistingSheaf R).inv.app (overlap R) (twistOverlapOne R) =
      logDifferential R := by
  let f : Γ(Proj.twistingSheaf
      (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), overlap R) →ₗ[
        Γ(projectiveLine R, overlap R)]
      Γ((projectiveLine R).relativeDifferentials R, overlap R) :=
    ((relativeDifferentialsIsoTwistingSheaf R).inv.val.app (op (overlap R))).hom
  rw [twistOverlapOne_eq, logDifferential_def]
  -- `f` is the underlying component linear map, so use its explicit scalar law.
  erw [f.map_smul]
  have h := relativeDifferentialsIsoTwistingSheaf_inv_chartGenerator R 0 (overlap R) inf_le_left
  simp only [ite_true, one_smul] at h
  rw [PresheafOfModulesOfCommRing.Derivation.d_map]
  exact congrArg (fun a ↦
    (projectiveLine R).presheaf.map (homOfLE (show overlap R ≤ _ from inf_le_right)).op
      (affineCoordinate R 1) • a) h

/-- The inverse of the normalized cohomology comparison sends `1` to the class of `dt/t`. -/
@[simp]
lemma cohomologyOneDifferentialsLinearEquiv_symm_one :
    (cohomologyOneDifferentialsLinearEquiv R).symm 1 =
      mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R) (logDifferential R) := by
  simp only [cohomologyOneDifferentialsLinearEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, cohomologyBaseLinearEquivOfIso_symm_apply]
  -- The degree-zero specialization identifies `-(0 + 2)` with `-2` in the source
  -- cohomology module before the public twisting-cohomology application law can match.
  change cohomologyMapBaseLinear R (projectiveLine R)
    (relativeDifferentialsIsoTwistingSheaf R).inv 1
    ((cohomologyOneTwistingSheafLinearEquiv R 0).symm
      ((TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R (Fin 2 → R)).symm 1)) = _
  rw [cohomologyOneTwistingSheafLinearEquiv_symm_apply,
    cohomologyMapBaseLinear_apply, ← cohomologyMapLinear_apply]
  -- Only the local generator name and its specialized degree differ now; the cohomology
  -- map and boundary are kept opaque and are used through their application/naturality laws.
  change cohomologyMapLinear (relativeDifferentialsIsoTwistingSheaf R).inv 1
    (mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R) (twistOverlapOne R)) = _
  rw [mayerVietorisBoundaryLinear_naturality, differentialIsoTwist_inv_twistOverlapOne]

/-- The coordinate-normalized trace takes the Mayer–Vietoris class of `dt/t` to `1`. -/
@[simp]
lemma cohomologyOneDifferentialsLinearEquiv_logDifferential :
    cohomologyOneDifferentialsLinearEquiv R
      (mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R)
        (logDifferential R)) = 1 := by
  rw [← cohomologyOneDifferentialsLinearEquiv_symm_one, LinearEquiv.apply_symm_apply]

end

end TauCeti.AlgebraicGeometry.projectiveLine
