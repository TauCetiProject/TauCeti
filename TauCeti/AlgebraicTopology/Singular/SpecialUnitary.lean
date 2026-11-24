/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.Algebra.Quaternion.Unitary
public import TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary

/-!
# The singular homology of `SU(2)` and `SU(3)`

With coefficients in any ring `R`, the singular homology of the special unitary group `SU(3)` is
`R` in the degrees `0`, `3`, `5` and `8` and zero in every other degree
(`TauCeti.singularHomologySpecialUnitaryGroupThreeIso`,
`TauCeti.isZero_singularHomology_specialUnitaryGroup_three`).

**`SU(2)`.** The unit quaternions form the group `SU(2)`, so `SU(2)` is the three-sphere
(`TauCeti.specialUnitaryGroupTwoHomeomorphSphere`). Its homology is `R` in degrees `0` and `3` and
zero otherwise (`TauCeti.singularHomologySpecialUnitaryGroupTwoIso`,
`TauCeti.isZero_singularHomology_specialUnitaryGroup_two`).

**`SU(3)`.** Evaluation on the first coordinate vector, `A ↦ A e₀`, is a locally trivial bundle
`SU(2) → SU(3) → S⁵` (`TauCeti.specialUnitarySphereMap_mem_serreFibrations`), with fibre
`A · diag(1, SU(2))` over `A e₀` (`TauCeti.specialUnitarySphereFiberHomeomorphMul`). Filter `SU(3)`
by the preimages of the skeleta of the CW structure of `S⁵` with one `0`-cell and one `5`-cell. The
first page of this filtration has two columns, `H_*(SU(2))` over the `0`-cell and `H_*(SU(2))`
shifted by `5` over the `5`-cell (`TauCeti.TopCat.sphereFibrationSingularHomologyIso`). Its
nonzero entries have total degrees `0`, `3` and `5`, `8`. Every differential from the second
column lands in total degree `4` or `7`, where the first column vanishes, so the filtration
collapses and there is no extension problem, each total degree carrying a single entry. In terms of
the long exact sequence of the pair `(SU(3), F)`, `F` the fibre over the pole:

* below degree `4`, the inclusion `F ⟶ SU(3)` is an isomorphism on homology, so
  `Hₖ(SU(3)) ≅ Hₖ(SU(2))` (`TauCeti.singularHomologySpecialUnitaryGroupThreeIsoOfLt`);
* `H₄(SU(3)) = 0`, since `H₄(F)` and `H₄(SU(3), F)` vanish
  (`TauCeti.isZero_singularHomology_specialUnitaryGroup_three_four`);
* from degree `5` on, `F` has no homology in the degrees `q + 5` and `q + 4`, so
  `Hq+5(SU(3)) ≅ Hq+5(SU(3), F) ≅ Hq(SU(2))`
  (`TauCeti.singularHomologySpecialUnitaryGroupThreeAddFiveIso`).

The ring structure `H^*(SU(3); ℤ) = Λ(x₃, x₅)` needs products and is not computed here.

## Main definitions

* `TauCeti.singularHomologySpecialUnitaryGroupTwoIso`: `Hₖ(SU(2); R) ≅ R` for `k ∈ {0, 3}`.
* `TauCeti.singularHomologySpecialUnitaryGroupThreeIsoOfLt`: `Hₖ(SU(3); R) ≅ Hₖ(SU(2); R)` for
  `k < 4`.
* `TauCeti.singularHomologySpecialUnitaryGroupThreeAddFiveIso`:
  `Hq+5(SU(3); R) ≅ Hq(SU(2); R)`.
* `TauCeti.singularHomologySpecialUnitaryGroupThreeIso`: `Hₖ(SU(3); R) ≅ R` for
  `k ∈ {0, 3, 5, 8}`.

## Main results

* `TauCeti.isZero_singularHomology_specialUnitaryGroup_two`: `Hₖ(SU(2); R) = 0` for
  `k ∉ {0, 3}`.
* `TauCeti.isZero_singularHomology_specialUnitaryGroup_three`: `Hₖ(SU(3); R) = 0` for
  `k ∉ {0, 3, 5, 8}`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (the bundles
  `SU(n) → SU(n + 1) → S^(2n+1)`) and §3.D (the homology of `SU(n)`).
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1 (the Wang sequence of a fibration over a sphere).
-/

public section

noncomputable section

open CategoryTheory Limits Matrix Metric Module AlgebraicTopology
open scoped Quaternion

namespace TauCeti

variable (R : Type) [Ring R]

/-! ### `SU(2)` -/

/-- **`SU(2)` is the three-sphere**: the unit quaternions form the group `SU(2)`, and they are the
unit sphere of `ℍ`. -/
def specialUnitaryGroupTwoHomeomorphSphere :
    specialUnitaryGroup (Fin 2) ℂ ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.symm.toHomeomorph.trans
    Quaternion.unitaryHomeomorphSphere

/-- The point of the three-sphere attached to `A ∈ SU(2)` is the unit quaternion whose complex
matrix is `A`. -/
@[simp]
theorem toComplexMatrix_specialUnitaryGroupTwoHomeomorphSphere_apply
    (A : specialUnitaryGroup (Fin 2) ℂ) :
    Quaternion.toComplexMatrix (specialUnitaryGroupTwoHomeomorphSphere A : ℍ[ℝ]) =
      (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- The homeomorphism underlying a continuous multiplicative equivalence applies it, by definition.
  have h : Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.symm.toHomeomorph A =
      Quaternion.unitaryEquivSpecialUnitaryGroup.symm A :=
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup_symm_apply A
  rw [specialUnitaryGroupTwoHomeomorphSphere, Homeomorph.trans_apply,
    Quaternion.coe_unitaryHomeomorphSphere_apply, h]
  exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_symm_apply A

/-- The quaternions have real dimension `3 + 1`. -/
private lemma finrank_quaternion : finrank ℝ ℍ[ℝ] = 3 + 1 :=
  Quaternion.finrank_eq_four

/-- `SU(2)` is path connected, as the three-sphere is. -/
private lemma pathConnectedSpace_specialUnitaryGroup_two :
    PathConnectedSpace (specialUnitaryGroup (Fin 2) ℂ) :=
  have : PathConnectedSpace (sphere (0 : ℍ[ℝ]) 1) :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere (by
      rw [← finrank_eq_rank, finrank_quaternion]; norm_num) 0 zero_le_one)
  specialUnitaryGroupTwoHomeomorphSphere.symm.surjective.pathConnectedSpace
    specialUnitaryGroupTwoHomeomorphSphere.symm.continuous

/-- **The homology of `SU(2)` vanishes outside degrees `0` and `3`**, with coefficients in any
ring. -/
theorem isZero_singularHomology_specialUnitaryGroup_two {k : ℕ} (h₀ : k ≠ 0) (h₃ : k ≠ 3) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h₀
  exact ((isZero_reducedSingularHomologyFunctor_sphere_of_ne (ModuleCat.of R R)
    finrank_quaternion (by omega)).of_iso
      (specialUnitaryGroupTwoHomeomorphSphere.toHomotopyEquiv.reducedSingularHomologyIso
        _ _)).of_iso
    ((reducedSingularHomologySuccIso (ModuleCat.of R R) k).app _).symm

/-- `H₃(SU(2); R) ≅ R`: the top homology of the three-sphere, with the generator given by an
orthonormal basis of `ℍ`. -/
private def singularHomologySpecialUnitaryGroupTwoThreeIso :
    ((singularHomologyFunctor (ModuleCat.{0} R) 3).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)) ≅ ModuleCat.of R R :=
  ((reducedSingularHomologySuccIso (ModuleCat.of R R) 2).app _).symm ≪≫
    specialUnitaryGroupTwoHomeomorphSphere.toHomotopyEquiv.reducedSingularHomologyIso _ 3 ≪≫
    reducedSingularHomologySphereIso (ModuleCat.of R R)
      ((stdOrthonormalBasis ℝ ℍ[ℝ]).reindex (finCongr finrank_quaternion))

/-- **The homology of `SU(2)` in degrees `0` and `3`**: `Hₖ(SU(2); R) ≅ R` for `k ∈ {0, 3}`. In
degree `0` this is the augmentation, `SU(2)` being path connected; in degree `3` it is the top
homology of the three-sphere. -/
def singularHomologySpecialUnitaryGroupTwoIso {k : ℕ} (hk : k = 0 ∨ k = 3) :
    ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)) ≅ ModuleCat.of R R :=
  if h : k = 0 then
    haveI := pathConnectedSpace_specialUnitaryGroup_two
    eqToIso (by rw [h]) ≪≫
      asIso ((_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)).singularHomology₀ε
        (ModuleCat.of R R))
  else
    eqToIso (by rw [hk.resolve_left h]) ≪≫ singularHomologySpecialUnitaryGroupTwoThreeIso R

/-! ### The bundle `SU(2) → SU(3) → S⁵` -/

/-- The unit sphere `S⁵` of `ℝ⁶`, which carries the CW structure with one `0`-cell and one
`5`-cell. -/
private abbrev FiveSphere : Type := sphere (0 : EuclideanSpace ℝ (Fin (5 + 1))) 1

private lemma card_fin_six : Fintype.card (Fin (5 + 1)) = 5 + 1 :=
  Fintype.card_fin _

/-- The unit sphere of `ℂ³` is the five-sphere. -/
private def fiveSphereHomeomorph :
    sphere (0 : EuclideanSpace ℂ (Fin (1 + 2))) 1 ≃ₜ FiveSphere :=
  sphereHomeomorphOfFinrankEq (by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin])

/-- The bundle `SU(3) → S⁵`, `A ↦ A e₀`, read on the five-sphere of `ℝ⁶`. -/
private abbrev fiveSphereProj :
    _root_.TopCat.of (specialUnitaryGroup (Fin (1 + 2)) ℂ) ⟶ _root_.TopCat.of FiveSphere :=
  _root_.TopCat.ofHom ⟨specialUnitarySphereMap 2, continuous_specialUnitarySphereMap ℂ 2⟩ ≫
    (_root_.TopCat.isoOfHomeo fiveSphereHomeomorph).hom

private lemma serreFibrations_fiveSphereProj : TopCat.serreFibrations fiveSphereProj :=
  MorphismProperty.RespectsIso.postcomp TopCat.serreFibrations _ _
    (specialUnitarySphereMap_mem_serreFibrations (𝕜 := ℂ) (n := 2))

/-- Every fibre of `SU(3) → S⁵` is homeomorphic to `SU(2)`. -/
private def fiveSphereProjFiberHomeomorph (b : FiveSphere) :
    specialUnitaryGroup (Fin 2) ℂ ≃ₜ
      (fiveSphereProj ⁻¹' {b} : Set (specialUnitaryGroup (Fin (1 + 2)) ℂ)) :=
  let A := (surjective_specialUnitarySphereMap (𝕜 := ℂ) (n := 2)
    (fiveSphereHomeomorph.symm b)).choose
  (specialUnitarySphereFiberHomeomorphMul ℂ 2 A).trans (Homeomorph.setCongr (by
    ext B
    simp only [Set.mem_preimage, Set.mem_singleton_iff, A,
      (surjective_specialUnitarySphereMap (fiveSphereHomeomorph.symm b)).choose_spec]
    exact fiveSphereHomeomorph.eq_symm_apply))

/-- The homology of a fibre of `SU(3) → S⁵` is that of `SU(2)`. -/
private def singularHomologyFiveSphereProjFiberIso (b : FiveSphere) (k : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (fiveSphereProj ⁻¹' {b} : Set (specialUnitaryGroup (Fin (1 + 2)) ℂ))) ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)) :=
  ((fiveSphereProjFiberHomeomorph b).toHomotopyEquiv.singularHomologyIso _ k).symm

/-! ### `SU(3)` -/

/-- **Below degree `4`, `SU(3)` has the homology of `SU(2)`**: `Hₖ(SU(3); R) ≅ Hₖ(SU(2); R)` for
`k < 4`, through the inclusion of a fibre of `SU(3) → S⁵`. -/
def singularHomologySpecialUnitaryGroupThreeIsoOfLt {k : ℕ} (hk : k < 4) :
    ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ)) ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)) :=
  (@asIso _ _ _ _ _ (TopCat.isIso_homologyMap_sphereFibration_of_lt card_fin_six
      serreFibrations_fiveSphereProj R (k := k) (by omega))).symm ≪≫
    singularHomologyFiveSphereProjFiberIso R _ k

/-- **`H₄(SU(3); R) = 0`**: both `H₄` of a fibre of `SU(3) → S⁵` and `H₄` of `SU(3)` modulo that
fibre vanish. -/
theorem isZero_singularHomology_specialUnitaryGroup_three_four :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) 4).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ))) :=
  TopPair.isZero_singularHomology_fst_of_isZero
    (TopPair.ofSubset (fiveSphereProj ⁻¹' {spherePolePoint card_fin_six})) (ModuleCat.of R R)
    ((isZero_singularHomology_specialUnitaryGroup_two R (by omega) (by omega)).of_iso
      (singularHomologyFiveSphereProjFiberIso R _ 4))
    (TopCat.isZero_singularHomology_sphereFibration_of_lt card_fin_six
      serreFibrations_fiveSphereProj R (by omega))

/-- **From degree `5` on, `SU(3)` has the homology of `SU(2)` shifted by `5`**:
`Hq+5(SU(3); R) ≅ Hq(SU(2); R)`, through the relative homology of `SU(3)` modulo a fibre of
`SU(3) → S⁵`. -/
def singularHomologySpecialUnitaryGroupThreeAddFiveIso (q : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) (q + 5)).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ)) ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) q).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)) :=
  TopCat.singularHomologySphereFibrationIsoOfIsZero card_fin_six serreFibrations_fiveSphereProj R
      (by omega) (m := q + 4) (by omega)
      ((isZero_singularHomology_specialUnitaryGroup_two R (by omega) (by omega)).of_iso
        (singularHomologyFiveSphereProjFiberIso R _ _))
      ((isZero_singularHomology_specialUnitaryGroup_two R (by omega) (by omega)).of_iso
        (singularHomologyFiveSphereProjFiberIso R _ _)) ≪≫
    singularHomologyFiveSphereProjFiberIso R _ q

/-- **The homology of `SU(3)` vanishes outside degrees `0`, `3`, `5` and `8`**, with coefficients
in any ring. -/
theorem isZero_singularHomology_specialUnitaryGroup_three {k : ℕ} (h₀ : k ≠ 0) (h₃ : k ≠ 3)
    (h₅ : k ≠ 5) (h₈ : k ≠ 8) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ))) := by
  rcases lt_trichotomy k 4 with hk | rfl | hk
  · exact (isZero_singularHomology_specialUnitaryGroup_two R h₀ h₃).of_iso
      (singularHomologySpecialUnitaryGroupThreeIsoOfLt R hk)
  · exact isZero_singularHomology_specialUnitaryGroup_three_four R
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 5 := ⟨k - 5, by omega⟩
    exact (isZero_singularHomology_specialUnitaryGroup_two R (by omega) (by omega)).of_iso
      (singularHomologySpecialUnitaryGroupThreeAddFiveIso R q)

/-- **The homology of `SU(3)` in degrees `0`, `3`, `5` and `8`**: `Hₖ(SU(3); R) ≅ R` for
`k ∈ {0, 3, 5, 8}`. In degrees `0` and `3` it comes from a fibre `SU(2)` of `SU(3) → S⁵`; in
degrees `5` and `8` it is the homology of `SU(2)` in degrees `0` and `3` shifted by the top cell of
`S⁵`. -/
def singularHomologySpecialUnitaryGroupThreeIso {k : ℕ} (hk : k = 0 ∨ k = 3 ∨ k = 5 ∨ k = 8) :
    ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ)) ≅ ModuleCat.of R R :=
  if h : k < 4 then
    singularHomologySpecialUnitaryGroupThreeIsoOfLt R h ≪≫
      singularHomologySpecialUnitaryGroupTwoIso R (by omega)
  else
    eqToIso (congrArg (fun j ↦ ((singularHomologyFunctor (ModuleCat.{0} R) j).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ)))
      (by omega : k = k - 5 + 5)) ≪≫
      singularHomologySpecialUnitaryGroupThreeAddFiveIso R (k - 5) ≪≫
      singularHomologySpecialUnitaryGroupTwoIso R (by omega)

end TauCeti
