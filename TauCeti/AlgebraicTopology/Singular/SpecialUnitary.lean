/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Algebra.Quaternion.Unitary
public import TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary

/-!
# The singular homology of `SU(2)` and `SU(3)`

With coefficients in any ring `R`, the singular homology of the special unitary group `SU(3)` is
`R` in the degrees `0`, `3`, `5` and `8` and zero in every other degree
(`TauCeti.singularHomologySpecialUnitaryGroupThreeIso`,
`TauCeti.isZero_singularHomology_specialUnitaryGroup_three`).

**`SU(2)`.** The unit quaternions form the group `SU(2)`, so `SU(2)` is the three-sphere
(`TauCeti.specialUnitaryGroupTwoHomeomorphSphere`). With coefficients `M` in any abelian category
with coproducts, its homology is `M` in degrees `0` and `3` and zero otherwise
(`TauCeti.singularHomologySpecialUnitaryGroupTwoIso`,
`TauCeti.isZero_singularHomology_specialUnitaryGroup_two`).

**`SU(3)`.** Evaluation on the first coordinate vector, `A ↦ A e₀`, is a locally trivial bundle
`SU(2) → SU(3) → S⁵` (`TauCeti.exists_trivialization_specialUnitarySphereMap`), hence a Serre
fibration (`TauCeti.specialUnitarySphereMap_mem_serreFibrations`) whose every fibre is homeomorphic
to `SU(2)`. Filter `SU(3)` by the preimages of the skeleta of the CW structure of `S⁵` with one
`0`-cell and one `5`-cell. The
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

* `TauCeti.singularHomologySpecialUnitaryGroupTwoIso`: `Hₖ(SU(2); M) ≅ M` for `k ∈ {0, 3}`.
* `TauCeti.singularHomologySpecialUnitaryGroupThreeIsoOfLt`: `Hₖ(SU(3); R) ≅ Hₖ(SU(2); R)` for
  `k < 4`.
* `TauCeti.singularHomologySpecialUnitaryGroupThreeAddFiveIso`:
  `Hq+5(SU(3); R) ≅ Hq(SU(2); R)`.
* `TauCeti.singularHomologySpecialUnitaryGroupThreeIso`: `Hₖ(SU(3); R) ≅ R` for
  `k ∈ {0, 3, 5, 8}`.

## Main results

* `TauCeti.isZero_singularHomology_specialUnitaryGroup_two`: `Hₖ(SU(2); M) = 0` for
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

universe u v

/-! ### `SU(2)` -/

section SpecialUnitaryTwo

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (M : C)

/-- The quaternions have real dimension `3 + 1`. -/
private lemma finrank_quaternion : finrank ℝ ℍ[ℝ] = 3 + 1 :=
  Quaternion.finrank_eq_four

/-- **The homology of `SU(2)` vanishes outside degrees `0` and `3`**, with any coefficients. -/
theorem isZero_singularHomology_specialUnitaryGroup_two {k : ℕ} (h₀ : k ≠ 0) (h₃ : k ≠ 3) :
    IsZero (((singularHomologyFunctor C k).obj M).obj
      (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ))) :=
  specialUnitaryGroupTwoHomeomorphSphere.toHomotopyEquiv.isZero_singularHomology_of_sphere_of_ne
    M finrank_quaternion h₀ h₃

/-- **The homology of `SU(2)` in degrees `0` and `3`**: `Hₖ(SU(2); M) ≅ M` for `k ∈ {0, 3}`. In
degree `0` this is the augmentation, `SU(2)` being path connected; in degree `3` it is the top
homology of the three-sphere. -/
def singularHomologySpecialUnitaryGroupTwoIso {k : ℕ} (hk : k = 0 ∨ k = 3) :
    ((singularHomologyFunctor C k).obj M).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)) ≅ M :=
  if h : k = 0 then
    eqToIso (by rw [h]) ≪≫
      asIso ((_root_.TopCat.of (specialUnitaryGroup (Fin 2) ℂ)).singularHomology₀ε M)
  else
    eqToIso (by rw [hk.resolve_left h]) ≪≫
      specialUnitaryGroupTwoHomeomorphSphere.toHomotopyEquiv.singularHomologySphereIso M
        finrank_quaternion (by norm_num)

end SpecialUnitaryTwo

variable (R : Type) [Ring R]

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

/-- `fiveSphereProj` evaluates `A ↦ A e₀` and reads the result on the five-sphere of `ℝ⁶`. -/
private lemma fiveSphereProj_apply (A : specialUnitaryGroup (Fin (1 + 2)) ℂ) :
    fiveSphereProj A = fiveSphereHomeomorph (specialUnitarySphereMap 2 A) :=
  rfl

private lemma serreFibrations_fiveSphereProj : TopCat.serreFibrations fiveSphereProj :=
  MorphismProperty.RespectsIso.postcomp TopCat.serreFibrations _ _
    (specialUnitarySphereMap_mem_serreFibrations (𝕜 := ℂ) (n := 2))

/-- Every fibre of `SU(3) → S⁵` is homeomorphic to `SU(2)`, through a local trivialization of
the bundle around the corresponding point of the sphere of `ℂ³`. -/
private def fiveSphereProjFiberHomeomorph (b : FiveSphere) :
    specialUnitaryGroup (Fin 2) ℂ ≃ₜ
      (fiveSphereProj ⁻¹' {b} : Set (specialUnitaryGroup (Fin (1 + 2)) ℂ)) :=
  let h := exists_trivialization_specialUnitarySphereMap (𝕜 := ℂ) (n := 2)
    (fiveSphereHomeomorph.symm b)
  (h.choose.preimageSingletonHomeomorph h.choose_spec).symm.trans (Homeomorph.setCongr (by
    ext B
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [fiveSphereProj_apply]
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
  -- `SU(3)` is `SU(1 + 2)`, the total space of the bundle, as `1 + 2` reduces to `3`.
  (@asIso _ _ _ _ _ (TopCat.isIso_singularHomologyMap_fiberι R serreFibrations_fiveSphereProj
    (b := spherePolePoint card_fin_six) (n := 4) (fun j hj ↦
      subsingleton_homotopyGroup_sphere_of_lt (n := 5) finrank_euclideanSpace_fin
        (by simpa using Nat.lt_succ_of_le hj) _) hk)).symm ≪≫
    singularHomologyFiveSphereProjFiberIso R _ k

/-- **`H₄(SU(3); R) = 0`**: both `H₄` of a fibre of `SU(3) → S⁵` and `H₄` of `SU(3)` modulo that
fibre vanish. -/
theorem isZero_singularHomology_specialUnitaryGroup_three_four :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) 4).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ))) := by
  -- `SU(3)` is `SU(1 + 2)`, the total space of the bundle, as `1 + 2` reduces to `3`.
  change IsZero (((singularHomologyFunctor (ModuleCat.{0} R) 4).obj (ModuleCat.of R R)).obj
    (_root_.TopCat.of (specialUnitaryGroup (Fin (1 + 2)) ℂ)))
  have hF := (isZero_singularHomology_specialUnitaryGroup_two (ModuleCat.of R R)
    (k := 4) (by omega) (by omega)).of_iso (singularHomologyFiveSphereProjFiberIso R
      (spherePolePoint card_fin_six) 4)
  rw [singularHomologyFunctor_obj_obj_eq_toSSet_homology] at hF ⊢
  exact TopPair.isZero_singularHomology_fst_of_isZero
    (TopPair.ofSubset (fiveSphereProj ⁻¹' {spherePolePoint card_fin_six})) (ModuleCat.of R R) hF
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
  -- `SU(3)` is `SU(1 + 2)`, the total space of the bundle, as `1 + 2` reduces to `3`.
  TopCat.singularHomologySphereFibrationIsoOfIsZero card_fin_six serreFibrations_fiveSphereProj R
      (by omega) (m := q + 4) (by omega)
      ((isZero_singularHomology_specialUnitaryGroup_two (ModuleCat.of R R) (by omega)
        (by omega)).of_iso (singularHomologyFiveSphereProjFiberIso R _ _))
      ((isZero_singularHomology_specialUnitaryGroup_two (ModuleCat.of R R) (by omega)
        (by omega)).of_iso (singularHomologyFiveSphereProjFiberIso R _ _)) ≪≫
    singularHomologyFiveSphereProjFiberIso R _ q

/-- **The homology of `SU(3)` vanishes outside degrees `0`, `3`, `5` and `8`**, with coefficients
in any ring. -/
theorem isZero_singularHomology_specialUnitaryGroup_three {k : ℕ} (h₀ : k ≠ 0) (h₃ : k ≠ 3)
    (h₅ : k ≠ 5) (h₈ : k ≠ 8) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ))) := by
  rcases lt_trichotomy k 4 with hk | rfl | hk
  · exact (isZero_singularHomology_specialUnitaryGroup_two (ModuleCat.of R R) h₀ h₃).of_iso
      (singularHomologySpecialUnitaryGroupThreeIsoOfLt R hk)
  · exact isZero_singularHomology_specialUnitaryGroup_three_four R
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 5 := ⟨k - 5, by omega⟩
    exact (isZero_singularHomology_specialUnitaryGroup_two (ModuleCat.of R R) (by omega)
      (by omega)).of_iso (singularHomologySpecialUnitaryGroupThreeAddFiveIso R q)

/-- **The homology of `SU(3)` in degrees `0`, `3`, `5` and `8`**: `Hₖ(SU(3); R) ≅ R` for
`k ∈ {0, 3, 5, 8}`. In degrees `0` and `3` it comes from a fibre `SU(2)` of `SU(3) → S⁵`; in
degrees `5` and `8` it is the homology of `SU(2)` in degrees `0` and `3` shifted by the top cell of
`S⁵`. -/
def singularHomologySpecialUnitaryGroupThreeIso {k : ℕ} (hk : k = 0 ∨ k = 3 ∨ k = 5 ∨ k = 8) :
    ((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ)) ≅ ModuleCat.of R R :=
  if h : k < 4 then
    singularHomologySpecialUnitaryGroupThreeIsoOfLt R h ≪≫
      singularHomologySpecialUnitaryGroupTwoIso (ModuleCat.of R R) (by omega)
  else
    eqToIso (congrArg (fun j ↦ ((singularHomologyFunctor (ModuleCat.{0} R) j).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (specialUnitaryGroup (Fin 3) ℂ)))
      (by omega : k = k - 5 + 5)) ≪≫
      singularHomologySpecialUnitaryGroupThreeAddFiveIso R (k - 5) ≪≫
      singularHomologySpecialUnitaryGroupTwoIso (ModuleCat.of R R) (by omega)

end TauCeti
