/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Dimension
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
public import TauCeti.Algebra.Homology.LinearHomComplex.Torsion
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mirror

/-!
# Duality of Khovanov homology under mirroring

The normalized Khovanov complex of the mirror `D.mirror` of a planar oriented code `D` in quantum
degree `j` is the dual `Hom(C(D)_{-j}, R)` of the Khovanov complex of `D` in quantum degree `-j`
(`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`, inducing
`TauCeti.OrientedPDCode.khovanovHomologyMirrorIso` on cohomology). The universal coefficient
sequence of a dual complex (`TauCeti.Algebra.Homology.LinearHomComplex.Single`) turns this into
statements about Khovanov homology. The Kronecker map

`Khⁱʲ(D.mirror; R) →ₗ[R] (Kh^{-i,-j}(D; R) ⟶ R)`

evaluates a class of the mirror on classes of `D` through the Frobenius pairing of complementary
states (`TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`).

* Over a self-injective coefficient ring, for instance a field, it is an isomorphism:
  `Khⁱʲ(D.mirror; R)` is the dual of `Kh^{-i,-j}(D; R)`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual`).
* Over a hereditary coefficient ring, for instance `ℤ` or any principal ideal domain, it is
  surjective with kernel `Ext¹(Kh^{1-i,-j}(D; R), R)`: the sequence

  `0 ⟶ Ext¹(Kh^{1-i,-j}(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Hom(Kh^{-i,-j}(D; R), R) ⟶ 0`

  is exact and splits non-canonically
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientEquiv`). When
  `Kh^{1-i,-j}(D; R)` is projective, `Ext¹` vanishes and the Kronecker map is an isomorphism
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDualOfProjective`).
* Over a principal ideal domain (in particular over `ℤ`), `Ext¹(Kh^{1-i,-j}(D; R), R)` is
  canonically the torsion submodule of `Khⁱʲ(D.mirror; R)`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorExtEquivTorsion`), the torsion-free quotient is
  canonically `Module.Dual R (Kh^{-i,-j}(D; R))`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorModTorsionEquivDual`), and `Khⁱʲ(D.mirror; R)` and
  `Kh^{-i,-j}(D; R)` have the same `Module.finrank`
  (`TauCeti.OrientedPDCode.finrank_khovanovHomology_mirror`).

## Main definitions and results

* `TauCeti.OrientedPDCode.khovanovHomologyMirrorIso`: cohomology isomorphism
  `Khⁱʲ(D.mirror; R) ≅ Hⁱ(Hom(C(D)_{-j}, R))`.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`: the Kronecker map of the mirror,
  characterized by `TauCeti.OrientedPDCode.homologyπ_khovanovHomologyMirrorKronecker`.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_bijective` and
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual`: duality over a self-injective ring.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology`, characterized by
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology_extClass_comp_mk₀`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology_injective`,
  `TauCeti.OrientedPDCode.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker`
  and `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_surjective`, together with
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientEquiv` and
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDualOfProjective`: the split short exact
  sequence and projective-bidegree duality over a hereditary ring.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtEquivTorsion`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorModTorsionEquivDual`, and
  `TauCeti.OrientedPDCode.finrank_khovanovHomology_mirror`: canonical torsion, mod-torsion, and
  free-rank duality over a principal ideal domain.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3,
  Proposition 32 and Corollary 11.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian CochainComplex

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  (hD' : D.mirror.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **Mirror Khovanov homology as cohomology of the dual complex.** Passing to cohomology in degree
`i` along `TauCeti.OrientedPDCode.khovanovComplexMirrorIso` identifies `Khⁱʲ(D.mirror; R)` with
`Hⁱ(Hom(C(D)_{-j}, R))`. -/
def khovanovHomologyMirrorIso (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≅
      (linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homology i :=
  (homologyFunctor _ _ i).mapIso (D.khovanovComplexMirrorIso hD R j hD')

/-- `khovanovHomologyMirrorIso.hom` maps the homology class of a mirror cocycle `z` to the homology
class of its image under `khovanovComplexMirrorIso.hom`. -/
@[simp]
lemma khovanovHomologyMirrorIso_hom_homologyπ (i j : ℤ)
    (z : (D.mirror.khovanovComplex hD' R j).cycles i) :
    (D.khovanovHomologyMirrorIso hD hD' R i j).hom
        ((D.mirror.khovanovComplex hD' R j).homologyπ i z) =
      (linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homologyπ i
        (cyclesMap (D.khovanovComplexMirrorIso hD R j hD').hom i z) :=
  moduleCat_homologyMap_homologyπ (D.khovanovComplexMirrorIso hD R j hD').hom i z

/-- `khovanovHomologyMirrorIso.inv` maps the homology class of a dual cocycle `φ` to the homology
class of its image under `khovanovComplexMirrorIso.inv`. -/
@[simp]
lemma khovanovHomologyMirrorIso_inv_homologyπ (i j : ℤ)
    (φ : (linearHomComplex R (D.khovanovComplex hD R (-j))
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).cycles i) :
    (D.khovanovHomologyMirrorIso hD hD' R i j).inv
        ((linearHomComplex R (D.khovanovComplex hD R (-j))
          ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homologyπ i φ) =
      (D.mirror.khovanovComplex hD' R j).homologyπ i
        (cyclesMap (D.khovanovComplexMirrorIso hD R j hD').inv i φ) :=
  moduleCat_homologyMap_homologyπ (D.khovanovComplexMirrorIso hD R j hD').inv i φ

/-- Khovanov homology of the mirror is the cohomology of the dual of the Khovanov complex of `D`,
through `TauCeti.OrientedPDCode.khovanovHomologyMirrorIso`. -/
private def mirrorHomologyEquiv (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      (linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homology i :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv

/-- **The Kronecker map of the mirror**: Khovanov homology of the mirror `D.mirror` in bidegree
`(i, j)` maps to the linear forms on Khovanov homology of `D` in bidegree `(-i, -j)`. A cocycle
of the mirror complex is identified with a cocycle of the dual complex `Hom(C(D)_{-j}, R)` by
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`, which is a linear form on `C(D)^{-i}_{-j}`
vanishing on coboundaries; its restriction to cocycles descends to homology
(`TauCeti.OrientedPDCode.homologyπ_khovanovHomologyMirrorKronecker`). -/
def khovanovHomologyMirrorKronecker (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j →ₗ[R]
      (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :=
  linearHomComplexSingleKronecker R _ _ i ∘ₗ (mirrorHomologyEquiv D hD hD' R i j).toLinearMap

/-- **The Kronecker map of the mirror on classes**: the class of a cocycle `z` of the mirror
complex evaluates on the class of a cocycle of `D` of degree `-i` as the linear form
`C(D)^{-i}_{-j} ⟶ R` underlying the image of `z` under the mirror isomorphism, which
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso_hom_f_apply` computes by the Frobenius pairing of
complementary states. -/
@[reassoc (attr := simp)]
lemma homologyπ_khovanovHomologyMirrorKronecker (i j : ℤ)
    (z : (D.mirror.khovanovComplex hD' R j).cycles i) :
    (D.khovanovComplex hD R (-j)).homologyπ (-i) ≫
        D.khovanovHomologyMirrorKronecker hD hD' R i j
          ((D.mirror.khovanovComplex hD' R j).homologyπ i z) =
      (D.khovanovComplex hD R (-j)).iCycles (-i) ≫
        HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
          ((D.khovanovComplexMirrorIso hD R j hD').hom.f i
            ((D.mirror.khovanovComplex hD' R j).iCycles i z)) := by
  simp [khovanovHomologyMirrorKronecker, mirrorHomologyEquiv, khovanovHomologyMirrorIso,
    moduleCat_homologyMap_homologyπ, moduleCat_iCycles_cyclesMap_apply, -linearHomComplex_X]

section Injective

variable [Module.Injective R R]

/-- **Duality of Khovanov homology under mirroring** over a self-injective coefficient ring, for
instance a field: the Kronecker map `Khⁱʲ(D.mirror; R) →ₗ[R] (Kh^{-i,-j}(D; R) ⟶ R)` is
bijective. -/
theorem khovanovHomologyMirrorKronecker_bijective (i j : ℤ) :
    Function.Bijective (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  have := Module.injective_object_of_injective_module R R
  rw [khovanovHomologyMirrorKronecker, LinearMap.coe_comp]
  exact (linearHomComplexSingleKronecker_bijective _ _ i).comp (LinearEquiv.bijective _)

/-- **Khovanov homology of the mirror is the dual of Khovanov homology** over a self-injective
coefficient ring `R`, for instance a field (`Module.injective_of_isSemisimpleRing`):
`Khⁱʲ(D.mirror; R) ≃ₗ[R] Hom(Kh^{-i,-j}(D; R), R)`, given by the Kronecker map
`TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`. -/
def khovanovHomologyMirrorEquivDual (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R] Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  (LinearEquiv.ofBijective _ (D.khovanovHomologyMirrorKronecker_bijective hD hD' R i j)).trans
    ModuleCat.homLinearEquiv

/-- The duality `TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual` is the Kronecker map,
read as a linear form. -/
@[simp]
lemma khovanovHomologyMirrorEquivDual_apply (i j : ℤ) (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorEquivDual hD hD' R i j x =
      (D.khovanovHomologyMirrorKronecker hD hD' R i j x).hom :=
  (rfl)

end Injective

section Hereditary

variable [∀ V : ModuleCat.{u} R, HasProjectiveDimensionLE V 1]

/-- **The `Ext` term of the mirror duality sequence** over a hereditary coefficient ring `R`, for
instance `ℤ` or any principal ideal domain: the `R`-linear map
`Ext¹(Kh^{1-i,-j}(D; R), R) →ₗ[R] Khⁱʲ(D.mirror; R)`. It is the `Ext¹` term of the universal
coefficient sequence of the dual complex (`CochainComplex.linearHomComplexSingleExtToHomology`)
transported along the mirror isomorphism `TauCeti.OrientedPDCode.khovanovComplexMirrorIso`. -/
def khovanovHomologyMirrorExtToHomology (i j : ℤ) :
    Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1 →ₗ[R]
      D.mirror.khovanovHomology hD' R i j :=
  (mirrorHomologyEquiv D hD hD' R i j).symm.toLinearMap ∘ₗ
    linearHomComplexSingleExtToHomology R _ _ i

/-- **The characterization of `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology`**: the
class in `Ext¹(Kh^{1-i,-j}(D; R), R)` of a linear form `β` on the coboundaries of `C(D)_{-j}` in
cochain degree `1 - i` goes to the class of a cocycle `z` of the mirror complex whose linear form
on `C(D)^{-i}_{-j}`, under the mirror isomorphism
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`, is the differential followed by `β`. -/
lemma khovanovHomologyMirrorExtToHomology_extClass_comp_mk₀ (i j : ℤ)
    (β : kernel ((D.khovanovComplex hD R (-j)).homologyπ (1 - i)) ⟶ ModuleCat.of R R)
    (z : (D.mirror.khovanovComplex hD' R j).cycles i)
    (hz : HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        ((D.khovanovComplexMirrorIso hD R j hD').hom.f i
          ((D.mirror.khovanovComplex hD' R j).iCycles i z)) =
      (D.khovanovComplex hD R (-j)).toBoundaries (-i) (1 - i) ≫ β) :
    D.khovanovHomologyMirrorExtToHomology hD hD' R i j
        ((TauCeti.kernelSequence_shortExact
          ((D.khovanovComplex hD R (-j)).homologyπ (1 - i))).extClass.comp (Ext.mk₀ β)
          (add_zero 1)) =
      (D.mirror.khovanovComplex hD' R j).homologyπ i z := by
  refine (LinearEquiv.symm_apply_eq (mirrorHomologyEquiv D hD hD' R i j)).2
    ((linearHomComplexSingleExtToHomology_extClass_comp_mk₀ _ _ i β _ ?_).trans
      (khovanovHomologyMirrorIso_hom_homologyπ D hD hD' R i j z).symm)
  rw [moduleCat_iCycles_cyclesMap_apply, hz]

/-- **Injectivity in the mirror duality sequence**: over a hereditary coefficient ring the map
`Ext¹(Kh^{1-i,-j}(D; R), R) →ₗ[R] Khⁱʲ(D.mirror; R)` is injective. -/
theorem khovanovHomologyMirrorExtToHomology_injective (i j : ℤ) :
    Function.Injective (D.khovanovHomologyMirrorExtToHomology hD hD' R i j) := by
  rw [khovanovHomologyMirrorExtToHomology, LinearMap.coe_comp]
  exact (LinearEquiv.injective _).comp (linearHomComplexSingleExtToHomology_injective _ _ i)

/-- **Exactness in the middle of the mirror duality sequence**: over a hereditary coefficient
ring, a class in `Khⁱʲ(D.mirror; R)` evaluates to zero on `Kh^{-i,-j}(D; R)` exactly when it comes
from `Ext¹(Kh^{1-i,-j}(D; R), R)`. -/
theorem exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker (i j : ℤ) :
    Function.Exact (D.khovanovHomologyMirrorExtToHomology hD hD' R i j)
      (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  rw [khovanovHomologyMirrorExtToHomology, khovanovHomologyMirrorKronecker,
    LinearEquiv.conj_symm_exact_iff_exact]
  exact exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker _ _ i

/-- `khovanovHomologyMirrorKronecker` vanishes on the image of
`khovanovHomologyMirrorExtToHomology`. -/
@[simp]
lemma khovanovHomologyMirrorKronecker_khovanovHomologyMirrorExtToHomology (i j : ℤ)
    (e : Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) :
    D.khovanovHomologyMirrorKronecker hD hD' R i j
        (D.khovanovHomologyMirrorExtToHomology hD hD' R i j e) = 0 :=
  (D.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker hD hD' R i
    j).apply_apply_eq_zero e

/-- Over a hereditary coefficient ring, a chosen `R`-linear section of
`khovanovHomologyMirrorKronecker`, extending a morphism `Kh^{-i,-j}(D; R) ⟶ R` along a cycle
retraction of `C(D)_{-j}` in degree `-i`
(`TauCeti.OrientedPDCode.khovanovHomologyMirrorKroneckerSection_apply`). -/
def khovanovHomologyMirrorKroneckerSection (i j : ℤ) :
    (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) →ₗ[R]
      D.mirror.khovanovHomology hD' R i j :=
  (mirrorHomologyEquiv D hD hD' R i j).symm.toLinearMap ∘ₗ
    linearHomComplexSingleKroneckerSection R (D.khovanovComplex hD R (-j)) (ModuleCat.of R R) i

/-- `khovanovHomologyMirrorKroneckerSection` sends `g` to the class of any mirror cocycle `z` whose
underlying morphism on `C(D)^{-i}_{-j}` under `khovanovComplexMirrorIso` is
`retraction ((D.khovanovComplex hD R (-j)).iCycles (-i)) ≫ homologyπ (-i) ≫ g`. -/
lemma khovanovHomologyMirrorKroneckerSection_apply (i j : ℤ)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R)
    (z : (D.mirror.khovanovComplex hD' R j).cycles i)
    (hz : HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        ((D.khovanovComplexMirrorIso hD R j hD').hom.f i
          ((D.mirror.khovanovComplex hD' R j).iCycles i z)) =
      retraction ((D.khovanovComplex hD R (-j)).iCycles (-i)) ≫
        (D.khovanovComplex hD R (-j)).homologyπ (-i) ≫ g) :
    D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g =
      (D.mirror.khovanovComplex hD' R j).homologyπ i z := by
  refine (LinearEquiv.symm_apply_eq (mirrorHomologyEquiv D hD hD' R i j)).2
    ((linearHomComplexSingleKroneckerSection_apply _ _ i g _ ?_).trans
      (khovanovHomologyMirrorIso_hom_homologyπ D hD hD' R i j z).symm)
  rw [moduleCat_iCycles_cyclesMap_apply, hz]

@[simp]
lemma khovanovHomologyMirrorKronecker_khovanovHomologyMirrorKroneckerSection (i j : ℤ)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :
    D.khovanovHomologyMirrorKronecker hD hD' R i j
        (D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g) = g := by
  simp [khovanovHomologyMirrorKronecker, khovanovHomologyMirrorKroneckerSection]

/-- **Surjectivity in the mirror duality sequence**: over a hereditary coefficient ring every
linear form on `Kh^{-i,-j}(D; R)` is the evaluation of a class of `Khⁱʲ(D.mirror; R)`. -/
theorem khovanovHomologyMirrorKronecker_surjective (i j : ℤ) :
    Function.Surjective (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  rw [khovanovHomologyMirrorKronecker, LinearMap.coe_comp]
  exact (linearHomComplexSingleKronecker_surjective _ _ i).comp (LinearEquiv.surjective _)

/-- **Split universal coefficient decomposition for mirror Khovanov homology**: over a hereditary
coefficient ring `R`,
`Khⁱʲ(D.mirror; R) ≃ₗ[R] Ext¹(Kh^{1-i,-j}(D; R), R) × (Kh^{-i,-j}(D; R) ⟶ R)`. The splitting depends
on a chosen cycle retraction in `C(D)_{-j}`. -/
def khovanovHomologyMirrorUniversalCoefficientEquiv (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1 ×
        (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :=
  (mirrorHomologyEquiv D hD hD' R i j).trans
    (linearHomComplexSingleUniversalCoefficientEquiv.{u} R
      (D.khovanovComplex hD R (-j)) (ModuleCat.of R R) i)

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_symm_inl (i j : ℤ)
    (e : Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) :
    (D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j).symm (e, 0) =
      D.khovanovHomologyMirrorExtToHomology hD hD' R i j e := by
  simp [khovanovHomologyMirrorUniversalCoefficientEquiv, khovanovHomologyMirrorExtToHomology]

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_symm_inr (i j : ℤ)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :
    (D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j).symm (0, g) =
      D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g := by
  simp [khovanovHomologyMirrorUniversalCoefficientEquiv, khovanovHomologyMirrorKroneckerSection]

lemma khovanovHomologyMirrorUniversalCoefficientEquiv_symm_apply (i j : ℤ)
    (e : Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :
    (D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j).symm (e, g) =
      D.khovanovHomologyMirrorExtToHomology hD hD' R i j e +
        D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g := by
  have h : (e, g) = (e, 0) + (0, g) := by ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, khovanovHomologyMirrorUniversalCoefficientEquiv_symm_inl,
    khovanovHomologyMirrorUniversalCoefficientEquiv_symm_inr]

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_khovanovHomologyMirrorExtToHomology (i j : ℤ)
    (e : Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) :
    D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j
        (D.khovanovHomologyMirrorExtToHomology hD hD' R i j e) =
      (e, 0) := by
  rw [← khovanovHomologyMirrorUniversalCoefficientEquiv_symm_inl, LinearEquiv.apply_symm_apply]

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_khovanovHomologyMirrorKroneckerSection
    (i j : ℤ) (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :
    D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j
        (D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g) =
      (0, g) := by
  rw [← khovanovHomologyMirrorUniversalCoefficientEquiv_symm_inr, LinearEquiv.apply_symm_apply]

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_apply_snd (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' R i j) :
    (D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j x).2 =
      D.khovanovHomologyMirrorKronecker hD hD' R i j x := by
  simp [khovanovHomologyMirrorUniversalCoefficientEquiv, khovanovHomologyMirrorKronecker]

/-- Over a hereditary coefficient ring `R`, when `Kh^{1-i,-j}(D; R)` is projective, the mirror
Kronecker map `Khⁱʲ(D.mirror; R) →ₗ[R] (Kh^{-i,-j}(D; R) ⟶ R)` is bijective. -/
theorem khovanovHomologyMirrorKronecker_bijective_of_projective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))] :
    Function.Bijective (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  have : Projective (D.khovanovHomology hD R (1 - i) (-j)) :=
    ModuleCat.projective_of_categoryTheory_projective _
  rw [khovanovHomologyMirrorKronecker, LinearMap.coe_comp]
  exact (linearHomComplexSingleKronecker_bijective_of_projective_homology _ _ i).comp
    (LinearEquiv.bijective _)

/-- Over a hereditary coefficient ring `R`, when `Kh^{1-i,-j}(D; R)` is projective, the mirror
Kronecker map is a canonical `R`-linear equivalence
`Khⁱʲ(D.mirror; R) ≃ₗ[R] Module.Dual R (Kh^{-i,-j}(D; R))`. -/
def khovanovHomologyMirrorEquivDualOfProjective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))] :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  (LinearEquiv.ofBijective _
    (D.khovanovHomologyMirrorKronecker_bijective_of_projective hD hD' R i j)).trans
    ModuleCat.homLinearEquiv

@[simp]
lemma khovanovHomologyMirrorEquivDualOfProjective_apply (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))]
    (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorEquivDualOfProjective hD hD' R i j x =
      (D.khovanovHomologyMirrorKronecker hD hD' R i j x).hom :=
  (rfl)

/-- Over a hereditary coefficient ring `R`, if `Kh^{1-i,-j}(D; R)` is projective and
`Kh^{-i,-j}(D; R)` is zero, then `Khⁱʲ(D.mirror; R)` is zero. -/
theorem isZero_khovanovHomology_mirror_of_projective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))]
    (h : IsZero (D.khovanovHomology hD R (-i) (-j))) :
    IsZero (D.mirror.khovanovHomology hD' R i j) := by
  have : Projective (D.khovanovHomology hD R (1 - i) (-j)) :=
    ModuleCat.projective_of_categoryTheory_projective _
  exact (isZero_homology_linearHomComplex_single_of_projective_homology
    (k := R) _ (ModuleCat.of R R) i h).of_iso (D.khovanovHomologyMirrorIso hD hD' R i j)

end Hereditary

section PrincipalIdealDomain

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a principal ideal domain, the image of `khovanovHomologyMirrorExtToHomology` is the torsion
submodule of `Khⁱʲ(D.mirror; R)`. -/
@[simp]
theorem range_khovanovHomologyMirrorExtToHomology (i j : ℤ) :
    LinearMap.range (D.khovanovHomologyMirrorExtToHomology hD hD' R i j) =
      Submodule.torsion R (D.mirror.khovanovHomology hD' R i j) := by
  rw [khovanovHomologyMirrorExtToHomology, LinearMap.range_comp,
    range_linearHomComplexSingleExtToHomology_eq_torsion]
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, exists_eq_right,
    Submodule.mem_torsion_iff, Submonoid.smul_def, ← map_smul, LinearEquiv.map_eq_zero_iff]

/-- **Canonical torsion duality for mirror Khovanov homology.** Over a principal ideal domain (in
particular over `ℤ`), `Ext¹(Kh^{1-i,-j}(D; R), R)` is canonically `R`-linearly equivalent to the
torsion submodule of `Khⁱʲ(D.mirror; R)`, with no choice of cycle retraction. -/
def khovanovHomologyMirrorExtEquivTorsion (i j : ℤ) :
    Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1 ≃ₗ[R]
      Submodule.torsion R (D.mirror.khovanovHomology hD' R i j) :=
  (LinearEquiv.ofInjective (D.khovanovHomologyMirrorExtToHomology hD hD' R i j)
    (D.khovanovHomologyMirrorExtToHomology_injective hD hD' R i j)).trans
    (LinearEquiv.ofEq _ _ (D.range_khovanovHomologyMirrorExtToHomology hD hD' R i j))

@[simp]
lemma coe_khovanovHomologyMirrorExtEquivTorsion_apply (i j : ℤ)
    (e : Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) :
    (D.khovanovHomologyMirrorExtEquivTorsion hD hD' R i j e :
      D.mirror.khovanovHomology hD' R i j) =
      D.khovanovHomologyMirrorExtToHomology hD hD' R i j e := by
  simp [khovanovHomologyMirrorExtEquivTorsion]

/-- **Canonical torsion-free quotient duality for mirror Khovanov homology.** Over a principal ideal
domain, the quotient of `Khⁱʲ(D.mirror; R)` by its torsion submodule is canonically `R`-linearly
equivalent to `Module.Dual R (Kh^{-i,-j}(D; R))` via `khovanovHomologyMirrorKronecker`. -/
def khovanovHomologyMirrorModTorsionEquivDual (i j : ℤ) :
    (D.mirror.khovanovHomology hD' R i j ⧸
        Submodule.torsion R (D.mirror.khovanovHomology hD' R i j)) ≃ₗ[R]
      Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  have hker := (D.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker
    hD hD' R i j).linearMap_ker_eq
  ((Submodule.quotEquivOfEq _ _
    (hker.trans (D.range_khovanovHomologyMirrorExtToHomology hD hD' R i j)).symm).trans
    ((D.khovanovHomologyMirrorKronecker hD hD' R i j).quotKerEquivOfSurjective
      (D.khovanovHomologyMirrorKronecker_surjective hD hD' R i j))).trans
    ModuleCat.homLinearEquiv

@[simp]
lemma khovanovHomologyMirrorModTorsionEquivDual_mk (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorModTorsionEquivDual hD hD' R i j (Submodule.Quotient.mk x) =
      (D.khovanovHomologyMirrorKronecker hD hD' R i j x).hom := by
  simp [khovanovHomologyMirrorModTorsionEquivDual]
  rfl

/-- **Free-rank mirror symmetry of Khovanov homology.** Over any principal ideal domain `R` (in
particular over `ℤ` and over any field), `Khⁱʲ(D.mirror; R)` and `Kh^{-i,-j}(D; R)` have the same
`Module.finrank`. -/
theorem finrank_khovanovHomology_mirror (i j : ℤ) :
    Module.finrank R (D.mirror.khovanovHomology hD' R i j) =
      Module.finrank R (D.khovanovHomology hD R (-i) (-j)) :=
  (mirrorHomologyEquiv D hD hD' R i j).finrank_eq.trans
    ((D.khovanovComplex hD R (-j)).finrank_homology_linearHomComplex_single i)

end PrincipalIdealDomain

end TauCeti.OrientedPDCode
