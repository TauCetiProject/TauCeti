/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Dimension
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mirror
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.Algebra.Homology.ShortComplex.Splitting
import TauCeti.Algebra.Module.Injective.DivisionRing

/-!
# Duality of Khovanov homology under mirroring

The normalized Khovanov complex of the mirror `D.mirror` of a planar oriented code `D` in quantum
degree `j` is the dual `Hom(C(D)_{-j}, R)` of the Khovanov complex of `D` in quantum degree `-j`
(`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`). The universal coefficient sequence of a dual
complex (`TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic`) turns this into statements
about Khovanov homology. The Kronecker map

`Khⁱʲ(D.mirror; R) →ₗ[R] (Kh^{-i,-j}(D; R) ⟶ R)`

evaluates a class of the mirror on classes of `D` through the Frobenius pairing of complementary
states (`TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`).

* Over a self-injective coefficient ring, for instance a field, it is an isomorphism:
  `Khⁱʲ(D.mirror; R)` is the dual of `Kh^{-i,-j}(D; R)`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual`), giving equality of Betti
  numbers over any field (`TauCeti.OrientedPDCode.finrank_khovanovHomology_mirror`).
* Over a hereditary coefficient ring, for instance `ℤ`, it is split surjective with kernel
  `Ext¹(Kh^{1-i,-j}(D; R), R)`: the sequence

  `0 ⟶ Ext¹(Kh^{1-i,-j}(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Hom(Kh^{-i,-j}(D; R), R) ⟶ 0`

  is split exact (`TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientShortComplex`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientSplitting`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientEquiv`). Over `ℤ`, the
  quotient `Hom(Kh^{-i,-j}(D), ℤ)` of `Khⁱʲ(D.mirror)` only sees the free part of
  `Kh^{-i,-j}(D)`, while the submodule `Ext¹(Kh^{1-i,-j}(D), ℤ)` only sees the torsion of
  `Kh^{1-i,-j}(D)`, which is one cochain degree higher.

## Main definitions and results

* `TauCeti.OrientedPDCode.khovanovHomologyMirrorIso`: cohomology isomorphism with the dual complex.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`: the Kronecker map of the mirror,
  characterized by `TauCeti.OrientedPDCode.homologyπ_khovanovHomologyMirrorKronecker`.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_bijective`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual`, and
  `TauCeti.OrientedPDCode.finrank_khovanovHomology_mirror`: duality over a self-injective ring and
  field Betti number symmetry.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology`, characterized by
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology_extClass_comp_mk₀`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology_injective`, and the exactness,
  surjectivity, splitting, and universal coefficient results for
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`:
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_surjective`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorKroneckerSection`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientEquiv`, and
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorUniversalCoefficientSplitting`: the split short
  exact sequence over a hereditary ring.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
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

/-- **Mirror Khovanov cohomology is the cohomology of the dual complex**: in bidegree `(i, j)`,
`Khⁱʲ(D.mirror; R)` is isomorphic to `Hⁱ(Hom_R(C(D; R)_{-j}, R[0]))` via
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`. -/
def khovanovHomologyMirrorIso (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≅
      (linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homology i :=
  (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
    (D.khovanovComplexMirrorIso hD R j hD')

@[simp]
lemma khovanovHomologyMirrorIso_hom (i j : ℤ) :
    (D.khovanovHomologyMirrorIso hD hD' R i j).hom =
      homologyMap (D.khovanovComplexMirrorIso hD R j hD').hom i := (rfl)

@[simp]
lemma khovanovHomologyMirrorIso_inv (i j : ℤ) :
    (D.khovanovHomologyMirrorIso hD hD' R i j).inv =
      homologyMap (D.khovanovComplexMirrorIso hD R j hD').inv i := (rfl)

/-- **The Kronecker map of the mirror**: Khovanov homology of the mirror `D.mirror` in bidegree
`(i, j)` maps to the linear forms on Khovanov homology of `D` in bidegree `(-i, -j)`. A cocycle
of the mirror complex is identified with a cocycle of the dual complex `Hom(C(D)_{-j}, R)` by
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`, which is a linear form on `C(D)^{-i}_{-j}`
vanishing on coboundaries; its restriction to cocycles descends to homology
(`TauCeti.OrientedPDCode.homologyπ_khovanovHomologyMirrorKronecker`). -/
def khovanovHomologyMirrorKronecker (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j →ₗ[R]
      (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :=
  linearHomComplexSingleKronecker R _ _ i ∘ₗ
    (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.toLinearMap

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
  simp [khovanovHomologyMirrorKronecker, moduleCat_homologyMap_homologyπ,
    moduleCat_iCycles_cyclesMap_apply, -linearHomComplex_X]

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

omit R [CommRing R] in
/-- **Mirror symmetry of Khovanov Betti numbers**: over any field `F`,
`finrank F Khⁱʲ(D.mirror; F) = finrank F Kh⁻ⁱ,⁻ʲ(D; F)`. -/
theorem finrank_khovanovHomology_mirror (F : Type u) [Field F] (i j : ℤ) :
    Module.finrank F (D.mirror.khovanovHomology hD' F i j) =
      Module.finrank F (D.khovanovHomology hD F (-i) (-j)) :=
  (D.khovanovHomologyMirrorEquivDual hD hD' F i j).finrank_eq.trans Subspace.dual_finrank_eq

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
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.symm.toLinearMap ∘ₗ
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
  refine (LinearEquiv.symm_apply_eq (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv).2
    ((linearHomComplexSingleExtToHomology_extClass_comp_mk₀ _ _ i β _ ?_).trans
      (moduleCat_homologyMap_homologyπ _ i z).symm)
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

/-- **Surjectivity in the mirror duality sequence**: over a hereditary coefficient ring every
linear form on `Kh^{-i,-j}(D; R)` is the evaluation of a class of `Khⁱʲ(D.mirror; R)`. -/
theorem khovanovHomologyMirrorKronecker_surjective (i j : ℤ) :
    Function.Surjective (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  rw [khovanovHomologyMirrorKronecker, LinearMap.coe_comp]
  exact (linearHomComplexSingleKronecker_surjective _ _ i).comp (LinearEquiv.surjective _)

/-- **A splitting section of `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`** over a
hereditary commutative ring. -/
def khovanovHomologyMirrorKroneckerSection (i j : ℤ) :
    (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) →ₗ[R]
      D.mirror.khovanovHomology hD' R i j :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.symm.toLinearMap ∘ₗ
    linearHomComplexSingleKroneckerSection R _ _ i

/-- **Characterization of `TauCeti.OrientedPDCode.khovanovHomologyMirrorKroneckerSection`**: a
linear form `g : Kh^{-i,-j}(D; R) ⟶ R` maps to the class of any mirror cocycle whose linear form
on `C(D)^{-i}_{-j}` under `TauCeti.OrientedPDCode.khovanovComplexMirrorIso` is
`retraction (iCycles (-i)) ≫ homologyπ (-i) ≫ g`. -/
lemma khovanovHomologyMirrorKroneckerSection_eq_homologyπ (i j : ℤ)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R)
    (z : (D.mirror.khovanovComplex hD' R j).cycles i)
    (hz : HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        ((D.khovanovComplexMirrorIso hD R j hD').hom.f i
          ((D.mirror.khovanovComplex hD' R j).iCycles i z)) =
      retraction ((D.khovanovComplex hD R (-j)).iCycles (-i)) ≫
        (D.khovanovComplex hD R (-j)).homologyπ (-i) ≫ g) :
    D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g =
      (D.mirror.khovanovComplex hD' R j).homologyπ i z := by
  refine (LinearEquiv.symm_apply_eq (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv).2
    ((linearHomComplexSingleKroneckerSection_apply i g _ ?_).trans
      (moduleCat_homologyMap_homologyπ _ i z).symm)
  rw [HomComplex.Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe,
    moduleCat_iCycles_cyclesMap_apply]
  exact hz

@[simp]
theorem khovanovHomologyMirrorKronecker_khovanovHomologyMirrorKroneckerSection (i j : ℤ)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :
    D.khovanovHomologyMirrorKronecker hD hD' R i j
        (D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g) = g := by
  simp only [khovanovHomologyMirrorKronecker, khovanovHomologyMirrorKroneckerSection,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection]

/-- **The mirror universal coefficient short complex** in `ModuleCat R`:
`Ext¹(Kh^{1-i,-j}(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ (Kh^{-i,-j}(D; R) ⟶ R)`. -/
@[expose]
def khovanovHomologyMirrorUniversalCoefficientShortComplex (i j : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (D.khovanovHomologyMirrorExtToHomology hD hD' R i j))
    (ModuleCat.ofHom (D.khovanovHomologyMirrorKronecker hD hD' R i j))
    (ModuleCat.hom_ext <| LinearMap.ext fun e ↦
      (D.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker hD hD' R i j
        ).apply_apply_eq_zero e)

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientShortComplex_X₁ (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).X₁ =
      ModuleCat.of R (Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1) :=
  (rfl)

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientShortComplex_X₂ (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).X₂ =
      D.mirror.khovanovHomology hD' R i j := (rfl)

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientShortComplex_X₃ (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).X₃ =
      ModuleCat.of R (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) := (rfl)

/-- The mirror universal coefficient sequence consists of `khovanovHomologyMirrorExtToHomology`
and `khovanovHomologyMirrorKronecker`. This constructor equation also identifies the dependent
carriers of its two maps. -/
lemma khovanovHomologyMirrorUniversalCoefficientShortComplex_def (i j : ℤ) :
    D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j =
      ShortComplex.mk
        (ModuleCat.ofHom (D.khovanovHomologyMirrorExtToHomology hD hD' R i j))
        (ModuleCat.ofHom (D.khovanovHomologyMirrorKronecker hD hD' R i j))
        (ModuleCat.hom_ext <| LinearMap.ext fun e ↦
          (D.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker hD hD' R i j
            ).apply_apply_eq_zero e) := (rfl)

/-- The inclusion of `khovanovHomologyMirrorUniversalCoefficientShortComplex` is
`khovanovHomologyMirrorExtToHomology`. -/
lemma khovanovHomologyMirrorUniversalCoefficientShortComplex_f (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).f =
      ModuleCat.ofHom (D.khovanovHomologyMirrorExtToHomology hD hD' R i j) :=
  (rfl)

/-- The projection of `khovanovHomologyMirrorUniversalCoefficientShortComplex` is
`khovanovHomologyMirrorKronecker`. -/
lemma khovanovHomologyMirrorUniversalCoefficientShortComplex_g (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).g =
      ModuleCat.ofHom (D.khovanovHomologyMirrorKronecker hD hD' R i j) :=
  (rfl)

/-- **Splitting of `khovanovHomologyMirrorUniversalCoefficientShortComplex`** in `ModuleCat R`. -/
def khovanovHomologyMirrorUniversalCoefficientSplitting (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (D.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker hD hD' R i j))
    (ModuleCat.ofHom (D.khovanovHomologyMirrorKroneckerSection hD hD' R i j))
    (ModuleCat.hom_ext <| LinearMap.ext
      (D.khovanovHomologyMirrorKronecker_khovanovHomologyMirrorKroneckerSection hD hD' R i j))
    ((ModuleCat.mono_iff_injective _).2
      (D.khovanovHomologyMirrorExtToHomology_injective hD hD' R i j))

/-- The section of `khovanovHomologyMirrorUniversalCoefficientSplitting` is
`khovanovHomologyMirrorKroneckerSection`. -/
lemma khovanovHomologyMirrorUniversalCoefficientSplitting_s (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientSplitting hD hD' R i j).s =
      ModuleCat.ofHom (D.khovanovHomologyMirrorKroneckerSection hD hD' R i j) :=
  ShortComplex.Splitting.ofExactOfSection_s _ _ _ _ _

/-- `khovanovHomologyMirrorUniversalCoefficientShortComplex` is short exact in `ModuleCat R`. -/
theorem khovanovHomologyMirrorUniversalCoefficientShortComplex_shortExact (i j : ℤ) :
    (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).ShortExact :=
  (D.khovanovHomologyMirrorUniversalCoefficientSplitting hD hD' R i j).shortExact

/-- **The universal coefficient decomposition for mirror Khovanov cohomology** over a hereditary
commutative ring:
`Khⁱʲ(D.mirror; R) ≃ₗ[R] Ext¹(Kh^{1-i,-j}(D; R), R) × (Kh^{-i,-j}(D; R) ⟶ R)`. -/
def khovanovHomologyMirrorUniversalCoefficientEquiv (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1 ×
        (D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :=
  ((D.khovanovHomologyMirrorUniversalCoefficientSplitting hD hD' R i j).isoBinaryBiproduct ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_symm_apply (i j : ℤ)
    (e : Ext.{u} (D.khovanovHomology hD R (1 - i) (-j)) (ModuleCat.of R R) 1)
    (g : D.khovanovHomology hD R (-i) (-j) ⟶ ModuleCat.of R R) :
    (D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j).symm (e, g) =
      D.khovanovHomologyMirrorExtToHomology hD hD' R i j e +
        D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g := by
  have hf : (D.khovanovHomologyMirrorUniversalCoefficientShortComplex hD hD' R i j).f e =
      D.khovanovHomologyMirrorExtToHomology hD hD' R i j e :=
    (ConcreteCategory.congr_hom
      (D.khovanovHomologyMirrorUniversalCoefficientShortComplex_f hD hD' R i j) e).trans
      (ModuleCat.ofHom_apply _ e)
  have hs : (D.khovanovHomologyMirrorUniversalCoefficientSplitting hD hD' R i j).s g =
      D.khovanovHomologyMirrorKroneckerSection hD hD' R i j g :=
    (ConcreteCategory.congr_hom
      (D.khovanovHomologyMirrorUniversalCoefficientSplitting_s hD hD' R i j) g).trans
      (ModuleCat.ofHom_apply _ g)
  exact ((D.khovanovHomologyMirrorUniversalCoefficientSplitting hD hD' R i j
    ).isoBinaryBiproduct_trans_biprodIsoProd_symm_apply e g).trans (congrArg₂ (· + ·) hf hs)

@[simp]
lemma khovanovHomologyMirrorUniversalCoefficientEquiv_apply_snd (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' R i j) :
    (D.khovanovHomologyMirrorUniversalCoefficientEquiv hD hD' R i j x).2 =
      D.khovanovHomologyMirrorKronecker hD hD' R i j x :=
  ((D.khovanovHomologyMirrorUniversalCoefficientSplitting hD hD' R i j
    ).isoBinaryBiproduct_trans_biprodIsoProd_apply_snd x).trans
    ((ConcreteCategory.congr_hom
      (D.khovanovHomologyMirrorUniversalCoefficientShortComplex_g hD hD' R i j) x).trans
      (ModuleCat.ofHom_apply _ x))

/-- Over a hereditary commutative ring, if `Kh^{1-i,-j}(D; R)` is projective,
`khovanovHomologyMirrorKronecker` gives an equivalence with the dual. -/
def khovanovHomologyMirrorEquivDualOfProjective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))] :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  (D.khovanovHomologyMirrorIso hD hD' R i j).toLinearEquiv.trans <|
    (linearHomComplexSingleKroneckerEquivOfProjectiveHomology R _ _ i).trans
      ModuleCat.homLinearEquiv

@[simp]
lemma khovanovHomologyMirrorEquivDualOfProjective_apply (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))]
    (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorEquivDualOfProjective hD hD' R i j x =
      (D.khovanovHomologyMirrorKronecker hD hD' R i j x).hom := by
  simp only [khovanovHomologyMirrorEquivDualOfProjective, khovanovHomologyMirrorKronecker,
    LinearEquiv.trans_apply, linearHomComplexSingleKroneckerEquivOfProjectiveHomology_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [ModuleCat.homLinearEquiv_apply, AddEquiv.toFun_eq_coe, ModuleCat.homAddEquiv_apply]

/-- Over a hereditary commutative ring, if `Kh^{1-i,-j}(D; R)` is projective and `Kh^{-i,-j}(D; R)`
vanishes, so does `Khⁱʲ(D.mirror; R)`. -/
theorem isZero_khovanovHomology_mirror_of_projective (i j : ℤ)
    [Module.Projective R (D.khovanovHomology hD R (1 - i) (-j))]
    (h0 : IsZero (D.khovanovHomology hD R (-i) (-j))) :
    IsZero (D.mirror.khovanovHomology hD' R i j) :=
  (isZero_homology_linearHomComplex_of_projective_homology (k := R)
    (K := D.khovanovComplex hD R (-j)) (Y := ModuleCat.of R R) i h0).of_iso
    (D.khovanovHomologyMirrorIso hD hD' R i j)

end Hereditary

end TauCeti.OrientedPDCode
