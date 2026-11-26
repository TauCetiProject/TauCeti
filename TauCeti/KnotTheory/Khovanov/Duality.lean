/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Dimension
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mirror

/-!
# Duality of Khovanov homology under mirroring

The normalized Khovanov complex of the mirror `D.mirror` of a planar oriented code `D` in quantum
degree `j` is the dual `Hom(C(D)_{-j}, R)` of the Khovanov complex of `D` in quantum degree `-j`
(`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`). The universal coefficient sequence of a dual
complex (`TauCeti.Algebra.Homology.LinearHomComplex.Single`) turns this into statements about
Khovanov homology. The Kronecker map

`Khⁱʲ(D.mirror; R) →ₗ[R] (Kh^{-i,-j}(D; R) ⟶ R)`

evaluates a class of the mirror on classes of `D` through the Frobenius pairing of complementary
states (`TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`).

* Over a self-injective coefficient ring, for instance a field, it is an isomorphism:
  `Khⁱʲ(D.mirror; R)` is the dual of `Kh^{-i,-j}(D; R)`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual`).
* Over a hereditary coefficient ring, for instance `ℤ`, it is surjective with kernel
  `Ext¹(Kh^{1-i,-j}(D; R), R)`: the sequence

  `0 ⟶ Ext¹(Kh^{1-i,-j}(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Hom(Kh^{-i,-j}(D; R), R) ⟶ 0`

  is exact. Over `ℤ`, the quotient `Hom(Kh^{-i,-j}(D), ℤ)` of `Khⁱʲ(D.mirror)` only sees the
  free part of `Kh^{-i,-j}(D)`, while the submodule `Ext¹(Kh^{1-i,-j}(D), ℤ)` only sees the
  torsion of `Kh^{1-i,-j}(D)`, which is one cochain degree higher.

## Main definitions and results

* `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`: the Kronecker map of the mirror,
  characterized by `TauCeti.OrientedPDCode.homologyπ_khovanovHomologyMirrorKronecker`.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_bijective` and
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorEquivDual`: duality over a self-injective ring.
* `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology`, characterized by
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology_extClass_comp_mk₀`,
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorExtToHomology_injective`,
  `TauCeti.OrientedPDCode.exact_khovanovHomologyMirrorExtToHomology_khovanovHomologyMirrorKronecker`
  and
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_surjective`: the short exact sequence over
  a hereditary ring.

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

/-- Khovanov homology of the mirror is the cohomology of the dual of the Khovanov complex of `D`,
through `TauCeti.OrientedPDCode.khovanovComplexMirrorIso`. -/
private def mirrorHomologyEquiv (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R]
      (linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).homology i :=
  ((homologyFunctor _ _ i).mapIso (D.khovanovComplexMirrorIso hD R j hD')).toLinearEquiv

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
  simp [khovanovHomologyMirrorKronecker, mirrorHomologyEquiv, moduleCat_homologyMap_homologyπ,
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

end Hereditary

end TauCeti.OrientedPDCode
