/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Grothendieck classes of finite direct sums of graded modules

In the exact and Laurent Grothendieck groups of any shift-stable, extension-closed full subcategory
of `TauCeti.GradedModuleCat 𝒜` (in particular, `K₀^gr(proj A)` and `G₀^gr(mod A)`), the class of a
finite coproduct (such as a degreewise direct sum `TauCeti.GradedModuleCat.directSumObj` over a
finite index type) is the sum of the classes of its summands, and the class of any graded module
with trivial underlying carrier vanishes.

Stating the coproduct additivity for an arbitrary colimit cofan in `TauCeti.GradedModuleCat`
allows the finite index type `J` to live in an arbitrary universe without forcing `max uJ uA = uA`
in the statement; `TauCeti.GradedModuleCat.coproductCofanIsColimit` supplies the colimit witness
whenever `directSumObj` lives in `GradedModuleCat.{uA} 𝒜`.

## Main results

* `TauCeti.laurentK0_fullSubcategory_of_eq_zero_of_subsingleton`,
  `TauCeti.laurentK0_of_eq_zero_of_subsingleton`, and
  `TauCeti.laurentK0_projective_of_eq_zero_of_subsingleton`: a graded module in a shift-stable
  extension-closed full subcategory whose carrier is a subsingleton has class `0`.
* `TauCeti.exactK0_fullSubcategory_of_isColimit_cofan` and
  `TauCeti.laurentK0_fullSubcategory_of_isColimit_cofan`: the class of the vertex of a finite
  colimit cofan in an extension-closed (and shift-stable) full subcategory of `GradedModuleCat 𝒜` is
  the sum of the classes of its summands, with specializations
  `TauCeti.laurentK0_of_isColimit_cofan` and `TauCeti.laurentK0_projective_of_isColimit_cofan`.

## References

* C. A. Weibel, *The K-book*, Chapter II, Sections 6--7.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe uJ uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- In a shift-stable, extension-closed full subcategory of `GradedModuleCat 𝒜`, any object whose
underlying carrier is a subsingleton has class `0` in `LaurentK0`. -/
@[simp]
theorem laurentK0_fullSubcategory_of_eq_zero_of_subsingleton
    {P : ObjectProperty (GradedModuleCat.{uA} 𝒜)}
    [ObjectProperty.EssentiallySmall.{uA} P] [P.ContainsZero]
    [P.IsClosedUnderBinaryProducts]
    (hP : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage (gradedModuleCanonicalExactStructure 𝒜).shift.functor = P)
    (M : P.FullSubcategory) [Subsingleton M.obj] :
    LaurentK0.of.{uA} ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory P hP hshift) M =
      0 := by
  have hM : IsZero M := (IsZero.iff_id_eq_zero M).2 <|
    ObjectProperty.hom_ext _ <| GradedModuleCat.hom_ext <|
      LinearMap.ext fun _ => Subsingleton.elim _ _
  rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hM, map_zero]

/-- A finite graded module whose underlying carrier is a subsingleton has class `0` in
`G₀^gr(mod A)`. -/
@[simp]
theorem laurentK0_of_eq_zero_of_subsingleton
    (M : (gradedFiniteModules 𝒜).FullSubcategory) [Subsingleton M.obj] :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M = 0 :=
  laurentK0_fullSubcategory_of_eq_zero_of_subsingleton
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteModules_gradedAbelian_shift M

/-- A finite graded projective module whose underlying carrier is a subsingleton has class `0` in
`K₀^gr(proj A)`. -/
@[simp]
theorem laurentK0_projective_of_eq_zero_of_subsingleton
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) [Subsingleton P.obj] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P = 0 :=
  laurentK0_fullSubcategory_of_eq_zero_of_subsingleton
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift P

section Cofan

/-- **Finite-cofan additivity in `ExactK0` of an extension-closed full subcategory of graded
modules.** If `c` is a colimit cofan in `GradedModuleCat 𝒜` over a finite family `M` in `P` whose
cocone point is `N`, then `[N] = ∑ j, [M j]`. -/
theorem exactK0_fullSubcategory_of_isColimit_cofan
    {P : ObjectProperty (GradedModuleCat.{uA} 𝒜)}
    [ObjectProperty.EssentiallySmall.{uA} P] [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]
    (hP : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.IsExtensionClosed P)
    {J : Type uJ} [Fintype J]
    (M : J → P.FullSubcategory) (N : P.FullSubcategory)
    {c : Cofan fun j => (M j).obj} (hc : IsColimit c) (hpt : c.pt = N.obj) :
    (ExactK0.of.{uA} N : ExactK0.{uA}
        ((gradedModuleCanonicalExactStructure 𝒜).toExactStructure.fullSubcategory P hP)) =
      ∑ j, ExactK0.of.{uA} (M j) := by
  let _ : HasFiniteCoproducts (GradedModuleCat.{uA} 𝒜) := ⟨fun _ => inferInstance⟩
  let _ : HasFiniteBiproducts (GradedModuleCat.{uA} 𝒜) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let _ : HasFiniteProducts (GradedModuleCat.{uA} 𝒜) :=
    hasFiniteProducts_of_hasFiniteBiproducts (GradedModuleCat.{uA} 𝒜)
  let _ : P.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let f : Fin (Fintype.card J) → P.FullSubcategory := fun i => M (e i)
  let cFin : Cofan fun i : Fin (Fintype.card J) => (f i).obj :=
    Cofan.mk c.pt fun i => c.inj (e i)
  have hcFin : IsColimit cFin := by
    refine IsColimit.ofIsoColimit ?_ (Cocone.ext (Iso.refl _) (by simp [cFin, f]))
    exact (IsColimit.precomposeHomEquiv (Discrete.functorComp (fun j => (M j).obj) e) _).symm
      (IsColimit.whiskerEquivalence hc (Discrete.equivalence e))
  let isoC : N.obj ≅ ⨁ fun i => (f i).obj :=
    eqToIso hpt.symm ≪≫ hcFin.coconePointUniqueUpToIso (biproduct.isColimit _)
  let isoSub : N ≅ ⨁ f :=
    P.fullyFaithfulι.preimageIso (isoC ≪≫ (P.ι.mapBiproduct f).symm)
  rw [ExactK0.of_congr.{uA} isoSub, ← ExactK0.fromSplit_of.{uA},
    SplitK0.of_biproduct.{uA} f, map_sum]
  simp only [ExactK0.fromSplit_of, f]
  exact e.sum_comp fun j => ExactK0.of.{uA} (M j)

/-- **Finite-cofan additivity in `LaurentK0` of a shift-stable, extension-closed full subcategory
of graded modules.** If `c` is a colimit cofan in `GradedModuleCat 𝒜` over a finite family `M` in
`P` whose cocone point is `N`, then `[N] = ∑ j, [M j]`. -/
theorem laurentK0_fullSubcategory_of_isColimit_cofan
    {P : ObjectProperty (GradedModuleCat.{uA} 𝒜)}
    [ObjectProperty.EssentiallySmall.{uA} P] [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]
    (hP : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage (gradedModuleCanonicalExactStructure 𝒜).shift.functor = P)
    {J : Type uJ} [Fintype J]
    (M : J → P.FullSubcategory) (N : P.FullSubcategory)
    {c : Cofan fun j => (M j).obj} (hc : IsColimit c) (hpt : c.pt = N.obj) :
    LaurentK0.of.{uA} ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory P hP hshift) N =
      ∑ j, LaurentK0.of.{uA}
        ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory P hP hshift) (M j) := by
  have hexact := exactK0_fullSubcategory_of_isColimit_cofan hP M N hc hpt
  rw [← GradedExactStructure.fullSubcategory_toExactStructure
    (E := gradedModuleCanonicalExactStructure 𝒜) (P := P) hP hshift] at hexact
  have hlaurent := congrArg
    (LaurentK0.ofExactK0.{uA}
      ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory P hP hshift)) hexact
  simp only [map_sum, LaurentK0.ofExactK0_exactK0_of] at hlaurent
  exact hlaurent

/-- **The class of a finite coproduct in `G₀^gr(mod A)` is the sum of the classes of its
summands.** -/
theorem laurentK0_of_isColimit_cofan {J : Type uJ} [Fintype J]
    (M : J → (gradedFiniteModules 𝒜).FullSubcategory)
    (N : (gradedFiniteModules 𝒜).FullSubcategory)
    {c : Cofan fun j => (M j).obj} (hc : IsColimit c) (hpt : c.pt = N.obj) :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) N =
      ∑ j, LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j) :=
  laurentK0_fullSubcategory_of_isColimit_cofan (𝒜 := 𝒜)
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteModules_gradedAbelian_shift M N hc hpt

/-- **The class of a finite coproduct in `K₀^gr(proj A)` is the sum of the classes of its
summands.** -/
theorem laurentK0_projective_of_isColimit_cofan {J : Type uJ} [Fintype J]
    (P : J → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (N : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    {c : Cofan fun j => (P j).obj} (hc : IsColimit c) (hpt : c.pt = N.obj) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) N =
      ∑ j, LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P j) :=
  laurentK0_fullSubcategory_of_isColimit_cofan (𝒜 := 𝒜)
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift P N hc hpt

end Cofan

end TauCeti
