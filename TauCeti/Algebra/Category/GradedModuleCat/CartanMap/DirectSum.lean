/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic

/-!
# Grothendieck classes of finite direct sums of graded modules

In the Laurent Grothendieck groups `K₀^gr(proj A)` and `G₀^gr(mod A)`, the class of a finite
coproduct (in particular, a degreewise direct sum `TauCeti.GradedModuleCat.directSumObj` over a
finite index type) is the sum of the classes of its summands, and the class of any graded module
with trivial underlying carrier vanishes.

Stating the coproduct additivity for an arbitrary colimit cofan in `TauCeti.GradedModuleCat`
allows the finite index type `J` to live in an arbitrary universe without forcing `max uJ uA = uA`
in the statement; `TauCeti.GradedModuleCat.coproductCofanIsColimit` supplies the colimit witness
whenever `directSumObj` lives in `GradedModuleCat.{uA} 𝒜`.

## Main results

* `TauCeti.laurentK0_of_eq_zero_of_subsingleton` and
  `TauCeti.laurentK0_projective_of_eq_zero_of_subsingleton`: a finite graded (projective) module
  with subsingleton carrier has class `0`.
* `TauCeti.laurentK0_of_isColimit_cofan` and `TauCeti.laurentK0_projective_of_isColimit_cofan`:
  the class of the vertex of a finite colimit cofan is the sum of the classes of its summands.

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

/-- A finite graded module whose underlying carrier is a subsingleton has class `0` in
`G₀^gr(mod A)`. -/
@[simp]
theorem laurentK0_of_eq_zero_of_subsingleton
    (M : (gradedFiniteModules 𝒜).FullSubcategory) [Subsingleton M.obj] :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M = 0 := by
  have hM : IsZero M := (IsZero.iff_id_eq_zero M).2 <|
    ObjectProperty.hom_ext _ <| GradedModuleCat.hom_ext <|
      LinearMap.ext fun _ => Subsingleton.elim _ _
  rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hM, map_zero]

/-- A finite graded projective module whose underlying carrier is a subsingleton has class `0` in
`K₀^gr(proj A)`. -/
@[simp]
theorem laurentK0_projective_of_eq_zero_of_subsingleton
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) [Subsingleton P.obj] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P = 0 := by
  have hP : IsZero P := (IsZero.iff_id_eq_zero P).2 <|
    ObjectProperty.hom_ext _ <| GradedModuleCat.hom_ext <|
      LinearMap.ext fun _ => Subsingleton.elim _ _
  rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hP, map_zero]

section Cofan

private theorem exactK0_of_biproduct_fin_aux
    {P : ObjectProperty (GradedModuleCat.{uA} 𝒜)}
    [ObjectProperty.EssentiallySmall.{uA} P] [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]
    (hP : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.IsExtensionClosed P) :
    ∀ (n : ℕ) (M : Fin n → P.FullSubcategory) (N : P.FullSubcategory)
      {c : Cofan fun i : Fin n => (M i).obj} (_ : IsColimit c) (_ : c.pt = N.obj),
      (ExactK0.of.{uA} N : ExactK0.{uA}
        ((gradedModuleCanonicalExactStructure 𝒜).toExactStructure.fullSubcategory P hP)) =
        ∑ i : Fin n, ExactK0.of.{uA} (M i)
  | 0, M, N, c, hc, hpt => by
    let _ : ∀ {I : Type} [Fintype I] (F : I → GradedModuleCat.{uA} 𝒜), HasBiproduct F :=
      fun F => HasBiproduct.of_hasCoproduct F
    have hzero : IsZero (⨁ fun i : Fin 0 => (M i).obj) :=
      (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i => Fin.elim0 i)
    let isoN : N.obj ≅ ⨁ fun i : Fin 0 => (M i).obj :=
      eqToIso hpt.symm ≪≫ hc.coconePointUniqueUpToIso (biproduct.isColimit _)
    have hN : IsZero N := (IsZero.iff_id_eq_zero N).2 <| ObjectProperty.hom_ext _ <|
      ((IsZero.iff_id_eq_zero N.obj).1 (hzero.of_iso isoN))
    rw [ExactK0.of_eq_zero_of_isZero.{uA} hN, Finset.univ_eq_empty, Finset.sum_empty]
  | n + 1, M, N, c, hc, hpt => by
    let _ : ∀ {I : Type} [Fintype I] (F : I → GradedModuleCat.{uA} 𝒜), HasBiproduct F :=
      fun F => HasBiproduct.of_hasCoproduct F
    let tailObj : GradedModuleCat.{uA} 𝒜 := ⨁ fun i : Fin n => (M i.succ).obj
    have htail : P tailObj := by
      clear N c hc hpt
      induction n with
      | zero =>
        exact P.prop_of_isZero
          ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i => Fin.elim0 i))
      | succ m ih =>
        let eOpt : (⨁ fun i : Fin (m + 1) => (M i.succ).obj) ≅
            (M (Fin.succ 0)).obj ⊞ (⨁ fun i : Fin m => (M i.succ.succ).obj) :=
          (biproduct.whiskerEquiv (finSuccEquiv m).symm fun _ => Iso.refl _).symm ≪≫
            biproductOptionIso fun o => (M (((finSuccEquiv m).symm o).succ)).obj
        exact P.prop_of_iso eOpt.symm (P.prop_biprod_of_isClosedUnderBinaryProducts
          (M (Fin.succ 0)).property (ih fun i => M i.succ))
    let isoN : N.obj ≅ ⨁ fun i : Fin (n + 1) => (M i).obj :=
      eqToIso hpt.symm ≪≫ hc.coconePointUniqueUpToIso (biproduct.isColimit _)
    let eStep : N.obj ≅ (M 0).obj ⊞ tailObj :=
      isoN ≪≫ (biproduct.whiskerEquiv (finSuccEquiv n).symm fun _ => Iso.refl _).symm ≪≫
        biproductOptionIso fun o => (M ((finSuccEquiv n).symm o)).obj
    have hbiprod := ExactK0.of_biprod_fullSubcategory.{uA} hP (M 0).property htail
    rw [ExactK0.of_congr.{uA} (P.isoMk
        (Y := ⟨(M 0).obj ⊞ tailObj,
          P.prop_biprod_of_isClosedUnderBinaryProducts (M 0).property htail⟩) eStep),
      hbiprod,
      exactK0_of_biproduct_fin_aux hP n (fun i => M i.succ) ⟨tailObj, htail⟩
        (biproduct.isColimit _) rfl,
      Fin.sum_univ_succ]

private theorem laurentK0_of_isColimit_cofan_aux
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
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let cFin : Cofan fun i : Fin (Fintype.card J) => (M (e i)).obj :=
    Cofan.mk c.pt fun i => c.inj (e i)
  have hcFin : IsColimit cFin := by
    refine IsColimit.ofIsoColimit ?_ (Cocone.ext (Iso.refl _) (by simp [cFin]))
    exact (IsColimit.precomposeHomEquiv (Discrete.functorComp (fun j => (M j).obj) e) _).symm
      (IsColimit.whiskerEquivalence hc (Discrete.equivalence e))
  have hexact := exactK0_of_biproduct_fin_aux hP (Fintype.card J) (fun i => M (e i)) N hcFin hpt
  rw [← GradedExactStructure.fullSubcategory_toExactStructure
    (E := gradedModuleCanonicalExactStructure 𝒜) (P := P) hP hshift] at hexact
  have hlaurent := congrArg
    (LaurentK0.ofExactK0.{uA}
      ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory P hP hshift)) hexact
  simp only [map_sum, LaurentK0.ofExactK0_exactK0_of] at hlaurent
  exact hlaurent.trans (e.sum_comp fun j => LaurentK0.of.{uA} _ (M j))

/-- **The class of a finite coproduct in `G₀^gr(mod A)` is the sum of the classes of its
summands.** -/
theorem laurentK0_of_isColimit_cofan {J : Type uJ} [Fintype J]
    (M : J → (gradedFiniteModules 𝒜).FullSubcategory)
    (N : (gradedFiniteModules 𝒜).FullSubcategory)
    {c : Cofan fun j => (M j).obj} (hc : IsColimit c) (hpt : c.pt = N.obj) :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) N =
      ∑ j, LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j) :=
  laurentK0_of_isColimit_cofan_aux (𝒜 := 𝒜)
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
  laurentK0_of_isColimit_cofan_aux (𝒜 := 𝒜)
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift P N hc hpt

end Cofan

end TauCeti
