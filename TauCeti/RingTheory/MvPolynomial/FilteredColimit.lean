/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomials over filtered colimits of rings

A finite family of polynomials over a filtered ring colimit lifts to a common stage.
-/

public section

universe categoryObj categoryHom ringUniverse

open CategoryTheory Limits

namespace TauCeti.CommRingCat

variable {Index : Type categoryObj} [Category.{categoryHom} Index] [IsFiltered Index]
  (diagram : Index ⥤ CommRingCat.{ringUniverse}) (cocone : Cocone diagram)
  [PreservesColimit diagram (forget CommRingCat)] {indeterminates : Type*}

omit [IsFiltered Index] [PreservesColimit diagram (forget CommRingCat)] in
lemma range_map_ι_app_subset {sourceIndex targetIndex : Index}
    (transition : sourceIndex ⟶ targetIndex) :
    Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app sourceIndex).hom) ⊆
      Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app targetIndex).hom) := by
  have maps_comp : (cocone.ι.app targetIndex).hom.comp (diagram.map transition).hom =
      (cocone.ι.app sourceIndex).hom :=
    congrArg CommRingCat.Hom.hom (cocone.w transition)
  rintro _ ⟨p, rfl⟩
  exact ⟨MvPolynomial.map (diagram.map transition).hom p, by
    rw [MvPolynomial.map_map, maps_comp]⟩

variable (colimit : IsColimit cocone)

include colimit in
/-- Every polynomial over a filtered colimit of rings lifts to one stage. -/
lemma exists_mem_range_map_ι_app (p : MvPolynomial indeterminates cocone.pt) :
    ∃ stage, p ∈ Set.range (MvPolynomial.map (σ := indeterminates)
      (cocone.ι.app stage).hom) := by
  induction p using MvPolynomial.induction_on with
  | C coefficient =>
    -- Forgetting rings preserves the coefficient carrier and the cocone component map.
    let coefficient' : ((forget CommRingCat).mapCocone cocone).pt := coefficient
    obtain ⟨stage, lift, hlift⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget _) colimit) coefficient'
    change (cocone.ι.app stage).hom lift = coefficient at hlift
    exact ⟨stage, MvPolynomial.C lift, by
      rw [MvPolynomial.map_C]
      exact congrArg MvPolynomial.C hlift⟩
  | add p q hp hq =>
    obtain ⟨i, p, rfl⟩ := hp
    obtain ⟨j, q, rfl⟩ := hq
    obtain ⟨pᵢ, hpᵢ⟩ := range_map_ι_app_subset diagram cocone
      (IsFiltered.leftToMax i j) ⟨p, rfl⟩
    obtain ⟨qⱼ, hqⱼ⟩ := range_map_ι_app_subset diagram cocone
      (IsFiltered.rightToMax i j) ⟨q, rfl⟩
    exact ⟨IsFiltered.max i j, pᵢ + qⱼ, by
      rw [map_add]
      exact congrArg₂ (· + ·) hpᵢ hqⱼ⟩
  | mul_X p j polynomialLift =>
    obtain ⟨stage, p, rfl⟩ := polynomialLift
    exact ⟨stage, p * MvPolynomial.X j, by
      rw [map_mul]
      exact congrArg (MvPolynomial.map (cocone.ι.app stage).hom p * ·)
        (MvPolynomial.map_X _ _)⟩

include colimit in
/-- A finite set of polynomials over a filtered colimit lifts to a common stage. -/
lemma exists_forall_mem_range_map_ι_app
    (polynomials : Finset (MvPolynomial indeterminates cocone.pt)) :
    ∃ stage, ∀ p ∈ polynomials,
      p ∈ Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app stage).hom) := by
  classical
  choose j hlift using fun p : polynomials ↦
    exists_mem_range_map_ι_app diagram cocone colimit
      (p : MvPolynomial indeterminates cocone.pt)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  refine ⟨k, fun p membership ↦ ?_⟩
  obtain ⟨transition⟩ := hk
    (Finset.mem_image_of_mem j (Finset.mem_univ (⟨p, membership⟩ : polynomials)))
  exact range_map_ι_app_subset diagram cocone transition (hlift ⟨p, membership⟩)

end TauCeti.CommRingCat
