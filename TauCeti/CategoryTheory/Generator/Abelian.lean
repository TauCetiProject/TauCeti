/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import TauCeti.CategoryTheory.Abelian.ImageSubobject

/-!
# Epimorphisms out of coproducts of a separator

Let `G` be a separator of an abelian category and let `r : Z ⟶ P` be an epimorphism. For every
proper subobject `P'` of `P` there is a morphism `G ⟶ Z` whose composite with `r` does not
factor through `P'`. Choosing one such morphism for each subobject of `P` gives a morphism
`∐ G ⟶ Z` whose composite with `r` is still an epimorphism
(`IsSeparator.exists_epi_sigmaDesc_comp`). Hence the subobject of `Z` it generates maps onto `P`,
and its size is controlled by the subobjects of `P` alone, independently of `Z`.

The variant `IsSeparator.exists_epi_sigmaDesc_comp_of_le_imageSubobject` allows the target to be
a subobject of the image of a morphism `g : P ⟶ X`, still indexing the coproduct by subobjects
of `P`. This is the form used to bound the sizes of acyclic subcomplexes in Grothendieck abelian
categories.

## References

* [Stacks: Lemma 079J](https://stacks.math.columbia.edu/tag/079J)
-/

public section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {G : C}

/-- If `G` is a separator and `r : Z ⟶ P` is an epimorphism, then every proper subobject of `P`
misses the composite of `r` with some morphism `G ⟶ Z`. -/
lemma IsSeparator.exists_not_factors_comp (hG : IsSeparator G) {Z P : C} (r : Z ⟶ P) [Epi r]
    {P' : Subobject P} (hP' : P' ≠ ⊤) : ∃ φ : G ⟶ Z, ¬ P'.Factors (φ ≫ r) := by
  by_contra! h
  apply hP'
  have hr : r ≫ cokernel.π P'.arrow = 0 := hG.def _ _ fun φ ↦ by
    rw [comp_zero, ← Category.assoc, ← Subobject.factorThru_arrow _ _ (h φ), Category.assoc,
      cokernel.condition, comp_zero]
  have : Epi P'.arrow := Preadditive.epi_of_cokernel_zero (by rwa [← cancel_epi r, comp_zero])
  rw [← Subobject.isIso_arrow_iff_eq_top]
  exact isIso_of_mono_of_epi _

/-- Let `G` be a separator and `r : Z ⟶ P` an epimorphism. If `I` surjects onto the subobjects
of `P`, there are morphisms `φ i : G ⟶ Z` such that `Sigma.desc φ ≫ r : ∐ G ⟶ P` is still an
epimorphism. -/
theorem IsSeparator.exists_epi_sigmaDesc_comp (hG : IsSeparator G) {Z P : C} (r : Z ⟶ P) [Epi r]
    {I : Type*} [HasCoproduct fun _ : I ↦ G] (e : I → Subobject P) (he : Function.Surjective e) :
    ∃ φ : I → (G ⟶ Z), Epi (Sigma.desc φ ≫ r) := by
  classical
  let φ : I → (G ⟶ Z) := fun i ↦
    if h : ∃ φ : G ⟶ Z, ¬ (e i).Factors (φ ≫ r) then h.choose else 0
  refine ⟨φ, ?_⟩
  suffices hg : imageSubobject (Sigma.desc φ ≫ r) = ⊤ by
    have : IsIso (imageSubobject (Sigma.desc φ ≫ r)).arrow := by
      rw [Subobject.isIso_arrow_iff_eq_top]
      exact hg
    rw [← imageSubobject_arrow_comp (Sigma.desc φ ≫ r)]
    exact epi_comp _ _
  by_contra hne
  obtain ⟨i, hi⟩ := he (imageSubobject (Sigma.desc φ ≫ r))
  have h : ∃ φ : G ⟶ Z, ¬ (e i).Factors (φ ≫ r) := hi ▸ hG.exists_not_factors_comp r hne
  have hφ : φ i = h.choose := dite_eq_left h
  apply h.choose_spec
  rw [← hφ, hi]
  have : φ i ≫ r = Sigma.ι (fun _ : I ↦ G) i ≫ Sigma.desc φ ≫ r := by simp
  rw [this]
  exact imageSubobject_factors_comp_self _ _

/-- Let `G` be a separator, `g : P ⟶ X` a morphism and `Y` a subobject of the image of `g`. If `I`
surjects onto the subobjects of `P`, then for every epimorphism `π : Z ⟶ Y` there are morphisms
`φ i : G ⟶ Z` such that `Sigma.desc φ ≫ π : ∐ G ⟶ Y` is still an epimorphism. -/
theorem IsSeparator.exists_epi_sigmaDesc_comp_of_le_imageSubobject (hG : IsSeparator G)
    {P X Z : C} (g : P ⟶ X) {Y : Subobject X} (hY : Y ≤ imageSubobject g) (π : Z ⟶ Y) [Epi π]
    {I : Type*} [HasCoproduct fun _ : I ↦ G] (e : I → Subobject P) (he : Function.Surjective e) :
    ∃ φ : I → (G ⟶ Z), Epi (Sigma.desc φ ≫ π) := by
  have := Subobject.epi_pullbackπ_of_le_imageSubobject g hY
  set Q := (Subobject.pullback g).obj Y
  obtain ⟨φ, hφ⟩ := hG.exists_epi_sigmaDesc_comp (pullback.snd π (Subobject.pullbackπ g Y))
    (fun i ↦ (Subobject.pullback Q.arrow).obj (e i)) fun Q' ↦ by
      obtain ⟨i, hi⟩ := he ((Subobject.map Q.arrow).obj Q')
      exact ⟨i, by simp only [hi, Subobject.pullback_map_self]⟩
  refine ⟨fun i ↦ φ i ≫ pullback.fst _ _, ?_⟩
  have h : Sigma.desc (fun i ↦ φ i ≫ pullback.fst π (Subobject.pullbackπ g Y)) ≫ π =
      (Sigma.desc φ ≫ pullback.snd _ _) ≫ Subobject.pullbackπ g Y := by
    ext
    simp [pullback.condition]
  rw [h]
  exact epi_comp _ _

end CategoryTheory
