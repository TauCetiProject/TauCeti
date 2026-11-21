/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion

import Mathlib.CategoryTheory.Sites.Whiskering
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Laurent.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Basic

/-!
# Algebraic exactness of simple Laurent covers from sheafiness

Over a complete Hausdorff Huber ring `R` equipped with a Huber pair `S` whose presentation-limit
structure presheaf is a sheaf (`IsSheafyForEveryPresentation S.plus`), this file deduces left
exactness of the simple Laurent sequence `0 → R → R₁ × R₂ → R₁₂` for any models `R₁`, `R₂`,
`R₁₂` of `R⟨{f, 1}/1⟩`, `R⟨{1}/f⟩`, and `R⟨{f², 1}/f⟩` connected by continuous `R`-algebra maps.

## Main results

* `TauCeti.Huber.laurent_injective_and_exact_of_isSheafyForEveryPresentation` : injectivity of
  `R → R₁ × R₂` and exactness at `R₁ × R₂` of `0 → R → R₁ × R₂ → R₁₂`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, proof of Theorem 2.4.23.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.ValuationSpectrum

namespace TauCeti.Huber

/-- Sheafiness of `presentationLimitPresheaf P Aplus` implies the sheaf condition for the two-piece
Laurent cover on `presentationLimit`. -/
private theorem existsUnique_presentationLimit_laurent {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsHuberRing R] [DecidableEq R]
    (P : PairOfDefinition R) {Aplus : Subring R} (hs : IsSheafyForEveryPresentation Aplus) (f : R)
    (x₁ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus {f, 1} 1))
    (x₂ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus {1} f))
    (hx : (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val x₁ =
      (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val x₂) :
    ∃! a : presentationLimit (P := P) Aplus ⊤,
      (presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus {f, 1} 1 ≤ ⊤)).hom.val a = x₁ ∧
      (presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus {1} f ≤ ⊤)).hom.val a = x₂ := by
  have hsheaf := ((isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).mp hs).2
  have hsheafG : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _root_.TopCommRingCat)
      (Presheaf.isSheaf_comp_of_isSheaf _ (presentationLimitPresheaf P Aplus)
        TopCommRingCat.isCompleteSeparated.ι hsheaf)
  let U : Bool → Opens ↥(spa Aplus) :=
    fun b ↦ b.rec (spaBasicOpen Aplus {1} f) (spaBasicOpen Aplus {f, 1} 1)
  have hcov : Sieve.ofArrows U (fun _ ↦ homOfLE le_top) ∈
      Opens.grothendieckTopology ↥(spa Aplus) ⊤ := fun v _ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (spa_subset_iUnion_laurentCover Aplus f v.property)
    refine ⟨U b, homOfLE le_top, Sieve.ofArrows_mk _ _ b, ?_⟩
    cases b <;> simpa [U, mem_spaBasicOpen, mem_rationalSubset_iff] using hb
  have hfor := (Presieve.isSheafFor_iff_generate _).mpr (hsheafG.isSheafFor _ hcov)
  obtain ⟨a, ha, hu⟩ := (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P
    (fun (b : Bool) ↦ (le_top : U b ≤ ⊤))).mp hfor (fun b ↦ b.rec x₂ x₁) fun i j ↦ by
    cases i <;> cases j
    · rfl
    · have h := congrArg (presentationLimitMap (P := P)
          (le_inf inf_le_right inf_le_left : U false ⊓ U true ≤ U true ⊓ U false)).hom.val hx.symm
      rwa [presentationLimitMap_apply_presentationLimitMap_apply,
        presentationLimitMap_apply_presentationLimitMap_apply] at h
    · exact hx
    · rfl
  exact ⟨a, ⟨ha true, ha false⟩, fun a' ⟨ha'₁, ha'₂⟩ ↦ hu a' fun b ↦ by cases b <;> assumption⟩

section Main

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [CompleteSpace R] [T0Space R]
  [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [DecidableEq R]
  {P : PairOfDefinition R} {f : R}
  {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
  {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
  {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}

omit [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] in
private theorem presentationLimitMap_laurentInf_eq {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁) (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂))
    {y₁ : R₁} {y₂ : R₂} (hy : algebraMap R₁ R₁₂ y₁ = algebraMap R₂ R₁₂ y₂) :
    (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val
      ((rationalSectionRingEquiv P hAplus {f, 1} 1 hT₁ h₁).symm y₁) =
    (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val
      ((rationalSectionRingEquiv P hAplus {1} f hT₂ h₂).symm y₂) := by
  have hEq := spaBasicOpen_laurentOverlap_eq_inf Aplus f
  set e₁ := rationalSectionRingEquiv P hAplus {f, 1} 1 hT₁ h₁
  set e₂ := rationalSectionRingEquiv P hAplus {1} f hT₂ h₂
  set e₁₂ := rationalSectionRingEquiv P hAplus {f * f, 1} f hT₁₂ h₁₂
  have hInv : Function.LeftInverse (presentationLimitMap (P := P) hEq.ge).hom.val
      (presentationLimitMap (P := P) hEq.le).hom.val := fun z ↦ by
    rw [presentationLimitMap_apply_presentationLimitMap_apply, presentationLimitMap_refl]
    exact ConcreteCategory.id_apply z
  refine hInv.injective (e₁₂.injective ?_)
  rw [presentationLimitMap_apply_presentationLimitMap_apply,
    presentationLimitMap_apply_presentationLimitMap_apply,
    rationalSectionRingEquiv_map_le P hAplus hT₁ hT₁₂ (hEq.le.trans inf_le_left) h₁ h₁₂ hc₁,
    rationalSectionRingEquiv_map_le P hAplus hT₂ hT₁₂ (hEq.le.trans inf_le_right) h₂ h₁₂ hc₂,
    e₁.apply_symm_apply, e₂.apply_symm_apply, hy]

/-- Over a complete Hausdorff Huber ring `R` equipped with a Huber pair `S` satisfying
`IsSheafyForEveryPresentation S.plus`, the simple Laurent sequence `0 → R → R₁ × R₂ → R₁₂` is
injective on `R` and exact in the middle. -/
theorem laurent_injective_and_exact_of_isSheafyForEveryPresentation [IsHuberRing R] (S : Pair R)
    (hs : IsSheafyForEveryPresentation S.plus) (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂) (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    (Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)) ∧
      Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
        fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 := by
  have hSplus : ∀ ⦃a⦄, a ∈ S.plus → IsPowerBounded a :=
    fun _ ha ↦ mem_powerBoundedSubring.mp (S.isRingOfIntegralElements.le_powerBoundedSubring ha)
  set e₀ := topSectionRingEquiv P hSplus
  set e₁ := rationalSectionRingEquiv P hSplus {f, 1} 1 hT₁ h₁
  set e₂ := rationalSectionRingEquiv P hSplus {1} f hT₂ h₂
  refine ⟨fun r₁ r₂ hr ↦ ?_, fun ⟨x₁, x₂⟩ ↦ ⟨fun hsub ↦ ?_, ?_⟩⟩
  · have hglue := existsUnique_presentationLimit_laurent P hs f
      (e₁.symm (algebraMap R R₁ r₁)) (e₂.symm (algebraMap R R₂ r₁))
      (presentationLimitMap_laurentInf_eq hSplus h₁ h₂ h₁₂ hc₁ hc₂ (by
        rw [← IsScalarTower.algebraMap_apply R R₁ R₁₂,
          ← IsScalarTower.algebraMap_apply R R₂ R₁₂]))
    have htop₁ (r : R) : e₁ ((presentationLimitMap (P := P) le_top).hom.val (e₀.symm r)) =
        algebraMap R R₁ r := by rw [rationalSectionRingEquiv_map_top, e₀.apply_symm_apply]
    have htop₂ (r : R) : e₂ ((presentationLimitMap (P := P) le_top).hom.val (e₀.symm r)) =
        algebraMap R R₂ r := by rw [rationalSectionRingEquiv_map_top, e₀.apply_symm_apply]
    exact e₀.symm.injective (hglue.unique
      ⟨e₁.injective (by rw [e₁.apply_symm_apply, htop₁]),
       e₂.injective (by rw [e₂.apply_symm_apply, htop₂])⟩
      ⟨e₁.injective (by rw [e₁.apply_symm_apply, htop₁]; exact (congrArg Prod.fst hr).symm),
       e₂.injective (by rw [e₂.apply_symm_apply, htop₂]; exact (congrArg Prod.snd hr).symm)⟩)
  · obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := existsUnique_presentationLimit_laurent P hs f
      (e₁.symm x₁) (e₂.symm x₂)
      (presentationLimitMap_laurentInf_eq hSplus h₁ h₂ h₁₂ hc₁ hc₂ (sub_eq_zero.mp hsub))
    refine ⟨e₀ a, Prod.ext ?_ ?_⟩
    · have h := congrArg e₁ ha₁; rwa [e₁.apply_symm_apply, rationalSectionRingEquiv_map_top] at h
    · have h := congrArg e₂ ha₂; rwa [e₂.apply_symm_apply, rationalSectionRingEquiv_map_top] at h
  · rintro ⟨r, hr⟩
    rcases Prod.mk.inj hr with ⟨rfl, rfl⟩
    simp [← IsScalarTower.algebraMap_apply R R₁ R₁₂, ← IsScalarTower.algebraMap_apply R R₂ R₁₂]

end Main

end TauCeti.Huber

end
