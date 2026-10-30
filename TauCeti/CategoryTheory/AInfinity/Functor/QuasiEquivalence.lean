/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.CategoryTheory.AInfinity.Functor.HomotopyCategory

/-!
# Quasi-equivalences of A-infinity categories

An `A∞` functor `ℱ : ℬ ⟶ 𝒞` is **quasi-fully faithful** when its arity-one component
`f₁ : Hom(X, Y) ⟶ Hom(F X, F Y)`, which is a chain map for the differentials `m₁`, induces a
bijection on the cohomology of every Hom complex.  The cohomology used here is that of the whole
graded Hom module, `ker m₁ ⧸ im m₁`.  Since `m₁` raises degrees by one and `f₁` preserves them,
this is the direct sum of the cohomology groups in the individual degrees.  Its degree-zero part
is the Hom space of `H⁰`, and bijectivity there is
`TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.homClassMap_bijective`.  A **quasi-equivalence**
into a cohomologically
unital `A∞` category `𝒞` is a quasi-fully faithful functor which is essentially surjective on
`H⁰`: every object of `𝒞` is isomorphic in `H⁰(𝒞)` to the image of an object of `ℬ`.

Neither unitality of `ℬ` nor unitality of `ℱ` has to be assumed.  Let `e'` be cohomological units
of `𝒞`.  Since `f₁` is surjective on cohomology, each `e' (F X)` is cohomologous to `f₁ (e X)`
for a closed degree-zero endomorphism `e X` of `X`.  Since `f₁` is injective on cohomology and
multiplicative up to boundaries, `e X` acts as the identity on cohomology, because its image does.
So `ℬ` is cohomologically unital
(`TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.cohomologicallyUnital`).  Comparing unit classes
in the same way shows that every quasi-fully faithful functor is unital
(`TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.isUnital`).  It therefore induces a functor
`H⁰(ℱ)` of homotopy categories.  This functor is fully faithful, and it is an equivalence when `ℱ`
is a quasi-equivalence.  The converse fails: `H⁰(ℱ)` only sees the degree-zero cohomology of the
Hom complexes.

These are the `A∞` counterparts of the quasi-fully faithful DG functors and DG quasi-equivalences
of `TauCeti/CategoryTheory/DG/QuasiEquivalence.lean`.

## Main definitions

* `TauCeti.AInfinityFunctor.homCohomologyMap`: the map induced by an `A∞` functor on the cohomology
  of a Hom complex.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful`: an `A∞` functor inducing bijections on the
  cohomology of all Hom complexes.
* `TauCeti.AInfinityFunctor.IsQuasiEquivalence`: a quasi-fully faithful `A∞` functor which is
  essentially surjective on `H⁰`.

## Main results

* `TauCeti.AInfinityFunctor.isQuasiFullyFaithful_iff`: the elementwise description by cycles and
  boundaries.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.homClassMap_bijective`: a quasi-fully faithful
  functor induces bijections on the Hom classes of closed degree-zero morphisms.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.isUnital`: a quasi-fully faithful functor is
  unital.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.cohomologicallyUnital`: the source of a
  quasi-fully faithful functor into a cohomologically unital `A∞` category is cohomologically
  unital.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.full_mapHomotopyCategory` and
  `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.faithful_mapHomotopyCategory`: `H⁰(ℱ)` is fully
  faithful.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.isQuasiEquivalence_iff_essSurj`: a quasi-fully
  faithful functor is a quasi-equivalence exactly when `H⁰(ℱ)` is essentially surjective.
* `TauCeti.AInfinityFunctor.IsQuasiEquivalence.isEquivalence_mapHomotopyCategory`: a
  quasi-equivalence induces an equivalence `H⁰(ℬ) ≌ H⁰(𝒞)`.
* `TauCeti.AInfinityFunctor.isQuasiEquivalence_id`: the identity `A∞` functor is a
  quasi-equivalence.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.
* P. Seidel, *Fukaya categories and Picard-Lefschetz theory*, Chapter I, for cohomologically
  full and faithful functors and quasi-equivalences of cohomologically unital `A∞` categories.
-/

public section

open CategoryTheory

namespace TauCeti

universe u₁ u₂ v₁ v₂ w

open GradedLinearQuiver

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]

namespace AInfinityFunctor

variable {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D} (ℱ : AInfinityFunctor ℬ 𝒞)

/-! ### The map on Hom cohomology -/

/-- The **map induced by an `A∞` functor on the cohomology of a Hom complex**, in all degrees at
once: the class of a closed morphism `f` goes to the class of `f₁(f)`
(`TauCeti.AInfinityFunctor.homCohomologyMap_mk`). -/
noncomputable def homCohomologyMap (X Y : C) :
    (ℬ.homDifferential X Y).homology (ℬ.homDifferential_comp_homDifferential X Y) →ₗ[R]
      (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)).homology
        (𝒞.homDifferential_comp_homDifferential (ℱ.obj X) (ℱ.obj Y)) :=
  LinearMap.homologyMap (ℱ.map X Y) _ _ (ℱ.map_comp_homDifferential X Y)

/-- The map on Hom cohomology sends the class of a closed morphism `f` to the class of `f₁(f)`. -/
@[simp]
theorem homCohomologyMap_mk {X Y : C} (f : LinearMap.ker (ℬ.homDifferential X Y)) :
    ℱ.homCohomologyMap X Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk ⟨ℱ.map X Y f, ℱ.homDifferential_map_eq_zero f.2⟩ :=
  LinearMap.homologyMap_mk _ _ _ _ f

/-! ### Quasi-fully faithful functors -/

/-- An `A∞` functor is **quasi-fully faithful** if its arity-one component `f₁` induces a
bijection on the cohomology `ker m₁ ⧸ im m₁` of every Hom module. -/
def IsQuasiFullyFaithful : Prop :=
  ∀ X Y : C, Function.Bijective (ℱ.homCohomologyMap X Y)

/-- An `A∞` functor is quasi-fully faithful exactly when it induces a bijection on the cohomology
of every Hom module. -/
theorem isQuasiFullyFaithful_def :
    ℱ.IsQuasiFullyFaithful ↔ ∀ X Y : C, Function.Bijective (ℱ.homCohomologyMap X Y) :=
  Iff.rfl

/-- **The elementwise description of quasi-full faithfulness.**  An `A∞` functor is quasi-fully
faithful exactly when, on every Hom complex, a closed morphism whose image under `f₁` is a
boundary is itself a boundary, and every closed morphism between images differs from the image of
a closed morphism by a boundary. -/
theorem isQuasiFullyFaithful_iff : ℱ.IsQuasiFullyFaithful ↔ ∀ X Y : C,
    (∀ f, ℬ.homDifferential X Y f = 0 →
      ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)) →
        f ∈ LinearMap.range (ℬ.homDifferential X Y)) ∧
    ∀ g, 𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) g = 0 → ∃ f, ℬ.homDifferential X Y f = 0 ∧
      g - ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)) := by
  refine forall₂_congr fun X Y ↦ ?_
  rw [Function.Bijective, homCohomologyMap, LinearMap.homologyMap_injective_iff,
    LinearMap.homologyMap_surjective_iff]
  simp only [LinearMap.mem_ker]

/-- The identity `A∞` functor is quasi-fully faithful. -/
@[simp]
theorem isQuasiFullyFaithful_id : (AInfinityFunctor.id ℬ).IsQuasiFullyFaithful := by
  refine (isQuasiFullyFaithful_iff _).mpr fun X Y ↦ ⟨fun f _ hf ↦ ?_, fun g hg ↦ ⟨g, hg, ?_⟩⟩
  · rwa [id_map_apply] at hf
  · refine ⟨0, ?_⟩
    rw [map_zero, eq_comm, sub_eq_zero]
    exact (id_map_apply ℬ g).symm

namespace IsQuasiFullyFaithful

variable {ℱ} (hℱ : ℱ.IsQuasiFullyFaithful)
include hℱ

/-- A quasi-fully faithful functor is injective on Hom cohomology: a closed morphism whose image
is a boundary is a boundary. -/
theorem mem_range_of_map_mem_range {X Y : C} {f : homModule (R := R) X Y}
    (hf : ℬ.homDifferential X Y f = 0)
    (h : ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y))) :
    f ∈ LinearMap.range (ℬ.homDifferential X Y) :=
  ((ℱ.isQuasiFullyFaithful_iff.mp hℱ X Y).1 f hf h)

/-- A quasi-fully faithful functor is surjective on Hom cohomology: every closed morphism between
images differs from the image of a closed morphism by a boundary. -/
theorem exists_sub_map_mem_range {X Y : C} {g : homModule (R := R) (ℱ.obj X) (ℱ.obj Y)}
    (hg : 𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) g = 0) :
    ∃ f, ℬ.homDifferential X Y f = 0 ∧
      g - ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)) :=
  (ℱ.isQuasiFullyFaithful_iff.mp hℱ X Y).2 g hg

/-- A closed degree-zero morphism between images differs from the image of a closed degree-zero
morphism by a boundary. -/
theorem exists_mem_homCyclesZero_sub_map_mem_range {X Y : C}
    {g : homModule (R := R) (ℱ.obj X) (ℱ.obj Y)} (hg : g ∈ 𝒞.homCyclesZero (ℱ.obj X) (ℱ.obj Y)) :
    ∃ f ∈ ℬ.homCyclesZero X Y,
      g - ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)) := by
  rw [AInfinityCategory.mem_homCyclesZero] at hg
  obtain ⟨f, hf, h, hh⟩ := hℱ.exists_sub_map_mem_range hg.2
  -- Keep the degree-zero components: `m₁` raises degrees by one and `f₁` preserves them.
  refine ⟨DirectSum.decompose (grading (R := R) X Y).piece f 0,
    ℬ.mem_homCyclesZero.mpr ⟨(DirectSum.decompose (grading (R := R) X Y).piece f 0).property, ?_⟩,
    DirectSum.decompose (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece h (-1), ?_⟩
  · simp [ℬ.homDifferential_decompose, hf]
  · rw [𝒞.homDifferential_decompose, neg_add_cancel, hh]
    simp [DirectSum.decompose_of_mem_same _ hg.1, ℱ.map_decompose]

/-- **A quasi-fully faithful functor is bijective on Hom classes** of closed degree-zero
morphisms. -/
theorem homClassMap_bijective (X Y : C) : Function.Bijective (ℱ.homClassMap X Y) := by
  refine ⟨(injective_iff_map_eq_zero (ℱ.homClassMap X Y)).mpr fun a ha ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
    rw [homClassMap_homClass, AInfinityCategory.homClass_eq_zero_iff] at ha
    obtain ⟨h, hh⟩ := ha
    obtain ⟨k, hk⟩ := hℱ.mem_range_of_map_mem_range (ℬ.mem_homCyclesZero.mp hf).2 ⟨h, hh⟩
    rw [← ℬ.homClass_zero, AInfinityCategory.homClass_eq_iff_sub_mem_range, sub_zero]
    exact ⟨k, hk⟩
  · obtain ⟨g, hg, rfl⟩ := 𝒞.exists_homClass_eq b
    obtain ⟨f, hf, hgf⟩ := hℱ.exists_mem_homCyclesZero_sub_map_mem_range hg
    refine ⟨ℬ.homClass f hf, ?_⟩
    rw [homClassMap_homClass, AInfinityCategory.homClass_eq_iff_sub_mem_range, ← neg_sub]
    exact neg_mem hgf

/-- **A quasi-fully faithful functor is unital**: its arity-one component carries cohomological
units to cohomological units modulo boundaries. -/
theorem isUnital : ℱ.IsUnital := by
  refine ℱ.isUnital_def.mpr fun e e' he he' X ↦ ?_
  obtain ⟨c, hc⟩ := (hℱ.homClassMap_bijective X X).2 (𝒞.homClass (e' (ℱ.obj X))
    (he'.cycle (ℱ.obj X)))
  -- The class of `f₁ (e X)` followed by the unit class `ℱ.homClassMap c` is the image of `e X`
  -- followed by `c`, which is the image of `c`.
  have key := ℱ.homClassMap_homCohomologyComp (ℬ.homClass (e X) (he.cycle X)) c
  rw [he.id_comp, hc, he'.comp_id, homClassMap_homClass] at key
  exact (AInfinityCategory.homClass_eq_iff_sub_mem_range _ _ _).mp key.symm

/-- Let `e` be a closed endomorphism of `Y` whose image under `f₁` is cohomologous to an
endomorphism `e'` of `F Y`.  If composing with `e'` on the left fixes `f₁ f` up to a boundary, for
a closed morphism `f`, then composing with `e` on the left fixes `f` up to a boundary. -/
theorem comp_sub_mem_range_of_map_sub_mem_range_left {X Y : C} {e : homModule (R := R) Y Y}
    {e' : homModule (R := R) (ℱ.obj Y) (ℱ.obj Y)} {f : homModule (R := R) X Y}
    (he : ℬ.homDifferential Y Y e = 0) (hf : ℬ.homDifferential X Y f = 0)
    (hee' : ℱ.map Y Y e - e' ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj Y) (ℱ.obj Y)))
    (he' : 𝒞.comp (ℱ.obj X) (ℱ.obj Y) (ℱ.obj Y) e' (ℱ.map X Y f) - ℱ.map X Y f ∈
      LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y))) :
    ℬ.comp X Y Y e f - f ∈ LinearMap.range (ℬ.homDifferential X Y) := by
  -- Up to boundaries, `f₁ (m₂(e, f) - f)` is `m₂(e', f₁ f) - f₁ f`.
  refine hℱ.mem_range_of_map_mem_range ?_ ?_
  · rw [map_sub, ℬ.homDifferential_comp_eq_zero he hf, hf, sub_zero]
  · convert add_mem (add_mem (ℱ.map_comp_sub_comp_mem_range he hf)
      (𝒞.comp_mem_range_homDifferential_of_left hee' (ℱ.homDifferential_map_eq_zero hf))) he'
      using 1
    rw [map_sub, LinearMap.map_sub₂]
    abel

/-- Let `e` be a closed endomorphism of `X` whose image under `f₁` is cohomologous to an
endomorphism `e'` of `F X`.  If composing with `e'` on the right fixes `f₁ f` up to a boundary,
for a closed morphism `f`, then composing with `e` on the right fixes `f` up to a boundary. -/
theorem comp_sub_mem_range_of_map_sub_mem_range_right {X Y : C} {e : homModule (R := R) X X}
    {e' : homModule (R := R) (ℱ.obj X) (ℱ.obj X)} {f : homModule (R := R) X Y}
    (hf : ℬ.homDifferential X Y f = 0) (he : ℬ.homDifferential X X e = 0)
    (hee' : ℱ.map X X e - e' ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj X)))
    (he' : 𝒞.comp (ℱ.obj X) (ℱ.obj X) (ℱ.obj Y) (ℱ.map X Y f) e' - ℱ.map X Y f ∈
      LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y))) :
    ℬ.comp X X Y f e - f ∈ LinearMap.range (ℬ.homDifferential X Y) := by
  -- Up to boundaries, `f₁ (m₂(f, e) - f)` is `m₂(f₁ f, e') - f₁ f`.
  refine hℱ.mem_range_of_map_mem_range ?_ ?_
  · rw [map_sub, ℬ.homDifferential_comp_eq_zero hf he, hf, sub_zero]
  · convert add_mem (add_mem (ℱ.map_comp_sub_comp_mem_range hf he)
      (𝒞.comp_mem_range_homDifferential_of_right (ℱ.homDifferential_map_eq_zero hf) hee')) he'
      using 1
    rw [map_sub, map_sub]
    abel

/-- **Cohomological unitality descends along quasi-fully faithful functors.**  If `𝒞` is
cohomologically unital, so is `ℬ`. -/
theorem cohomologicallyUnital (h𝒞 : 𝒞.CohomologicallyUnital) : ℬ.CohomologicallyUnital := by
  obtain ⟨e', he'⟩ := 𝒞.cohomologicallyUnital_iff.mp h𝒞
  choose e he hee using fun X ↦
    hℱ.exists_mem_homCyclesZero_sub_map_mem_range (he'.cycle (ℱ.obj X))
  -- The image of `e X` is cohomologous to the unit `e' (ℱ.obj X)`.
  have hunit : ∀ X, ℱ.map X X (e X) - e' (ℱ.obj X) ∈
      LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj X)) := fun X ↦ by
    rw [← neg_sub]
    exact neg_mem (hee X)
  refine ℬ.cohomologicallyUnital_iff.mpr ⟨e, he, fun X Y f hf ↦ ?_, fun X Y f hf ↦ ?_⟩
  · exact hℱ.comp_sub_mem_range_of_map_sub_mem_range_left (ℬ.mem_homCyclesZero.mp (he Y)).2 hf
      (hunit Y) (he'.left_unit _ _ _ (ℱ.homDifferential_map_eq_zero hf))
  · exact hℱ.comp_sub_mem_range_of_map_sub_mem_range_right hf (ℬ.mem_homCyclesZero.mp (he X)).2
      (hunit X) (he'.right_unit _ _ _ (ℱ.homDifferential_map_eq_zero hf))

variable (hℬ : ℬ.CohomologicallyUnital) (h𝒞 : 𝒞.CohomologicallyUnital)

/-- A quasi-fully faithful `A∞` functor induces a full functor on homotopy categories. -/
theorem full_mapHomotopyCategory : (mapHomotopyCategory hℬ h𝒞 hℱ.isUnital).Full :=
  ⟨fun {X Y} a ↦ by
    obtain ⟨b, hb⟩ := (hℱ.homClassMap_bijective X.obj Y.obj).2 a
    exact ⟨b, by rw [mapHomotopyCategory_map, hb]⟩⟩

/-- A quasi-fully faithful `A∞` functor induces a faithful functor on homotopy categories. -/
theorem faithful_mapHomotopyCategory : (mapHomotopyCategory hℬ h𝒞 hℱ.isUnital).Faithful :=
  ⟨fun {X Y} a b h ↦ (hℱ.homClassMap_bijective X.obj Y.obj).1 <| by
    rwa [mapHomotopyCategory_map, mapHomotopyCategory_map] at h⟩

end IsQuasiFullyFaithful

/-! ### Quasi-equivalences -/

/-- An `A∞` functor into a cohomologically unital `A∞` category is a **quasi-equivalence** if it
is quasi-fully faithful and essentially surjective on `H⁰`: every object of the target is
isomorphic in `H⁰` to the image of an object of the source. -/
def IsQuasiEquivalence (h𝒞 : 𝒞.CohomologicallyUnital) : Prop :=
  ℱ.IsQuasiFullyFaithful ∧ ∀ Y : D, ∃ X : C,
    Nonempty (AInfinityHomotopyCategory.of (h𝒞 := h𝒞) (ℱ.obj X) ≅ .of Y)

variable {ℱ} {h𝒞 : 𝒞.CohomologicallyUnital}

/-- An `A∞` functor is a quasi-equivalence exactly when it is quasi-fully faithful and every
object of the target is isomorphic in `H⁰` to the image of an object of the source. -/
theorem isQuasiEquivalence_iff : ℱ.IsQuasiEquivalence h𝒞 ↔ ℱ.IsQuasiFullyFaithful ∧
    ∀ Y : D, ∃ X : C, Nonempty (AInfinityHomotopyCategory.of (h𝒞 := h𝒞) (ℱ.obj X) ≅ .of Y) :=
  Iff.rfl

/-- A quasi-equivalence is quasi-fully faithful. -/
theorem IsQuasiEquivalence.isQuasiFullyFaithful (hℱ : ℱ.IsQuasiEquivalence h𝒞) :
    ℱ.IsQuasiFullyFaithful :=
  hℱ.1

/-- A quasi-equivalence reaches every object of the target up to isomorphism in `H⁰`. -/
theorem IsQuasiEquivalence.exists_iso (hℱ : ℱ.IsQuasiEquivalence h𝒞) (Y : D) :
    ∃ X : C, Nonempty (AInfinityHomotopyCategory.of (h𝒞 := h𝒞) (ℱ.obj X) ≅ .of Y) :=
  hℱ.2 Y

/-- The source of a quasi-equivalence is cohomologically unital. -/
theorem IsQuasiEquivalence.cohomologicallyUnital (hℱ : ℱ.IsQuasiEquivalence h𝒞) :
    ℬ.CohomologicallyUnital :=
  hℱ.1.cohomologicallyUnital h𝒞

/-- A quasi-fully faithful `A∞` functor is a quasi-equivalence exactly when the functor it induces
on homotopy categories is essentially surjective. -/
theorem IsQuasiFullyFaithful.isQuasiEquivalence_iff_essSurj (hℱ : ℱ.IsQuasiFullyFaithful)
    (hℬ : ℬ.CohomologicallyUnital) :
    ℱ.IsQuasiEquivalence h𝒞 ↔ (mapHomotopyCategory hℬ h𝒞 hℱ.isUnital).EssSurj := by
  rw [isQuasiEquivalence_iff, and_iff_right hℱ]
  refine ⟨fun h ↦ ⟨fun Y ↦ ?_⟩, fun h Y ↦ ?_⟩
  · obtain ⟨X, ⟨i⟩⟩ := h Y.obj
    refine ⟨.of X, ?_⟩
    rw [mapHomotopyCategory_obj]
    exact ⟨i⟩
  · obtain ⟨X, ⟨i⟩⟩ := h.mem_essImage (.of Y)
    rw [mapHomotopyCategory_obj] at i
    exact ⟨X.obj, ⟨i⟩⟩

/-- **A quasi-equivalence of `A∞` categories induces an equivalence of homotopy categories.** -/
theorem IsQuasiEquivalence.isEquivalence_mapHomotopyCategory (hℱ : ℱ.IsQuasiEquivalence h𝒞)
    (hℬ : ℬ.CohomologicallyUnital) :
    (mapHomotopyCategory hℬ h𝒞 hℱ.isQuasiFullyFaithful.isUnital).IsEquivalence where
  faithful := hℱ.isQuasiFullyFaithful.faithful_mapHomotopyCategory hℬ h𝒞
  full := hℱ.isQuasiFullyFaithful.full_mapHomotopyCategory hℬ h𝒞
  essSurj := (hℱ.isQuasiFullyFaithful.isQuasiEquivalence_iff_essSurj hℬ).mp hℱ

/-- The identity `A∞` functor of a cohomologically unital `A∞` category is a quasi-equivalence. -/
@[simp]
theorem isQuasiEquivalence_id (hℬ : ℬ.CohomologicallyUnital) :
    (AInfinityFunctor.id ℬ).IsQuasiEquivalence hℬ :=
  isQuasiEquivalence_iff.mpr ⟨isQuasiFullyFaithful_id, fun Y ↦ ⟨Y, ⟨Iso.refl _⟩⟩⟩

end AInfinityFunctor

end TauCeti
