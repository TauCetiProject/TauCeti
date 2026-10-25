/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Functor.Comp
public import TauCeti.CategoryTheory.AInfinity.Functor.HomotopyCategory

/-!
# Quasi-equivalences of A-infinity categories

An `A∞` functor `ℱ : ℬ ⟶ 𝒞` is **quasi-fully faithful** when its arity-one component
`f₁ : Hom(X, Y) ⟶ Hom(ℱ X, ℱ Y)` induces a bijection on the cohomology of every Hom complex.  It is
a **quasi-equivalence** when, moreover, every object of `𝒞` is isomorphic in `H⁰(𝒞)` to an object
in the image of `ℱ`.  These are the weak equivalences between `A∞` categories: Hom complexes are
compared only up to quasi-isomorphism, and objects only up to isomorphism in the homotopy
category.

The grading of a Hom module is internal and `m₁` and `f₁` are homogeneous, so a bijection on the
total cohomology of a Hom complex is the same as a bijection on its cohomology in every degree.
Surjectivity in a given degree is
`TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.exists_mem_piece_map_sub_mem_range`.  Taking the
direct sum over all pairs of objects, `ℱ` is quasi-fully faithful exactly when the `A∞` morphism
of total algebras of morphisms underlying it is a quasi-isomorphism
(`TauCeti.AInfinityFunctor.isQuasiFullyFaithful_iff_isQuasiIso_toAInfinityHom`).

Between cohomologically unital `A∞` categories a quasi-fully faithful functor is automatically
unital: on `H⁰(ℱ X, ℱ X)` the class `u` of `f₁(e_X)` satisfies `u ∘ v = v` for every class `v` in
the image of `H⁰(X, X)`, which is everything, so `u` is the identity.  Hence `ℱ` induces a functor
`H⁰(ℱ)` on homotopy categories, which is fully faithful, and an equivalence when `ℱ` is a
quasi-equivalence.  The converse fails: `H⁰(ℱ)` only sees the degree-zero cohomology of the Hom
complexes.

## Main definitions

* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful`: an `A∞` functor inducing bijections on the
  cohomology of all Hom complexes.
* `TauCeti.AInfinityFunctor.IsQuasiEquivalence`: a quasi-fully faithful `A∞` functor which is
  essentially surjective on `H⁰`.

## Main results

* `TauCeti.AInfinityFunctor.isQuasiFullyFaithful_iff_isQuasiIso_toAInfinityHom`: quasi-full
  faithfulness is the quasi-isomorphism property of the underlying `A∞` morphism of total
  algebras.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.homClassMap_bijective`: a quasi-fully faithful
  functor is bijective on the Hom classes of closed degree-zero morphisms.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.isUnital`: a quasi-fully faithful functor between
  cohomologically unital `A∞` categories is unital.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.full_mapHomotopyCategory` and
  `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.faithful_mapHomotopyCategory`: a quasi-fully
  faithful functor induces a fully faithful functor on homotopy categories.
* `TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.isQuasiEquivalence_iff_essSurj`: a quasi-fully
  faithful functor is a quasi-equivalence exactly when its functor on homotopy categories is
  essentially surjective.
* `TauCeti.AInfinityFunctor.IsQuasiEquivalence.isEquivalence_mapHomotopyCategory`: a
  quasi-equivalence induces an equivalence of homotopy categories.
* `TauCeti.AInfinityFunctor.isQuasiEquivalence_id` and
  `TauCeti.AInfinityFunctor.IsQuasiEquivalence.comp`: identities are quasi-equivalences, and
  quasi-equivalences compose.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.
* P. Seidel, *Fukaya categories and Picard--Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Chapter I, for cohomologically full and faithful functors and
  quasi-equivalences.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for unital `A∞` functors.
-/

public section

open CategoryTheory

namespace TauCeti

universe u₀ u₁ u₂ v₀ v₁ v₂ w

open GradedLinearQuiver

variable {R : Type w} [CommRing R] {B : Type u₀} {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₀, v₀, w} R B] [GradedLinearQuiver.{u₁, v₁, w} R C]
  [GradedLinearQuiver.{u₂, v₂, w} R D]

namespace AInfinityFunctor

variable {𝒜 : AInfinityCategory R B} {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D}

/-! ### Quasi-fully faithful functors -/

/-- An `A∞` functor is **quasi-fully faithful** when its arity-one component
`f₁ : Hom(X, Y) ⟶ Hom(ℱ X, ℱ Y)` induces a bijection on the cohomology of every Hom complex:
every closed morphism `ℱ X ⟶ ℱ Y` differs from the image of a closed morphism `X ⟶ Y` by a
boundary, and a closed morphism whose image is a boundary is itself a boundary.  As the grading is
internal, this is a bijection on cohomology in every degree
(`TauCeti.AInfinityFunctor.IsQuasiFullyFaithful.exists_mem_piece_map_sub_mem_range`). -/
structure IsQuasiFullyFaithful (ℱ : AInfinityFunctor ℬ 𝒞) : Prop where
  /-- Surjectivity on cohomology: every closed morphism `ℱ X ⟶ ℱ Y` is the image of a closed
  morphism `X ⟶ Y` up to a boundary. -/
  exists_map_sub_mem_range (X Y : C) {g : homModule (R := R) (ℱ.obj X) (ℱ.obj Y)}
    (hg : 𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) g = 0) :
    ∃ f : homModule (R := R) X Y, ℬ.homDifferential X Y f = 0 ∧
      ℱ.map X Y f - g ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y))
  /-- Injectivity on cohomology: a closed morphism whose image is a boundary is a boundary. -/
  mem_range_of_map_mem_range (X Y : C) {f : homModule (R := R) X Y}
    (hf : ℬ.homDifferential X Y f = 0)
    (hf' : ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y))) :
    f ∈ LinearMap.range (ℬ.homDifferential X Y)

variable {ℱ : AInfinityFunctor ℬ 𝒞}

/-- **Quasi-full faithfulness holds degreewise.**  A closed morphism `ℱ X ⟶ ℱ Y` of degree `n`
differs by a boundary from the image of a closed morphism `X ⟶ Y` of degree `n`. -/
theorem IsQuasiFullyFaithful.exists_mem_piece_map_sub_mem_range (hℱ : ℱ.IsQuasiFullyFaithful)
    {X Y : C} {n : ℤ} {g : homModule (R := R) (ℱ.obj X) (ℱ.obj Y)}
    (hgn : g ∈ (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece n)
    (hg : 𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) g = 0) :
    ∃ f ∈ (grading (R := R) X Y).piece n, ℬ.homDifferential X Y f = 0 ∧
      ℱ.map X Y f - g ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)) := by
  obtain ⟨f, hf, hfg⟩ := hℱ.exists_map_sub_mem_range X Y hg
  -- Keep the degree-`n` component of `f`: the differential and `f₁` are homogeneous, so its
  -- differential and its defect are the degree-`n` components of those of `f`.
  have hd (Z W : C) : LinearMap.IsHomogeneous (ℬ.homDifferential Z W)
      (grading (R := R) Z W).piece (grading (R := R) Z W).piece 1 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ ℬ.homDifferential_mem_piece hx
  have hd' : LinearMap.IsHomogeneous (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y))
      (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece
      (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece 1 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ 𝒞.homDifferential_mem_piece hx
  have hm : LinearMap.IsHomogeneous (ℱ.map X Y) (grading (R := R) X Y).piece
      (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by simpa using ℱ.map_mem X Y hx
  refine ⟨DirectSum.decompose (grading (R := R) X Y).piece f n,
    (DirectSum.decompose (grading (R := R) X Y).piece f n).property,
    (hd X Y).isHomogeneous_ker n (LinearMap.mem_ker.mpr hf), ?_⟩
  have h := hd'.isHomogeneous_range n hfg
  rwa [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub,
    DirectSum.decompose_of_mem_same _ hgn, ← add_zero n, ← hm.map_decompose] at h

/-- The identity `A∞` functor is quasi-fully faithful. -/
@[simp]
theorem isQuasiFullyFaithful_id : (AInfinityFunctor.id ℬ).IsQuasiFullyFaithful where
  exists_map_sub_mem_range X Y g hg := ⟨g, hg, 0, by
    rw [map_zero]
    exact (sub_eq_zero.mpr (id_map_apply ℬ g)).symm⟩
  mem_range_of_map_mem_range X Y f _ hf := by
    rw [id_map_apply] at hf
    exact hf

/-- **Quasi-fully faithful functors compose.** -/
theorem IsQuasiFullyFaithful.comp {𝒢 : AInfinityFunctor 𝒜 ℬ} (hℱ : ℱ.IsQuasiFullyFaithful)
    (h𝒢 : 𝒢.IsQuasiFullyFaithful) : (ℱ.comp 𝒢).IsQuasiFullyFaithful where
  exists_map_sub_mem_range X Y g hg := by
    obtain ⟨f', hf', k, hk⟩ := hℱ.exists_map_sub_mem_range (𝒢.obj X) (𝒢.obj Y) hg
    obtain ⟨f, hf, k', hk'⟩ := h𝒢.exists_map_sub_mem_range X Y hf'
    -- `g₁(f₁ f) - g = g₁(f₁ f - f') + (g₁ f' - g)` is the differential of `g₁ k' + k`.
    have h := congr (congrArg HAdd.hAdd (congrArg (ℱ.map (𝒢.obj X) (𝒢.obj Y)) hk')) hk
    rw [map_homDifferential, map_sub, ← map_add] at h
    refine ⟨f, hf, ℱ.map _ _ k' + k, ?_⟩
    rw [comp_map_apply]
    exact h.trans (sub_add_sub_cancel _ _ _)
  mem_range_of_map_mem_range X Y f hf hf' := by
    rw [comp_map_apply] at hf'
    exact h𝒢.mem_range_of_map_mem_range X Y hf <| hℱ.mem_range_of_map_mem_range _ _
      (by rw [← map_homDifferential, hf, map_zero]) hf'

/-! ### Comparison with the `A∞` morphism of total algebras -/

/-- **Quasi-full faithfulness is a quasi-isomorphism of total algebras.**  An `A∞` functor is
quasi-fully faithful exactly when the `A∞` morphism of total algebras of morphisms underlying it is
a quasi-isomorphism: the cohomology of the total algebras is the direct sum of the cohomology of
the Hom complexes, and the linear part is the direct sum of the maps on Hom complexes. -/
theorem isQuasiFullyFaithful_iff_isQuasiIso_toAInfinityHom (ℱ : AInfinityFunctor ℬ 𝒞) :
    ℱ.IsQuasiFullyFaithful ↔ ℱ.toAInfinityHom.IsQuasiIso := by
  rw [AInfinityHom.isQuasiIso_iff_forall_cycles]
  simp only [AInfinityAlgebra.cycles_def, AInfinityAlgebra.boundaries_def, LinearMap.mem_ker]
  constructor
  · intro hℱ
    refine ⟨fun y hy ↦ ?_, fun x hx hx' ↦ ?_⟩
    · -- Lift each component of the cycle `y` separately, and add up the lifts.
      refine totalHom_induction_homProjection (P := fun y ↦ ∃ x,
          ℬ.toAInfinityAlgebra.differential x = 0 ∧ ℱ.toAInfinityHom.linearPart x - y ∈
            LinearMap.range (𝒞.induced ℱ.obj).toAInfinityAlgebra.differential)
        ⟨0, map_zero _, by simp⟩ (fun y y' ⟨x, hx, hxy⟩ ⟨x', hx', hxy'⟩ ↦ ?_) y fun X Y ↦ ?_
      · refine ⟨x + x', by rw [map_add, hx, hx', add_zero], ?_⟩
        rw [map_add, add_sub_add_comm]
        exact add_mem hxy hxy'
      · have hg := congrArg (homProjection (R := R) X Y) hy
        rw [AInfinityCategory.homProjection_differential, map_zero,
          AInfinityCategory.homDifferential_induced] at hg
        obtain ⟨f, hf, k, hk⟩ := hℱ.exists_map_sub_mem_range X.obj Y.obj hg
        refine ⟨homInclusion X.obj Y.obj f, by
          rw [← AInfinityCategory.homInclusion_homDifferential, hf, map_zero],
          ⟨homInclusion X Y k, ?_⟩⟩
        rw [← AInfinityCategory.homInclusion_homDifferential,
          AInfinityCategory.homDifferential_induced, hk, map_sub, homInclusion_map]
    · -- Each component of the cycle `x` is a boundary, so `x` is a boundary.
      refine totalHom_induction_homProjection
        (P := (· ∈ LinearMap.range ℬ.toAInfinityAlgebra.differential)) (zero_mem _)
        (fun _ _ ↦ add_mem) x fun X Y ↦ ?_
      · obtain ⟨w, hw⟩ := hx'
        have hc := congrArg (homProjection (R := R) X Y) hx
        rw [AInfinityCategory.homProjection_differential, map_zero] at hc
        obtain ⟨k, hk⟩ := hℱ.mem_range_of_map_mem_range X Y hc
          ⟨homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩ w, by
            rw [← AInfinityCategory.homDifferential_induced 𝒞 ℱ.obj ⟨X⟩ ⟨Y⟩,
              ← AInfinityCategory.homProjection_differential, hw, homProjection_linearPart]⟩
        exact ⟨homInclusion X Y k, by rw [← AInfinityCategory.homInclusion_homDifferential, hk]⟩
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun X Y g hg ↦ ?_, fun X Y f hf hf' ↦ ?_⟩
    · obtain ⟨x, hx, w, hw⟩ := hsurj (homInclusion (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩ g)
        (by rw [← AInfinityCategory.homInclusion_homDifferential,
          AInfinityCategory.homDifferential_induced, hg, map_zero])
      refine ⟨homProjection X Y x, by
        rw [← AInfinityCategory.homProjection_differential, hx, map_zero],
        homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩ w, ?_⟩
      rw [← AInfinityCategory.homDifferential_induced 𝒞 ℱ.obj ⟨X⟩ ⟨Y⟩,
        ← AInfinityCategory.homProjection_differential, hw, map_sub, homProjection_linearPart,
        homProjection_homInclusion]
    · obtain ⟨k, hk⟩ := hf'
      obtain ⟨w, hw⟩ := hinj (homInclusion X Y f)
        (by rw [← AInfinityCategory.homInclusion_homDifferential, hf, map_zero])
        ⟨homInclusion (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩ k, by
          rw [← AInfinityCategory.homInclusion_homDifferential,
            AInfinityCategory.homDifferential_induced, hk, homInclusion_map]⟩
      exact ⟨homProjection X Y w, by
        rw [← AInfinityCategory.homProjection_differential, hw, homProjection_homInclusion]⟩

/-! ### Homotopy categories -/

/-- A quasi-fully faithful functor induces a bijection on the Hom classes of closed degree-zero
morphisms. -/
theorem IsQuasiFullyFaithful.homClassMap_bijective (hℱ : ℱ.IsQuasiFullyFaithful) (X Y : C) :
    Function.Bijective (ℱ.homClassMap X Y) := by
  refine ⟨(injective_iff_map_eq_zero (ℱ.homClassMap X Y)).2 fun a ha ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
    rw [homClassMap_homClass, AInfinityCategory.homClass_eq_zero_iff_mem_range] at ha
    rw [AInfinityCategory.homClass_eq_zero_iff_mem_range]
    exact hℱ.mem_range_of_map_mem_range X Y ((ℬ.mem_homCyclesZero).mp hf).2 ha
  · obtain ⟨g, hg, rfl⟩ := 𝒞.exists_homClass_eq b
    obtain ⟨f, hf₀, hf, hfg⟩ := hℱ.exists_mem_piece_map_sub_mem_range
      ((𝒞.mem_homCyclesZero).mp hg).1 ((𝒞.mem_homCyclesZero).mp hg).2
    refine ⟨ℬ.homClass f ((ℬ.mem_homCyclesZero).mpr ⟨hf₀, hf⟩), ?_⟩
    rw [homClassMap_homClass, AInfinityCategory.homClass_eq_iff_sub_mem_range]
    exact hfg

/-- **A quasi-fully faithful functor is unital.**  Between cohomologically unital `A∞` categories,
the class `u` of `f₁(e X)` is a right identity on the image of `H⁰(X, X)`, which is all of
`H⁰(ℱ X, ℱ X)`; in particular `u` is the class of the unit of `ℱ X`. -/
theorem IsQuasiFullyFaithful.isUnital (hℱ : ℱ.IsQuasiFullyFaithful)
    (hℬ : ℬ.CohomologicallyUnital) (h𝒞 : 𝒞.CohomologicallyUnital) : ℱ.IsUnital := by
  obtain ⟨e, he⟩ := ℬ.cohomologicallyUnital_iff.mp hℬ
  obtain ⟨e', he'⟩ := 𝒞.cohomologicallyUnital_iff.mp h𝒞
  refine (ℱ.isUnital_iff he he').2 fun X ↦ ?_
  obtain ⟨a, ha⟩ := (hℱ.homClassMap_bijective X X).2 (𝒞.homClass (e' (ℱ.obj X)) (he'.cycle _))
  have key := congrArg (ℱ.homClassMap X X) (he.comp_id a)
  rw [homClassMap_homCohomologyComp, ha, homClassMap_homClass, he'.id_comp] at key
  rw [← AInfinityCategory.homClass_eq_iff_sub_mem_range _ (ℱ.map_mem_homCyclesZero (he.cycle X))
    (he'.cycle _)]
  exact key

variable (hℬ : ℬ.CohomologicallyUnital) (h𝒞 : 𝒞.CohomologicallyUnital)

/-- A quasi-fully faithful functor induces a full functor on homotopy categories. -/
theorem IsQuasiFullyFaithful.full_mapHomotopyCategory (hℱ : ℱ.IsQuasiFullyFaithful)
    (hu : ℱ.IsUnital) : (mapHomotopyCategory hℬ h𝒞 hu).Full :=
  ⟨fun {X Y} ↦ (hℱ.homClassMap_bijective X.obj Y.obj).2⟩

/-- A quasi-fully faithful functor induces a faithful functor on homotopy categories. -/
theorem IsQuasiFullyFaithful.faithful_mapHomotopyCategory (hℱ : ℱ.IsQuasiFullyFaithful)
    (hu : ℱ.IsUnital) : (mapHomotopyCategory hℬ h𝒞 hu).Faithful :=
  ⟨fun {X Y} ↦ (hℱ.homClassMap_bijective X.obj Y.obj).1⟩

/-! ### Quasi-equivalences -/

variable (ℱ) in
/-- An `A∞` functor is a **quasi-equivalence** when it is quasi-fully faithful and every object of
the target is isomorphic in the homotopy category `H⁰(𝒞)` to the image of an object. -/
structure IsQuasiEquivalence : Prop extends ℱ.IsQuasiFullyFaithful where
  /-- Essential surjectivity on `H⁰`: every object of the target is isomorphic in `H⁰(𝒞)` to the
  image of an object. -/
  exists_nonempty_iso (Y : D) : ∃ X : C,
    Nonempty (AInfinityHomotopyCategory.of (h𝒞 := h𝒞) (ℱ.obj X) ≅ AInfinityHomotopyCategory.of Y)

variable {hℬ h𝒞}

/-- **A quasi-fully faithful functor is a quasi-equivalence exactly when it is essentially
surjective on homotopy categories.** -/
theorem IsQuasiFullyFaithful.isQuasiEquivalence_iff_essSurj (hℱ : ℱ.IsQuasiFullyFaithful)
    (hu : ℱ.IsUnital) : ℱ.IsQuasiEquivalence h𝒞 ↔ (mapHomotopyCategory hℬ h𝒞 hu).EssSurj := by
  refine ⟨fun h ↦ ⟨fun Y ↦ ?_⟩, fun h ↦ ⟨hℱ, fun Y ↦ ?_⟩⟩
  · obtain ⟨X, ⟨e⟩⟩ := h.exists_nonempty_iso Y.obj
    -- `H⁰(ℱ)` sends the object `X` of `H⁰(ℬ)` to the object `ℱ X` of `H⁰(𝒞)`.
    exact ⟨.of X, ⟨e⟩⟩
  · obtain ⟨X, ⟨e⟩⟩ := h.mem_essImage (.of Y)
    exact ⟨X.obj, ⟨e⟩⟩

/-- **A quasi-equivalence induces an equivalence of homotopy categories.** -/
theorem IsQuasiEquivalence.isEquivalence_mapHomotopyCategory (hℱ : ℱ.IsQuasiEquivalence h𝒞)
    (hu : ℱ.IsUnital) : (mapHomotopyCategory hℬ h𝒞 hu).IsEquivalence where
  faithful := hℱ.faithful_mapHomotopyCategory hℬ h𝒞 hu
  full := hℱ.full_mapHomotopyCategory hℬ h𝒞 hu
  essSurj := (hℱ.isQuasiEquivalence_iff_essSurj hu).1 hℱ

/-- The identity `A∞` functor is a quasi-equivalence. -/
@[simp]
theorem isQuasiEquivalence_id : (AInfinityFunctor.id ℬ).IsQuasiEquivalence hℬ where
  toIsQuasiFullyFaithful := isQuasiFullyFaithful_id
  exists_nonempty_iso X := ⟨X, ⟨Iso.refl _⟩⟩

/-- **Quasi-equivalences compose.** -/
theorem IsQuasiEquivalence.comp {𝒢 : AInfinityFunctor 𝒜 ℬ}
    (hℱ : ℱ.IsQuasiEquivalence h𝒞) (h𝒢 : 𝒢.IsQuasiEquivalence hℬ) :
    (ℱ.comp 𝒢).IsQuasiEquivalence h𝒞 where
  toIsQuasiFullyFaithful := hℱ.toIsQuasiFullyFaithful.comp h𝒢.toIsQuasiFullyFaithful
  exists_nonempty_iso Z := by
    obtain ⟨Y, ⟨e⟩⟩ := hℱ.exists_nonempty_iso Z
    obtain ⟨X, ⟨e'⟩⟩ := h𝒢.exists_nonempty_iso Y
    -- Transport `𝒢 X ≅ Y` along `H⁰(ℱ)` and compose with `ℱ Y ≅ Z`.
    exact ⟨X, ⟨(mapHomotopyCategory hℬ h𝒞
      (hℱ.toIsQuasiFullyFaithful.isUnital hℬ h𝒞)).mapIso e' ≪≫ e⟩⟩

end AInfinityFunctor

end TauCeti
