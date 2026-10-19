/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Equiv
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Subdivision
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Subfan
public import TauCeti.Geometry.Toric.Analytic.Fan.Subfan.Holomorphic

/-!
# The blow-down of a star subdivision away from the exceptional divisor

Let `Φ` be a regular fan, `σ` a nonzero cone of `Φ`, and `π` the analytic blow-down map from the
realization of the star subdivision `Fan.starSubdivisionAlong Φ σ` to that of `Φ`. The preimage
under `π` of the orbit closure `Z` of `σ` is the exceptional divisor `E`, the boundary component of
the ray through the sum of the primitive generators of the rays of `σ`. This file proves that `π`
restricts to a biholomorphism from the complement of `E` onto the complement of `Z`.

Combinatorially, the complement of `Z` is the open subset of the open subfan of cones of `Φ` not
containing `σ` (`Fan.range_subfanAnalyticMap_setOf_not_le`). Its preimage under `π` is the open
subset of the preimage subfan, which consists of the same cones
(`Fan.not_le_leastCone_starSubdivisionAlong_iff`), so the restriction of `π` is induced by the
identity fan equivalence between the two subfans. The restriction square is a pullback
(`FanHom.range_preimageSubfanAnalyticMap`) and both open-subfan embeddings are local
biholomorphisms, so `π` is an injective local biholomorphism on the complement of `E`.

## Main declarations

* `TauCeti.Toric.Fan.image_analyticMap_starSubdivisionAlong_compl`: `π` maps the complement of the
  exceptional divisor onto the complement of the orbit closure of `σ`.
* `TauCeti.Toric.Fan.injOn_analyticMap_starSubdivisionAlong_compl`: `π` is injective there.
* `TauCeti.Toric.Fan.isLocalDiffeomorphOn_analyticMap_starSubdivisionAlong_compl`: `π` is a local
  biholomorphism there.
* `TauCeti.Toric.Fan.starSubdivisionAlongPartialDiffeomorph`: `π` as a biholomorphism from the
  complement of the exceptional divisor onto the complement of the orbit closure of `σ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (hΦ : Φ.IsRegular) {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) (hσ0 : σ ≠ ⊥)

/-! ### The open subfans away from the center -/

private theorem preimageCones_starSubdivisionAlong :
    (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageCones
        {C | C ∈ Φ.cones ∧ ¬σ ≤ C} = {C | C ∈ Φ.cones ∧ ¬σ ≤ C} := by
  ext C
  by_cases hC : C ∈ (Φ.starSubdivisionAlong hΦ hσ).cones
  · rw [FanHom.mem_preimageCones_iff _ _ hC]
    exact (and_iff_right (FanHom.leastCone_mem _ hC)).trans
      (Φ.not_le_leastCone_starSubdivisionAlong_iff hΦ hσ hσ0 hC)
  · exact iff_of_false (fun h ↦ hC (FanHom.preimageCones_subset _ _ h))
      fun h ↦ hC (Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ hσ h.1 h.2)

/-- Over the cones of `Φ` not containing `σ`, the restriction of the blow-down is the identity
fan equivalence between the preimage subfan and the subfan of those cones. -/
private noncomputable def complFanEquiv :
    FanEquiv ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageSubfan
        {C | C ∈ Φ.cones ∧ ¬σ ≤ C} (Φ.setOf_not_le_closedUnderFaces σ))
      (Φ.subfan {C | C ∈ Φ.cones ∧ ¬σ ≤ C} (Φ.setOf_not_le_subset_cones σ)
        (Φ.setOf_not_le_closedUnderFaces σ)) where
  latticeEquiv := AddEquiv.refl N
  realEquiv := LinearEquiv.refl ℝ V
  map_lattice _ := rfl
  map_mem C := by
    rw [LinearEquiv.refl_toLinearMap, PointedCone.map_id, subfan_cones, subfan_cones,
      preimageCones_starSubdivisionAlong Φ hΦ hσ hσ0]

private theorem toFanHom_complFanEquiv :
    (complFanEquiv Φ hΦ hσ hσ0).toFanHom =
      (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.restrictToPreimage
        {C | C ∈ Φ.cones ∧ ¬σ ≤ C} (Φ.setOf_not_le_subset_cones σ)
        (Φ.setOf_not_le_closedUnderFaces σ) :=
  FanHom.ext (by simp [complFanEquiv])

/-- The open subset of the preimage subfan is the complement of the exceptional divisor. -/
private theorem range_subfanAnalyticMap_preimageCones :
    range ((Φ.starSubdivisionAlong hΦ hσ).subfanAnalyticMap (Φ.isRegular_starSubdivisionAlong hΦ hσ)
        _ ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageCones_subset
          {C | C ∈ Φ.cones ∧ ¬σ ≤ C})
        ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageCones_closedUnderFaces
          _ (Φ.setOf_not_le_closedUnderFaces σ))) =
      ((Φ.starSubdivisionAlong hΦ hσ).analyticBoundaryComponent
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0))ᶜ := by
  rw [FanHom.range_preimageSubfanAnalyticMap _ _ hΦ _ (Φ.setOf_not_le_subset_cones σ)
      (Φ.setOf_not_le_closedUnderFaces σ),
    Φ.range_subfanAnalyticMap_setOf_not_le hΦ ⟨σ, hσ⟩, preimage_compl,
    preimage_analyticMap_closure_analyticConeOrbit_starSubdivisionAlong]

/-- On the open subset of the preimage subfan, the blow-down is the map induced by the identity fan
equivalence, followed by the open-subfan embedding of `Φ`. -/
private theorem analyticMap_comp_subfanAnalyticMap :
    (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ ∘
      (Φ.starSubdivisionAlong hΦ hσ).subfanAnalyticMap (Φ.isRegular_starSubdivisionAlong hΦ hσ) _
        ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageCones_subset
          {C | C ∈ Φ.cones ∧ ¬σ ≤ C})
        ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageCones_closedUnderFaces
          _ (Φ.setOf_not_le_closedUnderFaces σ)) =
      Φ.subfanAnalyticMap hΦ _ (Φ.setOf_not_le_subset_cones σ)
          (Φ.setOf_not_le_closedUnderFaces σ) ∘
        (complFanEquiv Φ hΦ hσ hσ0).toFanHom.analyticMap
          ((Φ.isRegular_starSubdivisionAlong hΦ hσ).preimageSubfan _ _
            (Φ.setOf_not_le_closedUnderFaces σ)) (hΦ.subfan _ (Φ.setOf_not_le_subset_cones σ)
              (Φ.setOf_not_le_closedUnderFaces σ)) := by
  ext x
  rw [toFanHom_complFanEquiv]
  exact ConcreteCategory.congr_hom (FanHom.preimageSubfanAnalyticMap_comp_analyticMap _ _ hΦ _
    (Φ.setOf_not_le_subset_cones σ) (Φ.setOf_not_le_closedUnderFaces σ)) x

private theorem bijective_analyticMap_complFanEquiv :
    Function.Bijective ((complFanEquiv Φ hΦ hσ hσ0).toFanHom.analyticMap
      ((Φ.isRegular_starSubdivisionAlong hΦ hσ).preimageSubfan _ _
        (Φ.setOf_not_le_closedUnderFaces σ))
      (hΦ.subfan _ (Φ.setOf_not_le_subset_cones σ) (Φ.setOf_not_le_closedUnderFaces σ))) := by
  rw [← FanEquiv.analyticIso_hom]
  exact ConcreteCategory.bijective_of_isIso _

/-- The star subdivision has a cone, so its realization is nonempty. -/
private theorem nonempty_analyticRealization_starSubdivisionAlong (hσ0 : σ ≠ ⊥) :
    Nonempty ((Φ.starSubdivisionAlong hΦ hσ).analyticRealization
      (Φ.isRegular_starSubdivisionAlong hΦ hσ)) :=
  ⟨(Φ.starSubdivisionAlong hΦ hσ).analyticDistinguishedPoint
    (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0).1⟩

/-! ### The blow-down away from the exceptional divisor -/

/-- The blow-down of the star subdivision of a regular fan `Φ` along a nonzero cone `σ` maps the
complement of the exceptional divisor onto the complement of the orbit closure of `σ`. -/
theorem image_analyticMap_starSubdivisionAlong_compl :
    (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ ''
          ((Φ.starSubdivisionAlong hΦ hσ).analyticBoundaryComponent
            (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0))ᶜ =
      (closure (Φ.analyticConeOrbit hΦ ⟨σ, hσ⟩))ᶜ := by
  rw [← range_subfanAnalyticMap_preimageCones, ← range_comp,
    analyticMap_comp_subfanAnalyticMap Φ hΦ hσ hσ0, range_comp,
    (bijective_analyticMap_complFanEquiv Φ hΦ hσ hσ0).surjective.range_eq, image_univ,
    Φ.range_subfanAnalyticMap_setOf_not_le hΦ ⟨σ, hσ⟩]

/-- The blow-down of the star subdivision of a regular fan `Φ` along a nonzero cone `σ` is
injective on the complement of the exceptional divisor. -/
theorem injOn_analyticMap_starSubdivisionAlong_compl :
    InjOn ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ)
      ((Φ.starSubdivisionAlong hΦ hσ).analyticBoundaryComponent
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0))ᶜ := by
  have hinj := (Φ.subfanAnalyticMap_injective hΦ _ (Φ.setOf_not_le_subset_cones σ)
    (Φ.setOf_not_le_closedUnderFaces σ)).comp
      (bijective_analyticMap_complFanEquiv Φ hΦ hσ hσ0).injective
  rw [← analyticMap_comp_subfanAnalyticMap Φ hΦ hσ hσ0] at hinj
  rw [← range_subfanAnalyticMap_preimageCones]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact congrArg _ (hinj h)

/-- The blow-down of the star subdivision of a regular fan `Φ` along a nonzero cone `σ` is a local
biholomorphism on the complement of the exceptional divisor, for the complex manifold structures of
the two realizations. -/
theorem isLocalDiffeomorphOn_analyticMap_starSubdivisionAlong_compl (n : ℕ∞ω) :
    letI := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
      (Φ.isRegular_starSubdivisionAlong hΦ hσ)
    letI := Φ.analyticChartedSpace hΦ
    IsLocalDiffeomorphOn 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ)
      ((Φ.starSubdivisionAlong hΦ hσ).analyticBoundaryComponent
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0))ᶜ := by
  let _ := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
    (Φ.isRegular_starSubdivisionAlong hΦ hσ)
  let _ := Φ.analyticChartedSpace hΦ
  -- The complex structures of the two open subfans, which the chain rule below passes through.
  let _ := ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.preimageSubfan
    _ (Φ.setOf_not_le_closedUnderFaces σ)).analyticChartedSpace
      ((Φ.isRegular_starSubdivisionAlong hΦ hσ).preimageSubfan _ _
        (Φ.setOf_not_le_closedUnderFaces σ))
  let _ := (Φ.subfan _ (Φ.setOf_not_le_subset_cones σ)
    (Φ.setOf_not_le_closedUnderFaces σ)).analyticChartedSpace
    (hΦ.subfan _ (Φ.setOf_not_le_subset_cones σ) (Φ.setOf_not_le_closedUnderFaces σ))
  rintro ⟨_, hx⟩
  rw [← range_subfanAnalyticMap_preimageCones] at hx
  obtain ⟨a, rfl⟩ := hx
  dsimp only
  refine IsLocalDiffeomorphAt.of_comp_right ?_
    ((Φ.starSubdivisionAlong hΦ hσ).isLocalDiffeomorph_subfanAnalyticMap
      (Φ.isRegular_starSubdivisionAlong hΦ hσ) _ _ _ n a)
  rw [analyticMap_comp_subfanAnalyticMap Φ hΦ hσ hσ0, ← FanEquiv.coe_analyticDiffeomorph _ _ _ n]
  exact (Diffeomorph.isLocalDiffeomorph _ a).comp (hg := Φ.isLocalDiffeomorph_subfanAnalyticMap hΦ
    _ (Φ.setOf_not_le_subset_cones σ) (Φ.setOf_not_le_closedUnderFaces σ) n _)

/-- The blow-down of the star subdivision of a regular fan `Φ` along a nonzero cone `σ`, as a
biholomorphism from the complement of the exceptional divisor onto the complement of the orbit
closure of `σ`. -/
noncomputable def starSubdivisionAlongPartialDiffeomorph (hσ0 : σ ≠ ⊥) (n : ℕ∞ω) :
    letI := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
      (Φ.isRegular_starSubdivisionAlong hΦ hσ)
    letI := Φ.analyticChartedSpace hΦ
    PartialDiffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      ((Φ.starSubdivisionAlong hΦ hσ).analyticRealization (Φ.isRegular_starSubdivisionAlong hΦ hσ))
      (Φ.analyticRealization hΦ) n :=
  letI := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
    (Φ.isRegular_starSubdivisionAlong hΦ hσ)
  letI := Φ.analyticChartedSpace hΦ
  haveI := nonempty_analyticRealization_starSubdivisionAlong Φ hΦ hσ hσ0
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn
    (Φ.isLocalDiffeomorphOn_analyticMap_starSubdivisionAlong_compl hΦ hσ hσ0 n)
    (range_subfanAnalyticMap_preimageCones Φ hΦ hσ hσ0 ▸
      ((Φ.starSubdivisionAlong hΦ hσ).isOpenEmbedding_subfanAnalyticMap _ _ _ _).isOpen_range)
    (Φ.injOn_analyticMap_starSubdivisionAlong_compl hΦ hσ hσ0)

/-- The biholomorphism of `Fan.starSubdivisionAlongPartialDiffeomorph` is the blow-down map. -/
@[simp]
theorem coe_starSubdivisionAlongPartialDiffeomorph (n : ℕ∞ω) :
    ⇑(Φ.starSubdivisionAlongPartialDiffeomorph hΦ hσ hσ0 n) =
      (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ := by
  let _ := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
    (Φ.isRegular_starSubdivisionAlong hΦ hσ)
  let _ := Φ.analyticChartedSpace hΦ
  have := nonempty_analyticRealization_starSubdivisionAlong Φ hΦ hσ hσ0
  exact IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn ..

/-- The source of `Fan.starSubdivisionAlongPartialDiffeomorph` is the complement of the exceptional
divisor. -/
@[simp]
theorem starSubdivisionAlongPartialDiffeomorph_source (n : ℕ∞ω) :
    (Φ.starSubdivisionAlongPartialDiffeomorph hΦ hσ hσ0 n).source =
      ((Φ.starSubdivisionAlong hΦ hσ).analyticBoundaryComponent
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0))ᶜ := by
  let _ := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
    (Φ.isRegular_starSubdivisionAlong hΦ hσ)
  let _ := Φ.analyticChartedSpace hΦ
  have := nonempty_analyticRealization_starSubdivisionAlong Φ hΦ hσ hσ0
  exact IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source ..

/-- The target of `Fan.starSubdivisionAlongPartialDiffeomorph` is the complement of the orbit
closure of `σ`. -/
@[simp]
theorem starSubdivisionAlongPartialDiffeomorph_target (n : ℕ∞ω) :
    (Φ.starSubdivisionAlongPartialDiffeomorph hΦ hσ hσ0 n).target =
      (closure (Φ.analyticConeOrbit hΦ ⟨σ, hσ⟩))ᶜ := by
  let _ := (Φ.starSubdivisionAlong hΦ hσ).analyticChartedSpace
    (Φ.isRegular_starSubdivisionAlong hΦ hσ)
  let _ := Φ.analyticChartedSpace hΦ
  have := nonempty_analyticRealization_starSubdivisionAlong Φ hΦ hσ hσ0
  exact (IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target ..).trans
    (Φ.image_analyticMap_starSubdivisionAlong_compl hΦ hσ hσ0)

end TauCeti.Toric.Fan
