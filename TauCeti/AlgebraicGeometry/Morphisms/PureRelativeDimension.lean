/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
public import TauCeti.Topology.PureDimension

/-!
# Morphisms of pure relative dimension

A morphism of schemes has pure relative dimension `d` when it has relative dimension at most `d`
and every irreducible component of every nonempty fibre has dimension exactly `d`. Empty fibres
impose no component condition. The definition is expressed using set-theoretic fibres; Mathlib's
homeomorphism between a scheme-theoretic fibre and the corresponding set-theoretic fibre gives the
equivalent scheme-theoretic formulation.

The explicit dimension bound is included because the definition makes sense without a finiteness
hypothesis. For locally finite type morphisms it follows mathematically from equidimensionality of
the locally Noetherian fibres. Keeping it in the predicate makes the generally useful implication
to `RelativeDimensionLE` available without silently assuming local finite type.

Locally quasi-finite morphisms supply the basic example: their fibres are discrete and therefore
pure zero-dimensional. The property is invariant under isomorphisms of arrows and local on the
target. For morphisms locally of finite type it is also local on the source: the fibres are then
locally of finite type over a field, where a nonempty open part of an irreducible component has
the dimension of the component, so pure-dimensionality of a fibre can be tested on an open cover.
Without the finiteness hypothesis locality on the source fails already for
`Spec k[x]_(x) → Spec k`: its only fibre is irreducible of dimension one, while its open generic
point has dimension zero.

## Main declarations

* `TauCeti.AlgebraicGeometry.PureRelativeDimension d f`: `f` has relative dimension at most `d`,
  and every fibre is pure-dimensional of dimension `d`.
* `pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber`: the
  scheme-theoretic fibre characterization.
* `TauCeti.AlgebraicGeometry.PureRelativeDimension.isPureDimensional_fiber`: the
  scheme-theoretic fibre formulation.
* `TauCeti.AlgebraicGeometry.PureRelativeDimension.of_locallyQuasiFinite`: locally quasi-finite
  morphisms have pure relative dimension zero.
* `TauCeti.AlgebraicGeometry.pureRelativeDimension_iff_of_field`: over a field, pure relative
  dimension is pure dimension of the source together with the dimension bound.
* `TauCeti.AlgebraicGeometry.pureRelativeDimension_comp_iff_of_injective`: postcomposition with a
  morphism injective on points does not change pure relative dimension.
* `TauCeti.AlgebraicGeometry.PureRelativeDimension.isZariskiLocalAtTarget`: locality on the target.
* `TauCeti.AlgebraicGeometry.PureRelativeDimension.isOpenImmersion_comp` and
  `TauCeti.AlgebraicGeometry.pureRelativeDimension_iff_of_openCover`: locality on the source for
  morphisms locally of finite type.

## References

* [Stacks Project, Tag 02NI](https://stacks.math.columbia.edu/tag/02NI)
-/

public section

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A morphism of schemes has pure relative dimension `d` if it has relative dimension at most
`d` and every irreducible component of every set-theoretic fibre has Krull dimension `d`. -/
@[mk_iff]
class PureRelativeDimension (d : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
    extends RelativeDimensionLE d f where
  isPureDimensional_preimage (y : Y) : IsPureDimensional d (f ⁻¹' {y})

variable {d : ℕ} {X Y Z : Scheme.{u}}

/-- A morphism has pure relative dimension `d` if and only if it has relative dimension at most
`d` and every scheme-theoretic fibre is pure-dimensional of dimension `d`. -/
theorem pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber (f : X ⟶ Y) :
    PureRelativeDimension d f ↔
      RelativeDimensionLE d f ∧ ∀ y : Y, IsPureDimensional d (f.fiber y) := by
  constructor
  · intro h
    exact ⟨h.toRelativeDimensionLE, fun y ↦
      (f.fiberHomeo y).isPureDimensional_iff.mpr (h.isPureDimensional_preimage y)⟩
  · rintro ⟨hle, hpure⟩
    let _ : RelativeDimensionLE d f := hle
    exact ⟨fun y ↦ (f.fiberHomeo y).isPureDimensional_iff.mp (hpure y)⟩

private theorem preimage_comp (i : Z ⟶ X) (f : X ⟶ Y) (s : Set Y) :
    (i ≫ f) ⁻¹' s = i ⁻¹' (f ⁻¹' s) := by
  ext
  simp

/-- Precomposing with an embedding whose range contains the fibre over `y` does not change that
fibre up to homeomorphism. -/
private theorem isPureDimensional_preimage_comp_iff (i : Z ⟶ X) (hi : IsEmbedding i) (f : X ⟶ Y)
    (y : Y) (hy : f ⁻¹' {y} ⊆ Set.range i) :
    IsPureDimensional d ↥((i ≫ f) ⁻¹' {y}) ↔ IsPureDimensional d ↥(f ⁻¹' {y}) := by
  rw [preimage_comp]
  exact (hi.homeomorphOfSubsetRange hy).isPureDimensional_iff

/-- Postcomposing with a morphism that is injective on points does not change the pure relative
dimension. -/
theorem pureRelativeDimension_comp_iff_of_injective (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Function.Injective g) : PureRelativeDimension d (f ≫ g) ↔ PureRelativeDimension d f := by
  have hpre (y : Y) : (f ≫ g) ⁻¹' {g y} = f ⁻¹' {y} := by
    ext x
    simp [hg.eq_iff]
  simp_rw [pureRelativeDimension_iff, relativeDimensionLE_comp_iff_of_injective f g hg]
  refine and_congr_right fun _ ↦ ⟨fun h y ↦ hpre y ▸ h (g y), fun h z ↦ ?_⟩
  by_cases hz : z ∈ Set.range g
  · obtain ⟨y, rfl⟩ := hz
    exact hpre y ▸ h y
  · have : IsEmpty ((f ≫ g) ⁻¹' {z}) := ⟨fun x ↦ hz ⟨f x, by simpa using x.2⟩⟩
    exact isPureDimensional_of_isEmpty _ _

namespace PureRelativeDimension

/-- Every scheme-theoretic fibre of a morphism of pure relative dimension `d` is
pure-dimensional of dimension `d`. -/
theorem isPureDimensional_fiber (f : X ⟶ Y) [PureRelativeDimension d f] (y : Y) :
    IsPureDimensional d (f.fiber y) :=
  ((pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber f).mp
    inferInstance).2 y

/-- A locally quasi-finite morphism has pure relative dimension zero. -/
instance (priority := low) of_locallyQuasiFinite (f : X ⟶ Y) [LocallyQuasiFinite f] :
    PureRelativeDimension 0 f where
  isPureDimensional_preimage y := by
    let hdisc : DiscreteTopology (f ⁻¹' {y}) :=
      isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton y)
    exact @isPureDimensional_zero_of_discreteTopology (f ⁻¹' {y}) _ hdisc

private theorem precomp_iso (e : Z ≅ X) (f : X ⟶ Y) [PureRelativeDimension d f] :
    PureRelativeDimension d (e.hom ≫ f) := by
  refine { toRelativeDimensionLE := inferInstance, isPureDimensional_preimage := fun y ↦ ?_ }
  have h : IsPureDimensional d (f ⁻¹' {y}) :=
    PureRelativeDimension.isPureDimensional_preimage (f := f) y
  have he : (e.hom ⁻¹' (f ⁻¹' {y})) ≃ₜ (f ⁻¹' {y}) :=
    e.hom.homeomorph.isEmbedding.homeomorphOfSubsetRange (by simp)
  have hpure : IsPureDimensional d (e.hom ⁻¹' (f ⁻¹' {y})) :=
    he.isPureDimensional_iff.mpr h
  have hpre : (e.hom ≫ f) ⁻¹' {y} = e.hom ⁻¹' (f ⁻¹' {y}) := by
    rw [← Set.preimage_comp]
    congr 1
  rw [hpre]
  exact hpure

/-- Having pure relative dimension `d` is invariant under isomorphisms of arrows. -/
instance respectsIso (d : ℕ) :
    MorphismProperty.RespectsIso (@PureRelativeDimension.{u} d) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f (_ : PureRelativeDimension d f) ↦ precomp_iso e f)
    (fun e f (_ : PureRelativeDimension d f) ↦
      (pureRelativeDimension_comp_iff_of_injective f e.hom e.hom.isEmbedding.injective).mpr ‹_›)

/-- Precomposing a morphism locally of finite type with an open immersion preserves pure relative
dimension. -/
instance isOpenImmersion_comp (i : Z ⟶ X) [IsOpenImmersion i] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [PureRelativeDimension d f] : PureRelativeDimension d (i ≫ f) where
  isPureDimensional_preimage y := by
    rw [preimage_comp]
    exact (isPureDimensional_fiber f y).of_isOpenEmbedding
      (topologicalKrullDim_fiber_inter_eq f y) (isOpenEmbedding_fiber i f y)

/-- Having pure relative dimension `d` is local on the target. -/
instance isZariskiLocalAtTarget (d : ℕ) :
    IsZariskiLocalAtTarget (@PureRelativeDimension.{u} d) := by
  refine .mk' (fun f U (_ : PureRelativeDimension d f) ↦ ?_) fun f ι U hU hf ↦ ?_
  · rw [← pureRelativeDimension_comp_iff_of_injective _ U.ι U.ι.isEmbedding.injective,
      morphismRestrict_ι]
    refine { isPureDimensional_preimage := fun y ↦ ?_ }
    by_cases hy : y ∈ U
    · rw [isPureDimensional_preimage_comp_iff _ (f ⁻¹ᵁ U).ι.isEmbedding f y
        fun x hx ↦ ⟨⟨x, by simpa [Set.mem_singleton_iff.mp hx] using hy⟩, rfl⟩]
      exact isPureDimensional_preimage y
    · -- A point of `f ⁻¹ᵁ U` maps into `U`, so nothing in it lies over `y`.
      have : IsEmpty (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹' {y}) :=
        ⟨fun x ↦ hy (by simpa [preimage_comp] using x.2 ▸ x.1.2)⟩
      exact isPureDimensional_of_isEmpty _ _
  have : RelativeDimensionLE d f :=
    IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ (hf i).toRelativeDimensionLE
  refine { isPureDimensional_preimage := fun y ↦ ?_ }
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : y ∈ iSup U)
  have : PureRelativeDimension d ((f ⁻¹ᵁ U i).ι ≫ f) := by
    rw [← morphismRestrict_ι, pureRelativeDimension_comp_iff_of_injective _ _
      (U i).ι.isEmbedding.injective]
    exact hf i
  rw [← isPureDimensional_preimage_comp_iff _ (f ⁻¹ᵁ U i).ι.isEmbedding f y
    fun x hx ↦ ⟨⟨x, by simpa [Set.mem_singleton_iff.mp hx] using hi⟩, rfl⟩]
  exact isPureDimensional_preimage y

end PureRelativeDimension

/-- A morphism locally of finite type has pure relative dimension `d` exactly when its
restrictions to the members of an open cover of the source do. -/
theorem pureRelativeDimension_iff_of_openCover (f : X ⟶ Y) [LocallyOfFiniteType f]
    (𝒰 : X.OpenCover) : PureRelativeDimension d f ↔ ∀ i, PureRelativeDimension d (𝒰.f i ≫ f) := by
  refine ⟨fun _ i ↦ inferInstance, fun h ↦ ?_⟩
  have : RelativeDimensionLE d f :=
    (IsZariskiLocalAtSource.iff_of_openCover (P := @RelativeDimensionLE d) 𝒰).mpr
      fun i ↦ (h i).toRelativeDimensionLE
  refine { isPureDimensional_preimage := fun y ↦ ?_ }
  -- The fibres of the restrictions are open subspaces covering the fibre of `f`.
  rw [← (f.fiberHomeo y).isPureDimensional_iff, isPureDimensional_iff_forall_of_isOpenEmbedding
    (topologicalKrullDim_fiber_inter_eq f y) _ (fun i ↦ isOpenEmbedding_fiber (𝒰.f i) f y)]
  · intro i
    rw [← preimage_comp]
    exact (h i).isPureDimensional_preimage y
  · intro p
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq (f.fiberHomeo y p).1
    refine ⟨i, ⟨z, by simpa [hz] using (f.fiberHomeo y p).2⟩, ?_⟩
    apply (f.fiberHomeo y).injective
    ext
    simpa using hz

/-- Over a field, a morphism has pure relative dimension `d` exactly when its source is
pure-dimensional of dimension `d` and the morphism has relative dimension at most `d`. -/
theorem pureRelativeDimension_iff_of_field {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) :
    PureRelativeDimension d f ↔ RelativeDimensionLE d f ∧ IsPureDimensional d X := by
  have hpre (y : Spec (.of K)) : f ⁻¹' {y} = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Subsingleton.elim (f x) y
  constructor
  · intro h
    refine ⟨h.toRelativeDimensionLE, ?_⟩
    obtain ⟨y⟩ : Nonempty (Spec (.of K)) := inferInstance
    have hpure := h.isPureDimensional_preimage y
    rw [hpre y] at hpure
    exact (Homeomorph.Set.univ X).isPureDimensional_iff.mp hpure
  · rintro ⟨hle, hpure⟩
    refine { toRelativeDimensionLE := hle, isPureDimensional_preimage := fun y ↦ ?_ }
    rw [hpre y]
    exact (Homeomorph.Set.univ X).isPureDimensional_iff.mpr hpure

end AlgebraicGeometry

end TauCeti
