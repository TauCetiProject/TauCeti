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
the Noetherian fibres. Keeping it in the predicate makes the generally useful implication to
`RelativeDimensionLE` available without silently assuming local finite type.

Locally quasi-finite morphisms supply the basic example: their fibres are discrete and therefore
pure zero-dimensional. The property is invariant under isomorphisms of arrows.

## Main declarations

* `TauCeti.AlgebraicGeometry.PureRelativeDimension d f`: every nonempty fibre of `f` is
  equidimensional of dimension `d`.
* `TauCeti.AlgebraicGeometry.PureRelativeDimension.isPureDimensional_fiber`: the
  scheme-theoretic fibre formulation.
* `TauCeti.AlgebraicGeometry.PureRelativeDimension.of_locallyQuasiFinite`: locally quasi-finite
  morphisms have pure relative dimension zero.
* `TauCeti.AlgebraicGeometry.pureRelativeDimension_iff_of_field`: over a field, pure relative
  dimension is pure dimension of the source together with the dimension bound.

## References

* [Stacks Project, Tag 02NI](https://stacks.math.columbia.edu/tag/02NI)
-/

public section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

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

namespace PureRelativeDimension

/-- Every set-theoretic fibre of a morphism of pure relative dimension `d` is pure-dimensional
of dimension `d`. -/
theorem isPureDimensional_setFiber (f : X ⟶ Y) [PureRelativeDimension d f] (y : Y) :
    IsPureDimensional d (f ⁻¹' {y}) :=
  PureRelativeDimension.isPureDimensional_preimage (f := f) y

/-- Every scheme-theoretic fibre of a morphism of pure relative dimension `d` is
pure-dimensional of dimension `d`. -/
theorem isPureDimensional_fiber (f : X ⟶ Y) [PureRelativeDimension d f] (y : Y) :
    IsPureDimensional d (f.fiber y) :=
  (f.fiberHomeo y).isPureDimensional_iff.mpr
    (isPureDimensional_setFiber f y)

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
    isPureDimensional_setFiber (d := d) f y
  have he : (e.hom ⁻¹' (f ⁻¹' {y})) ≃ₜ (f ⁻¹' {y}) :=
    e.hom.homeomorph.isEmbedding.homeomorphOfSubsetRange (by simp)
  have hpure : IsPureDimensional d (e.hom ⁻¹' (f ⁻¹' {y})) :=
    he.isPureDimensional_iff.mpr h
  have hpre : (e.hom ≫ f) ⁻¹' {y} = e.hom ⁻¹' (f ⁻¹' {y}) := by
    ext x
    rfl
  rw [hpre]
  exact hpure

private theorem postcomp_iso (f : X ⟶ Y) (e : Y ≅ Z) [PureRelativeDimension d f] :
    PureRelativeDimension d (f ≫ e.hom) := by
  refine { toRelativeDimensionLE := inferInstance, isPureDimensional_preimage := fun z ↦ ?_ }
  have hpre : (f ≫ e.hom) ⁻¹' {z} = f ⁻¹' {e.inv z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change e.hom (f x) = z ↔ f x = e.inv z
    constructor
    · intro h
      apply_fun e.inv at h
      simpa using h
    · intro h
      simp [h]
  rw [hpre]
  exact isPureDimensional_setFiber f (e.inv z)

/-- Having pure relative dimension `d` is invariant under isomorphisms of arrows. -/
instance respectsIso (d : ℕ) :
    MorphismProperty.RespectsIso (@PureRelativeDimension.{u} d) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f (_ : PureRelativeDimension d f) ↦ precomp_iso e f)
    (fun e f (_ : PureRelativeDimension d f) ↦ postcomp_iso f e)

end PureRelativeDimension

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
