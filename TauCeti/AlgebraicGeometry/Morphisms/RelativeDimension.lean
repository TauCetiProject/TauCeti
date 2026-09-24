/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Morphisms of relative dimension at most `d`

A morphism of schemes `f : X ⟶ Y` has relative dimension at most `d` if every scheme-theoretic
fibre `f.fiber y` has Krull dimension at most `d`. This is the fibrewise dimension bound in the
definition of a family of curves: a proper, flat, finitely presented morphism of relative
dimension at most one.

The fibre `f.fiber y` is homeomorphic to the set-theoretic fibre `f ⁻¹' {y}`, so the condition is
topological. It is invariant under isomorphisms and local on both the source and the target in
the Zariski topology. For a morphism locally of finite type it is stable under arbitrary base
change: the fibre of a base change at `y'` is the base change of the fibre at the image of `y'`
along the extension of residue fields, which does not change the Krull dimension of a scheme
locally of finite type over a field. Without a finiteness hypothesis the bound is not stable
under base change: `Spec K → Spec k` has relative dimension zero for every field extension
`K / k`, while `Spec (K ⊗[k] K)` can have positive dimension when `K / k` is transcendental.

## Main declarations

* `TauCeti.AlgebraicGeometry.RelativeDimensionLE d f`: every fibre of `f` has Krull dimension at
  most `d`.
* `TauCeti.AlgebraicGeometry.relativeDimensionLE_iff_topologicalKrullDim_preimage_le`: the
  condition in terms of set-theoretic fibres.
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_fiber_inter_eq`: in a fibre of a morphism locally
  of finite type, a nonempty open part of an irreducible component has the dimension of the
  component.
* `TauCeti.AlgebraicGeometry.isOpenEmbedding_fiber`: the fibre of the restriction of a morphism
  to an open subscheme is an open subspace of the fibre of the morphism.
* `TauCeti.AlgebraicGeometry.RelativeDimensionLE.isZariskiLocalAtSource` and
  `TauCeti.AlgebraicGeometry.RelativeDimensionLE.isZariskiLocalAtTarget`: locality.
* `TauCeti.AlgebraicGeometry.RelativeDimensionLE.of_isPullback`: stability under base change of
  morphisms locally of finite type.
* `TauCeti.AlgebraicGeometry.relativeDimensionLE_iff_of_field`: over a field, the condition bounds
  the Krull dimension of the source.

## References

* [Stacks Project, Tag 02NI](https://stacks.math.columbia.edu/tag/02NI)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

public section

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A morphism of schemes `f : X ⟶ Y` has relative dimension at most `d` if every
scheme-theoretic fibre `f.fiber y` has Krull dimension at most `d`. -/
class RelativeDimensionLE (d : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  topologicalKrullDim_fiber_le (y : Y) : topologicalKrullDim (f.fiber y) ≤ d

variable {d e : ℕ} {X Y Z : Scheme.{u}}

/-- A morphism has relative dimension at most `d` if and only if every set-theoretic fibre has
Krull dimension at most `d`. -/
theorem relativeDimensionLE_iff_topologicalKrullDim_preimage_le (f : X ⟶ Y) :
    RelativeDimensionLE d f ↔ ∀ y : Y, topologicalKrullDim (f ⁻¹' {y}) ≤ d := by
  simp_rw [← (f.fiberHomeo _).isHomeomorph.topologicalKrullDim_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

/-- Every set-theoretic fibre of a morphism of relative dimension at most `d` has Krull dimension
at most `d`. -/
theorem RelativeDimensionLE.topologicalKrullDim_preimage_le (f : X ⟶ Y) [RelativeDimensionLE d f]
    (y : Y) : topologicalKrullDim (f ⁻¹' {y}) ≤ d :=
  (relativeDimensionLE_iff_topologicalKrullDim_preimage_le f).mp ‹_› y

/-- A morphism of relative dimension at most `d` has relative dimension at most every `e ≥ d`. -/
theorem RelativeDimensionLE.mono (f : X ⟶ Y) [RelativeDimensionLE d f] (hde : d ≤ e) :
    RelativeDimensionLE e f :=
  ⟨fun y ↦ (topologicalKrullDim_fiber_le y).trans (mod_cast hde)⟩

/-- In a fibre of a morphism locally of finite type, a nonempty open part of an irreducible
component has the dimension of the component. -/
theorem topologicalKrullDim_fiber_inter_eq (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) :
    ∀ C ∈ irreducibleComponents (f.fiber y), ∀ U : Set (f.fiber y), IsOpen U →
      (C ∩ U).Nonempty → topologicalKrullDim ↥(C ∩ U) = topologicalKrullDim C := by
  intro C hC U hU hCU
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
  exact topologicalKrullDim_inter_eq_of_locallyOfFiniteType (K := Y.residueField y)
    (f.fiberToSpecResidueField y) hC.1 (isClosed_of_mem_irreducibleComponents C hC) hU hCU

/-- The fibre over `y` of the restriction of `f` along an open immersion `i` is an open subspace
of the scheme-theoretic fibre of `f` over `y`. -/
theorem isOpenEmbedding_fiber (i : Z ⟶ X) [IsOpenImmersion i] (f : X ⟶ Y) (y : Y) :
    IsOpenEmbedding ((f.fiberHomeo y).symm ∘ (f ⁻¹' {y}).restrictPreimage i) :=
  (f.fiberHomeo y).symm.isOpenEmbedding.comp (i.isOpenEmbedding.restrictPreimage _)

private theorem preimage_comp (i : Z ⟶ X) (f : X ⟶ Y) (s : Set Y) :
    (i ≫ f) ⁻¹' s = i ⁻¹' (f ⁻¹' s) := by
  ext
  simp

/-- Precomposing with an embedding restricts a fibre to a subspace of that fibre. -/
private theorem topologicalKrullDim_preimage_comp_le (i : Z ⟶ X) (hi : IsEmbedding i)
    (f : X ⟶ Y) (y : Y) :
    topologicalKrullDim ((i ≫ f) ⁻¹' {y}) ≤ topologicalKrullDim (f ⁻¹' {y}) := by
  rw [preimage_comp]
  exact (hi.restrictPreimage (f ⁻¹' {y})).isInducing.topologicalKrullDim_le

/-- Precomposing with an embedding whose range contains the fibre over `y` does not change that
fibre. -/
private theorem topologicalKrullDim_preimage_comp_eq (i : Z ⟶ X) (hi : IsEmbedding i)
    (f : X ⟶ Y) (y : Y) (hy : f ⁻¹' {y} ⊆ Set.range i) :
    topologicalKrullDim ((i ≫ f) ⁻¹' {y}) = topologicalKrullDim (f ⁻¹' {y}) := by
  rw [preimage_comp]
  refine IsHomeomorph.topologicalKrullDim_eq _ <| isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨hi.restrictPreimage (f ⁻¹' {y}), fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := hy x.2
  exact ⟨⟨z, by simp [hz]⟩, Subtype.ext hz⟩

/-- Precomposing with a preimmersion, such as an open or closed immersion, preserves the bound on
the relative dimension. -/
instance RelativeDimensionLE.isPreimmersion_comp (i : Z ⟶ X) [IsPreimmersion i] (f : X ⟶ Y)
    [RelativeDimensionLE d f] : RelativeDimensionLE d (i ≫ f) :=
  (relativeDimensionLE_iff_topologicalKrullDim_preimage_le _).mpr fun y ↦
    (topologicalKrullDim_preimage_comp_le i i.isEmbedding f y).trans
      (topologicalKrullDim_preimage_le f y)

/-- Postcomposing with a morphism that is injective on points does not change the relative
dimension. -/
theorem relativeDimensionLE_comp_iff_of_injective (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Function.Injective g) : RelativeDimensionLE d (f ≫ g) ↔ RelativeDimensionLE d f := by
  have hpre (y : Y) : (f ≫ g) ⁻¹' {g y} = f ⁻¹' {y} := by
    ext x
    simp [hg.eq_iff]
  simp_rw [relativeDimensionLE_iff_topologicalKrullDim_preimage_le]
  refine ⟨fun h y ↦ hpre y ▸ h (g y), fun h z ↦ ?_⟩
  by_cases hz : z ∈ Set.range g
  · obtain ⟨y, rfl⟩ := hz
    exact hpre y ▸ h y
  · have : IsEmpty ((f ≫ g) ⁻¹' {z}) := ⟨fun x ↦ hz ⟨f x, by simpa using x.2⟩⟩
    exact (topologicalKrullDim_zero_of_discreteTopology _).trans (mod_cast d.zero_le)

/-- Postcomposing with a preimmersion, such as an open or closed immersion, preserves the bound on
the relative dimension. -/
instance RelativeDimensionLE.comp_isPreimmersion (f : X ⟶ Y) [RelativeDimensionLE d f]
    (g : Y ⟶ Z) [IsPreimmersion g] : RelativeDimensionLE d (f ≫ g) :=
  (relativeDimensionLE_comp_iff_of_injective f g g.isEmbedding.injective).mpr ‹_›

/-- A locally quasi-finite morphism, such as a finite morphism or an immersion, has relative
dimension zero: its fibres are discrete. -/
instance (priority := low) RelativeDimensionLE.of_locallyQuasiFinite (f : X ⟶ Y)
    [LocallyQuasiFinite f] : RelativeDimensionLE 0 f := by
  refine (relativeDimensionLE_iff_topologicalKrullDim_preimage_le f).mpr fun y ↦ ?_
  have := isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton y)
  exact_mod_cast topologicalKrullDim_zero_of_discreteTopology _

/-- Having relative dimension at most `d` is invariant under isomorphisms of arrows. -/
instance RelativeDimensionLE.respectsIso (d : ℕ) :
    MorphismProperty.RespectsIso (@RelativeDimensionLE.{u} d) :=
  MorphismProperty.RespectsIso.mk _ (fun e f (_ : RelativeDimensionLE d f) ↦
    RelativeDimensionLE.isPreimmersion_comp e.hom f)
    (fun e f (_ : RelativeDimensionLE d f) ↦
      RelativeDimensionLE.comp_isPreimmersion f e.hom)

/-- Having relative dimension at most `d` is local on the source. -/
instance RelativeDimensionLE.isZariskiLocalAtSource (d : ℕ) :
    IsZariskiLocalAtSource (@RelativeDimensionLE.{u} d) := by
  refine .mk' (fun f U hf ↦ ?_) fun f ι U hU hf ↦ ?_
  · have : RelativeDimensionLE d f := hf
    exact RelativeDimensionLE.isPreimmersion_comp U.ι f
  refine (relativeDimensionLE_iff_topologicalKrullDim_preimage_le f).mpr fun y ↦ ?_
  have hcover (x : f ⁻¹' {y}) : ∃ i, x ∈ Set.range ((f ⁻¹' {y}).restrictPreimage (U i).ι) := by
    have hx : x.1 ∈ iSup U := by
      rw [hU]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨i, ⟨⟨x.1, hi⟩, x.2⟩, rfl⟩
  rw [topologicalKrullDim_eq_iSup_of_isOpenEmbedding _
    (fun i ↦ (U i).ι.isOpenEmbedding.restrictPreimage _) hcover]
  refine iSup_le fun i ↦ ?_
  have := hf i
  rw [← preimage_comp]
  exact topologicalKrullDim_preimage_le _ y

/-- Having relative dimension at most `d` is local on the target. -/
instance RelativeDimensionLE.isZariskiLocalAtTarget (d : ℕ) :
    IsZariskiLocalAtTarget (@RelativeDimensionLE.{u} d) := by
  refine .mk' (fun f U (_ : RelativeDimensionLE d f) ↦ ?_) fun f ι U hU hf ↦ ?_
  · rw [← relativeDimensionLE_comp_iff_of_injective _ U.ι U.ι.isEmbedding.injective,
      morphismRestrict_ι]
    infer_instance
  refine (relativeDimensionLE_iff_topologicalKrullDim_preimage_le f).mpr fun y ↦ ?_
  have hy : y ∈ iSup U := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  have : RelativeDimensionLE d ((f ⁻¹ᵁ U i).ι ≫ f) := by
    rw [← morphismRestrict_ι, relativeDimensionLE_comp_iff_of_injective _ _
      (U i).ι.isEmbedding.injective]
    exact hf i
  rw [← topologicalKrullDim_preimage_comp_eq (f ⁻¹ᵁ U i).ι (f ⁻¹ᵁ U i).ι.isEmbedding f y
    fun x hx ↦ by simpa [Set.mem_singleton_iff.mp hx] using hi]
  exact topologicalKrullDim_preimage_le _ y

/-- Having relative dimension at most `d` is stable under base change of morphisms locally of
finite type. -/
theorem RelativeDimensionLE.of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [LocallyOfFiniteType f]
    [RelativeDimensionLE d f] : RelativeDimensionLE d snd := by
  refine ⟨fun y ↦ ?_⟩
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Z.fromSpecResidueField (g y))))
  let := (g.residueFieldMap y).hom.toAlgebra
  -- The fibre of `snd` at `y` is the base change of the fibre of `f` at `g y` along the
  -- extension of residue fields `κ(g y) → κ(y)`. The pullback square of Mathlib's
  -- `isPullback_fiberToSpecResidueField_of_isPullback` has `snd.fiber y` as its corner, since
  -- `Scheme.Hom.fiber` is defined as that pullback.
  exact ((isPullback_fiberToSpecResidueField_of_isPullback h y).isoPullback.hom.homeomorph
    |>.isHomeomorph.topologicalKrullDim_eq).trans_le <|
    (topologicalKrullDim_pullback_Spec_map_of_field (K := Z.residueField (g y))
      (L := Y.residueField y) (f.fiberToSpecResidueField (g y))).trans_le
      (topologicalKrullDim_fiber_le (g y))

/-- The base change `pullback.snd f g` of a morphism `f` locally of finite type has relative
dimension at most that of `f`. -/
instance RelativeDimensionLE.pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFiniteType f]
    [RelativeDimensionLE d f] : RelativeDimensionLE d (pullback.snd f g) :=
  .of_isPullback (.of_hasPullback f g)

/-- The base change `pullback.fst f g` of a morphism `g` locally of finite type has relative
dimension at most that of `g`. -/
instance RelativeDimensionLE.pullback_fst (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFiniteType g]
    [RelativeDimensionLE d g] : RelativeDimensionLE d (pullback.fst f g) :=
  .of_isPullback (IsPullback.of_hasPullback f g).flip

/-- A scheme over a field has relative dimension at most `d` over it if and only if its Krull
dimension is at most `d`. -/
theorem relativeDimensionLE_iff_of_field {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) :
    RelativeDimensionLE d f ↔ topologicalKrullDim X ≤ d := by
  have hpre (y : Spec (.of K)) : f ⁻¹' {y} = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Subsingleton.elim (α := PrimeSpectrum K) _ _
  have hdim (y : Spec (.of K)) : topologicalKrullDim (f ⁻¹' {y}) = topologicalKrullDim X := by
    rw [hpre]
    exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  simp_rw [relativeDimensionLE_iff_topologicalKrullDim_preimage_le, hdim]
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  exact ⟨fun h ↦ h y, fun h _ ↦ h⟩

end AlgebraicGeometry

end TauCeti
