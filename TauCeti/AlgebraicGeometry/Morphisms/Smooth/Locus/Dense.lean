/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Frobenius.Perfection
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.Topology.Sober

/-!
# Dense smooth loci over a field

For a scheme `X` locally of finite presentation over a field `k`, the smooth locus `X_sm` of
`X ⟶ Spec k` is dense exactly when `X` is geometrically reduced over `k`. This is the setting
of the Nash blowup: a reduced scheme locally of finite type over `k` whose smooth locus is dense.

The forward direction uses no hypothesis on `k`. The inclusion `X_sm ⟶ X` is quasi-compact, since
`X` is locally Noetherian, and dominant, so it is scheme-theoretically dominant on the reduced
`X`. Its base change along `Spec K ⟶ Spec k` is again scheme-theoretically dominant, `Spec K` being
flat over `Spec k`, and its source `X_sm ×_k K` is reduced since smooth morphisms are geometrically
reduced. Hence `X ×_k K` is reduced.

For the converse, over a perfect field this is Mathlib's
`Scheme.Hom.dense_smoothLocus_of_perfectField`. In characteristic `p`, let `k'` be the perfect
closure of `k`. The projection `X ×_k k' ⟶ X` is a universal homeomorphism, the smooth locus `W'`
of the reduced `X ×_k k'` is dense, and its image `W` is a dense open of `X` with preimage `W'`.
So `W ×_k k' ≅ W'` is smooth over `k'`, and smoothness descends along `Spec k' ⟶ Spec k`.

In a locally Noetherian scheme a dense open, such as a dense smooth locus, contains the generic
point of every irreducible component and meets every irreducible component in a dense subset.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smooth_ι_comp_iff_le_smoothLocus`: `f` is smooth on an open `U`
  exactly when `U` lies in the smooth locus of `f`.
* `AlgebraicGeometry.Scheme.Hom.geometricallyReduced_of_dense_smoothLocus` and
  `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_geometricallyReduced`: the two directions,
  combined in `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_iff_geometricallyReduced`.
* `AlgebraicGeometry.Scheme.Opens.genericPoints_subset_of_dense` and
  `AlgebraicGeometry.Scheme.Opens.closure_inter_eq_of_dense`: a dense open of a locally Noetherian
  scheme contains every component-generic point and is dense in every irreducible component.

## References

* The Stacks Project, *Varieties*, Lemma 33.25.7 (Tag 056V).
-/

public section

open CategoryTheory Limits Topology TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- In a locally Noetherian scheme, a dense open contains the generic point of every irreducible
component. -/
theorem Scheme.Opens.genericPoints_subset_of_dense {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X)) : genericPoints X ⊆ U :=
  hU.genericPoints_subset_of_nonempty_interior
    (fun _ hx ↦ TauCeti.AlgebraicGeometry.nonempty_interior_of_mem_irreducibleComponents hx)
    U.isOpen.stableUnderGeneralization

/-- In a locally Noetherian scheme, a dense open `U` meets every irreducible component `C` in a
dense subset of `C`. -/
theorem Scheme.Opens.closure_inter_eq_of_dense {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X)) {C : Set X} (hC : C ∈ irreducibleComponents X) :
    closure ((U : Set X) ∩ C) = C := by
  have hCc := isClosed_of_mem_irreducibleComponents C hC
  have hη := hC.1.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hη
  refine subset_antisymm ((closure_mono Set.inter_subset_right).trans hCc.closure_subset) ?_
  have hηU : hC.1.genericPoint ∈ U :=
    U.genericPoints_subset_of_dense hU (show closure {_} ∈ _ by rwa [hη.def])
  calc C = closure {hC.1.genericPoint} := hη.def.symm
    _ ⊆ closure ((U : Set X) ∩ C) := closure_mono (Set.singleton_subset_iff.mpr ⟨hηU, hη.mem⟩)

namespace Scheme.Hom

/-- A morphism `f` locally of finite presentation is smooth on an open `U` exactly when `U` lies in
the smooth locus of `f`. -/
theorem smooth_ι_comp_iff_le_smoothLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (U : X.Opens) :
    Smooth (U.ι ≫ f) ↔ U ≤ f.smoothLocus := by
  rw [← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq, ← top_le_iff]
  exact ⟨fun h x hx ↦ h (Set.mem_univ (⟨x, hx⟩ : U)), fun h x _ ↦ h x.property⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Every morphism from the spectrum of a ring to the spectrum of a field is flat. -/
private theorem flat_of_field {R : CommRingCat.{u}} (y : Spec R ⟶ Spec (.of k)) : Flat y := by
  rw [← Spec.map_preimage y, Flat.SpecMap_iff]
  algebraize [(Spec.preimage y).hom]
  exact (inferInstance : Module.Flat k R)

/-- A geometrically reduced scheme over a field is reduced. -/
private theorem isReduced_of_geometricallyReduced [GeometricallyReduced f] : IsReduced X :=
  GeometricallyReduced.geometrically_isReduced (f := f) (𝟙 _) (𝟙 X) f
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

variable [LocallyOfFinitePresentation f]

/-- **A reduced scheme over a field with dense smooth locus is geometrically reduced.** -/
theorem geometricallyReduced_of_dense_smoothLocus [IsReduced X]
    (h : Dense (f.smoothLocus : Set X)) : GeometricallyReduced f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsDominant f.smoothLocus.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : IsSchemeTheoreticallyDominant f.smoothLocus.ι := .of_isDominant _
  refine ⟨fun K _ y Z fst snd H ↦ ?_⟩
  have : Flat y := flat_of_field y
  have : Flat fst := MorphismProperty.of_isPullback H.flip ‹_›
  have H' := isPullback_morphismRestrict fst f.smoothLocus
  have : QuasiCompact (fst ⁻¹ᵁ f.smoothLocus).ι :=
    MorphismProperty.of_isPullback H' (inferInstanceAs (QuasiCompact f.smoothLocus.ι))
  have : IsSchemeTheoreticallyDominant (fst ⁻¹ᵁ f.smoothLocus).ι := .of_isPullback H'
  have : IsReduced (fst ⁻¹ᵁ f.smoothLocus) :=
    GeometricallyReduced.geometrically_isReduced (f := f.smoothLocus.ι ≫ f) y _ _
      (H'.paste_vert H)
  exact IsSchemeTheoreticallyDominant.isReduced (fst ⁻¹ᵁ f.smoothLocus).ι

/-- If `X` is geometrically reduced over `k` and `Spec K ⟶ Spec k` is a universal homeomorphism
with `K` perfect, the smooth locus of `X ⟶ Spec k` is dense. -/
private theorem dense_smoothLocus_of_isUniversalHomeomorphism [GeometricallyReduced f]
    {K : Type u} [Field K] [PerfectField K] (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    [IsUniversalHomeomorphism (Spec.map φ)] : Dense (f.smoothLocus : Set X) := by
  let y := Spec.map φ
  let p := pullback.snd y f
  let q := pullback.fst y f
  have H : IsPullback p q f y := (IsPullback.of_hasPullback y f).flip
  have : IsReduced (pullback y f) := GeometricallyReduced.geometrically_isReduced y p q H
  have hp : IsHomeomorph p := IsUniversalHomeomorphism.isHomeomorph p
  let W : X.Opens := ⟨p '' q.smoothLocus, hp.isOpenMap _ q.smoothLocus.isOpen⟩
  have hpre : p ⁻¹ᵁ W = q.smoothLocus :=
    TopologicalSpace.Opens.ext (hp.injective.preimage_image _)
  have hW : Dense (W : Set X) :=
    hp.surjective.denseRange.dense_image hp.continuous q.dense_smoothLocus_of_perfectField
  refine hW.mono ((smooth_ι_comp_iff_le_smoothLocus f W).mp ?_)
  have hsm : Smooth ((p ⁻¹ᵁ W).ι ≫ q) := (smooth_ι_comp_iff_le_smoothLocus q _).mpr hpre.le
  have : Flat y := flat_of_field y
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((isPullback_morphismRestrict p W).paste_vert H).flip ⟨⟨inferInstance, ‹_›⟩, inferInstance⟩
    hsm

/-- **A geometrically reduced scheme over a field has dense smooth locus.** -/
theorem dense_smoothLocus_of_geometricallyReduced [GeometricallyReduced f] :
    Dense (f.smoothLocus : Set X) := by
  have := isReduced_of_geometricallyReduced f
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · have : Fact p.Prime := ⟨hpp⟩
    exact dense_smoothLocus_of_isUniversalHomeomorphism f
      (CommRingCat.ofHom (PerfectClosure.of k p))
  · have : CharZero k := CharP.charP_to_charZero k
    exact f.dense_smoothLocus_of_perfectField

/-- **Dense smooth locus.** A reduced scheme locally of finite presentation over a field `k` has
dense smooth locus if and only if it is geometrically reduced over `k`. -/
theorem dense_smoothLocus_iff_geometricallyReduced [IsReduced X] :
    Dense (f.smoothLocus : Set X) ↔ GeometricallyReduced f :=
  ⟨f.geometricallyReduced_of_dense_smoothLocus, fun _ ↦ f.dense_smoothLocus_of_geometricallyReduced⟩

end Scheme.Hom

end AlgebraicGeometry
