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

/-!
# Dense smooth loci over a field

For a reduced scheme `X` locally of finite presentation over a field `k`, the smooth locus `X_sm`
of `X ⟶ Spec k` is dense exactly when `X` is geometrically reduced over `k`; the direction
geometrically reduced ⇒ dense needs no reducedness. This is the setting of the Nash blowup: a
reduced scheme locally of finite type over `k` whose smooth locus is dense.

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

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.geometricallyReduced_of_dense_smoothLocus` and
  `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_geometricallyReduced`: the two directions,
  combined in `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_iff_geometricallyReduced`.

## References

* The Stacks Project, *Varieties*, Lemma 33.25.7 (Tag 056V).
-/

public section

open CategoryTheory Limits Topology TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

variable [LocallyOfFinitePresentation f]

/-- **A reduced scheme over a field with dense smooth locus is geometrically reduced.** -/
theorem geometricallyReduced_of_dense_smoothLocus [IsReduced X]
    (h : Dense (f.smoothLocus : Set X)) : GeometricallyReduced f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsDominant f.smoothLocus.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : IsSchemeTheoreticallyDominant f.smoothLocus.ι := .of_isDominant _
  refine ⟨fun K _ y Z fst snd H ↦ ?_⟩
  have : Flat fst := MorphismProperty.of_isPullback H.flip inferInstance
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
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((isPullback_morphismRestrict p W).paste_vert H).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    hsm

/-- **A geometrically reduced scheme over a field has dense smooth locus.** -/
theorem dense_smoothLocus_of_geometricallyReduced [GeometricallyReduced f] :
    Dense (f.smoothLocus : Set X) := by
  have := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
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
