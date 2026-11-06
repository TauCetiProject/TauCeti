/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Groupoid

/-!
# Composition in the affine Weierstrass groupoid

The scheme of composable arrows is `Spec (ChangeRing ArrowRing)`. Its two projections
form a fibre product of the target and source maps, not merely a parametrization on
field-valued points. The coproduct of the Weierstrass Hopf algebroid therefore defines
composition of scheme-valued arrows. This file proves its source, target, identity,
inverse and associativity laws.

The first projection selects the first arrow. Thus a pair with changes `C₁, C₂`
composes to the change `C₂ * C₁`, in the native left-action convention. All constructions
retain arbitrary coefficient rings, including nilpotents and the zero ring.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the
  Weierstrass groupoid and its Hopf algebroid.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TauCeti.WeierstrassHopfAlgebroid

open TauCeti.WeierstrassChange TauCeti.WeierstrassChange.ChangeRing

/-- The scheme of two composable Weierstrass arrows. -/
abbrev ComposablePairs := Spec (.of (ChangeRing ArrowRing))

/-- The first arrow of a composable pair. -/
def first : ComposablePairs ⟶ Spec (.of ArrowRing) :=
  Spec.map (CommRingCat.ofHom (algebraMap ArrowRing (ChangeRing ArrowRing)))

/-- The second arrow of a composable pair. -/
def second : ComposablePairs ⟶ Spec (.of ArrowRing) :=
  Spec.map (CommRingCat.ofHom (ChangeRing.map rightUnit))

/-- The composable-pair scheme is the fibre product of target and source. -/
theorem isPullback_first_second : IsPullback first second target source := by
  simpa only [first, second, target_def, source_def] using
    isPullback_SpecMap_of_isPushout _ _ _ _ (ChangeRing.isPushout rightUnit)

/-- The target of the first arrow equals the source of the second. -/
@[reassoc (attr := simp)]
theorem first_target : first ≫ target = second ≫ source :=
  isPullback_first_second.w

/-- Composition of a composable pair, induced by the Hopf-algebroid coproduct. -/
def composition : ComposablePairs ⟶ Spec (.of ArrowRing) :=
  Spec.map (CommRingCat.ofHom coproduct)

/-- Composition has the source of the first arrow. -/
@[reassoc (attr := simp)]
theorem composition_source : composition ≫ source = first ≫ source := by
  simp only [composition, first, source_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coproduct_comp_algebraMap]

/-- Composition has the target of the second arrow. -/
@[reassoc (attr := simp)]
theorem composition_target : composition ≫ target = second ≫ target := by
  simp only [composition, second, target_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coproduct_comp_rightUnit]

/-- Pair an identity arrow with the arrow following it. -/
def identityFirst : Spec (.of ArrowRing) ⟶ ComposablePairs :=
  isPullback_first_second.lift (source ≫ identity) (𝟙 _) (by simp)

/-- Pair an arrow with the identity at its target. -/
def identitySecond : Spec (.of ArrowRing) ⟶ ComposablePairs :=
  isPullback_first_second.lift (𝟙 _) (target ≫ identity) (by simp)

/-- The identity-first pair starts at the source identity. -/
@[reassoc (attr := simp)]
theorem identityFirst_first : identityFirst ≫ first = source ≫ identity :=
  isPullback_first_second.lift_fst _ _ _

/-- The identity-first pair ends with the original arrow. -/
@[reassoc (attr := simp)]
theorem identityFirst_second : identityFirst ≫ second = 𝟙 _ :=
  isPullback_first_second.lift_snd _ _ _

/-- The identity-second pair starts with the original arrow. -/
@[reassoc (attr := simp)]
theorem identitySecond_first : identitySecond ≫ first = 𝟙 _ :=
  isPullback_first_second.lift_fst _ _ _

/-- The identity-second pair ends at the target identity. -/
@[reassoc (attr := simp)]
theorem identitySecond_second : identitySecond ≫ second = target ≫ identity :=
  isPullback_first_second.lift_snd _ _ _

/-- Composing an identity followed by an arrow gives that arrow. -/
@[reassoc (attr := simp)]
theorem identityFirst_composition : identityFirst ≫ composition = 𝟙 _ := by
  let k := pushoutLift rightUnit
    ⟨((algebraMap (MvPolynomial WeierstrassCurve.Coeff ℤ) ArrowRing).comp counit,
      RingHom.id ArrowRing), by simp [RingHom.comp_assoc]⟩
  have hk : identityFirst = Spec.map (CommRingCat.ofHom k) := by
    apply isPullback_first_second.hom_ext
    · rw [identityFirst_first]
      simp [first, k, source_def, identity_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [identityFirst_second]
      simp [second, k, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hk, composition, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simpa only [k, CommRingCat.ofHom_id, Spec.map_id] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) pushoutLift_counit_id_comp_coproduct

/-- Composing an arrow followed by an identity gives that arrow. -/
@[reassoc (attr := simp)]
theorem identitySecond_composition : identitySecond ≫ composition = 𝟙 _ := by
  let k := pushoutLift rightUnit
    ⟨(RingHom.id ArrowRing, rightUnit.comp counit), by simp [RingHom.comp_assoc]⟩
  have hk : identitySecond = Spec.map (CommRingCat.ofHom k) := by
    apply isPullback_first_second.hom_ext
    · rw [identitySecond_first]
      simp [first, k, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [identitySecond_second]
      simp [second, k, target_def, identity_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hk, composition, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simpa only [k, CommRingCat.ofHom_id, Spec.map_id] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) pushoutLift_id_counit_comp_coproduct

/-- Pair an arrow with its inverse. -/
def arrowInverse : Spec (.of ArrowRing) ⟶ ComposablePairs :=
  isPullback_first_second.lift (𝟙 _) inversion.hom (by simp)

/-- Pair the inverse of an arrow with the original arrow. -/
def inverseArrow : Spec (.of ArrowRing) ⟶ ComposablePairs :=
  isPullback_first_second.lift inversion.hom (𝟙 _) (by simp)

/-- The arrow-inverse pair starts with the original arrow. -/
@[reassoc (attr := simp)]
theorem arrowInverse_first : arrowInverse ≫ first = 𝟙 _ :=
  isPullback_first_second.lift_fst _ _ _

/-- The arrow-inverse pair ends with the inverse arrow. -/
@[reassoc (attr := simp)]
theorem arrowInverse_second : arrowInverse ≫ second = inversion.hom :=
  isPullback_first_second.lift_snd _ _ _

/-- The inverse-arrow pair starts with the inverse arrow. -/
@[reassoc (attr := simp)]
theorem inverseArrow_first : inverseArrow ≫ first = inversion.hom :=
  isPullback_first_second.lift_fst _ _ _

/-- The inverse-arrow pair ends with the original arrow. -/
@[reassoc (attr := simp)]
theorem inverseArrow_second : inverseArrow ≫ second = 𝟙 _ :=
  isPullback_first_second.lift_snd _ _ _

/-- An arrow followed by its inverse gives the identity at its source. -/
@[reassoc (attr := simp)]
theorem arrowInverse_composition : arrowInverse ≫ composition = source ≫ identity := by
  let k := pushoutLift rightUnit
    ⟨(RingHom.id ArrowRing, conjugation), by simp⟩
  have hk : arrowInverse = Spec.map (CommRingCat.ofHom k) := by
    apply isPullback_first_second.hom_ext
    · rw [arrowInverse_first]
      simp [first, k, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [arrowInverse_second]
      simp [second, k, inversion_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hk, composition, source_def, identity_def, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    pushoutLift_id_conjugation_comp_coproduct

/-- The inverse followed by the original arrow gives the identity at its target. -/
@[reassoc (attr := simp)]
theorem inverseArrow_composition : inverseArrow ≫ composition = target ≫ identity := by
  let k := pushoutLift rightUnit
    ⟨(conjugation, RingHom.id ArrowRing), by simp⟩
  have hk : inverseArrow = Spec.map (CommRingCat.ofHom k) := by
    apply isPullback_first_second.hom_ext
    · rw [inverseArrow_first]
      simp [first, k, inversion_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [inverseArrow_second]
      simp [second, k, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hk, composition, target_def, identity_def, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    pushoutLift_conjugation_id_comp_coproduct

/-- The scheme of three composable Weierstrass arrows. -/
abbrev ComposableTriples := Spec (.of (ChangeRing (ChangeRing ArrowRing)))

/-- The first two arrows of a composable triple. -/
def initialPair : ComposableTriples ⟶ ComposablePairs :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChangeRing ArrowRing) _))

/-- The final arrow of a composable triple. -/
def last : ComposableTriples ⟶ Spec (.of ArrowRing) :=
  Spec.map (CommRingCat.ofHom (ChangeRing.map ((ChangeRing.map rightUnit).comp rightUnit)))

/-- The triple scheme is the fibre product adjoining a third composable arrow. -/
theorem isPullback_initialPair_last : IsPullback initialPair last (second ≫ target) source := by
  simpa only [initialPair, last, source_def, second, target_def,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    isPullback_SpecMap_of_isPushout _ _ _ _
      (ChangeRing.isPushout ((ChangeRing.map rightUnit).comp rightUnit))

/-- The second and third arrows of a composable triple. -/
def suffix : ComposableTriples ⟶ ComposablePairs :=
  Spec.map (CommRingCat.ofHom (ChangeRing.map (ChangeRing.map rightUnit)))

/-- The first arrow in the suffix is the second arrow in the prefix. -/
@[reassoc (attr := simp)]
theorem suffix_first : suffix ≫ first = initialPair ≫ second := by
  simp [suffix, first, initialPair, second, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The last arrow in the suffix is the final arrow of the triple. -/
@[reassoc (attr := simp)]
theorem suffix_second : suffix ≫ second = last := by
  simp [suffix, second, last, ← Spec.map_comp, ← CommRingCat.ofHom_comp, map_comp]

/-- Compose the first two arrows, leaving the third unchanged. -/
def composePrefix : ComposableTriples ⟶ ComposablePairs :=
  isPullback_first_second.lift (initialPair ≫ composition) last (by
    simpa using isPullback_initialPair_last.w)

/-- Leave the first arrow unchanged and compose the final two. -/
def composeSuffix : ComposableTriples ⟶ ComposablePairs :=
  isPullback_first_second.lift (initialPair ≫ first) (suffix ≫ composition) (by simp)

/-- The first component after composing the prefix. -/
@[reassoc (attr := simp)]
theorem composePrefix_first : composePrefix ≫ first = initialPair ≫ composition :=
  isPullback_first_second.lift_fst _ _ _

/-- The second component after composing the prefix. -/
@[reassoc (attr := simp)]
theorem composePrefix_second : composePrefix ≫ second = last :=
  isPullback_first_second.lift_snd _ _ _

/-- The first component after composing the suffix. -/
@[reassoc (attr := simp)]
theorem composeSuffix_first : composeSuffix ≫ first = initialPair ≫ first :=
  isPullback_first_second.lift_fst _ _ _

/-- The second component after composing the suffix. -/
@[reassoc (attr := simp)]
theorem composeSuffix_second : composeSuffix ≫ second = suffix ≫ composition :=
  isPullback_first_second.lift_snd _ _ _

/-- Composition of Weierstrass arrows is associative on the scheme of composable triples. -/
theorem composition_assoc : composePrefix ≫ composition = composeSuffix ≫ composition := by
  let k₁ := pushoutLift rightUnit
    ⟨((algebraMap (ChangeRing ArrowRing) _).comp coproduct,
      ChangeRing.map ((ChangeRing.map rightUnit).comp rightUnit)), by
      dsimp only
      rw [RingHom.comp_assoc, coproduct_comp_rightUnit, map_comp_algebraMap]⟩
  let k₂ := pushoutLift rightUnit
    ⟨((algebraMap (ChangeRing ArrowRing) _).comp (algebraMap ArrowRing _),
      (ChangeRing.map (ChangeRing.map rightUnit)).comp coproduct), by
      exact RingHom.ext fun x ↦ by simp⟩
  have h₁ : composePrefix = Spec.map (CommRingCat.ofHom k₁) := by
    apply isPullback_first_second.hom_ext
    · rw [composePrefix_first]
      simp [first, initialPair, composition, k₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [composePrefix_second]
      simp [second, last, k₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h₂ : composeSuffix = Spec.map (CommRingCat.ofHom k₂) := by
    apply isPullback_first_second.hom_ext
    · rw [composeSuffix_first]
      simp [first, initialPair, k₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [composeSuffix_second]
      simp [second, suffix, composition, k₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [h₁, h₂, composition, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) coproduct_coassoc

end TauCeti.WeierstrassHopfAlgebroid
