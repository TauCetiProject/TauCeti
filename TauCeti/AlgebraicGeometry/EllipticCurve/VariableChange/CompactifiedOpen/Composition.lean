/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.CompactifiedOpen.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Composition

/-!
# Composition on the smooth-or-nodal Weierstrass atlas

The invariant open `U = D(c₄) ∪ D(Δ)` retains smooth and nodal cubics. The restricted
source, target, identity and inversion maps extend to a groupoid presentation: its scheme of
composable pairs is the fibre product of the restricted target and source. Composition is
the restriction of the affine Weierstrass composition, with its identity, inverse and
associativity laws. Thus the open `U`, nodal boundary included, is closed under scheme-level
composition.

`compactifiedCompose` gives the operation on arrows parametrized by any test scheme. Its
inclusion compatibility identifies the composite with the full affine composite and pins the
order: the first arrow is followed by the second, with coordinate change `C₂ * C₁`.
These constructions supply groupoid operations, not a quotient-stack or moduli identification.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3.
* P. Goerss, *Topological modular forms [after Hopkins, Miller, and Lurie]*, §3.1.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TauCeti.WeierstrassHopfAlgebroid

/-- Composable arrows on the smooth-or-nodal Weierstrass atlas, with the first arrow in the
first factor. This is a scheme fibre product, including nonreduced test schemes. -/
abbrev CompactifiedPairs := pullback compactifiedTarget compactifiedSource

/-- Inclusion of composable smooth-or-nodal arrows into the full composable-pair scheme. -/
def compactifiedPairInclusion : CompactifiedPairs ⟶ ComposablePairs :=
  isPullback_first_second.lift
    (pullback.fst _ _ ≫ compactifiedArrowOpen.ι)
    (pullback.snd _ _ ≫ compactifiedArrowOpen.ι) (by
      rw [Category.assoc, Category.assoc, ← compactifiedTarget_ι, ← compactifiedSource_ι,
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The first arrow is unchanged by inclusion. -/
@[reassoc (attr := simp)]
theorem compactifiedPairInclusion_first :
    compactifiedPairInclusion ≫ first = pullback.fst _ _ ≫ compactifiedArrowOpen.ι :=
  isPullback_first_second.lift_fst _ _ _

/-- The second arrow is unchanged by inclusion. -/
@[reassoc (attr := simp)]
theorem compactifiedPairInclusion_second :
    compactifiedPairInclusion ≫ second = pullback.snd _ _ ≫ compactifiedArrowOpen.ι :=
  isPullback_first_second.lift_snd _ _ _

/-- Composition on the smooth-or-nodal open. The source of the full composite lies in the
open, so the source pullback uniquely factors it through the restricted arrow scheme. -/
def compactifiedComposition : CompactifiedPairs ⟶ compactifiedArrowOpen :=
  isPullback_compactifiedSource.lift
    (pullback.fst _ _ ≫ compactifiedSource)
    (compactifiedPairInclusion ≫ composition) (by simp [Category.assoc])

/-- Restricted composition agrees with full composition after inclusion. -/
@[reassoc (attr := simp)]
theorem compactifiedComposition_ι :
    compactifiedComposition ≫ compactifiedArrowOpen.ι =
      compactifiedPairInclusion ≫ composition :=
  isPullback_compactifiedSource.lift_snd _ _ _

/-- The composite has the source of its first arrow. -/
@[reassoc (attr := simp)]
theorem compactifiedComposition_source :
    compactifiedComposition ≫ compactifiedSource = pullback.fst _ _ ≫ compactifiedSource :=
  isPullback_compactifiedSource.lift_fst _ _ _

/-- The composite has the target of its second arrow. -/
@[reassoc (attr := simp)]
theorem compactifiedComposition_target :
    compactifiedComposition ≫ compactifiedTarget = pullback.snd _ _ ≫ compactifiedTarget := by
  rw [← cancel_mono _root_.WeierstrassCurve.Universal.compactifiedOpen.ι]
  simp

/-- The restricted composable-pair scheme is the inverse image of the restricted arrow
scheme under the full first projection. In particular its inclusion is an open immersion. -/
theorem isPullback_compactifiedPairInclusion :
    IsPullback (pullback.fst compactifiedTarget compactifiedSource) compactifiedPairInclusion
      compactifiedArrowOpen.ι first := by
  have h := (IsPullback.of_hasPullback compactifiedTarget compactifiedSource).paste_vert
    isPullback_compactifiedSource
  rw [compactifiedTarget_ι] at h
  exact h.of_bot' isPullback_first_second

/-- The inclusion of composable smooth-or-nodal arrows is an open immersion. -/
instance isOpenImmersion_compactifiedPairInclusion :
    IsOpenImmersion compactifiedPairInclusion :=
  MorphismProperty.of_isPullback isPullback_compactifiedPairInclusion inferInstance

variable {X : Scheme}

/-- Compose two smooth-or-nodal arrows parametrized by a test scheme, in the order first
`f`, then `g`. The equality `hfg` records their composability. -/
def compactifiedCompose (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) : X ⟶ compactifiedArrowOpen :=
  pullback.lift f g hfg ≫ compactifiedComposition

/-- Inclusion preserves composability of parametrized smooth-or-nodal arrows. -/
theorem compactifiedComposable_ι (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) :
    (f ≫ compactifiedArrowOpen.ι) ≫ target = (g ≫ compactifiedArrowOpen.ι) ≫ source := by
  simpa only [Category.assoc, compactifiedTarget_ι, compactifiedSource_ι] using
    congrArg (· ≫ _root_.WeierstrassCurve.Universal.compactifiedOpen.ι) hfg

/-- Inclusion commutes with the lift of a parametrized composable pair. -/
@[reassoc (attr := simp)]
theorem lift_compactifiedPairInclusion (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) :
    pullback.lift f g hfg ≫ compactifiedPairInclusion =
      isPullback_first_second.lift (f ≫ compactifiedArrowOpen.ι)
        (g ≫ compactifiedArrowOpen.ι) (compactifiedComposable_ι f g hfg) := by
  apply isPullback_first_second.hom_ext <;> simp

/-- Inclusion of a test-scheme composite is the composite of the included arrows. -/
@[reassoc (attr := simp)]
theorem compactifiedCompose_ι (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) :
    compactifiedCompose f g hfg ≫ compactifiedArrowOpen.ι =
      isPullback_first_second.lift (f ≫ compactifiedArrowOpen.ι)
        (g ≫ compactifiedArrowOpen.ι) (compactifiedComposable_ι f g hfg) ≫ composition := by
  simp [compactifiedCompose]

/-- A parametrized composite starts at the source of the first arrow. -/
@[reassoc (attr := simp)]
theorem compactifiedCompose_source (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) :
    compactifiedCompose f g hfg ≫ compactifiedSource = f ≫ compactifiedSource := by
  simp [compactifiedCompose]

/-- A parametrized composite ends at the target of the second arrow. -/
@[reassoc (attr := simp)]
theorem compactifiedCompose_target (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) :
    compactifiedCompose f g hfg ≫ compactifiedTarget = g ≫ compactifiedTarget := by
  simp [compactifiedCompose]

/-- Pulling back a parametrized pair along a test-scheme morphism commutes with composition. -/
@[reassoc]
theorem comp_compactifiedCompose {Y : Scheme} (a : Y ⟶ X)
    (f g : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource) :
    a ≫ compactifiedCompose f g hfg =
      compactifiedCompose (a ≫ f) (a ≫ g) (by simp only [Category.assoc, hfg]) := by
  have hp : a ≫ pullback.lift f g hfg = pullback.lift (a ≫ f) (a ≫ g)
      (by simp only [Category.assoc, hfg]) := by
    apply pullback.hom_ext <;> simp
  simp only [compactifiedCompose, ← Category.assoc, hp]

/-- An identity arrow followed by an arrow is that arrow. -/
@[simp]
theorem compactifiedCompose_identity_first (f : X ⟶ compactifiedArrowOpen) :
    compactifiedCompose (f ≫ compactifiedSource ≫ compactifiedIdentity) f (by simp) = f := by
  rw [← cancel_mono compactifiedArrowOpen.ι, compactifiedCompose_ι,
    composition_lift_eq _ _ _ (f ≫ compactifiedArrowOpen.ι ≫ identityFirst) (by simp) (by simp)]
  simp

/-- An arrow followed by the identity at its target is that arrow. -/
@[simp]
theorem compactifiedCompose_identity_second (f : X ⟶ compactifiedArrowOpen) :
    compactifiedCompose f (f ≫ compactifiedTarget ≫ compactifiedIdentity) (by simp) = f := by
  rw [← cancel_mono compactifiedArrowOpen.ι, compactifiedCompose_ι,
    composition_lift_eq _ _ _ (f ≫ compactifiedArrowOpen.ι ≫ identitySecond) (by simp) (by simp)]
  simp

/-- An arrow followed by its inverse is the identity at its source. -/
@[simp]
theorem compactifiedCompose_arrow_inverse (f : X ⟶ compactifiedArrowOpen) :
    compactifiedCompose f (f ≫ compactifiedInversion.hom) (by simp) =
      f ≫ compactifiedSource ≫ compactifiedIdentity := by
  rw [← cancel_mono compactifiedArrowOpen.ι, compactifiedCompose_ι,
    composition_lift_eq _ _ _ (f ≫ compactifiedArrowOpen.ι ≫ arrowInverse) (by simp) (by simp)]
  simp

/-- The inverse followed by the original arrow is the identity at its target. -/
@[simp]
theorem compactifiedCompose_inverse_arrow (f : X ⟶ compactifiedArrowOpen) :
    compactifiedCompose (f ≫ compactifiedInversion.hom) f (by simp) =
      f ≫ compactifiedTarget ≫ compactifiedIdentity := by
  rw [← cancel_mono compactifiedArrowOpen.ι, compactifiedCompose_ι,
    composition_lift_eq _ _ _ (f ≫ compactifiedArrowOpen.ι ≫ inverseArrow) (by simp) (by simp)]
  simp

/-- Composition on the smooth-or-nodal open is associative on every test scheme. -/
theorem compactifiedCompose_assoc (f g h : X ⟶ compactifiedArrowOpen)
    (hfg : f ≫ compactifiedTarget = g ≫ compactifiedSource)
    (hgh : g ≫ compactifiedTarget = h ≫ compactifiedSource) :
    compactifiedCompose (compactifiedCompose f g hfg) h (by simp [hgh]) =
      compactifiedCompose f (compactifiedCompose g h hgh) (by simp [hfg]) := by
  rw [← cancel_mono compactifiedArrowOpen.ι]
  simp only [compactifiedCompose_ι]
  apply composition_lift_assoc

end TauCeti.WeierstrassHopfAlgebroid
