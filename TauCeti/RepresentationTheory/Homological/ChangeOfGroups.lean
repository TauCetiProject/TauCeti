/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Augmented
public import TauCeti.RepresentationTheory.Homological.Resolution

/-!
# Resolution comparisons commute with change of groups up to homotopy

Let `f : G →* H`, and let `P` and `Q` resolve the trivial representations of `G` and `H`.
An augmentation-preserving map from `P` to the restriction of `Q` commutes, up to homotopy,
with the comparison maps from the bar resolutions. The bar map is the existing
`TauCeti.Rep.barComplex.resChainMap`, which applies `f` to each group label.

This holds for every homomorphism: the restricted target is exact, but is not assumed
projective. The homotopy square is the resolution-comparison ingredient for naturality
of group homology and cohomology computed from equivariant geometric resolutions.

We use Mathlib's projective-resolution lifts, by Kim Morrison and Joël Riou, and Amelia
Livingston's bar resolution. No replacement resolution is introduced.

## References

* K. S. Brown, *Cohomology of Groups*, Chapters I.7 and III.8.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace MonoidHom

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- Maps into a restricted projective resolution that agree after augmentation are
homotopic. Only the source complex must be degreewise projective; restriction along `f`
is not assumed to preserve projective objects. -/
def homotopyOfCompResAugmentationEq (f : G →* H)
    {P : ChainComplex (Rep k G) ℕ} [∀ n, Projective (P.X n)]
    {Z : Rep.{u} k H} (Q : ProjectiveResolution Z)
    (α β : P ⟶ ((Rep.resFunctor f).mapHomologicalComplex _).obj Q.complex)
    (h : α.f 0 ≫ (Rep.resFunctor f).map (Q.π.f 0) =
      β.f 0 ≫ (Rep.resFunctor f).map (Q.π.f 0)) : Homotopy α β :=
  ChainComplex.homotopyOfCompAugmentationEq _
    ((Functor.map_comp (Rep.resFunctor f) _ _).symm.trans
      ((congrArg (Rep.resFunctor f).map Q.complex_d_comp_π_f_zero).trans
        ((Rep.resFunctor f).map_zero _ _)))
    (Q.exact₀.map (Rep.resFunctor f))
    (fun n ↦ (Q.exact_succ n).map (Rep.resFunctor f)) α β h

/-- **Bar-resolution comparisons commute with arbitrary change of groups up to homotopy.**
For an augmentation-preserving map `φ` from `P` to the restriction of `Q`, comparing from
the bar resolution before applying `φ` is homotopic to first relabelling the bar resolution
and then comparing to `Q`. No injectivity assumption on `f` is needed. -/
def barResolutionComparisonHomotopy (f : G →* H)
    (P : ProjectiveResolution (Rep.trivial k G k))
    (Q : ProjectiveResolution (Rep.trivial k H k))
    (φ : P.complex ⟶ ((Rep.resFunctor f).mapHomologicalComplex _).obj Q.complex)
    (hφ : φ.f 0 ≫ (Rep.resFunctor f).map (Q.π.f 0) = P.π.f 0) :
    Homotopy
      (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P ≫ φ)
      (TauCeti.Rep.barComplex.resChainMap f ≫
        ((Rep.resFunctor f).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k H) Q)) := by
  apply f.homotopyOfCompResAugmentationEq Q
  -- The restricted complex and its morphisms are presented through `mapHomologicalComplex`.
  -- Their carriers unfold to restricted representations; exposing the component composite
  -- lets the augmentation identities rewrite without transporting those carrier objects.
  change (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P).f 0 ≫
      φ.f 0 ≫ (Rep.resFunctor f).map (Q.π.f 0) =
    (TauCeti.Rep.barComplex.resChainMap f).f 0 ≫
      (Rep.resFunctor f).map
        ((ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k H) Q).f 0) ≫
          (Rep.resFunctor f).map (Q.π.f 0)
  have hG := (ProjectiveResolution.lift_commutes_zero (𝟙 _)
    (Rep.barResolution k G) P).trans (Category.comp_id _)
  have hH := (ProjectiveResolution.lift_commutes_zero (𝟙 _)
    (Rep.barResolution k H) Q).trans (Category.comp_id _)
  have hr := congrArg
    (fun t ↦ (TauCeti.Rep.barComplex.resChainMap f).f 0 ≫ (Rep.resFunctor f).map t) hH
  have hr' := (congrArg ((TauCeti.Rep.barComplex.resChainMap f).f 0 ≫ ·)
    ((Rep.resFunctor f).map_comp _ _)).symm.trans hr
  exact ((congrArg
    ((ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P).f 0 ≫ ·) hφ).trans hG).trans
      (hr'.trans (TauCeti.Rep.barComplex.resChainMap_f_zero_comp_π f)).symm

end MonoidHom
