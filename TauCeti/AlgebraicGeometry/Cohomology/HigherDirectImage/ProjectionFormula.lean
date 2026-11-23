/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# The projection formula for higher direct images

For any scheme morphism `f : X ⟶ Y` and finite locally free sheaf `E` on `Y`, tensoring
`Rⁿf_* F` with `E` is naturally isomorphic to `Rⁿf_* (f^*E ⊗ F)`.
No quasi-coherence condition on `F` or finiteness condition on `f` is needed.

Tensoring by a finite locally free sheaf is exact and preserves injective objects: it is
right adjoint to the exact functor given by tensoring with its dual. Consequently the
ordinary projection formula lifts through native right derived functors in every degree.

The structure-sheaf specialization computes the higher direct images of `f^*E` from those
of `𝒪_X`. In particular, vanishing of `Rⁿf_*𝒪_X` implies vanishing of `Rⁿf_*(f^*E)`,
a form used for pullbacks along contractions.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Exercise 8.3.
* The Stacks Project, Lemma 20.54.2, Tag 01E8.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)

/-- **The higher projection formula.** For a finite locally free sheaf `E` on `Y`,
`E ⊗ Rⁿf_* F ≅ Rⁿf_* (f^*E ⊗ F)`, naturally in every sheaf of modules `F` on `X`. -/
def higherDirectImageTensorLeftIso (n : ℕ) :
    f.higherDirectImage n ⋙ tensorLeft E.obj ≅
      tensorLeft ((pullback f).obj E).obj ⋙ f.higherDirectImage n := by
  let := exactPairingObjDual E
  let P := (pullback f).obj E
  let := exactPairingObjDual P
  let := exactPairingDualObj P
  have : Limits.PreservesLimits (tensorLeft E.obj) :=
    (tensorLeftAdjunction E.obj (dual E).obj).rightAdjoint_preservesLimits
  have : Limits.PreservesLimits (tensorLeft P.obj) :=
    (tensorLeftAdjunction P.obj (dual P).obj).rightAdjoint_preservesLimits
  have : Limits.PreservesLimits (tensorLeft (dual P).obj) :=
    (tensorLeftAdjunction (dual P).obj P.obj).rightAdjoint_preservesLimits
  have : (tensorLeft P.obj).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (tensorLeftAdjunction P.obj (dual P).obj)
  have := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  have := (tensorLeft E.obj).additive_of_preserves_binary_products
  have := (tensorLeft P.obj).additive_of_preserves_binary_products
  exact Functor.rightDerivedCompIso (Scheme.Modules.pushforward f)
    (tensorLeft E.obj) (tensorLeft P.obj) (Scheme.Modules.pushforward f)
    (pushforwardTensorLeftIso f E) n

/-- The higher direct images of a pulled-back finite locally free sheaf are obtained by
tensoring the higher direct images of the structure sheaf with that sheaf. -/
def higherDirectImagePullbackIso (n : ℕ) :
    E.obj ⊗ (f.higherDirectImage n).obj (𝟙_ X.Modules) ≅
      (f.higherDirectImage n).obj ((pullback f).obj E).obj :=
  (higherDirectImageTensorLeftIso f E n).app (𝟙_ X.Modules) ≪≫
    (f.higherDirectImage n).mapIso (ρ_ _)

/-- If `Rⁿf_*𝒪_X` vanishes, then so does `Rⁿf_*(f^*E)` for every finite locally free sheaf
`E` on the target. This applies in particular to higher-direct-image vanishing for pullbacks
along a contraction. -/
theorem isZero_higherDirectImage_pullback (n : ℕ)
    (h : Limits.IsZero ((f.higherDirectImage n).obj (𝟙_ X.Modules))) :
    Limits.IsZero ((f.higherDirectImage n).obj ((pullback f).obj E).obj) :=
  ((tensorLeft E.obj).map_isZero h).of_iso (higherDirectImagePullbackIso f E n).symm

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
