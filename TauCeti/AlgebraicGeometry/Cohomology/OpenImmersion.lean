/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Equivalence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over
public import TauCeti.Topology.Sheaves.Over

/-!
# Cohomology on the image of an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes and `M` a sheaf of modules on `X`. This file
identifies the cohomology `Hⁿ(f(Y), M)` of the open subset `f(Y)` of `X` with the cohomology
`Hⁿ(Y, M|_Y)` of the restriction of `M` along `f`.

Applied to the canonical open immersion `Spec Γ(X, U) ⟶ X` of an affine open `U`, it transports
Serre's vanishing theorem on the spectrum of a Noetherian ring to the affine opens of an arbitrary
scheme: a quasi-coherent sheaf has no cohomology in positive degrees on an affine open `U` with
`Γ(X, U)` Noetherian. With the Mayer–Vietoris sequence this computes the cohomology of a
quasi-coherent sheaf on a locally Noetherian scheme with affine diagonal from an affine open
cover; for a cover by two affine opens, cohomology vanishes above degree one.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.cohomologyOnOpensRangeNatIso`: the comparison
  `Hⁿ(f(Y), M) ≅ Hⁿ(Y, M|_Y)`, natural in `M`, and `cohomologyOnOpensRangeIso` its component at
  a single sheaf of modules.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen`: Serre's
  vanishing theorem on affine opens.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_isAffineOpen`: a
  quasi-coherent sheaf on a locally Noetherian scheme with affine diagonal covered by two affine
  opens has no cohomology in degrees at least two.

## Implementation notes

The comparison composes three steps: cohomology on `U = f(Y)` is the cohomology of the sheaf
restricted to the over category `Over U`
(`TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoFunctorOverH`); `Over U` is equivalent to
the site of open subsets of `Y` (`Topology.IsOpenEmbedding.overEquivalence`); and cohomology is
invariant under equivalences of sites
(`TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr`). The sheaf transported to `Y`
is definitionally the underlying abelian sheaf of `M|_Y`, whose sections over `V` are those of `M`
over `f(V)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5 and Theorem 3.7.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The cohomology of a sheaf of modules on the image of an open immersion `f : Y ⟶ X` is the
cohomology of its restriction along `f`, naturally in the sheaf of modules. -/
def cohomologyOnOpensRangeNatIso (n : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op f.opensRange) ≅
      Scheme.Modules.restrictFunctor f ⋙ cohomologyFunctor Y n :=
  let J := Opens.grothendieckTopology X
  let e := f.isOpenEmbedding.overEquivalence
  haveI : e.inverse.IsDenseSubsite (Opens.grothendieckTopology Y) (J.over f.opensRange) :=
    isDenseSubsite_overEquivalence_inverse f.isOpenEmbedding
  -- Cohomology on `f(Y)` is cohomology on the over category of `f(Y)`, which is equivalent to the
  -- site of open subsets of `Y`; the transported sheaf is the underlying sheaf of `M|_Y`.
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (CategoryTheory.cohomologyPresheafEvaluationIsoFunctorOverH J f.opensRange n) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙ J.overPullback AddCommGrpCat.{u} f.opensRange)
      ((CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over f.opensRange) n
        (isTerminalTop.isTerminalObj e.inverse)).symm ≪≫
      (CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr (J.over f.opensRange)
        (Opens.grothendieckTopology Y) e n ⊤).symm) ≪≫
    Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf)
      (CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH
        (Opens.grothendieckTopology Y) n isTerminalTop)

variable (M : X.Modules)

/-- The cohomology of a sheaf of modules `M` on the image of an open immersion `f : Y ⟶ X` is the
cohomology of the restriction of `M` along `f`. -/
def cohomologyOnOpensRangeIso (n : ℕ) :
    cohomologyOn M n f.opensRange ≅ AddCommGrpCat.of (Cohomology (M.restrict f) n) :=
  (cohomologyOnOpensRangeNatIso f n).app M

/-- **Serre's vanishing theorem on an affine open**: a quasi-coherent sheaf of modules has no
cohomology in positive degrees on an affine open subset `U` whose ring of sections is
Noetherian. -/
theorem subsingleton_cohomologyOn_succ_of_isAffineOpen [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] (n : ℕ) :
    Subsingleton (cohomologyOn M (n + 1) U) := by
  rw [← hU.opensRange_fromSpec]
  exact (cohomologyOnOpensRangeIso hU.fromSpec M (n + 1)).addCommGroupIsoToAddEquiv.toEquiv
    |>.subsingleton

/-- A quasi-coherent sheaf of modules on a locally Noetherian scheme with affine diagonal (for
instance a separated one) that is covered by two affine opens has no cohomology in degrees at
least two. -/
theorem subsingleton_cohomology_of_two_le_of_isAffineOpen [IsLocallyNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [M.IsQuasicoherent] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology M n) := by
  have hacyclic {W : X.Opens} (hW : IsAffineOpen W) (i : ℕ) (hi : 0 < i) :
      Subsingleton (cohomologyOn M i W) := by
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact subsingleton_cohomologyOn_succ_of_isAffineOpen M hW j
  exact subsingleton_cohomology_of_two_le M hUV n hn (hacyclic hU) (hacyclic hV)
    (hacyclic (hU.inf hV))

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
