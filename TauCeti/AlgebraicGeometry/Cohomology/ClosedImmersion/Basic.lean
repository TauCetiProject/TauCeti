/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pushforward
public import TauCeti.Topology.Sheaves.Cohomology

/-!
# Cohomology and direct image along a closed immersion

For a closed immersion `f : X ⟶ Y` and a sheaf of modules `M` on `X`,
`Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)`, naturally in `M`. This allows cohomology computations
on a closed subscheme to be performed on the ambient scheme. No quasi-coherence,
Noetherianity or properness assumption is needed for this additive comparison.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Direct image along a closed immersion preserves cohomology, naturally in the
coefficient sheaf of modules. -/
def cohomologyPushforwardNatIso (n : ℕ) :
    pushforward f ⋙ cohomologyFunctor Y n ≅ cohomologyFunctor X n := by
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have htop : (Opens.map f.base).obj ⊤ = ⊤ := rfl
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (pushforward_comp_toSheaf f))
      (_root_.CategoryTheory.Sheaf.functorH J n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F
      ((Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward AddCommGrpCat f.base)
        (_root_.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH J n
          isTerminalTop).symm) ≪≫
      Topology.cohomologyPushforwardNatIso f.base f.isClosedEmbedding n ⊤ ≪≫
      _root_.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH K n
        (htop ▸ isTerminalTop))

/-- The additive cohomology comparison for a sheaf of modules on a closed subscheme. -/
def cohomologyPushforwardIso (M : X.Modules) (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((pushforward f).obj M) n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  (cohomologyPushforwardNatIso f n).app M

@[simp]
lemma cohomologyPushforwardNatIso_app (M : X.Modules) (n : ℕ) :
    (cohomologyPushforwardNatIso f n).app M = cohomologyPushforwardIso f M n :=
  (rfl)

@[simp]
lemma cohomologyPushforwardNatIso_hom_app (M : X.Modules) (n : ℕ) :
    (cohomologyPushforwardNatIso f n).hom.app M = (cohomologyPushforwardIso f M n).hom :=
  (rfl)

/-- The additive comparison commutes with maps of coefficient sheaves. -/
@[reassoc]
lemma cohomologyPushforwardIso_naturality {M N : X.Modules} (α : M ⟶ N) (n : ℕ) :
    (pushforward f ⋙ cohomologyFunctor Y n).map α ≫
        (cohomologyPushforwardIso f N n).hom =
      (cohomologyPushforwardIso f M n).hom ≫ (cohomologyFunctor X n).map α :=
  (cohomologyPushforwardNatIso f n).hom.naturality α

end

end TauCeti.AlgebraicGeometry
