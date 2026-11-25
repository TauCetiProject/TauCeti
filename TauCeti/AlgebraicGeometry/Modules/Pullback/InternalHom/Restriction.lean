/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
import TauCeti.AlgebraicGeometry.Modules.Restriction.Closed
import TauCeti.CategoryTheory.Monoidal.Closed.Naturality

/-!
# Internal Hom under pullback to an open subscheme

The canonical internal-Hom comparison is invertible for the inclusion of an open subscheme,
with arbitrary source and target module sheaves. Restriction commutes
with internal Hom without a finiteness hypothesis. The restriction--pullback isomorphism
identifies that restriction comparison with the canonical pullback comparison by evaluation.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open Functor.LaxMonoidal Functor.OplaxMonoidal
open AlgebraicGeometry

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry

private theorem isIso_pullbackIhomComparison_app_of_restrictFunctor
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (M N : Y.Modules)
    (hR : IsIso (((Scheme.Modules.restrictFunctor j).ihomComparison M).app N)) :
    IsIso (((Scheme.Modules.pullback j).ihomComparison M).app N) := by
  let P := Scheme.Modules.pullback j
  let σ := (Scheme.Modules.restrictFunctorIsoPullback j).inv
  have hm : μ P M ((ihom M).obj N) ≫ σ.app (M ⊗ (ihom M).obj N) =
      (σ.app M ⊗ₘ σ.app ((ihom M).obj N)) ≫
        μ (Scheme.Modules.restrictFunctor j) M ((ihom M).obj N) := by
    apply (cancel_epi (δ P M ((ihom M).obj N))).mp
    have hδμ : δ P M ((ihom M).obj N) ≫ μ P M ((ihom M).obj N) = 𝟙 _ :=
      Functor.Monoidal.δ_μ P M ((ihom M).obj N)
    rw [reassoc_of% hδμ]
    rw [← Category.assoc,
      ← Scheme.Modules.restrictFunctorIsoPullback_inv_app_tensor,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (P.isIso_ihomComparison_app_iff_of_natIso (Scheme.Modules.restrictFunctor j)
    (Scheme.Modules.restrictFunctorIsoPullback j).symm M N hm).mpr hR

/-- Pullback to an open subscheme commutes with internal Hom of arbitrary module sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.isIso_pullbackIhomComparison_app
    {Y : Scheme.{u}} (U : Y.Opens) (M N : Y.Modules) :
    IsIso (((Scheme.Modules.pullback U.ι).ihomComparison M).app N) :=
  isIso_pullbackIhomComparison_app_of_restrictFunctor U.ι M N
    (Scheme.Modules.isIso_restrictFunctor_ihomComparison_app U M N)

end TauCeti.AlgebraicGeometry

end
