/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Identity coherence for tensor products under scheme-module pullback

Mathlib's `Scheme.Modules.pullbackId` identifies pullback along the identity scheme morphism
with the identity functor. The tensor comparison commutes with this identification on both
factors. Together with `Scheme.Modules.pullbackObjUnitIso_id` for the unit and
`Scheme.Modules.pullback_comp_δ` for composition, this gives the identity and composition
normalizations of the canonical oplax monoidal pullback structure.

The result specializes the identity coherence for sheaves of modules on a ringed site, with
no finiteness or quasi-coherence assumptions on the modules.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

/-- The canonical tensor comparison for pullback along the identity scheme morphism respects
Mathlib's identity isomorphism of module pullback. -/
@[reassoc (attr := simp)]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullback_id_δ
    (X : Scheme.{u}) (M N : X.Modules) :
    Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (𝟙 X)) M N ≫
      ((Scheme.Modules.pullbackId X).hom.app M ⊗ₘ (Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackId X).hom.app (M ⊗ N) :=
  SheafOfModules.pullback_id_δ X.sheaf M N

end

end TauCeti
