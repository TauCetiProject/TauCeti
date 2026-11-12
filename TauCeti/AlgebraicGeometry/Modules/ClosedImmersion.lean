/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.Topology.Sheaves.ClosedEmbedding

/-!
# Exact pushforward of modules along closed immersions

Pushforward along a closed immersion is exact on all sheaves of modules. This permits
injective-resolution computations of higher direct images without any quasicoherence
or flatness assumption on the coefficient.

Exactness is reflected by the exact faithful functor to abelian sheaves, using
`TauCeti.Topology.exact_pushforward_of_isClosedEmbedding` on their underlying spaces.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Closed-immersion pushforward is exact on all module sheaves. -/
theorem exact_pushforward_of_isClosedImmersion (S : ShortComplex X.Modules)
    (hS : S.Exact) : (S.map (Scheme.Modules.pushforward f)).Exact := by
  let G := TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf Y
  have : (TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).PreservesZeroMorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms
  apply G.reflects_exact_of_faithful
  have hS' := hS.map (TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X)
  have h := TauCeti.Topology.exact_pushforward_of_isClosedEmbedding f.base
    f.isClosedEmbedding _ hS'
  -- The forgetful functors and pushforward agree on the underlying abelian sheaves.
  exact h

/-- Closed-immersion pushforward preserves homology of complexes of module sheaves. -/
instance preservesHomology_pushforward_of_isClosedImmersion :
    (Scheme.Modules.pushforward f).PreservesHomology := by
  have : (Scheme.Modules.pushforward f).Additive :=
    (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  exact Functor.preservesHomology_of_map_exact _
    (fun S hS ↦ f.exact_pushforward_of_isClosedImmersion S hS)

end AlgebraicGeometry.Scheme.Hom
