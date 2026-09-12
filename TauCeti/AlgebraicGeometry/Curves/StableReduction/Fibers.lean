/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model

/-!
# Generic fibres of models over a discrete valuation ring

This file defines the canonical inclusion of a model's chosen generic fibre into its total space.
It records compatibility with the structure morphism and proves that the inclusion is open.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- The chosen generic fibre of a model, included into its total space. -/
noncomputable def genericι (M : Model R K C toK) : C ⟶ M.total :=
  M.genericFiberIso.inv.left ≫ genericFiberι R K M.toBase

/-- The inclusion of a model's chosen generic fibre lies over the fraction-field morphism. -/
@[reassoc (attr := simp)]
lemma genericι_toBase (M : Model R K C toK) :
    M.genericι ≫ M.toBase =
      toK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [genericι, Category.assoc, genericFiberι_toBase, ← Category.assoc, Over.w]
  rfl

/-- A model's chosen generic fibre is an open subscheme of its total space. -/
lemma isOpenImmersion_genericι (M : Model R K C toK) : IsOpenImmersion M.genericι := by
  let : IsOpenImmersion (genericFiberι R K M.toBase) :=
    isOpenImmersion_genericFiberι R K M.toBase
  let : IsIso M.genericFiberIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericFiberIso.inv))
  rw [genericι]
  infer_instance

end Model

end TauCeti
