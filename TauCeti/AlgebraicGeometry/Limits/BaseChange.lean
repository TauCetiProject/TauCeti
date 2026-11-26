/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Cofiltered

/-!
# Base change of a cofiltered diagram of schemes

Let `D : I ⥤ Scheme` be a diagram, `i : I`, and `r : Z ⟶ Dᵢ`. The base change
`D.pullbackOver r : Over i ⥤ Scheme`, `j ↦ Dⱼ ×_{Dᵢ} Z`, has limit `S ×_{Dᵢ} Z` when `D` is
cofiltered with limit `S` (Stacks, Section 32.10 (01ZL)). This file records that affine
transition maps, quasi-compactness and quasi-separation of the members pass to the base change, so
that the descent results for such limits apply to it.

Inheritance of a morphism property may be reduced to the diagram base changed along its target
using `CategoryTheory.MorphismProperty.exists_pullbackMap_of_pullbackOver`. The transport is
available through this module and applies to arbitrary categories with pullbacks, without a
cofilteredness or limit assumption.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type*} [Category* I] (D : I ⥤ Scheme.{u}) {i : I} {Z : Scheme.{u}}
  (r : Z ⟶ D.obj i)

instance [∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((D.pullbackOver r).map f) := by
  have sq := Over.isPullback_pullback_map_left r ((Over.post D).map f)
  -- Identify the over-category and diagram transition maps by their pullback projections.
  rw [show ((Over.pullback r).map ((Over.post D).map f)).left = (D.pullbackOver r).map f by
    apply pullback.hom_ext <;> simp] at sq
  exact MorphismProperty.of_isPullback sq.flip (inferInstance : IsAffineHom (D.map f.left))

instance [∀ j, CompactSpace (D.obj j)] [QuasiCompact r] (j : Over i) :
    CompactSpace ((D.pullbackOver r).obj j) := by
  dsimp; infer_instance

instance [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated r] (j : Over i) :
    QuasiSeparatedSpace ((D.pullbackOver r).obj j) := by
  dsimp; exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

end TauCeti.AlgebraicGeometry.Scheme
