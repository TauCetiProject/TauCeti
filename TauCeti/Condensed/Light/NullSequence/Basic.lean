/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.LightProfinite.Sequence
public import TauCeti.Condensed.Light.ReducedFree

/-!
# The marked convergent sequence in light condensed modules

The reduced free module on the convergent sequence, marked at infinity, represents null
sequences. Precomposition with its successor drops the first term of a null sequence.

The marked sequence follows Rodríguez Camargo, *Notes on Solid Geometry*, Definition 3.2.1,
and Wagner, *q-de Rham cohomology and topological Hochschild homology over ku*, §2.1.
-/

public section

universe u

open CategoryTheory Category LightCondensed

namespace TauCeti

variable (R : Type u) [Ring R]

/-- The reduced free light condensed module representing null sequences. -/
noncomputable abbrev nullSeq : LightCondMod R :=
  (reducedLightFree R).obj (Under.mk inftyPoint.{u})

/-- The endomorphism of the null-sequence module induced by successor on the sequence. -/
noncomputable def nullShift : nullSeq R ⟶ nullSeq R :=
  (reducedLightFree R).map (Under.homMk natShift.{u} inftyPoint_comp_natShift.{u})

/-- Precomposition by the null shift restricts a section along successor. -/
@[simp↓]
lemma reducedLightFreeHomEquiv_nullShift_val
    {M : LightCondMod R} (g : nullSeq R ⟶ M) :
    (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) M (nullShift R ≫ g)).val =
      M.obj.map natShift.op ((reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) M g).val) := by
  exact reducedLightFreeHomEquiv_comp_val R
    (X := Under.mk inftyPoint) (Y := Under.mk inftyPoint)
    (Under.homMk natShift inftyPoint_comp_natShift) g

end TauCeti
