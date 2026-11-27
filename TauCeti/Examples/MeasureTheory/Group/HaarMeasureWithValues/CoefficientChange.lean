/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Basic
import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.CoefficientChange

/-!
# Examples: change of coefficients for Hecke algebras

* Changing coefficients along the identity does not change the underlying function.
* For a compact open subgroup `U` of volume `2` over `ℤ`, `1_U ⋆ 1_U = 2 • 1_U` becomes zero
  after reduction modulo `2`.
-/

open TopologicalSpace LocallyConstant

namespace TauCeti.HaarMeasureWithValues

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- Changing coefficients along the identity does not change the underlying function. -/
example (A : Type*) [CommRing A] (μ : HaarMeasureWithValues A G) (f : HeckeAlgebra μ) :
    ((HeckeAlgebra.mapCoeff (RingHom.id A) μ f).toCompactlySupported : LocallyConstant G A) =
      f.toCompactlySupported := by
  ext x
  rw [HeckeAlgebra.toCompactlySupported_mapCoeff, mapCoeff_apply, RingHom.id_apply]

/-- For `μ(U) = 2` over `ℤ`, the reduction modulo `2` of `1_U ⋆ 1_U = 2 • 1_U` vanishes. -/
example (μ : HaarMeasureWithValues ℤ G) (U : OpenSubgroup G) (hU : IsCompact (U : Set G))
    (h2 : μ (U.toCompactOpens hU) = 2) :
    mapCoeff (Int.castRingHom (ZMod 2)) (μ.convolution
      ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩
      ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩) = 0 := by
  rw [convolution_compactOpenIndicator_self, h2, LinearMap.map_smulₛₗ]
  have : (Int.castRingHom (ZMod 2)) 2 = 0 := by decide
  rw [this, zero_smul]

end TauCeti.HaarMeasureWithValues
