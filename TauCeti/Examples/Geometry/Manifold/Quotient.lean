/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Covering.Quotient
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Instances.Quotient
import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Examples: the cylinder `ℂ / ℤ` and compact quotients of `ℂ`

The integers act on `ℂ` by translation through the discrete subgroup
`AddSubgroup.zmultiples (1 : ℂ)`. This action is free, properly discontinuous and by
biholomorphisms, so its orbit space, the cylinder `ℂ / ℤ`, receives Mathlib's quotient atlas, and
the installed quotient-manifold results apply to it with no further input:

* the cylinder is a Hausdorff complex analytic manifold (`TauCeti.instIsManifoldAddQuotient`);
* the orbit projection `ℂ → ℂ / ℤ` is a local biholomorphism
  (`TauCeti.isLocalDiffeomorph_addQuotientMk`) and a covering map with deck group `ℤ`
  (`isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd`);
* the cylinder is not compact: translation by integers preserves imaginary parts, so no bounded
  set meets every orbit
  (`TauCeti.AddAction.compactSpace_orbitRelQuotient_iff_exists_isCompact`).

By contrast, the closed unit square meets every orbit of the Gaussian integers `ℤ + ℤ i` acting
by translation, so their orbit space is compact
(`TauCeti.AddAction.compactSpace_orbitRelQuotient_of_isCompact`).
-/

open Set TauCeti
open scoped Manifold ContDiff

-- The cylinder `ℂ / ℤ` is a complex analytic manifold.
example : IsManifold 𝓘(ℂ) ω (AddAction.orbitRel.Quotient (AddSubgroup.zmultiples (1 : ℂ)) ℂ) :=
  inferInstance

-- The cylinder `ℂ / ℤ` is Hausdorff.
example : T2Space (AddAction.orbitRel.Quotient (AddSubgroup.zmultiples (1 : ℂ)) ℂ) :=
  inferInstance

-- The orbit projection `ℂ → ℂ / ℤ` is a local biholomorphism.
example : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
    (Quotient.mk (AddAction.orbitRel (AddSubgroup.zmultiples (1 : ℂ)) ℂ)) :=
  isLocalDiffeomorph_addQuotientMk

-- The orbit projection `ℂ → ℂ / ℤ` is a covering map with deck group the integer translations.
example : IsAddQuotientCoveringMap
    (Quotient.mk (AddAction.orbitRel (AddSubgroup.zmultiples (1 : ℂ)) ℂ))
    (AddSubgroup.zmultiples (1 : ℂ)) :=
  isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd

-- The cylinder `ℂ / ℤ` is not compact: integer translations preserve imaginary parts, so the
-- orbit of a point far up the imaginary axis misses every bounded set.
example : ¬ CompactSpace (AddAction.orbitRel.Quotient (AddSubgroup.zmultiples (1 : ℂ)) ℂ) := by
  rw [AddAction.compactSpace_orbitRelQuotient_iff_exists_isCompact]
  rintro ⟨K, hK, hKG⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨g, hg⟩ := hKG ((R + 1) * Complex.I)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
  have him := (Complex.abs_im_le_norm _).trans (mem_closedBall_zero_iff.1 (hR hg))
  rw [AddSubgroup.vadd_def, vadd_eq_add, Complex.add_im, ← hk] at him
  have him' : |R + 1| ≤ R := by simpa using him
  linarith [le_abs_self (R + 1)]

-- The closed unit square meets every orbit of the Gaussian integers acting on `ℂ` by
-- translation, so their orbit space is compact.
example : CompactSpace
    (AddAction.orbitRel.Quotient (AddSubgroup.closure {1, Complex.I} : AddSubgroup ℂ) ℂ) := by
  refine AddAction.compactSpace_orbitRelQuotient_of_isCompact
    (K := Icc 0 1 ×ℂ Icc 0 1) (isCompact_Icc.reProdIm isCompact_Icc) fun z ↦ ?_
  -- Translating by minus the integer parts of the coordinates lands in the unit square.
  refine ⟨⟨-(⌊z.re⌋ • 1 + ⌊z.im⌋ • Complex.I), ?_⟩, ?_⟩
  · exact neg_mem (add_mem (zsmul_mem (AddSubgroup.subset_closure (by simp)) _)
      (zsmul_mem (AddSubgroup.subset_closure (by simp)) _))
  · rw [AddSubgroup.vadd_def, vadd_eq_add, Complex.mem_reProdIm]
    simp [Int.floor_le, (Int.lt_floor_add_one _).le]
