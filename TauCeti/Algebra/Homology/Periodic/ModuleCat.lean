/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Exactness of two-periodic complexes of modules

A two-periodic complex `C` of modules, a complex for the shape `ComplexShape.up (ZMod 2)`, has two
differentials `C.d 0 1 : C₀ → C₁` and `C.d 1 0 : C₁ → C₀`. In this shape the degree preceding `j`
is also the degree following it (`CochainComplex.prev_zmod_two`), so exactness in degree `j`
compares the image of the differential into `Cⱼ` with the kernel of the differential out of `Cⱼ`,
both involving the same other degree.

## Main results

* `CochainComplex.prev_zmod_two`: the degree preceding `j` in the two-periodic shape is `j + 1`.
* `HomologicalComplex.exactAt_iff_range_eq_ker`: exactness in a degree.
* `HomologicalComplex.acyclic_iff_range_eq_ker`: a two-periodic complex of modules is acyclic
  exactly when the image of each differential is the kernel of the other.
-/

public section

open CategoryTheory

/-- In the two-periodic shape, the degree preceding `j` is the degree `k = j + 1` following it. -/
theorem CochainComplex.prev_zmod_two {j k : ZMod 2} (hjk : j + 1 = k) :
    (ComplexShape.up (ZMod 2)).prev j = k := by
  have hkj : k + 1 = j := by
    subst hjk
    revert j
    decide
  exact ComplexShape.prev_eq' _ hkj

namespace HomologicalComplex

variable {R : Type*} [Ring R] (C : HomologicalComplex (ModuleCat R) (ComplexShape.up (ZMod 2)))

/-- A two-periodic complex of modules is exact in degree `j` exactly when the image of the
differential into degree `j` is the kernel of the differential out of degree `j`. -/
theorem exactAt_iff_range_eq_ker {j k : ZMod 2} (hjk : j + 1 = k) :
    C.ExactAt j ↔ LinearMap.range (C.d k j).hom = LinearMap.ker (C.d j k).hom :=
  (C.exactAt_iff' k j k (CochainComplex.prev_zmod_two hjk) (ComplexShape.next_eq' _ hjk)).trans
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _)

/-- A two-periodic complex of modules is acyclic exactly when the image of each differential is
the kernel of the other. -/
theorem acyclic_iff_range_eq_ker :
    C.Acyclic ↔ LinearMap.range (C.d 1 0).hom = LinearMap.ker (C.d 0 1).hom ∧
      LinearMap.range (C.d 0 1).hom = LinearMap.ker (C.d 1 0).hom := by
  rw [← C.exactAt_iff_range_eq_ker (zero_add 1), ← C.exactAt_iff_range_eq_ker (by decide)]
  refine ⟨fun h ↦ ⟨h 0, h 1⟩, fun h i ↦ ?_⟩
  fin_cases i
  exacts [h.1, h.2]

end HomologicalComplex
