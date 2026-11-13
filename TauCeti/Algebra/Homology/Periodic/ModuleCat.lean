/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Exactness of two-periodic complexes of modules

A two-periodic complex `C` of modules, a complex for the shape `ComplexShape.up (ZMod 2)`, has two
differentials `C.d 0 1 : C₀ → C₁` and `C.d 1 0 : C₁ → C₀`. In this shape the degree preceding `j`
is also the degree following it, since `ZMod 2` has characteristic two, so exactness in degree `j`
compares the image of the differential into `Cⱼ` with the kernel of the differential out of `Cⱼ`,
both involving the same other degree.

## Main results

* `HomologicalComplex.exactAt_iff_range_eq_ker_zmod_two`: exactness in a degree.
* `HomologicalComplex.acyclic_iff_range_eq_ker_zmod_two`: a two-periodic complex of modules is
  acyclic exactly when the image of each differential is the kernel of the other.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] (C : HomologicalComplex (ModuleCat R) (ComplexShape.up (ZMod 2)))

/-- A two-periodic complex of modules is exact in degree `j` exactly when the image of the
differential into degree `j` is the kernel of the differential out of degree `j`. -/
theorem exactAt_iff_range_eq_ker_zmod_two {j k : ZMod 2} (hjk : j + 1 = k) :
    C.ExactAt j ↔ LinearMap.range (C.d k j).hom = LinearMap.ker (C.d j k).hom :=
  C.exactAt_iff_range_eq_ker ((ComplexShape.up _).prev_eq' (hjk ▸ CharTwo.add_cancel_right j 1))
    ((ComplexShape.up _).next_eq' hjk)

/-- A two-periodic complex of modules is acyclic exactly when the image of each differential is
the kernel of the other. -/
theorem acyclic_iff_range_eq_ker_zmod_two :
    C.Acyclic ↔ LinearMap.range (C.d 1 0).hom = LinearMap.ker (C.d 0 1).hom ∧
      LinearMap.range (C.d 0 1).hom = LinearMap.ker (C.d 1 0).hom := by
  rw [← C.exactAt_iff_range_eq_ker_zmod_two (zero_add 1),
    ← C.exactAt_iff_range_eq_ker_zmod_two (CharTwo.add_self_eq_zero 1)]
  refine ⟨fun h ↦ ⟨h 0, h 1⟩, fun h i ↦ ?_⟩
  fin_cases i
  exacts [h.1, h.2]

/-- A two-periodic complex of modules whose differential `C.d i i'` vanishes is acyclic exactly
when the other differential `C.d i' i` is bijective. -/
theorem acyclic_iff_bijective_of_d_eq_zero {i i' : ZMod 2} (hii' : i + 1 = i')
    (hd : C.d i i' = 0) : C.Acyclic ↔ Function.Bijective (C.d i' i).hom := by
  have hi : C.ExactAt i ↔ Function.Surjective (C.d i' i).hom := by
    rw [C.exactAt_iff_range_eq_ker_zmod_two hii', hd, ModuleCat.hom_zero, LinearMap.ker_zero,
      LinearMap.range_eq_top]
  have hi' : C.ExactAt i' ↔ Function.Injective (C.d i' i).hom := by
    rw [C.exactAt_iff_range_eq_ker_zmod_two (hii' ▸ CharTwo.add_cancel_right i 1), hd,
      ModuleCat.hom_zero, LinearMap.range_zero, eq_comm, LinearMap.ker_eq_bot]
  rw [Function.Bijective, ← hi, ← hi']
  refine ⟨fun h ↦ ⟨h i', h i⟩, fun h m ↦ ?_⟩
  have hm : ∀ a b : ZMod 2, b = a ∨ b = a + 1 := by decide
  obtain rfl | rfl : m = i ∨ m = i' := hii' ▸ hm i m
  exacts [h.2, h.1]

end HomologicalComplex
