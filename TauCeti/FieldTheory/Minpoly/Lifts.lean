/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Minimal polynomials with coefficients in a subfield

Let `k → F` be a ring map and `x` an element of an `F`-algebra, integral over `F`. If the
coefficients of the minimal polynomial `minpoly F x` all come from `k`, then `x` is already
integral over `k`. For a field extension `k → F`, Mathlib's `minpoly.map_algebraMap` then says
that `minpoly k x` is `minpoly F x` with its coefficients read in `k`, so adjoining `x` to `k` or
to `F` gives extensions of the same degree.

This is how a field generated over `F` by one element is descended to `k`: once the minimal
polynomial of the generator is known to have coefficients in `k`, for instance because it is fixed
by automorphisms whose fixed field is `k`, the field `k⟮x⟯` is a model of `F⟮x⟯` of the same
degree.

## Main results

* `IsIntegral.of_minpoly_mem_lifts`: `x` is integral over `k`.
* `IntermediateField.finrank_adjoin_simple_eq_of_minpoly_mem_lifts`: `[k⟮x⟯ : k] = [F⟮x⟯ : F]`.
-/

public section

open IntermediateField Polynomial

variable {k F E : Type*}

section Ring

variable [CommRing k] [CommRing F] [Algebra k F] [Ring E] [Algebra k E] [Algebra F E]
  [IsScalarTower k F E]

/-- An element integral over `F` whose minimal polynomial over `F` has all its coefficients in
the image of `k` is integral over `k`. -/
theorem IsIntegral.of_minpoly_mem_lifts {x : E} (hx : IsIntegral F x)
    (h : minpoly F x ∈ lifts (algebraMap k F)) : IsIntegral k x := by
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic hx)
  exact ⟨g, hgm, by rw [← aeval_def, ← aeval_map_algebraMap F, hg, minpoly.aeval]⟩

end Ring

variable [Field k] [Field F] [Algebra k F] [Field E] [Algebra k E] [Algebra F E]
  [IsScalarTower k F E]

/-- If `x` is integral over `F` and its minimal polynomial over `F` has all its coefficients in the
subfield `k`, then adjoining `x` to `k` and to `F` gives extensions of the same degree. -/
theorem IntermediateField.finrank_adjoin_simple_eq_of_minpoly_mem_lifts {x : E}
    (hx : IsIntegral F x) (h : minpoly F x ∈ lifts (algebraMap k F)) :
    Module.finrank k k⟮x⟯ = Module.finrank F F⟮x⟯ := by
  have hxk := hx.of_minpoly_mem_lifts h
  rw [adjoin.finrank hxk, adjoin.finrank hx, ← minpoly.map_algebraMap hxk h, natDegree_map]
