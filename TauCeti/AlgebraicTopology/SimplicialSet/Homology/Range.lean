/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Quasi-isomorphisms between ranges of monomorphisms

A monomorphism of simplicial sets `f : B ⟶ Z` is an isomorphism onto its range
(`SSet.Subcomplex.toRange`). So for monomorphisms `i : A ⟶ B` and `f : B ⟶ Z`, the inclusion of
the range of `i ≫ f` into the range of `f` is isomorphic, as an arrow, to `i`; in particular it is
a quasi-isomorphism on chains exactly when `i` is
(`SSet.quasiIso_chainComplexMap_iff_homOfLE_of_range_eq`). The ranges may be given by any
presentation as subcomplexes `S ≤ T` of `Z`.
-/

public section

open CategoryTheory Limits

universe u v w

namespace SSet

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- Let `i : A ⟶ B` and `f : B ⟶ Z` be monomorphisms of simplicial sets, and let `S ≤ T` be the
ranges of `i ≫ f` and of `f`. Then `i` is a quasi-isomorphism on chains exactly when the inclusion
of `S` into `T` is. -/
theorem quasiIso_chainComplexMap_iff_homOfLE_of_range_eq {A B Z : SSet.{u}} (i : A ⟶ B)
    (f : B ⟶ Z) [Mono i] [Mono f] {S T : Z.Subcomplex} (hST : S ≤ T)
    (hS : Subcomplex.range (i ≫ f) = S) (hT : Subcomplex.range f = T) :
    QuasiIso (chainComplexMap i R) ↔ QuasiIso (chainComplexMap (Subcomplex.homOfLE hST) R) := by
  subst hS hT
  have e : Subcomplex.toRange (i ≫ f) ≫ Subcomplex.homOfLE hST = i ≫ Subcomplex.toRange f := by
    rw [← cancel_mono (Subcomplex.range f).ι]
    simp
  have he := congrArg (chainComplexMap · R) e
  simp only [Functor.map_comp] at he
  rw [← quasiIso_iff_comp_right _ (chainComplexMap (Subcomplex.toRange f) R), ← he,
    quasiIso_iff_comp_left]

end SSet
