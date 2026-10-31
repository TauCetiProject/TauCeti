/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.CategoryTheory.Limits.Lattice
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
public import TauCeti.RingTheory.Flat.Pi

/-!
# Čech complexes of presheaves with flat values

Let `α` be a meet-semilattice with a top element, for instance the opens of a topological space,
let `U : ι → α` be a finite family and let `P` be a presheaf of `R`-modules on `α`. The degree `n`
term of the Čech complex `Č(U, P)` is the product, over `a : Fin (n + 1) → ι`, of the values of
`P` on the intersections `U (a 0) ⊓ ⋯ ⊓ U (a n)`. As `ι` is finite this is a finite product, so
when `P` takes flat values on the nonempty finite intersections of `U`, every term of `Č(U, P)` is
a flat `R`-module (`TauCeti.CategoryTheory.flat_cechComplexFunctor_obj_X`).

For a quasi-coherent sheaf `M` on a scheme over `R` and a cover `U` with affine finite
intersections, with `P` the presheaf of `R`-modules of sections of `M`, this gives the complex of
flat modules computing the cohomology of every base change of `M`
(`TauCeti.AlgebraicGeometry.Cohomology.Cech.BaseChange`), as in the proof of Hartshorne's
Proposition III.12.2.

## Main results

* `TauCeti.CategoryTheory.flat_cechComplexFunctor_obj_X`: the terms of `Č(U, P)` are flat
  `R`-modules when the values of `P` on the nonempty finite intersections of `U` are.

## References

* R. Hartshorne, *Algebraic Geometry*, the Čech complex in the proof of Proposition III.12.2.
-/

public section

open CategoryTheory Limits Opposite

universe u v w

namespace TauCeti.CategoryTheory

variable {R : Type u} [CommRing R] {α : Type w} [SemilatticeInf α] [OrderTop α]

/-- **The Čech complex of a presheaf with flat values consists of flat modules.** Let `P` be a
presheaf of `R`-modules on a meet-semilattice with a top element and `U` a finite family such that
the value of `P` on every nonempty finite intersection of `U` is a flat `R`-module. Then every term
of the Čech complex of `P` for `U` is a flat `R`-module. -/
theorem flat_cechComplexFunctor_obj_X {ι : Type v} [Finite ι] (U : ι → α)
    (P : αᵒᵖ ⥤ ModuleCat.{v} R)
    (hP : ∀ s : Finset ι, s.Nonempty → Module.Flat R (P.obj (op (s.inf U)))) (n : ℕ) :
    Module.Flat R (((cechComplexFunctor U).obj P).X n) := by
  have (a : Fin (n + 1) → ι) : Module.Flat R (P.obj (op (∏ᶜ fun j ↦ U (a j)))) :=
    CompleteLattice.finite_product_of_forall_finset_inf (p := fun W ↦ Module.Flat R (P.obj (op W)))
      U hP a
  -- The degree `n` term of `cechComplexFunctor` is, by definition, this product of values of `P`,
  -- as in `cechComplexFunctor_map_f_π`.
  let e : ((cechComplexFunctor U).obj P).X n ≅
      ∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
    Iso.refl _
  exact Module.Flat.of_linearEquiv
    (e ≪≫ ModuleCat.piIsoPi fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))).toLinearEquiv

end TauCeti.CategoryTheory
