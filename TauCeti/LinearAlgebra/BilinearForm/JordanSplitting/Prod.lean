/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.Submodule.Prod

/-!
# Jordan splittings of orthogonal sums

Jordan splittings of two forms combine scale by scale into a Jordan splitting of their orthogonal
sum: if `N` is a Jordan splitting of a form `B` on `M` and `N'` one of a form `C`
on `M'`, then the products `N i × N' i` form a Jordan splitting of the block-diagonal form
`B.prod C` on `M × M'` (`LinearMap.BilinForm.IsJordanSplitting.prod`). This is how the Jordan
data of an orthogonal sum of lattices are read off those of the summands.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {B : BilinForm R M} {C : BilinForm R M'} {π : R} {N : ℕ → Submodule R M}
  {N' : ℕ → Submodule R M'}

/-- **Jordan splittings of an orthogonal sum.** If `N` and `N'` are Jordan splittings of the
forms `B` and `C` with respect to `π`, then the products `N i × N' i` form a Jordan splitting of
the block-diagonal form `B.prod C`. -/
theorem IsJordanSplitting.prod (h : B.IsJordanSplitting π N) (h' : C.IsJordanSplitting π N') :
    (B.prod C).IsJordanSplitting π (fun i ↦ (N i).prod (N' i)) where
  isInternal := by
    obtain ⟨hind, htop⟩ :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).mp h.isInternal
    obtain ⟨hind', htop'⟩ :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N').mp h'.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨hind.prod hind', ?_⟩
    rw [TauCeti.iSup_prod_submodule, htop, htop', Submodule.prod_top]
  apply_eq_zero i j hij x hx y hy := by
    rw [prod_apply, h.apply_eq_zero i j hij _ hx.1 _ hy.1, h'.apply_eq_zero i j hij _ hx.2 _ hy.2,
      add_zero]
  isModular i := (h.isModular i).restrict_prod (h'.isModular i)

end LinearMap.BilinForm
