/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Prod

/-!
# Jordan splittings of orthogonal sums

The constituent of scale `π ^ i` of an orthogonal sum is the orthogonal sum of the constituents
of scale `π ^ i`: if `N` is a Jordan splitting of a symmetric form `B` on `M` and `N'` one of a
symmetric form `C` on `M'`, then the products `N i × N' i` form a Jordan splitting of the
block-diagonal form `B.prod C` on `M × M'`
(`LinearMap.BilinForm.IsJordanSplitting.prod`). This is how the Jordan data of an orthogonal sum
of lattices are read off those of the summands.

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
symmetric forms `B` and `C` with respect to a non-zero-divisor `π`, then the products
`N i × N' i` form a Jordan splitting of the block-diagonal form `B.prod C`. -/
theorem IsJordanSplitting.prod (h : B.IsJordanSplitting π N) (h' : C.IsJordanSplitting π N')
    (hB : B.IsSymm) (hC : C.IsSymm) (hπ : π ∈ nonZeroDivisors R) :
    (B.prod C).IsJordanSplitting π (fun i ↦ (N i).prod (N' i)) where
  isInternal := by
    obtain ⟨hind, htop⟩ :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).mp h.isInternal
    obtain ⟨hind', htop'⟩ :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N').mp h'.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
    · -- The constituents other than the `i`-th lie in the product of the corresponding sums.
      refine iSupIndep_def.mpr fun i ↦ Submodule.disjoint_def.mpr fun x hx hx' ↦ ?_
      have hle : (⨆ (j) (_ : j ≠ i), (N j).prod (N' j)) ≤
          (⨆ (j) (_ : j ≠ i), N j).prod (⨆ (j) (_ : j ≠ i), N' j) :=
        iSup₂_le fun j hj ↦ Submodule.prod_mono (le_iSup₂ (f := fun j (_ : j ≠ i) ↦ N j) j hj)
          (le_iSup₂ (f := fun j (_ : j ≠ i) ↦ N' j) j hj)
      obtain ⟨hx1, hx2⟩ := hle hx'
      exact Prod.ext (Submodule.disjoint_def.mp (iSupIndep_def.mp hind i) _ hx.1 hx1)
        (Submodule.disjoint_def.mp (iSupIndep_def.mp hind' i) _ hx.2 hx2)
    · refine eq_top_iff.mpr fun x _ ↦ ?_
      rw [← Prod.fst_add_snd x]
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.iSup_induction N (motive := fun y ↦ (y, 0) ∈ ⨆ i, (N i).prod (N' i))
          (htop ▸ Submodule.mem_top) (fun i y hy ↦ ?_) (Submodule.zero_mem _) fun y z hy hz ↦ ?_
        · exact Submodule.mem_iSup_of_mem i ⟨hy, (N' i).zero_mem⟩
        · simpa using Submodule.add_mem _ hy hz
      · refine Submodule.iSup_induction N' (motive := fun y ↦ (0, y) ∈ ⨆ i, (N i).prod (N' i))
          (htop' ▸ Submodule.mem_top) (fun i y hy ↦ ?_) (Submodule.zero_mem _) fun y z hy hz ↦ ?_
        · exact Submodule.mem_iSup_of_mem i ⟨(N i).zero_mem, hy⟩
        · simpa using Submodule.add_mem _ hy hz
  apply_eq_zero i j hij x hx y hy := by
    rw [prod_apply, h.apply_eq_zero i j hij _ hx.1 _ hy.1, h'.apply_eq_zero i j hij _ hx.2 _ hy.2,
      add_zero]
  isModular i := by
    rw [LinearMap.prod_eq_sup_map]
    refine IsModular.restrict_sup (isSymm_prod_iff.mpr ⟨hB, hC⟩) (pow_mem hπ i) ?_ ?_ ?_
    · exact (isModular_restrict_map_iff (LinearMap.inl_injective) (by simp)).mpr (h.isModular i)
    · exact (isModular_restrict_map_iff (LinearMap.inr_injective) (by simp)).mpr (h'.isModular i)
    · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
      simp

end LinearMap.BilinForm
