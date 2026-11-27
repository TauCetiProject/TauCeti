/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Filtration.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The total tensor filtration in coordinates

Let `b` be a basis of `M` and `deg` a degree on its indices, such that the `k`-th step `F k` of a
filtration of `M` is spanned by the basis vectors of degree at most `k`; for instance a basis of a
graded module made of homogeneous elements, with the filtration by degree. Every `t ∈ M ⊗ N` is
uniquely `∑ᵢ bᵢ ⊗ tᵢ` (`TensorProduct.equivFinsuppOfBasisLeft`). For an increasing family `G` of
submodules of `N`, `t` has total degree at most `n` exactly when every coefficient `tᵢ` lies in
`G (n - deg i)`, and vanishes if `deg i > n` (`TauCeti.mem_tensorFiltration_iff_of_basis`).

Consequently the total filtration is **strict** for an injective map `f : N' → N` on the second
factor: `t ∈ M ⊗ N'` has total degree at most `n` for the restricted family `f⁻¹(G j)` exactly
when its image `(id ⊗ f) t` has total degree at most `n` for `G`
(`TauCeti.lTensor_mem_tensorFiltration_iff_of_basis`). Without the basis this can fail, since
`(id ⊗ f) t` may be a sum of pure tensors of low degree that do not come from `M ⊗ N'`.

## Main results

* `TauCeti.tensorFiltration_le_comap_map`: tensor products of maps preserving the factor families
  preserve the total filtration.
* `TauCeti.mem_tensorFiltration_iff_of_basis`: the coefficient criterion.
* `TauCeti.lTensor_mem_tensorFiltration_iff_of_basis`: strictness along an injective map of the
  second factor.
-/

public section

open scoped TensorProduct

namespace TauCeti

open Submodule TensorProduct

variable {R M N : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Tensoring linear maps preserving the factor families preserves the total filtration. -/
theorem tensorFiltration_le_comap_map {M' N' : Type*}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    {F : ℕ → Submodule R M} {G : ℕ → Submodule R N}
    {F' : ℕ → Submodule R M'} {G' : ℕ → Submodule R N'}
    {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    (hf : ∀ i, F i ≤ (F' i).comap f) (hg : ∀ j, G j ≤ (G' j).comap g) (n : ℕ) :
    tensorFiltration F G n ≤ (tensorFiltration F' G' n).comap (TensorProduct.map f g) :=
  tensorFiltration_le_iff.mpr fun i j hij x hx y hy ↦ by
    simpa only [Submodule.mem_comap, TensorProduct.map_tmul] using
      tmul_mem_tensorFiltration hij (hf i hx) (hg j hy)

section Basis

variable {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R M) (deg : ι → ℕ)

/-- The submodule allowed for the `i`-th coefficient of a tensor of total degree at most `n`:
`G (n - deg i)` if `deg i ≤ n`, and `0` otherwise. -/
private def coeffBound (G : ℕ → Submodule R N) (n : ℕ) (i : ι) : Submodule R N :=
  if deg i ≤ n then G (n - deg i) else ⊥

/-- **Coefficient criterion for the total filtration.** If `F k` is spanned by the basis vectors
`b i` with `deg i ≤ k`, and `G` is increasing, then `t = ∑ᵢ bᵢ ⊗ tᵢ` has total degree at most
`n` exactly when `tᵢ ∈ G (n - deg i)` for `deg i ≤ n`, and `tᵢ = 0` for `deg i > n`. -/
theorem mem_tensorFiltration_iff_of_basis {F : ℕ → Submodule R M}
    (hF : ∀ k, F k = span R (b '' {i | deg i ≤ k})) {G : ℕ → Submodule R N} (hG : Monotone G)
    {n : ℕ} {t : M ⊗[R] N} :
    t ∈ tensorFiltration F G n ↔
      ∀ i, equivFinsuppOfBasisLeft b t i ∈ if deg i ≤ n then G (n - deg i) else ⊥ := by
  let P : Submodule R (M ⊗[R] N) := ⨅ i, (coeffBound deg G n i).comap
    ((Finsupp.lapply i).comp (equivFinsuppOfBasisLeft b).toLinearMap)
  have hP : ∀ s, s ∈ P ↔ ∀ i, equivFinsuppOfBasisLeft b s i ∈ coeffBound deg G n i := fun s ↦ by
    simp [P]
  change t ∈ tensorFiltration F G n ↔ ∀ i, _ ∈ coeffBound deg G n i
  rw [← hP]
  refine ⟨fun ht ↦ tensorFiltration_le_iff.mpr ?_ ht, fun ht ↦ ?_⟩
  · intro k j hkj x hx y hy
    refine (hP _).mpr fun i ↦ ?_
    rw [equivFinsuppOfBasisLeft_apply_tmul_apply]
    by_cases hi : b.repr x i = 0
    · rw [hi, zero_smul]
      exact zero_mem _
    have hik : deg i ≤ k := by
      rw [hF, Module.Basis.mem_span_image] at hx
      exact hx (Finsupp.mem_support_iff.mpr hi)
    rw [coeffBound, ite_eq_left_iff.mpr fun h ↦ absurd (hik.trans (le_of_add_le_left hkj)) h]
    exact smul_mem _ _ (hG (by omega) hy)
  · rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply t, equivFinsuppOfBasisLeft_symm_apply]
    refine sum_mem fun i hi ↦ ?_
    have hc := (hP t).mp ht i
    rw [coeffBound] at hc
    split_ifs at hc with hin
    · refine tmul_mem_tensorFiltration (i := deg i) (by omega) ?_ hc
      rw [hF]
      exact subset_span ⟨i, Set.mem_ofPred_eq ▸ le_rfl, rfl⟩
    · exact absurd ((mem_bot R).mp hc) (Finsupp.mem_support_iff.mp hi)

/-- The coefficients of `(id ⊗ f) t` are the images under `f` of the coefficients of `t`. -/
theorem equivFinsuppOfBasisLeft_lTensor_apply {N' : Type*} [AddCommMonoid N'] [Module R N']
    (f : N' →ₗ[R] N) (t : M ⊗[R] N') (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor M t) i = f (equivFinsuppOfBasisLeft b t i) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add s t hs ht => simp only [map_add, Finsupp.add_apply, hs, ht]

omit [DecidableEq ι] in
/-- **Strictness of the total filtration along an injective map of the second factor.** If
`F k` is spanned by the basis vectors of degree at most `k`, `G` is increasing and `f` is
injective, then `t ∈ M ⊗ N'` has total degree at most `n` for the family `f⁻¹(G j)` exactly when
`(id ⊗ f) t` has total degree at most `n` for `G`. -/
theorem lTensor_mem_tensorFiltration_iff_of_basis {N' : Type*} [AddCommMonoid N'] [Module R N']
    {F : ℕ → Submodule R M} (hF : ∀ k, F k = span R (b '' {i | deg i ≤ k}))
    {G : ℕ → Submodule R N} (hG : Monotone G) {f : N' →ₗ[R] N} (hf : Function.Injective f)
    {n : ℕ} {t : M ⊗[R] N'} :
    f.lTensor M t ∈ tensorFiltration F G n ↔
      t ∈ tensorFiltration F (fun j ↦ (G j).comap f) n := by
  classical
  rw [mem_tensorFiltration_iff_of_basis b deg hF hG,
    mem_tensorFiltration_iff_of_basis b deg hF (G := fun j ↦ (G j).comap f)
      fun _ _ h ↦ comap_mono (hG h)]
  refine forall_congr' fun i ↦ ?_
  rw [equivFinsuppOfBasisLeft_lTensor_apply]
  split_ifs
  · exact mem_comap.symm
  · simp only [mem_bot]
    exact ⟨fun h ↦ hf (h.trans (map_zero f).symm), fun h ↦ h ▸ map_zero f⟩

end Basis

end TauCeti
