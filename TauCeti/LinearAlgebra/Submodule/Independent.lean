/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.SupIndep
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Independent families of submodules, traces and kernels

The traces `(I i).comap S.subtype` of an independent family of submodules `I` on a submodule `S`
are independent (`iSupIndep.comap_subtype`). If a linear map carries each member of a spanning
family into the corresponding member of an independent family, then its kernel is spanned by its
intersections with the members of the source family, `LinearMap.ker_eq_iSup_inf_of_map_le`
(for the part of the kernel in the span, `LinearMap.ker_inf_iSup_eq_iSup_inf_of_map_le`).
Conversely, `iSupIndep.map_of_ker_inf_iSup_le` shows that a semilinear map preserves independence
when the part of its kernel in the span is spanned by its intersections with the summands.
-/

public section

/-- The traces of an independent family of submodules on a submodule `S` are independent. -/
theorem iSupIndep.comap_subtype {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {S : Submodule R M} {I : ι → Submodule R M} (hI : iSupIndep I) :
    iSupIndep fun i ↦ (I i).comap S.subtype := by
  let e : Submodule R S ≃o Set.Iic S := S.mapIic
  rw [← iSupIndep_map_orderIso_iff e]
  have he : (e ∘ fun i ↦ (I i).comap S.subtype) = fun i ↦
      ⟨I i ⊓ S, Set.mem_Iic.mpr inf_le_right⟩ := by
    funext i
    apply Subtype.ext
    simp only [Function.comp_apply, e, Submodule.coe_mapIic_apply, Submodule.map_comap_subtype]
    rw [inf_comm]
  rw [he]
  exact iSupIndep.of_coe_Iic_comp (hI.mono fun _ ↦ inf_le_left)

namespace LinearMap

variable {R R₂ ι M N : Type*} [Semiring R] [Ring R₂] {σ : R →+* R₂} [RingHomSurjective σ]
  [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R₂ N]

/-- **The part of the kernel of a map compatible with a decomposition lying in the span is spanned
by its homogeneous parts.**
If the submodules `A' i` are independent and `g` carries `A i` into `A' i`, then the intersection of
the kernel of `g` with the span of the `A i` is the supremum of its intersections with the `A i`. -/
theorem ker_inf_iSup_eq_iSup_inf_of_map_le (g : M →ₛₗ[σ] N) {A : ι → Submodule R M}
    {A' : ι → Submodule R₂ N} (hA' : iSupIndep A') (hg : ∀ i, (A i).map g ≤ A' i) :
    ker g ⊓ (⨆ i, A i) = ⨆ i, ker g ⊓ A i := by
  classical
  refine le_antisymm (fun x ⟨hx, hxA⟩ ↦ ?_) (iSup_le fun i ↦ inf_le_inf_left _ (le_iSup A i))
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp A x).1 hxA
  have hsum : ∑ i ∈ c.support, g (c i) = 0 := by
    rw [← map_sum]
    simpa [Finsupp.sum] using hx
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A').1 hA' c.support
    (fun i ↦ g (c i)) (fun i _ ↦ hg i ⟨c i, hc i, rfl⟩) hsum
  simp only [Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi ↦
    Submodule.mem_iSup_of_mem i ⟨mem_ker.2 (hzero i hi), hc i⟩

/-- **The kernel of a map compatible with a decomposition is spanned by its homogeneous parts.**
If the submodules `A i` span the source, the submodules `A' i` are independent, and `g` carries
`A i` into `A' i`, then the kernel of `g` is the supremum of its intersections with the `A i`.

The hypothesis on the source is only that its family spans; independence there is not used, and
an internal direct sum supplies it through `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
theorem ker_eq_iSup_inf_of_map_le (g : M →ₛₗ[σ] N) {A : ι → Submodule R M}
    {A' : ι → Submodule R₂ N} (hA : ⨆ i, A i = ⊤) (hA' : iSupIndep A')
    (hg : ∀ i, (A i).map g ≤ A' i) :
    ker g = ⨆ i, ker g ⊓ A i := by
  simpa [hA] using ker_inf_iSup_eq_iSup_inf_of_map_le g hA' hg

end LinearMap

/-- A semilinear map preserves independence of a family of submodules if the part of its kernel
in their span is spanned by its intersections with the family. In particular, a quotient by a
homogeneous submodule preserves independence.

The group hypothesis on the source is essential: for semimodules, even a map with zero kernel can
identify independent summands. -/
theorem iSupIndep.map_of_ker_inf_iSup_le {R R₂ ι M N : Type*} [Ring R] [Ring R₂]
    {σ : R →+* R₂} [RingHomSurjective σ] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R₂ N] {A : ι → Submodule R M} (hA : iSupIndep A) (f : M →ₛₗ[σ] N)
    (hker : LinearMap.ker f ⊓ (⨆ i, A i) ≤ ⨆ i, LinearMap.ker f ⊓ A i) :
    iSupIndep fun i ↦ (A i).map f := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  classical
  intro s v hv hv0 j hj
  have hall : ∀ i : ι, ∃ y, y ∈ A i ∧ (i ∈ s → f y = v i) ∧ (i ∉ s → y = 0) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨y, hy, hf⟩ := Submodule.mem_map.1 (hv i hi)
      exact ⟨y, hy, fun _ ↦ hf, fun h ↦ absurd hi h⟩
    · exact ⟨0, Submodule.zero_mem _, fun h ↦ absurd h hi, fun _ ↦ rfl⟩
  choose a haA haf ha0 using hall
  have hasum : ∑ i ∈ s, a i ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sum]
    exact (Finset.sum_congr rfl fun i hi ↦ haf i hi).trans hv0
  have hasumA : ∑ i ∈ s, a i ∈ ⨆ i, A i :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i (haA i)
  obtain ⟨c, hc, hca⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hker ⟨hasum, hasumA⟩)
  have haj : a j = c j := by
    refine (iSupIndep_iff_finsetSum_eq_imp_eq A).1 hA (s ∪ c.support) a c
      (fun i _ ↦ ⟨haA i, (hc i).2⟩) ?_ j (Finset.mem_union_left _ hj)
    calc
        ∑ i ∈ s ∪ c.support, a i = ∑ i ∈ s, a i := by
          symm
          apply Finset.sum_subset (Finset.subset_union_left)
          intro i _ hi
          exact ha0 i hi
        _ = ∑ i ∈ c.support, c i := hca.symm
        _ = ∑ i ∈ s ∪ c.support, c i := by
          apply Finset.sum_subset (Finset.subset_union_right)
          simp
  rw [← haf j hj, haj]
  exact LinearMap.mem_ker.mp (hc j).1
