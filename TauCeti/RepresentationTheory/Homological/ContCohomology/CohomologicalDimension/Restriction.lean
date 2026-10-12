/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Cohomological dimension and subgroups with injective restriction

Let `G` be a topological group and `H` a subgroup. If restriction `Hⁱ⁺¹(G, M) → Hⁱ⁺¹(H, M)` is
injective for every discrete `p`-primary torsion `G`-module `M` and every `i`, then vanishing of
cohomology transfers from `H` to `G`: `CohomologicalDimensionLE p H n` implies
`CohomologicalDimensionLE p G n`, and consequently `cd_p G ≤ cd_p H`. No topological hypothesis on
`G` or `H` is needed.

This is the common formal step behind the comparisons of `cd_p G` with the cohomological
dimension of a subgroup on which restriction is injective, such as an open subgroup of index
prime to `p` or a closed subgroup all of whose open neighbourhoods have index prime to `p`
(`TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.IndexNotDvd`).

## Main results

* `TauCeti.CohomologicalDimensionLE.of_forall_res_injective`: vanishing transfers along a
  subgroup on which restriction is injective in every positive degree.
* `TauCeti.cohomologicalDimensionAt_le_of_forall_res_injective`: **`cd_p G ≤ cd_p H`** for a
  subgroup `H` on which restriction is injective in every positive degree, for every discrete
  `p`-primary torsion `G`-module.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Vanishing transfers along a subgroup on which restriction is injective**, as the vanishing
predicate: if restriction `Hⁱ⁺¹(G, M) → Hⁱ⁺¹(H, M)` is injective for every discrete `p`-primary
torsion `G`-module `M` and every `i`, then `CohomologicalDimensionLE p H n` implies
`CohomologicalDimensionLE p G n`. -/
theorem CohomologicalDimensionLE.of_forall_res_injective {H : Subgroup G}
    (hres : ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M → ∀ i : ℕ,
      Function.Injective (ContinuousCohomology.res H (ofDiscreteModule ℤ G M) (i + 1)).hom)
    {n : ℕ} (h : CohomologicalDimensionLE.{v} p H n) : CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ hM i hi
  obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- `Hⁱ⁺¹(H, M)` vanishes, and restriction to `H` is injective.
  have hsub : Subsingleton (continuousCohomology (i + 1)
      (TopRep.res (H.subtype : H →* G) (ofDiscreteModule ℤ G M))) := by
    rw [res_ofDiscreteModule]
    exact h M hM (i + 1) hi
  exact subsingleton_of_forall_eq 0 fun x ↦ (injective_iff_map_eq_zero _).1 (hres M hM i) x
    (Subsingleton.elim _ _)

/-- **`cd_p G ≤ cd_p H` for a subgroup `H` on which restriction is injective**: if restriction
`Hⁱ⁺¹(G, M) → Hⁱ⁺¹(H, M)` is injective for every discrete `p`-primary torsion `G`-module `M` and
every `i`, then the `p`-cohomological dimension of `G` is at most that of `H`. -/
theorem cohomologicalDimensionAt_le_of_forall_res_injective {H : Subgroup G}
    (hres : ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M → ∀ i : ℕ,
      Function.Injective (ContinuousCohomology.res H (ofDiscreteModule ℤ G M) (i + 1)).hom) :
    cohomologicalDimensionAt.{v} p G ≤ cohomologicalDimensionAt.{v} p H := by
  induction hcd : cohomologicalDimensionAt.{v} p H using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    exact (cohomologicalDimensionAt_le_iff p G n).2
      (((cohomologicalDimensionAt_le_iff p H n).1 hcd.le).of_forall_res_injective hres)

end TauCeti
