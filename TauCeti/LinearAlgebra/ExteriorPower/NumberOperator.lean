/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KoszulComplex.Basic
import Mathlib.Data.Finset.Prod

/-!
# Number operators on exterior powers

For a finite basis `b`, let `εᵢ` be exterior multiplication by `b i` and `ιᵢ` contraction
by its coordinate functional. On degree `p`, the number operator `∑ i, εᵢ ιᵢ` is
`p • Id`. The increasing-pair operator `∑ i < j, εⱼ εᵢ ιᵢ ιⱼ` is
`p.choose 2 • Id`. These identities count occupied coordinates, with no division by
two, and hold over any commutative ring.

For an orthonormal basis the contractions are adjoints of exterior multiplication.
The identities then give the one- and two-contraction norm sums used in curvature
estimates on differential forms.

The proof uses `TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis` and
`TauCeti.ExteriorAlgebra.ι_mul_ι_mul_contractLeft_contractLeft_coord_basis`, the single and pair
occupation projections on the exterior-algebra basis, and Mathlib's
`Finset.card_product_filter_lt` to count increasing pairs.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, §6.1.
-/

public section

noncomputable section

open TauCeti CliffordAlgebra

namespace Module.Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [LinearOrder ι] (b : Basis ι R M)

omit [LinearOrder ι] in
/-- The sum of creation after coordinate contraction is multiplication by the degree. -/
theorem sum_wedgeLeft_comp_koszulDifferential_coord (n : ℕ) :
    ∑ i, ExteriorAlgebra.wedgeLeft (b i) n ∘ₗ koszulDifferential (b.coord i) n =
      (n + 1) • LinearMap.id := by
  classical
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  apply (b.exteriorPower (n + 1)).ext
  intro s
  apply Subtype.ext
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_sum,
    ExteriorAlgebra.coe_wedgeLeft_apply, coe_koszulDifferential_apply,
    ← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.ι_mul_contractLeft_coord_basis, LinearMap.smul_apply,
    LinearMap.id_apply, Submodule.coe_smul_of_tower]
  simp only [← Finset.sum_filter, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Set.powersetCard.card_eq]

/-- The increasing-pair creation/contraction sum is multiplication by the binomial
coefficient of the degree. The ordering counts each unordered pair exactly once. -/
theorem sum_wedgeLeft_comp_wedgeLeft_comp_koszulDifferential_comp_koszulDifferential_coord
    (n : ℕ) :
    ∑ ij ∈ Finset.univ.filter (fun ij : ι × ι ↦ ij.1 < ij.2),
      ExteriorAlgebra.wedgeLeft (b ij.2) (n + 1) ∘ₗ
        ExteriorAlgebra.wedgeLeft (b ij.1) n ∘ₗ
          koszulDifferential (b.coord ij.1) n ∘ₗ
            koszulDifferential (b.coord ij.2) (n + 1) =
      (n + 2).choose 2 • LinearMap.id := by
  classical
  apply (b.exteriorPower (n + 2)).ext
  intro s
  apply Subtype.ext
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_sum,
    ExteriorAlgebra.coe_wedgeLeft_apply, coe_koszulDifferential_apply,
    ← _root_.ExteriorAlgebra.basis_eq_coe_basis, LinearMap.smul_apply,
    LinearMap.id_apply, Submodule.coe_smul_of_tower]
  rw [Finset.sum_congr rfl fun ij hij ↦
    ExteriorAlgebra.ι_mul_ι_mul_contractLeft_contractLeft_coord_basis b
      (Finset.mem_filter.mp hij).2.ne s.val]
  have hfilter : (Finset.univ.filter
      (fun ij : ι × ι ↦ ij.1 < ij.2)).filter (fun ij ↦ ij.1 ∈ s.val ∧ ij.2 ∈ s.val) =
      (s.val ×ˢ s.val).filter (fun ij ↦ ij.1 < ij.2) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    tauto
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_product_filter_lt,
    Set.powersetCard.card_eq]

end Module.Basis
