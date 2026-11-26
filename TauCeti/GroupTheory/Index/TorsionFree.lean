/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.GroupTheory.Index.CosetAction
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Divisibility of the index of a torsion-free subgroup by orders of torsion elements

If `H` is a torsion-free subgroup (`IsMulTorsionFree H`) of a group `G`, no nonidentity finite-order
element of `G` has a conjugate in `H`:

* any torsion subgroup `K ≤ G` acts freely on `G ⧸ H`;
* for every finite subgroup `K ≤ G`, `Nat.card K ∣ H.index`;
* for every element `x : G` of finite order, `orderOf x ∣ H.index`.

## Main results

* `Subgroup.isCancelSMul_quotient_of_isMulTorsionFree`: a torsion subgroup `K` acts freely on
  `G ⧸ H` when `H` is torsion-free.
* `Subgroup.natCard_dvd_index_of_isMulTorsionFree`: `Nat.card K ∣ H.index` when `H` is torsion-free
  and `K` is finite.
* `Subgroup.orderOf_dvd_index_of_isMulTorsionFree`: `orderOf x ∣ H.index` for any finite-order
  element `x : G` and torsion-free subgroup `H ≤ G`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- If `H` is torsion-free, then any subgroup `K` all of whose elements have finite order acts
freely on `G ⧸ H`. -/
theorem isCancelSMul_quotient_of_isMulTorsionFree (H K : Subgroup G) [IsMulTorsionFree H]
    (hK : ∀ k : K, IsOfFinOrder k) : IsCancelSMul K (G ⧸ H) := by
  refine isCancelSMul_quotient_iff.mpr fun k hk g hmem ↦ ?_
  have hfin_k : IsOfFinOrder k := K.subtype.isOfFinOrder (hK ⟨k, hk⟩)
  have hconj : IsConj (g⁻¹ * k * g) k := isConj_iff.mpr ⟨g, by simp [mul_assoc]⟩
  have hfin_conj : IsOfFinOrder (g⁻¹ * k * g) := hconj.symm.isOfFinOrder hfin_k
  have hfin_sub : IsOfFinOrder (⟨g⁻¹ * k * g, hmem⟩ : H) :=
    (H.subtype_injective.isOfFinOrder_iff (f := H.subtype) (x := ⟨g⁻¹ * k * g, hmem⟩)).mp hfin_conj
  have hsub1 : (⟨g⁻¹ * k * g, hmem⟩ : H) = 1 := (isOfFinOrder_iff_eq_one _).mp hfin_sub
  have hconj1 : g⁻¹ * k * g = 1 := congrArg Subtype.val hsub1
  simpa [mul_assoc] using congrArg (fun x ↦ g * x * g⁻¹) hconj1

/-- The cardinality of any finite subgroup `K ≤ G` divides the index of any torsion-free subgroup
`H ≤ G`. -/
theorem natCard_dvd_index_of_isMulTorsionFree (H K : Subgroup G) [IsMulTorsionFree H] [Finite K] :
    Nat.card K ∣ H.index :=
  natCard_dvd_index_of_forall_conj_mem
    (isCancelSMul_quotient_iff.mp
      (isCancelSMul_quotient_of_isMulTorsionFree H K isOfFinOrder_of_finite))

/-- The order of any finite-order element `x : G` divides the index of any torsion-free subgroup
`H ≤ G`. -/
theorem orderOf_dvd_index_of_isMulTorsionFree (H : Subgroup G) [IsMulTorsionFree H] {x : G}
    (hx : IsOfFinOrder x) : orderOf x ∣ H.index := by
  have : Finite (zpowers x) := hx.finite_zpowers
  simpa only [Nat.card_zpowers] using H.natCard_dvd_index_of_isMulTorsionFree (zpowers x)

end Subgroup
