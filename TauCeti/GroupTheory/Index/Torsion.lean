/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Divisibility of subgroup indices by orders of torsion elements

If a subgroup `K ≤ G` meets every conjugate of a subgroup `H ≤ G` trivially, then `K` acts freely
on the coset space `G ⧸ H` by left multiplication, so `Nat.card K` divides `H.index` without any
finiteness hypothesis on `H.index` (`0` is divisible by every natural number). In particular, if
`H` contains no nontrivial element of finite order (for instance when `H` is torsion-free), the
order of every torsion element of `G` divides `H.index`.

## Main results

* `Subgroup.natCard_dvd_index_of_forall_conj_mem`: if `g⁻¹ * k * g ∈ H → k = 1` for all `g : G`
  and `k ∈ K`, then `Nat.card K ∣ H.index`.
* `Subgroup.orderOf_dvd_index_of_forall_isOfFinOrder_eq_one`: if `H` has no nontrivial torsion
  elements, then `orderOf x ∣ H.index` for every torsion element `x : G`.
* `Subgroup.eq_one_of_isOfFinOrder_mem`: a torsion-free subgroup contains no nontrivial ambient
  element of finite order.
* `Subgroup.orderOf_dvd_index_of_isMulTorsionFree`: typeclass form for `[IsMulTorsionFree H]`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- If `H ≤ G` is torsion-free, every element of `H` that has finite order in `G` is `1`. -/
theorem eq_one_of_isOfFinOrder_mem (H : Subgroup G) [IsMulTorsionFree H]
    {x : G} (hx : x ∈ H) (hfin : IsOfFinOrder x) : x = 1 :=
  congrArg Subtype.val (Submonoid.isOfFinOrder_coe.mp hfin : IsOfFinOrder (⟨x, hx⟩ : H)).eq_one'

/-- If a subgroup `K ≤ G` meets every conjugate of `H ≤ G` trivially, then `K` acts freely on
`G ⧸ H`, so `Nat.card K` divides `H.index`. No finiteness assumption on `H.index` is required. -/
theorem natCard_dvd_index_of_forall_conj_mem (H K : Subgroup G)
    (h : ∀ g : G, ∀ k ∈ K, g⁻¹ * k * g ∈ H → k = 1) :
    Nat.card K ∣ H.index := by
  have hcanc : IsCancelSMul K (G ⧸ H) :=
    { right_cancel' := fun k₁ k₂ q hq => by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        have hmem : ((k₁ : G) * g)⁻¹ * ((k₂ : G) * g) ∈ H :=
          QuotientGroup.eq.mp hq
        rw [mul_inv_rev, mul_assoc, ← mul_assoc (k₁ : G)⁻¹] at hmem
        have hk : ((k₁⁻¹ * k₂ : K) : G) = 1 :=
          h g _ (k₁⁻¹ * k₂).property (by simpa [mul_assoc] using hmem)
        exact inv_mul_eq_one.mp (Subtype.ext hk) }
  exact MulAction.natCard_dvd_natCard_of_isCancelSMul (G := K) (X := G ⧸ H)

/-- If `H ≤ G` contains no nontrivial element of finite order, then the order of every element of
finite order in `G` divides `H.index`. -/
theorem orderOf_dvd_index_of_forall_isOfFinOrder_eq_one (H : Subgroup G)
    (hH : ∀ y ∈ H, IsOfFinOrder y → y = 1) {x : G} (hx : IsOfFinOrder x) :
    orderOf x ∣ H.index := by
  have hdvd : Nat.card (zpowers x) ∣ H.index :=
    H.natCard_dvd_index_of_forall_conj_mem (zpowers x) fun g k hk hmem => by
      have hk_fin : IsOfFinOrder k := hx.of_mem_zpowers hk
      have hconj : IsConj k (g⁻¹ * k * g) := isConj_iff.mpr ⟨g⁻¹, by simp⟩
      have hconj_one : g⁻¹ * k * g = 1 := hH _ hmem (hconj.isOfFinOrder hk_fin)
      exact isConj_one_left.mp (hconj_one ▸ hconj)
  have hcard : Nat.card (zpowers x) = orderOf x :=
    (Nat.card_congr (finEquivZPowers hx).symm).trans (Nat.card_fin (orderOf x))
  rwa [hcard] at hdvd

/-- If `H ≤ G` is torsion-free, then the order of every element of finite order in `G` divides
`H.index`. -/
theorem orderOf_dvd_index_of_isMulTorsionFree (H : Subgroup G) [IsMulTorsionFree H]
    {x : G} (hx : IsOfFinOrder x) :
    orderOf x ∣ H.index :=
  H.orderOf_dvd_index_of_forall_isOfFinOrder_eq_one
    (fun _ hy hy_fin => H.eq_one_of_isOfFinOrder_mem hy hy_fin) hx

end Subgroup
