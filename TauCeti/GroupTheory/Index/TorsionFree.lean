/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Torsion
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Divisibility of the index of a torsion-free subgroup by orders of torsion elements

Let `H` and `K` be subgroups of a group `G`. Left multiplication by `K` on the coset space `G ⧸ H`
is free (`IsCancelSMul K (G ⧸ H)`) if and only if `K` meets every conjugate of `H` trivially, that
is, `g⁻¹ * k * g ∈ H → k = 1` for all `k ∈ K` and `g : G`. When this holds, every `K`-orbit in
`G ⧸ H` is a copy of `K`, so `Nat.card K` divides `H.index` without any finiteness assumption on
`H` or `G` (`H.index` is `0` for infinite-index subgroups).

In particular, if `H` is torsion-free (`IsMulTorsionFree H`), no nonidentity finite-order element
of `G` has a conjugate in `H`:

* for every finite subgroup `K ≤ G`, `Nat.card K ∣ H.index`;
* for every element `x : G` of finite order, `orderOf x ∣ H.index`.

## Main results

* `Subgroup.isCancelSMul_quotient_iff`: `K` acts freely on `G ⧸ H` if and only if no nonidentity
  element of `K` has a conjugate in `H`.
* `Subgroup.natCard_dvd_index_of_forall_conj_mem`: under that condition, `Nat.card K ∣ H.index`.
* `Subgroup.isCancelSMul_quotient_of_isMulTorsionFree`: a torsion subgroup `K` acts freely on
  `G ⧸ H` when `H` is torsion-free.
* `Subgroup.natCard_dvd_index_of_isMulTorsionFree`: `Nat.card K ∣ H.index` when `H` is torsion-free
  and `K` is finite.
* `Subgroup.orderOf_dvd_index_of_isMulTorsionFree`,
  `Subgroup.orderOf_dvd_index_of_forall_isOfFinOrder`: `orderOf x ∣ H.index` for any finite-order
  element `x : G` and torsion-free subgroup `H ≤ G`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup `K` acts freely by left multiplication on the coset space `G ⧸ H` if and only if `K`
meets every conjugate of `H` trivially. -/
theorem isCancelSMul_quotient_iff {H K : Subgroup G} :
    IsCancelSMul K (G ⧸ H) ↔ ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g ∈ H → k = 1 := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  refine ⟨fun hfree k hk g hmem ↦ ?_, fun hconj k q hkq ↦ ?_⟩
  · have hfix : (⟨k⁻¹, inv_mem hk⟩ : K) • (g : G ⧸ H) = (g : G ⧸ H) := by
      change ((k⁻¹ * g : G) : G ⧸ H) = (g : G ⧸ H)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hmem
    have hk1 : (⟨k⁻¹, inv_mem hk⟩ : K) = 1 := hfree ⟨k⁻¹, inv_mem hk⟩ (g : G ⧸ H) hfix
    exact inv_eq_one.mp (congrArg Subtype.val hk1)
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : g⁻¹ * (k : G)⁻¹ * g ∈ H := by
      have heq : (((k : G) * g : G) : G ⧸ H) = (g : G ⧸ H) := hkq
      simpa [mul_assoc] using QuotientGroup.eq.mp heq
    exact Subtype.ext (inv_eq_one.mp (hconj (k : G)⁻¹ (inv_mem k.2) g hmem))

/-- If a subgroup `K` meets every conjugate of `H` trivially, then `Nat.card K` divides `H.index`.
No finiteness assumption is needed since `H.index` vanishes when `G ⧸ H` is infinite. -/
theorem natCard_dvd_index_of_forall_conj_mem {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g ∈ H → k = 1) : Nat.card K ∣ H.index := by
  have : IsCancelSMul K (G ⧸ H) := isCancelSMul_quotient_iff.mpr h
  rw [H.index_eq_card]
  exact MulAction.natCard_dvd_natCard_of_isCancelSMul

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
    Nat.card K ∣ H.index := by
  have : IsCancelSMul K (G ⧸ H) :=
    isCancelSMul_quotient_of_isMulTorsionFree H K isOfFinOrder_of_finite
  rw [H.index_eq_card]
  exact MulAction.natCard_dvd_natCard_of_isCancelSMul

/-- The order of any finite-order element `x : G` divides the index of any torsion-free subgroup
`H ≤ G`. -/
theorem orderOf_dvd_index_of_isMulTorsionFree (H : Subgroup G) [IsMulTorsionFree H] {x : G}
    (hx : IsOfFinOrder x) : orderOf x ∣ H.index := by
  have : Finite (zpowers x) := hx.finite_zpowers
  rw [← Nat.card_zpowers x]
  exact natCard_dvd_index_of_isMulTorsionFree H (zpowers x)

/-- Elementwise form of `Subgroup.orderOf_dvd_index_of_isMulTorsionFree`: if every finite-order
element of `H` is `1`, then `orderOf x ∣ H.index` for every finite-order element `x : G`. -/
theorem orderOf_dvd_index_of_forall_isOfFinOrder {H : Subgroup G}
    (hH : ∀ g ∈ H, IsOfFinOrder g → g = 1) {x : G} (hx : IsOfFinOrder x) :
    orderOf x ∣ H.index := by
  have : IsMulTorsionFree H :=
    .of_not_isOfFinOrder fun y hy hfin ↦
      hy (Subtype.ext (hH y.1 y.2 (H.subtype.isOfFinOrder hfin)))
  exact orderOf_dvd_index_of_isMulTorsionFree H hx

end Subgroup
