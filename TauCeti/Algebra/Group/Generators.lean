/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.GroupTheory.OrderOfElement

/-!
# Generators of products of groups of coprime orders

For finite abelian groups of pairwise coprime orders, coordinatewise generating families
of a common length generate their product. Chinese remainder coefficients recover each
single-coordinate generator from the corresponding tuple. Consequently, the least number
of generators of the product is the maximum of the least numbers for its factors.

The generator number is Mathlib's `Submodule.spanFinrank` over `ℤ`.
-/

public section

namespace TauCeti.AddCommGroup

variable {ι : Type*} [Fintype ι] (M : ι → Type*)
  [∀ i, AddCommGroup (M i)]

omit [Fintype ι] [∀ i, AddCommGroup (M i)] in
/-- If the orders of the groups `M i` are pairwise coprime and `M i₀` is infinite (so its `Nat.card`
is `0`), then every other `M j` has order one. -/
private theorem subsingleton_of_not_finite_of_coprime_card
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j)))
    {i₀ : ι} (hi₀ : ¬ Finite (M i₀)) {j : ι} (hj : j ≠ i₀) : Subsingleton (M j) := by
  have h0 : Nat.card (M i₀) = 0 := by
    have := not_finite_iff_infinite.mp hi₀
    exact Nat.card_eq_zero_of_infinite
  have h : (Nat.card (M i₀)).Coprime (Nat.card (M j)) := hcop hj.symm
  rw [h0, Nat.coprime_zero_left] at h
  exact (Nat.card_eq_one_iff_unique.mp h).1

omit [Fintype ι] in
/-- In a product of abelian groups of pairwise coprime orders, tuples formed from
coordinatewise generating families themselves generate the product. -/
theorem span_range_pi_eq_top_of_coprime_card [Finite ι]
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j)))
    {κ : Type*} (v : ∀ i, κ → M i)
    (hv : ∀ i, Submodule.span ℤ (Set.range (v i)) = ⊤) :
    Submodule.span ℤ (Set.range (fun k i ↦ v i k)) = ⊤ := by
  classical
  let _ := Fintype.ofFinite ι
  let S := Submodule.span ℤ (Set.range (fun k i ↦ v i k))
  have hsingle (i : ι) (k : κ) : Pi.single i (v i k) ∈ S := by
    by_cases hfin : ∀ j, Finite (M j)
    swap
    · obtain ⟨i₀, hi₀⟩ := not_forall.mp hfin
      have hsub : ∀ j, j ≠ i₀ → Subsingleton (M j) := fun j hj ↦
      subsingleton_of_not_finite_of_coprime_card M hcop hi₀ hj
      by_cases hi : i = i₀
      · subst hi
        have he : (fun j ↦ v j k) = Pi.single i (v i k) := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · have := hsub _ hj
            simp [hj, Subsingleton.elim (v j k) 0]
        rw [← he]
        exact Submodule.subset_span ⟨k, rfl⟩
      · have := hsub _ hi
        rw [Subsingleton.elim (v i k) 0, Pi.single_zero]
        exact S.zero_mem
    have := hfin
    let c := Nat.chineseRemainderOfFinset (fun j ↦ if j = i then 1 else 0)
      (fun j ↦ Nat.card (M j)) Finset.univ (fun j _ ↦ Nat.card_pos.ne')
      (fun j _ l _ hjl ↦ hcop hjl)
    have he : (c.val : ℤ) • (fun j ↦ v j k) = Pi.single i (v i k) := by
      ext j
      have hc : c.val % Nat.card (M j) = (if j = i then 1 else 0) % Nat.card (M j) :=
        c.property j (Finset.mem_univ j)
      rw [Pi.smul_apply, natCast_zsmul, ← mod_natCard_nsmul (v j k) c.val, hc,
        mod_natCard_nsmul]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    rw [← he]
    exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hall (i : ι) (x : M i) : Pi.single i x ∈ S := by
    have hle : Submodule.span ℤ (Set.range (v i)) ≤
        S.comap (LinearMap.single ℤ M i) := by
      apply Submodule.span_le.mpr
      rintro x ⟨k, rfl⟩
      apply Submodule.mem_comap.mpr
      simpa only [LinearMap.single_apply] using hsingle i k
    have hx : LinearMap.single ℤ M i x ∈ S :=
      Submodule.mem_comap.mp (hle (hv i ▸ Submodule.mem_top))
    simpa only [LinearMap.single_apply] using hx
  apply top_unique
  intro x _
  rw [← Finset.univ_sum_single x]
  exact S.sum_mem (fun i _ ↦ hall i (x i))

/-- For abelian groups of pairwise coprime orders, the least number of generators
of their product is the maximum of the least numbers for the factors. The empty product
has generator number zero. -/
theorem spanFinrank_pi_eq_sup_of_coprime_card
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j))) :
    (⊤ : Submodule ℤ (∀ i, M i)).spanFinrank =
      Finset.univ.sup (fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank) := by
  classical
  by_cases hfin : ∀ i, Finite (M i)
  swap
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hfin
    have hsub : ∀ j, j ≠ i₀ → Subsingleton (M j) := fun j hj ↦
      subsingleton_of_not_finite_of_coprime_card M hcop hi₀ hj
    have hrange : (⊤ : Submodule ℤ (M i₀)).map (LinearMap.single ℤ M i₀) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      intro x
      refine ⟨x i₀, ?_⟩
      ext j
      by_cases hj : j = i₀
      · subst hj
        simp
      · have := hsub _ hj
        exact Subsingleton.elim _ _
    have heq : (⊤ : Submodule ℤ (∀ i, M i)).spanFinrank =
        (⊤ : Submodule ℤ (M i₀)).spanFinrank := by
      rw [← hrange, Submodule.spanFinrank_map_eq_of_injective _
        (fun a b h ↦ by simpa using congrFun h i₀)]
    rw [heq]
    refine le_antisymm (Finset.le_sup (f := fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank)
      (Finset.mem_univ i₀)) (Finset.sup_le fun i _ ↦ ?_)
    by_cases hi : i = i₀
    · subst hi
      exact le_rfl
    · have := hsub _ hi
      rw [Subsingleton.elim (⊤ : Submodule ℤ (M i)) ⊥, Submodule.spanFinrank_bot]
      exact Nat.zero_le _
  have := hfin
  let n := Finset.univ.sup (fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank)
  apply le_antisymm
  · have hgen (i : ι) : ∃ v : Fin n → M i, Submodule.span ℤ (Set.range v) = ⊤ :=
      ((Module.Finite.fg_top (R := ℤ) (M := M i)).spanFinrank_le_iff_exists_fin_generating_family
        n).mp (Finset.le_sup (f := fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank)
          (Finset.mem_univ i))
    choose v hv using hgen
    exact (Module.Finite.fg_top.spanFinrank_le_iff_exists_fin_generating_family n).mpr
      ⟨fun k i ↦ v i k, span_range_pi_eq_top_of_coprime_card M hcop v hv⟩
  · apply Finset.sup_le
    intro i _
    have h := Submodule.spanFinrank_map_le_of_fg (LinearMap.proj i)
      (Module.Finite.fg_top (R := ℤ) (M := ∀ i, M i))
    simpa only [Submodule.map_top, LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)]
      using h

end TauCeti.AddCommGroup
