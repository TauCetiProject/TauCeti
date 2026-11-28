/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DieudonneComplex.Saturated

/-!
# The Verschiebung filtration of a saturated Dieudonné complex

Let `M` be a saturated Dieudonné complex with Verschiebung `V`. For `r : ℕ` and a degree `n`,
the `r`-th step of the *Verschiebung filtration* is the subgroup
`Nʳ Mⁿ = im (Vʳ : Mⁿ → Mⁿ) + im (d ∘ Vʳ : Mⁿ⁻¹ → Mⁿ)` of `Mⁿ`. These subgroups form a
decreasing filtration by subcomplexes, and the quotients `Mⁿ / Nʳ Mⁿ` are the finite stages
`W_r(M)` of the strict completion of `M`, which for the saturated de Rham–Witt complex are the
de Rham–Witt complexes of finite level.

This file proves the interaction of the filtration with `d`, `F`, `V` and multiplication by `p`
that the finite quotients need: `d` preserves each level, `F` lowers the level by one, while `V`
and `p` raise it by one. It also proves the divisibility lemma of Bhatt–Lurie–Mathew that
`p • x ∈ Nʳ⁺¹` iff `x ∈ Nʳ`.

## Main definitions

* `TauCeti.DieudonneComplex.IsSaturated.verschiebungFiltration`: the subgroup
  `Nʳ Mⁿ = im Vʳ + im (d Vʳ)` of `Mⁿ`.

## Main results

* `TauCeti.DieudonneComplex.IsSaturated.mem_verschiebungFiltration_iff`: the elements of `Nʳ Mⁿ`
  are the sums `Vʳ a + d (Vʳ b)`.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungFiltration_zero` and
  `TauCeti.DieudonneComplex.IsSaturated.verschiebungFiltration_antitone`: the filtration starts
  at `Mⁿ` and is decreasing.
* `TauCeti.DieudonneComplex.IsSaturated.d_mem_verschiebungFiltration`: `d (Nʳ Mⁿ) ⊆ Nʳ Mⁿ⁺¹`.
* `TauCeti.DieudonneComplex.IsSaturated.F_mem_verschiebungFiltration`,
  `TauCeti.DieudonneComplex.IsSaturated.V_mem_verschiebungFiltration`: `F (Nʳ⁺¹) ⊆ Nʳ` and
  `V (Nʳ) ⊆ Nʳ⁺¹`.
* `TauCeti.DieudonneComplex.IsSaturated.smul_mem_verschiebungFiltration_succ_iff`:
  `p • x ∈ Nʳ⁺¹ ↔ x ∈ Nʳ`.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Construction 2.5.1, Remark 2.5.2, Lemma 2.6.4 and the proof of
  Proposition 2.6.2.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

namespace DieudonneComplex

namespace IsSaturated

variable {p : ℕ} {M : DieudonneComplex.{u} p} (hM : M.IsSaturated)
include hM

/-- The Verschiebung filtration `Nʳ Mⁿ = im Vʳ + im (d Vʳ)` of a saturated Dieudonné complex,
where `d Vʳ` is the composite `Mⁿ⁻¹ → Mⁿ⁻¹ → Mⁿ`. -/
noncomputable def verschiebungFiltration (r : ℕ) (n : ℤ) : AddSubgroup (M.X n) :=
  (AddMonoidHom.mk' (⇑(hM.V n).hom)^[r] (iterate_map_add _ r)).range ⊔
    ((M.d (n - 1) n).hom.comp
      (AddMonoidHom.mk' (⇑(hM.V (n - 1)).hom)^[r] (iterate_map_add _ r))).range

/-- The elements of `Nʳ Mⁿ` are the sums `Vʳ a + d (Vʳ b)`, with `b` in degree `i = n - 1`. -/
lemma mem_verschiebungFiltration_iff {r : ℕ} {i n : ℤ} (hin : i + 1 = n) {x : M.X n} :
    x ∈ hM.verschiebungFiltration r n ↔
      ∃ a b, (⇑(hM.V n).hom)^[r] a + (M.d i n).hom ((⇑(hM.V i).hom)^[r] b) = x := by
  obtain rfl : i = n - 1 := by omega
  simp [verschiebungFiltration, AddSubgroup.mem_sup]

/-- `Vʳ a ∈ Nʳ Mⁿ`. -/
lemma V_iterate_mem_verschiebungFiltration {n : ℤ} (r : ℕ) (a : M.X n) :
    (⇑(hM.V n).hom)^[r] a ∈ hM.verschiebungFiltration r n :=
  (hM.mem_verschiebungFiltration_iff (sub_add_cancel n 1)).2 ⟨a, 0, by simp⟩

/-- `d (Vʳ b) ∈ Nʳ Mⁿ`, for the differential from any degree. -/
lemma d_V_iterate_mem_verschiebungFiltration {i n : ℤ} (r : ℕ) (b : M.X i) :
    (M.d i n).hom ((⇑(hM.V i).hom)^[r] b) ∈ hM.verschiebungFiltration r n := by
  by_cases h : i + 1 = n
  · exact (hM.mem_verschiebungFiltration_iff h).2 ⟨0, b, by simp⟩
  · simp [M.shape i n h]

/-- `N⁰ Mⁿ = Mⁿ`. -/
@[simp]
lemma verschiebungFiltration_zero (n : ℤ) : hM.verschiebungFiltration 0 n = ⊤ :=
  eq_top_iff.2 fun x _ ↦ hM.V_iterate_mem_verschiebungFiltration 0 x

/-- `Nʳ⁺¹ Mⁿ ⊆ Nʳ Mⁿ`. -/
lemma verschiebungFiltration_succ_le (r : ℕ) (n : ℤ) :
    hM.verschiebungFiltration (r + 1) n ≤ hM.verschiebungFiltration r n := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
  exact add_mem (hM.V_iterate_mem_verschiebungFiltration r _)
    (hM.d_V_iterate_mem_verschiebungFiltration r _)

/-- The Verschiebung filtration is decreasing. -/
lemma verschiebungFiltration_antitone (n : ℤ) :
    Antitone fun r ↦ hM.verschiebungFiltration r n :=
  antitone_nat_of_succ_le fun r ↦ hM.verschiebungFiltration_succ_le r n

/-- The differential preserves the Verschiebung filtration: `d (Nʳ Mⁱ) ⊆ Nʳ Mʲ`. -/
lemma d_mem_verschiebungFiltration {r : ℕ} {i j : ℤ} {x : M.X i}
    (hx : x ∈ hM.verschiebungFiltration r i) :
    (M.d i j).hom x ∈ hM.verschiebungFiltration r j := by
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  rw [map_add, HomologicalComplex.addCommGrpCat_d_comp_d_apply, add_zero]
  exact hM.d_V_iterate_mem_verschiebungFiltration r a

/-- `Nʳ Mⁱ ≤ d⁻¹ (Nʳ Mʲ)`. -/
lemma verschiebungFiltration_le_comap_d (r : ℕ) (i j : ℤ) :
    hM.verschiebungFiltration r i ≤ (hM.verschiebungFiltration r j).comap (M.d i j).hom :=
  fun _ ↦ hM.d_mem_verschiebungFiltration

/-- The Frobenius lowers the Verschiebung filtration by one: `F (Nʳ⁺¹ Mⁿ) ⊆ Nʳ Mⁿ`. -/
lemma F_mem_verschiebungFiltration {r : ℕ} {n : ℤ} {x : M.X n}
    (hx : x ∈ hM.verschiebungFiltration (r + 1) n) :
    (M.F n).hom x ∈ hM.verschiebungFiltration r n := by
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  rw [map_add, Function.iterate_succ_apply', F_V_apply, hM.F_d_V_iterate_succ_apply]
  exact add_mem (AddSubgroup.nsmul_mem _ (hM.V_iterate_mem_verschiebungFiltration r a) p)
    (hM.d_V_iterate_mem_verschiebungFiltration r b)

/-- The Verschiebung raises the Verschiebung filtration by one: `V (Nʳ Mⁿ) ⊆ Nʳ⁺¹ Mⁿ`. -/
lemma V_mem_verschiebungFiltration {r : ℕ} {n : ℤ} {x : M.X n}
    (hx : x ∈ hM.verschiebungFiltration r n) :
    (hM.V n).hom x ∈ hM.verschiebungFiltration (r + 1) n := by
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  rw [map_add, ← Function.iterate_succ_apply' (⇑(hM.V n).hom), hM.V_d_V_iterate_apply]
  exact add_mem (hM.V_iterate_mem_verschiebungFiltration (r + 1) a)
    (AddSubgroup.nsmul_mem _ (hM.d_V_iterate_mem_verschiebungFiltration (r + 1) b) p)

/-- `Nʳ⁺¹ Mⁿ ≤ F⁻¹ (Nʳ Mⁿ)`. -/
lemma verschiebungFiltration_succ_le_comap_F (r : ℕ) (n : ℤ) :
    hM.verschiebungFiltration (r + 1) n ≤ (hM.verschiebungFiltration r n).comap (M.F n).hom :=
  fun _ ↦ hM.F_mem_verschiebungFiltration

/-- `Nʳ Mⁿ ≤ V⁻¹ (Nʳ⁺¹ Mⁿ)`. -/
lemma verschiebungFiltration_le_comap_V (r : ℕ) (n : ℤ) :
    hM.verschiebungFiltration r n ≤ (hM.verschiebungFiltration (r + 1) n).comap (hM.V n).hom :=
  fun _ ↦ hM.V_mem_verschiebungFiltration

/-- Multiplication by `p` raises the Verschiebung filtration by one: `p • Nʳ Mⁿ ⊆ Nʳ⁺¹ Mⁿ`. -/
lemma smul_mem_verschiebungFiltration {r : ℕ} {n : ℤ} {x : M.X n}
    (hx : x ∈ hM.verschiebungFiltration r n) :
    p • x ∈ hM.verschiebungFiltration (r + 1) n := by
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  rw [smul_add, ← map_nsmul, ← hM.V_iterate_succ_F_apply, ← hM.V_iterate_succ_F_apply]
  exact add_mem (hM.V_iterate_mem_verschiebungFiltration (r + 1) _)
    (hM.d_V_iterate_mem_verschiebungFiltration (r + 1) _)

/-- `pʳ • x ∈ Nʳ Mⁿ` for every `x`. -/
lemma pow_smul_mem_verschiebungFiltration (r : ℕ) {n : ℤ} (x : M.X n) :
    p ^ r • x ∈ hM.verschiebungFiltration r n := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ', mul_smul]; exact hM.smul_mem_verschiebungFiltration ih

/-- If `p • x ∈ Nʳ⁺¹ Mⁿ`, then `x ∈ Nʳ Mⁿ`. -/
lemma mem_verschiebungFiltration_of_smul_mem {r : ℕ} {n : ℤ} {x : M.X n}
    (hx : p • x ∈ hM.verschiebungFiltration (r + 1) n) :
    x ∈ hM.verschiebungFiltration r n := by
  obtain ⟨a, b, hab⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  -- Applying `d` gives `d (Vʳ⁺¹ a) = p • d x`, so `a = F a'`.
  obtain ⟨a', rfl⟩ := hM.mem_range_F_of_V_iterate_add_d_V_iterate_eq (c := 0)
    (by rw [hab, map_zero, add_zero])
  rw [hM.V_iterate_succ_F_apply] at hab
  -- Then `d (Vʳ⁺¹ b) = p • (x - Vʳ a')`, so `b = F b'`.
  obtain ⟨b', rfl⟩ := hM.mem_range_F_of_d_V_iterate (r := r + 1) (sub_add_cancel n 1)
    ⟨x - (⇑(hM.V n).hom)^[r] a', by rw [smul_sub, ← hab, add_sub_cancel_left]⟩
  rw [hM.V_iterate_succ_F_apply, map_nsmul, ← smul_add] at hab
  rw [← hM.isSMulRegular n hab]
  exact add_mem (hM.V_iterate_mem_verschiebungFiltration r a')
    (hM.d_V_iterate_mem_verschiebungFiltration r b')

/-- `p • x ∈ Nʳ⁺¹ Mⁿ` iff `x ∈ Nʳ Mⁿ`. -/
@[simp]
lemma smul_mem_verschiebungFiltration_succ_iff {r : ℕ} {n : ℤ} {x : M.X n} :
    p • x ∈ hM.verschiebungFiltration (r + 1) n ↔ x ∈ hM.verschiebungFiltration r n :=
  ⟨hM.mem_verschiebungFiltration_of_smul_mem, hM.smul_mem_verschiebungFiltration⟩

/-- A morphism of saturated Dieudonné complexes maps `Nʳ Mⁿ` into `Nʳ Nⁿ`. -/
lemma map_mem_verschiebungFiltration {N : DieudonneComplex.{u} p} (hN : N.IsSaturated)
    (f : M ⟶ N) {r : ℕ} {n : ℤ} {x : M.X n} (hx : x ∈ hM.verschiebungFiltration r n) :
    (f.hom.f n).hom x ∈ hN.verschiebungFiltration r n := by
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel _ 1)).1 hx
  have hV (i : ℤ) : Function.Semiconj (f.hom.f i).hom (hM.V i).hom (hN.V i).hom :=
    fun x ↦ Hom.comm_V_apply hM hN f x
  rw [map_add, (hV n).iterate_right, ← AddCommGrpCat.comp_apply _ (f.hom.f n), ← f.hom.comm,
    AddCommGrpCat.comp_apply, (hV (n - 1)).iterate_right]
  exact add_mem (hN.V_iterate_mem_verschiebungFiltration r _)
    (hN.d_V_iterate_mem_verschiebungFiltration r _)

/-- `Nʳ Mⁿ ≤ f⁻¹ (Nʳ Nⁿ)` for a morphism `f` of saturated Dieudonné complexes. -/
lemma verschiebungFiltration_le_comap {N : DieudonneComplex.{u} p} (hN : N.IsSaturated)
    (f : M ⟶ N) (r : ℕ) (n : ℤ) :
    hM.verschiebungFiltration r n ≤ (hN.verschiebungFiltration r n).comap (f.hom.f n).hom :=
  fun _ ↦ hM.map_mem_verschiebungFiltration hN f

end IsSaturated

end DieudonneComplex

end TauCeti
