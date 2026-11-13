/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Module.SpanRank
public import TauCeti.GroupTheory.Rank
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.GroupTheory.OrderOfElement

/-!
# Generators of products of groups of coprime orders

For finite abelian groups of pairwise coprime orders, coordinatewise generating families
of a common length generate their product. Chinese remainder coefficients recover each
single-coordinate generator from the corresponding tuple. Consequently, the least number
of generators of the product is the maximum of the least numbers for its factors.

Results are given for both `AddGroup.rank` and `Submodule.spanFinrank` over `ℤ`.
-/

public section

namespace TauCeti.AddCommGroup

variable {ι : Type*} [Fintype ι] (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Finite (M i)]

omit [Fintype ι] in
/-- In a product of finite abelian groups of pairwise coprime orders, tuples formed from
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

/-- For finite abelian groups of pairwise coprime orders, the least number of generators
of their product is the maximum of the least numbers for the factors. The empty product
has generator number zero. -/
theorem spanFinrank_pi_eq_sup_of_coprime_card
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j))) :
    (⊤ : Submodule ℤ (∀ i, M i)).spanFinrank =
      Finset.univ.sup (fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank) := by
  classical
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

namespace AddGroup

/-- For a finite family of finite abelian groups of pairwise coprime orders, `AddGroup.rank` of
their product is the supremum of the generator ranks of the factors. -/
theorem rank_pi_eq_sup_of_coprime_card {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Finite (M i)]
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j))) :
    AddGroup.rank (∀ i, M i) = Finset.univ.sup (fun i ↦ AddGroup.rank (M i)) := by
  simp_rw [AddGroup.rank_eq_spanFinrank_top]
  exact TauCeti.AddCommGroup.spanFinrank_pi_eq_sup_of_coprime_card M hcop

private theorem rank_prod_eq_max_of_coprime_card_aux.{u} {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
    (hcop : (Nat.card M).Coprime (Nat.card N)) :
    AddGroup.rank (M × N) = max (AddGroup.rank M) (AddGroup.rank N) := by
  let F : Bool → Type u := fun b ↦ match b with | true => M | false => N
  let _ : ∀ b, AddCommGroup (F b) := fun b ↦ by cases b <;> dsimp [F] <;> infer_instance
  have : ∀ b, Finite (F b) := fun b ↦ by cases b <;> dsimp [F] <;> infer_instance
  have hF : Pairwise fun i j ↦ (Nat.card (F i)).Coprime (Nat.card (F j)) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hcop.symm
    · exact hcop
    · exact (hij rfl).elim
  let e : (M × N) ≃+ ∀ b, F b :=
    { toFun := fun p b ↦ match b with | true => p.1 | false => p.2
      invFun := fun f ↦ (f true, f false)
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun f ↦ funext fun b ↦ by cases b <;> rfl
      map_add' := fun _ _ ↦ funext fun b ↦ by cases b <;> rfl }
  rw [AddGroup.rank_congr e, rank_pi_eq_sup_of_coprime_card F hF]
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [huniv, Finset.sup_insert, Finset.sup_singleton]

/-- For two finite abelian groups of coprime orders, `AddGroup.rank (M × N)` is the maximum of
`AddGroup.rank M` and `AddGroup.rank N`. -/
theorem rank_prod_eq_max_of_coprime_card.{u, v} (M : Type u) (N : Type v)
    [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
    (hcop : (Nat.card M).Coprime (Nat.card N)) :
    AddGroup.rank (M × N) = max (AddGroup.rank M) (AddGroup.rank N) := by
  have hcop' : (Nat.card (ULift.{v} M)).Coprime (Nat.card (ULift.{u} N)) := by
    simpa using hcop
  have eM : ULift.{v} M ≃+ M := AddEquiv.ulift
  have eN : ULift.{u} N ≃+ N := AddEquiv.ulift
  rw [← AddGroup.rank_congr (eM.prodCongr eN), rank_prod_eq_max_of_coprime_card_aux hcop',
    AddGroup.rank_congr eM, AddGroup.rank_congr eN]

end AddGroup
