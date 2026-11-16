/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.LinearAlgebra.Pi
public import TauCeti.Algebra.Module.SpanRank
public import TauCeti.GroupTheory.Rank
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Generators of products of groups of coprime orders

For abelian groups of pairwise coprime orders (`Nat.card`, which is `0` for an infinite group),
coordinatewise generating families of a common length generate their product. Chinese remainder
coefficients recover each single-coordinate generator from the corresponding tuple. Consequently,
the least number of generators of the product is the maximum of the least numbers for its factors.
If one factor is infinite, coprimality forces all the others to be trivial, and the statements
reduce to that factor.

Both Mathlib's `Submodule.spanFinrank` over `ℤ` and `AddGroup.rank` (when the factors are finitely
generated) are supported.
-/

public section

namespace TauCeti.AddCommGroup

variable {ι : Type*} [Fintype ι] (M : ι → Type*)
  [∀ i, AddCommGroup (M i)]

omit [Fintype ι] in
/-- If a family of abelian groups of pairwise coprime orders has an infinite member, then all the
other members are trivial, so the projection onto that member is a right inverse of its inclusion
into the product: every tuple is the inclusion of its coordinate there. -/
private theorem exists_subsingleton_and_rightInverse_single_of_not_finite [DecidableEq ι]
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j)))
    (hfin : ¬ ∀ j, Finite (M j)) :
    ∃ i₀, (∀ j, j ≠ i₀ → Subsingleton (M j)) ∧
      Function.RightInverse (fun x : ∀ j, M j ↦ x i₀) (LinearMap.single ℤ M i₀) := by
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hfin
  have := not_finite_iff_infinite.mp hi₀
  have hsub : ∀ j, j ≠ i₀ → Subsingleton (M j) := fun j hj ↦
    (hcop hj.symm).subsingleton_of_infinite
  refine ⟨i₀, hsub, fun x ↦ ?_⟩
  ext j
  by_cases hj : j = i₀
  · subst hj
    simp
  · have := hsub _ hj
    exact Subsingleton.elim _ _

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
  by_cases hfin : ∀ j, Finite (M j)
  swap
  · obtain ⟨i₀, -, hinv⟩ :=
      exists_subsingleton_and_rightInverse_single_of_not_finite M hcop hfin
    have hcomp : (fun k i ↦ v i k) = LinearMap.single ℤ M i₀ ∘ v i₀ :=
      funext fun k ↦ (hinv fun j ↦ v j k).symm
    rw [hcomp, Set.range_comp, ← Submodule.map_span, hv i₀, Submodule.map_top,
      LinearMap.range_eq_top]
    exact hinv.surjective
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

/-- For abelian groups of pairwise coprime orders, the least number of generators
of their product is the maximum of the least numbers for the factors, over the finite index type
`ι`. The empty product has generator number zero. Here `spanFinrank` is Mathlib's: it is the least
number of generators for a finitely generated group and `0` otherwise (for instance for an infinite
factor that is not finitely generated, which forces all other factors to be trivial). -/
theorem spanFinrank_pi_eq_sup_of_coprime_card
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j))) :
    (⊤ : Submodule ℤ (∀ i, M i)).spanFinrank =
      Finset.univ.sup (fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank) := by
  classical
  by_cases hfin : ∀ i, Finite (M i)
  swap
  · obtain ⟨i₀, hsub, hinv⟩ :=
      exists_subsingleton_and_rightInverse_single_of_not_finite M hcop hfin
    have hrange : (⊤ : Submodule ℤ (M i₀)).map (LinearMap.single ℤ M i₀) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      exact hinv.surjective
    have heq : (⊤ : Submodule ℤ (∀ i, M i)).spanFinrank =
        (⊤ : Submodule ℤ (M i₀)).spanFinrank := by
      rw [← hrange, Submodule.spanFinrank_map_eq_of_injective _ (Pi.single_injective i₀)]
    rw [heq]
    refine le_antisymm (Finset.le_sup (f := fun i ↦ (⊤ : Submodule ℤ (M i)).spanFinrank)
      (Finset.mem_univ i₀)) (Finset.sup_le fun i _ ↦ ?_)
    by_cases hi : i = i₀
    · subst hi
      exact le_rfl
    · have := hsub _ hi
      rw [Subsingleton.elim (⊤ : Submodule ℤ (M i)) ⊥, Submodule.spanFinrank_bot]
      exact Nat.zero_le _
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

/-- For finitely generated abelian groups of pairwise coprime orders, `AddGroup.rank` of their
product equals the supremum of the factor ranks. -/
theorem rank_pi_eq_sup_of_coprime_card [∀ i, AddGroup.FG (M i)]
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j))) :
    AddGroup.rank (∀ i, M i) = Finset.univ.sup (fun i ↦ AddGroup.rank (M i)) := by
  rw [AddGroup.rank_eq_spanFinrank_top, spanFinrank_pi_eq_sup_of_coprime_card M hcop]
  exact Finset.sup_congr rfl fun i _ ↦ (AddGroup.rank_eq_spanFinrank_top (M i)).symm

/-- For finitely generated abelian groups `A` and `B` of coprime orders, `AddGroup.rank (A × B)`
equals `max (AddGroup.rank A) (AddGroup.rank B)`. -/
theorem rank_prod_eq_max_of_coprime_card {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    [AddGroup.FG A] [AddGroup.FG B] (hcop : (Nat.card A).Coprime (Nat.card B)) :
    AddGroup.rank (A × B) = max (AddGroup.rank A) (AddGroup.rank B) := by
  let A' := ULift.{v} A
  let B' := ULift.{u} B
  let eA : A' ≃+ A := { toEquiv := Equiv.ulift, map_add' := fun _ _ ↦ rfl }
  let eB : B' ≃+ B := { toEquiv := Equiv.ulift, map_add' := fun _ _ ↦ rfl }
  have hfgA : AddGroup.FG A' :=
    AddGroup.fg_of_surjective (f := eA.symm.toAddMonoidHom) eA.symm.surjective
  have hfgB : AddGroup.FG B' :=
    AddGroup.fg_of_surjective (f := eB.symm.toAddMonoidHom) eB.symm.surjective
  let F : Bool → Type (max u v) | true => A' | false => B'
  let instGrp : ∀ b, AddCommGroup (F b)
    | true => inferInstanceAs (AddCommGroup A')
    | false => inferInstanceAs (AddCommGroup B')
  let instFG : ∀ b, AddGroup.FG (F b)
    | true => hfgA
    | false => hfgB
  let eProd : A × B ≃+ ∀ b : Bool, F b :=
    { toFun := fun x b ↦ match b with | true => eA.symm x.1 | false => eB.symm x.2
      invFun := fun y ↦ (eA (y true), eB (y false))
      left_inv := fun x ↦ Prod.ext (eA.apply_symm_apply x.1) (eB.apply_symm_apply x.2)
      right_inv := fun y ↦ funext fun b ↦ by
        cases b
        · exact eB.symm_apply_apply (y false)
        · exact eA.symm_apply_apply (y true)
      map_add' := fun _ _ ↦ funext fun b ↦ by cases b <;> rfl }
  have hcopF : Pairwise fun b₁ b₂ ↦ (Nat.card (F b₁)).Coprime (Nat.card (F b₂)) := by
    intro b₁ b₂ hne
    cases b₁ <;> cases b₂
    · exact absurd rfl hne
    · dsimp [F]
      rw [Nat.card_congr eB.toEquiv, Nat.card_congr eA.toEquiv]
      exact hcop.symm
    · dsimp [F]
      rw [Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]
      exact hcop
    · exact absurd rfl hne
  have htrue : AddGroup.rank (F true) = AddGroup.rank A := AddGroup.rank_congr eA
  have hfalse : AddGroup.rank (F false) = AddGroup.rank B := AddGroup.rank_congr eB
  rw [AddGroup.rank_congr eProd, rank_pi_eq_sup_of_coprime_card F hcopF]
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [huniv, Finset.sup_insert, Finset.sup_singleton, htrue, hfalse]

end TauCeti.AddCommGroup
