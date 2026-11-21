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
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Generators of products of groups of coprime orders

For abelian groups of pairwise coprime orders (`Nat.card`, which is `0` for an infinite group),
coordinatewise generating families of a common length generate their product. Chinese remainder
coefficients recover each single-coordinate generator from the corresponding tuple. Consequently,
the least number of generators of the product is the maximum of the least numbers for its factors.
If one factor is infinite, coprimality forces all the others to be trivial, and the statements
reduce to that factor.

Results are given for both Mathlib's `Submodule.spanFinrank` over `ℤ` and `AddGroup.rank`. By
Mathlib's convention `Submodule.spanFinrank` is `0` for a group that is not finitely generated, so
for such factors the `spanFinrank` statement holds by that convention only; the `AddGroup.rank`
statements assume finitely generated factors (`AddGroup.FG`). Combining this with
`AddGroup.rank_pi_zmod_of_dvd` yields the closed formula `AddGroup.rank_prod_zmod` for the
generator rank of `ZMod m × ZMod n` (and its prime-power specialization
`AddGroup.rank_prod_zmod_prime_pow`).
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

end TauCeti.AddCommGroup

namespace AddGroup

/-- For a finite family of finitely generated abelian groups of pairwise coprime orders,
`AddGroup.rank` of their product is the supremum of the generator ranks of the factors. -/
theorem rank_pi_eq_sup_of_coprime_card {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, AddGroup.FG (M i)]
    (hcop : Pairwise fun i j ↦ (Nat.card (M i)).Coprime (Nat.card (M j))) :
    AddGroup.rank (∀ i, M i) = Finset.univ.sup (fun i ↦ AddGroup.rank (M i)) := by
  simp_rw [AddGroup.rank_eq_spanFinrank_top]
  exact TauCeti.AddCommGroup.spanFinrank_pi_eq_sup_of_coprime_card M hcop

private def prodAddEquivPiBool.{u} (F : Bool → Type u) [∀ b, AddCommGroup (F b)] :
    (F true × F false) ≃+ ∀ b, F b where
  toFun p b := match b with | true => p.1 | false => p.2
  invFun f := (f true, f false)
  left_inv _ := rfl
  right_inv f := funext fun b ↦ by cases b <;> rfl
  map_add' _ _ := funext fun b ↦ by cases b <;> rfl

private theorem rank_prod_eq_max_of_coprime_card_aux.{u} {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddGroup.FG M] [AddGroup.FG N]
    (hcop : (Nat.card M).Coprime (Nat.card N)) :
    AddGroup.rank (M × N) = max (AddGroup.rank M) (AddGroup.rank N) := by
  let F : Bool → Type u := fun b ↦ match b with | true => M | false => N
  let _ : ∀ b, AddCommGroup (F b) := fun b ↦ by cases b <;> dsimp [F] <;> infer_instance
  have : ∀ b, AddGroup.FG (F b) := fun b ↦ by cases b <;> dsimp [F] <;> infer_instance
  have hF : Pairwise fun i j ↦ (Nat.card (F i)).Coprime (Nat.card (F j)) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hcop.symm
    · exact hcop
    · exact (hij rfl).elim
  rw [AddGroup.rank_congr (prodAddEquivPiBool F), rank_pi_eq_sup_of_coprime_card F hF]
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [huniv, Finset.sup_insert, Finset.sup_singleton]

/-- For two finitely generated abelian groups of coprime orders, `AddGroup.rank (M × N)` is the
maximum of `AddGroup.rank M` and `AddGroup.rank N`. -/
theorem rank_prod_eq_max_of_coprime_card.{u, v} (M : Type u) (N : Type v)
    [AddCommGroup M] [AddCommGroup N] [AddGroup.FG M] [AddGroup.FG N]
    (hcop : (Nat.card M).Coprime (Nat.card N)) :
    AddGroup.rank (M × N) = max (AddGroup.rank M) (AddGroup.rank N) := by
  have hcop' : (Nat.card (ULift.{v} M)).Coprime (Nat.card (ULift.{u} N)) := by
    simpa using hcop
  have eM : ULift.{v} M ≃+ M := AddEquiv.ulift
  have eN : ULift.{u} N ≃+ N := AddEquiv.ulift
  have : AddGroup.FG (ULift.{v} M) := .of_surjective eM.symm eM.symm.surjective
  have : AddGroup.FG (ULift.{u} N) := .of_surjective eN.symm eN.symm.surjective
  rw [← AddGroup.rank_congr (eM.prodCongr eN), rank_prod_eq_max_of_coprime_card_aux hcop',
    AddGroup.rank_congr eM, AddGroup.rank_congr eN]

/-- The generator rank of `ZMod m × ZMod n` is `0` if `m = 1` and `n = 1`, `1` if `m` and `n`
are coprime and not both `1`, and `2` otherwise. -/
theorem rank_prod_zmod (m n : ℕ) :
    AddGroup.rank (ZMod m × ZMod n) =
      if m = 1 ∧ n = 1 then 0 else if m.Coprime n then 1 else 2 := by
  split_ifs with h1 hcop
  · rcases h1 with ⟨rfl, rfl⟩
    exact AddGroup.rank_eq_zero _
  · have hcard : (Nat.card (ZMod m)).Coprime (Nat.card (ZMod n)) := by
      simpa [Nat.card_zmod] using hcop
    rw [rank_prod_eq_max_of_coprime_card (ZMod m) (ZMod n) hcard,
      AddGroup.rank_zmod, AddGroup.rank_zmod]
    split_ifs <;> simp_all
  · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hcop
    have hdvd : ∀ b : Bool, p ∣ cond b m n := by
      rintro (_ | _)
      · exact hp_dvd.trans (Nat.gcd_dvd_right m n)
      · exact hp_dvd.trans (Nat.gcd_dvd_left m n)
    have e : (ZMod m × ZMod n) ≃+ ∀ b : Bool, ZMod (cond b m n) :=
      prodAddEquivPiBool (fun b : Bool ↦ ZMod (cond b m n))
    rw [AddGroup.rank_congr e, AddGroup.rank_pi_zmod_of_dvd hp hdvd, Fintype.card_bool]

/-- For prime `p` and `k₁, k₂ > 0`, `ZMod (p ^ k₁) × ZMod (p ^ k₂)` has generator rank `2`. -/
theorem rank_prod_zmod_prime_pow {p k₁ k₂ : ℕ} (hp : p.Prime) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    AddGroup.rank (ZMod (p ^ k₁) × ZMod (p ^ k₂)) = 2 := by
  have hcop : ¬ (p ^ k₁).Coprime (p ^ k₂) :=
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p hk₁.ne') (dvd_pow_self p hk₂.ne')
  simp [rank_prod_zmod, hp.ne_one, hk₁.ne', hcop]

end AddGroup
