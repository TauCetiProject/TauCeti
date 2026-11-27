/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Superfluous

import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.EquivFin
import TauCeti.Algebra.Category.ModuleCat.Colimits

/-!
# Left T-nilpotence and Nakayama's lemma

A subset of a ring is left T-nilpotent if every sequence in it has a vanishing initial
product, with factors in sequence order. For a left ideal `I`, this is equivalent to
Nakayama's lemma for all left modules: `IM = M` forces `M = 0`, or equivalently,
`IM` is superfluous in `M`. For the converse, it suffices to test superfluity in the
countably generated free module. This criterion is used for projective covers over left
perfect rings.

## References

* F. W. Anderson and K. R. Fuller, *Rings and Categories of Modules*, second edition,
  Lemma 28.3, pp. 314–315.
* H. Bass, *Finitistic dimension and a homological generalization of semi-primary rings*,
  pp. 473–474.
-/

public section

namespace TauCeti

universe u v

/-- A subset is left T-nilpotent if each sequence `a₀, a₁, …` in it has a zero product
`a₀ * a₁ * ⋯ * aₙ₋₁` for some `n`. -/
def IsLeftTNilpotent {R : Type*} [MonoidWithZero R] (S : Set R) : Prop :=
  ∀ a : ℕ → R, (∀ i, a i ∈ S) → ∃ n, ((List.range n).map a).prod = 0

/-- Ordered initial products characterize left T-nilpotence. -/
theorem isLeftTNilpotent_iff {R : Type*} [MonoidWithZero R] {S : Set R} :
    IsLeftTNilpotent S ↔
      ∀ a : ℕ → R, (∀ i, a i ∈ S) → ∃ n, ((List.range n).map a).prod = 0 :=
  (Iff.rfl)

/-- Every element of a left T-nilpotent subset is nilpotent. -/
theorem IsLeftTNilpotent.isNilpotent {R : Type*} [MonoidWithZero R] {S : Set R}
    (hS : IsLeftTNilpotent S) {a : R} (ha : a ∈ S) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := hS (fun _ ↦ a) fun _ ↦ ha
  exact ⟨n, by simpa using hn⟩

section Semiring

variable {R : Type u} [Semiring R] {I : Ideal R}

/-- Nilpotence of a left ideal implies left T-nilpotence. -/
theorem isLeftTNilpotent_of_isNilpotent (hI : IsNilpotent I) :
    IsLeftTNilpotent (I : Set R) := by
  obtain ⟨n, hn⟩ := hI
  intro a ha
  have mem_pow (k : ℕ) : ((List.range k).map a).prod ∈ I ^ k := by
    induction k with
    | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
    | succ k ih =>
      rw [List.prod_range_succ, Submodule.pow_succ]
      exact Ideal.mul_mem_mul ih (ha k)
  exact ⟨n, by simpa [hn] using mem_pow n⟩

/-- **Nakayama's lemma for a left T-nilpotent ideal.** If `IM = M`, then `M` is zero,
with no finiteness hypothesis on `M`. -/
theorem IsLeftTNilpotent.subsingleton_of_smul_top_eq_top {M : Type v}
    [AddCommMonoid M] [Module R M] (hI : IsLeftTNilpotent (I : Set R))
    (hM : I • (⊤ : Submodule R M) = ⊤) : Subsingleton M := by
  classical
  -- Record the partial products that still act nontrivially on some element of M.
  let P := {r : R // ∃ x : M, r • x ≠ 0}
  have step (r : P) : ∃ a ∈ I, ∃ x : M, (r.val * a) • x ≠ 0 := by
    by_contra! h
    obtain ⟨x, hx⟩ := r.property
    have hxI : x ∈ I • (⊤ : Submodule R M) := hM.symm ▸ Submodule.mem_top
    exact hx (Submodule.smul_induction_on (p := fun y ↦ r.val • y = 0) hxI
      (fun a ha y _ ↦ by rw [← mul_smul]; exact h a ha y)
      (fun y z hy hz ↦ by simp [smul_add, hy, hz]))
  choose next hnext hact using step
  refine ⟨fun x y ↦ ?_⟩
  suffices every_zero : ∀ z : M, z = 0 from (every_zero x).trans (every_zero y).symm
  intro z
  by_contra hz
  let r : ℕ → P := fun n ↦ Nat.rec ⟨1, z, by simpa using hz⟩
    (fun _ s ↦ ⟨s.val * next s, hact s⟩) n
  let a : ℕ → R := fun n ↦ next (r n)
  have hr (n : ℕ) : (r n).val = ((List.range n).map a).prod := by
    induction n with
    | zero => rfl
    | succ n ih => exact (congrArg (· * a n) ih).trans (List.prod_range_succ a n).symm
  obtain ⟨n, hn⟩ := hI a fun n ↦ hnext (r n)
  obtain ⟨w, hw⟩ := (r n).property
  exact hw (by rw [hr, hn, zero_smul])

end Semiring

section Ring

variable {R : Type u} [Ring R] {I : Ideal R}

/-- Nakayama's vanishing criterion on the quotients of `M` implies superfluity in `M`. -/
private theorem isSuperfluous_smul_top_of_quotient {M : Type v} [AddCommGroup M] [Module R M]
    (h : ∀ N : Submodule R M, I • (⊤ : Submodule R (M ⧸ N)) = ⊤ → Subsingleton (M ⧸ N)) :
    IsSuperfluous (I • (⊤ : Submodule R M)) := by
  refine isSuperfluous_iff.2 fun N hN ↦ ?_
  have hmap := (N.map_mkQ_eq_top (I • ⊤)).2 (by simpa only [sup_comm] using hN)
  have hquot : I • (⊤ : Submodule R (M ⧸ N)) = ⊤ := by
    simpa only [Submodule.map_smul'', Submodule.map_top, N.range_mkQ] using hmap
  have := h N hquot
  exact eq_top_iff.2 fun x _ ↦ (Submodule.Quotient.mk_eq_zero N).1 (Subsingleton.elim _ _)

/-- A left T-nilpotent ideal times any module is a superfluous submodule. -/
theorem IsLeftTNilpotent.isSuperfluous_smul_top {M : Type v}
    [AddCommGroup M] [Module R M] (hI : IsLeftTNilpotent (I : Set R)) :
    IsSuperfluous (I • (⊤ : Submodule R M)) :=
  isSuperfluous_smul_top_of_quotient fun _ ↦ hI.subsingleton_of_smul_top_eq_top

open CategoryTheory DirectSum

private theorem isLeftTNilpotent_of_isSuperfluous_free
    (hI : IsSuperfluous (I • (⊤ : Submodule R (ℕ →₀ R)))) : IsLeftTNilpotent (I : Set R) := by
  classical
  intro a ha
  let X (_ : ℕ) := ModuleCat.of R R
  let F := Functor.ofSequence (X := X) fun n ↦ ModuleCat.ofHom (LinearMap.mulRight R (a n))
  let diff : (⨁ _ : ℕ, R) →ₗ[R] (⨁ _ : ℕ, R) := ModuleCat.telescopeDiff F
  let D := LinearMap.range diff
  let T : Submodule R (⨁ _ : ℕ, R) := I • ⊤
  have map_succ (n : ℕ) (x : R) :
      (F.map (homOfLE (n.le_add_right 1)) x : R) = x * a n := by
    simp only [F, Functor.ofSequence_map_homOfLE_succ]
    rfl
  have hsuper : IsSuperfluous T := by
    simpa [T, Submodule.map_top] using (hI.map (finsuppLEquivDirectSum R R ℕ).toLinearMap)
  have hDT : D ⊔ T = ⊤ := by
    suffices h : ∀ x, x ∈ D ⊔ T from eq_top_iff.2 fun x _ ↦ h x
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | of n x =>
      rw [← lof_eq_of R]
      let b := lof R ℕ (fun _ ↦ R) (n + 1)
      have hd : lof R ℕ (fun _ ↦ R) n x - b (x * a n) ∈ D := by
        refine ⟨lof R ℕ (fun _ ↦ R) n x, (ModuleCat.telescopeDiff_lof F n x).trans ?_⟩
        rw [map_succ]
        rfl
      have ht : b (x * a n) ∈ T := by
        have h := Submodule.smul_mem_smul (I.mul_mem_left x (ha n))
          (Submodule.mem_top (x := b 1))
        simpa only [← b.map_smul, smul_eq_mul, mul_one] using h
      simpa only [sub_add_cancel] using Submodule.add_mem_sup hd ht
  have hD : D = ⊤ := hsuper.eq_top_of_sup_eq_top (by simpa only [sup_comm] using hDT)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1
    (hD.symm ▸ Submodule.mem_top (x := lof R ℕ (fun _ ↦ R) 0 1))
  -- The coefficients of the preimage of the first basis element are the initial products.
  have hw_prod (n : ℕ) : w n = ((List.range n).map a).prod := by
    induction n with
    | zero => simpa [diff, lof_eq_of] using congr($hw 0)
    | succ n ih =>
      have he : w (n + 1) - w n * a n = 0 := by
        simpa [diff, map_succ, lof_eq_of, of_eq_of_ne] using congr($hw (n + 1))
      rw [List.prod_range_succ, ← ih]
      exact sub_eq_zero.mp he
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset w.support
  exact ⟨n, (hw_prod n).symm.trans (DFinsupp.notMem_support_iff.1 hn)⟩

/-- **Anderson–Fuller, Lemma 28.3.** For a left ideal `I`, left T-nilpotence, Nakayama's
vanishing criterion on all left modules, and superfluity of `IM` in all left modules are
equivalent. It suffices to test superfluity on the countably generated free module. -/
theorem isLeftTNilpotent_tfae (I : Ideal R) :
    List.TFAE
      [IsLeftTNilpotent (I : Set R),
        ∀ (M : Type u) [AddCommGroup M] [Module R M],
          I • (⊤ : Submodule R M) = ⊤ → Subsingleton M,
        ∀ (M : Type u) [AddCommGroup M] [Module R M],
          IsSuperfluous (I • (⊤ : Submodule R M)),
        IsSuperfluous (I • (⊤ : Submodule R (ℕ →₀ R)))] := by
  tfae_have 1 → 2 := fun h _ _ _ ↦ h.subsingleton_of_smul_top_eq_top
  tfae_have 2 → 3 := fun h M _ _ ↦ isSuperfluous_smul_top_of_quotient fun N ↦ h (M ⧸ N)
  tfae_have 3 → 4 := fun h ↦ h (ℕ →₀ R)
  tfae_have 4 → 1 := isLeftTNilpotent_of_isSuperfluous_free
  tfae_finish

end Ring

end TauCeti
