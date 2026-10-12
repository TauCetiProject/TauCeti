/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FixedPoints

/-!
# The trivial filtration of a finite `p`-primary module under a pro-`p` group

Let `G` be a pro-`p` group acting continuously on a finite discrete additive group `M` in which
every element has `p`-power order. Iterating the relative fixed-point theorem
`exists_notMem_nsmul_mem_smul_sub_mem_of_isProP`, which supplies for each `G`-stable subgroup
`N ≠ ⊤` an element `x ∉ N` with `p • x ∈ N` fixed modulo `N`, this file builds the
**trivial filtration** of `M`: a `G`-stable increasing chain of subgroups from `⊥` to `⊤` in which
every successive factor is a copy of `𝔽_p` with trivial `G`-action. The chain has length the
`p`-adic valuation of `|M|`, the composition length of `M`, and is constant at `⊤` from there on.
The successive quotients are then packaged as additive groups equivalent to `ZMod p`, with the
induced actions trivial. The ambient finite `p`-primary group need not be killed by `p`.

## Main results

* `TauCeti.exists_filtration_of_isProP`: the `G`-stable filtration with `𝔽_p`-factors and
  trivial action, of length `padicValNat p (Nat.card M)`, described by generators.
* `TauCeti.exists_filtration_with_trivial_factors_of_isProP`: the same filtration with explicit
  additive equivalences of the factors with `ZMod p` and trivial quotient actions.
-/

public section

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]
  {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]

section Filtration

variable (hG : IsProP p G) (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0)

open scoped Classical in
/-- One step of the trivial filtration: adjoin to a `G`-stable subgroup an element as in
`exists_notMem_nsmul_mem_smul_sub_mem_of_isProP`, or stay put at `⊤`. -/
private noncomputable def filtrationStep
    (N : {N : AddSubgroup M // ∀ g : G, ∀ x ∈ N, g • x ∈ N}) :
    {N : AddSubgroup M // ∀ g : G, ∀ x ∈ N, g • x ∈ N} :=
  if h : N.1 = ⊤ then N else
    ⟨N.1 ⊔ AddSubgroup.zmultiples
        (exists_notMem_nsmul_mem_smul_sub_mem_of_isProP hG htors N.2 h).choose,
      smul_mem_sup_zmultiples N.2
        (exists_notMem_nsmul_mem_smul_sub_mem_of_isProP hG htors N.2 h).choose_spec.2.2⟩

private theorem filtrationStep_of_ne_top
    {N : {N : AddSubgroup M // ∀ g : G, ∀ x ∈ N, g • x ∈ N}} (h : N.1 ≠ ⊤) :
    ∃ x : M, (filtrationStep hG htors N).1 = N.1 ⊔ AddSubgroup.zmultiples x ∧
      x ∉ N.1 ∧ p • x ∈ N.1 ∧ ∀ g : G, g • x - x ∈ N.1 :=
  ⟨_, by simp [filtrationStep, h],
    (exists_notMem_nsmul_mem_smul_sub_mem_of_isProP hG htors N.2 h).choose_spec⟩

private theorem filtrationStep_of_eq_top
    {N : {N : AddSubgroup M // ∀ g : G, ∀ x ∈ N, g • x ∈ N}} (h : N.1 = ⊤) :
    filtrationStep hG htors N = N := by
  simp [filtrationStep, h]

private theorem le_filtrationStep (N : {N : AddSubgroup M // ∀ g : G, ∀ x ∈ N, g • x ∈ N}) :
    N.1 ≤ (filtrationStep hG htors N).1 := by
  by_cases h : N.1 = ⊤
  · rw [filtrationStep_of_eq_top hG htors h]
  · obtain ⟨x, hx, -⟩ := filtrationStep_of_ne_top hG htors h
    rw [hx]
    exact le_sup_left

/-- The trivial filtration itself: the iterates of `filtrationStep` starting from `⊥`. -/
private noncomputable def filtrationChain (i : ℕ) :
    {N : AddSubgroup M // ∀ g : G, ∀ x ∈ N, g • x ∈ N} :=
  (filtrationStep hG htors)^[i] ⟨⊥, fun g x hx ↦ by
    rw [AddSubgroup.mem_bot] at hx ⊢
    rw [hx, smul_zero]⟩

private theorem filtrationChain_zero : (filtrationChain hG htors 0).1 = ⊥ := rfl

private theorem filtrationChain_succ (i : ℕ) :
    filtrationChain hG htors (i + 1) = filtrationStep hG htors (filtrationChain hG htors i) :=
  Function.iterate_succ_apply' _ _ _

private theorem monotone_filtrationChain : Monotone fun i ↦ (filtrationChain hG htors i).1 :=
  monotone_nat_of_le_succ fun i ↦ by
    rw [filtrationChain_succ]
    exact le_filtrationStep hG htors _

/-- Once the trivial filtration reaches `⊤` it stays there. -/
private theorem filtrationChain_eq_top_of_le {n : ℕ} (hn : (filtrationChain hG htors n).1 = ⊤) :
    ∀ i, n ≤ i → (filtrationChain hG htors i).1 = ⊤ := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact hn
  | succ i _ ih => rw [filtrationChain_succ, filtrationStep_of_eq_top hG htors ih, ih]

/-- The orders along the trivial filtration: the `i`-th term has order `p ^ i` as long as `i` is
at most the `p`-adic valuation of `|M|`. -/
private theorem natCard_filtrationChain :
    ∀ i ≤ padicValNat p (Nat.card M), Nat.card (filtrationChain hG htors i).1 = p ^ i := by
  intro i
  induction i with
  | zero => intro _; simp [filtrationChain_zero]
  | succ i ih =>
    intro hi
    have hcard := ih (Nat.le_of_succ_le hi)
    have hne : (filtrationChain hG htors i).1 ≠ ⊤ := by
      intro htop
      rw [htop, AddSubgroup.card_top,
        natCard_eq_pow_padicValNat_of_forall_exists_nsmul_eq_zero htors] at hcard
      have := Nat.pow_right_injective hp.out.two_le hcard
      omega
    obtain ⟨x, hx, hxN, hpx, -⟩ := filtrationStep_of_ne_top hG htors hne
    rw [filtrationChain_succ, hx, natCard_sup_zmultiples_of_nsmul_mem hxN hpx, hcard, pow_succ']

include hG htors in
/-- **The trivial-filtration theorem.** A finite discrete `p`-primary additive group `M` with a
continuous action of a pro-`p` group `G` has a `G`-stable increasing chain of subgroups
`N 0 = ⊥ ≤ N 1 ≤ …` reaching `⊤` after `padicValNat p (Nat.card M)` steps, the composition
length of `M`, and constant at `⊤` from there on, with `|N i| = p ^ i` along the way. Each step
adjoins an element `x` with `x ∉ N i`, `p • x ∈ N i` and `g • x - x ∈ N i` for every `g`, so
every factor `N (i + 1) ⧸ N i` is a copy of `𝔽_p` with trivial `G`-action. -/
theorem exists_filtration_of_isProP :
    ∃ N : ℕ → AddSubgroup M, N 0 = ⊥ ∧ Monotone N ∧
      (∀ i, padicValNat p (Nat.card M) ≤ i → N i = ⊤) ∧
      (∀ i, ∀ g : G, ∀ x ∈ N i, g • x ∈ N i) ∧
      (∀ i ≤ padicValNat p (Nat.card M), Nat.card (N i) = p ^ i) ∧
      ∀ i < padicValNat p (Nat.card M), ∃ x : M, N (i + 1) = N i ⊔ AddSubgroup.zmultiples x ∧
        x ∉ N i ∧ p • x ∈ N i ∧ ∀ g : G, g • x - x ∈ N i := by
  have hcard := natCard_filtrationChain hG htors
  refine ⟨fun i ↦ (filtrationChain hG htors i).1, filtrationChain_zero hG htors,
    monotone_filtrationChain hG htors, filtrationChain_eq_top_of_le hG htors ?_,
    fun i ↦ (filtrationChain hG htors i).2, hcard, fun i hi ↦ ?_⟩
  · rw [← AddSubgroup.card_eq_iff_eq_top, hcard _ le_rfl]
    exact (natCard_eq_pow_padicValNat_of_forall_exists_nsmul_eq_zero htors).symm
  · have hne : (filtrationChain hG htors i).1 ≠ ⊤ := by
      intro htop
      have := hcard i hi.le
      rw [htop, AddSubgroup.card_top,
        natCard_eq_pow_padicValNat_of_forall_exists_nsmul_eq_zero htors] at this
      have := Nat.pow_right_injective hp.out.two_le this
      omega
    obtain ⟨x, hx, hxN, hpx, hgx⟩ := filtrationStep_of_ne_top hG htors hne
    exact ⟨x, by simp only [filtrationChain_succ, hx], hxN, hpx, hgx⟩

end Filtration

/-- A finite discrete `p`-primary group with a continuous pro-`p` action has a stable filtration
whose successive quotients are additively equivalent to `ZMod p` and have trivial induced
action. Only indices below the composition length contribute a factor; the chain is constant
at `⊤` thereafter. -/
theorem exists_filtration_with_trivial_factors_of_isProP (hG : IsProP p G)
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) :
    ∃ (N : ℕ → AddSubgroup M) (hN : ∀ i, ∀ g : G, ∀ x ∈ N i, g • x ∈ N i),
      N 0 = ⊥ ∧ Monotone N ∧
      (∀ i, padicValNat p (Nat.card M) ≤ i → N i = ⊤) ∧
      (∀ i ≤ padicValNat p (Nat.card M), Nat.card (N i) = p ^ i) ∧
      ∀ i < padicValNat p (Nat.card M),
        letI := (N i).subquotientDistribMulAction (N (i + 1)) (hN i) (hN (i + 1))
        Nonempty ((N (i + 1) ⧸ (N i).addSubgroupOf (N (i + 1))) ≃+ ZMod p) ∧
          ∀ (g : G) (y : N (i + 1) ⧸ (N i).addSubgroupOf (N (i + 1))), g • y = y := by
  obtain ⟨N, h0, hmono, htop, hN, hcard, hgen⟩ := exists_filtration_of_isProP hG htors
  refine ⟨N, hN, h0, hmono, htop, hcard, fun i hi ↦ ?_⟩
  obtain ⟨x, hx, hxN, hpx, hgx⟩ := hgen i hi
  exact ⟨⟨subquotientEquivZModOfEqSupZmultiples hx hxN hpx⟩,
    subquotient_smul_eq_self_of_eq_sup_zmultiples (hN i) hx hgx⟩

end TauCeti
