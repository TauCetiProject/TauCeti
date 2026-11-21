/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint
public import TauCeti.SetTheory.Cardinal.Beth

/-!
# Cutoff cardinals

Sites of perfectoid spaces, such as the pro-étale and v-sites underlying diamonds, are not small.
They are made small by bounding the size of the spaces involved by a cardinal `κ`, and this bound
must survive the constructions performed on the site: power sets, countable unions, and limits of
fewer than `κ` stages of uniformly bounded size. Scholze isolates the cardinals for which this
works ([ECD] Lemma 4.1): a *cutoff cardinal* is an uncountable strong limit cardinal `κ` of
uncountable cofinality such that for every `c < κ` there is a strong limit cardinal `μ < κ` of
cofinality larger than `c`. The last clause supplies, between any cardinal below `κ` and `κ`,
a strong limit whose cofinality exceeds any prescribed size below `κ`; this bounds limits of
diagrams with fewer than `κ` arrows.

The cutoff cardinals form a cofinal class: above every cardinal there is one
(`Cardinal.exists_isCutoff_gt`). They exist in ZFC, with no large-cardinal axiom: every fixed
point `κ = ℶ_κ` of the beth function of uncountable cofinality is a cutoff cardinal
(`Cardinal.isCutoff_of_beth_ord_eq`), and such fixed points occur above every cardinal.

## Main definitions

* `Cardinal.IsCutoff κ`: `κ` is a cutoff cardinal.

## Main results

* `Cardinal.IsCutoff.aleph0_lt`: a cutoff cardinal is uncountable.
* `Cardinal.IsCutoff.iSup_lt_of_countable`: the supremum of countably many cardinals below a cutoff
  cardinal is below it.
* `Cardinal.IsCutoff.exists_isStrongLimit_mem_Ico`: between any `a < κ` and a cutoff cardinal `κ`
  there is a strong limit cardinal whose cofinality exceeds any given `c < κ`.
* `Cardinal.isCutoff_of_beth_ord_eq`: a beth fixed point of uncountable cofinality is a cutoff
  cardinal.
* `Cardinal.exists_isCutoff_gt`: above every cardinal there is a cutoff cardinal.
* `Cardinal.not_isCutoff_aleph0`, `Cardinal.not_isCutoff_beth_omega0`: `ℵ₀` and `ℶ_ω` are strong
  limit cardinals that are not cutoff cardinals.

## References

* [ECD] P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §4, Lemma 4.1 and the
  discussion following it.
-/

public section

universe u

open Ordinal Order

namespace Cardinal

/-- A *cutoff cardinal* ([ECD] Lemma 4.1): a strong limit cardinal `κ` of uncountable cofinality
such that below `κ` there are strong limit cardinals of arbitrarily large cofinality: for every
`c < κ` there is a strong limit cardinal `μ < κ` whose cofinality exceeds `c`.

Uncountable cofinality says that a countable family of cardinals below `κ` has its supremum below
`κ` (`Cardinal.IsCutoff.iSup_lt_of_countable`). The uncountability of `κ` itself, which [ECD]
lists as a separate clause, follows (`Cardinal.IsCutoff.aleph0_lt`). -/
@[mk_iff]
structure IsCutoff (κ : Cardinal.{u}) : Prop where
  /-- A cutoff cardinal is a strong limit cardinal. -/
  isStrongLimit : IsStrongLimit κ
  /-- A cutoff cardinal has uncountable cofinality. -/
  aleph0_lt_cof_ord : ℵ₀ < κ.ord.cof
  /-- Below a cutoff cardinal there are strong limit cardinals of arbitrarily large cofinality. -/
  exists_isStrongLimit_lt_cof : ∀ c < κ, ∃ μ < κ, IsStrongLimit μ ∧ c < μ.ord.cof

namespace IsCutoff

variable {κ : Cardinal.{u}}

/-- A cutoff cardinal is uncountable. -/
theorem aleph0_lt (h : IsCutoff κ) : ℵ₀ < κ :=
  h.aleph0_lt_cof_ord.trans_le (cof_ord_le κ)

/-- The supremum of a countable family of cardinals below a cutoff cardinal is below it. -/
theorem iSup_lt_of_countable (h : IsCutoff κ) {ι : Type*} [Countable ι] {f : ι → Cardinal.{u}}
    (hf : ∀ i, f i < κ) : ⨆ i, f i < κ := by
  refine lift_iSup_lt_of_lt_cof_ord ?_ hf
  rw [← lift_ord, ← lift_cof]
  exact (lift_le_aleph0.2 mk_le_aleph0).trans_lt (aleph0_lt_lift.2 h.aleph0_lt_cof_ord)

/-- Between any cardinal `a < κ` and a cutoff cardinal `κ` there is a strong limit cardinal whose
cofinality exceeds any given `c < κ`. -/
theorem exists_isStrongLimit_mem_Ico (h : IsCutoff κ) {a c : Cardinal.{u}} (ha : a < κ)
    (hc : c < κ) : ∃ μ ∈ Set.Ico a κ, IsStrongLimit μ ∧ c < μ.ord.cof := by
  obtain ⟨μ, hμκ, hμ, hcof⟩ := h.exists_isStrongLimit_lt_cof (max a c) (max_lt ha hc)
  exact ⟨μ, ⟨((le_max_left a c).trans hcof.le).trans (cof_ord_le μ), hμκ⟩, hμ,
    (le_max_right a c).trans_lt hcof⟩

end IsCutoff

/-- `0` is not a cutoff cardinal. -/
@[simp]
theorem not_isCutoff_zero : ¬ IsCutoff 0 :=
  fun h ↦ h.isStrongLimit.ne_zero rfl

/-- `ℵ₀` is a strong limit cardinal but not a cutoff cardinal, since it is countable. -/
@[simp]
theorem not_isCutoff_aleph0 : ¬ IsCutoff ℵ₀ :=
  fun h ↦ h.aleph0_lt.false

/-- `ℶ_ω` is an uncountable strong limit cardinal but not a cutoff cardinal, since its cofinality
is countable. -/
theorem not_isCutoff_beth_omega0 : ¬ IsCutoff (ℶ_ ω) := by
  intro h
  have := h.aleph0_lt_cof_ord
  rw [cof_ord_beth isSuccLimit_omega0, cof_omega0] at this
  exact this.false

/-- **Beth fixed points of uncountable cofinality are cutoff cardinals.** If `κ = ℶ_κ`, where `κ`
indexes the beth function through its initial ordinal, and `κ` has uncountable cofinality, then
`κ` is a cutoff cardinal. -/
theorem isCutoff_of_beth_ord_eq {κ : Cardinal.{u}} (hκ : ℶ_ κ.ord = κ) (hcof : ℵ₀ < κ.ord.cof) :
    IsCutoff κ := by
  have hlim : IsSuccLimit κ.ord := isSuccLimit_ord (hκ ▸ aleph0_le_beth _)
  have hstrong : IsStrongLimit κ := hκ ▸ isStrongLimit_beth.2 hlim.isSuccPrelimit
  refine ⟨hstrong, hcof, fun c hc ↦ ?_⟩
  -- The strong limit `ℶ_ ν.ord` for the regular cardinal `ν = succ (max c ℵ₀)` has cofinality
  -- `ν > c`, and it lies below `κ = ℶ_ κ.ord` because `ν < κ`.
  have hreg : (succ (max c ℵ₀)).IsRegular := isRegular_succ (le_max_right c ℵ₀)
  have hν : succ (max c ℵ₀) < κ :=
    hstrong.isSuccLimit.succ_lt (max_lt hc (hcof.trans_le (cof_ord_le κ)))
  refine ⟨ℶ_ (succ (max c ℵ₀)).ord, ?_, hreg.isStrongLimit_beth_ord, ?_⟩
  · conv_rhs => rw [← hκ]
    exact beth_strictMono (ord_strictMono hν)
  · rw [hreg.cof_ord_beth_ord]
    exact (le_max_left c ℵ₀).trans_lt (lt_succ _)

/-- **Cutoff cardinals are cofinal** ([ECD] Lemma 4.1): above every cardinal there is a cutoff
cardinal. -/
theorem exists_isCutoff_gt (c : Cardinal.{u}) : ∃ κ, c < κ ∧ IsCutoff κ := by
  -- Take the fixed point of `o ↦ (ℶ_ o).ord` enumerated at the initial ordinal `a` of the
  -- regular cardinal `succ (max c ℵ₀)`; it lies above `a` and has the cofinality of `a`.
  have hreg : (succ (max c ℵ₀)).IsRegular := isRegular_succ (le_max_right c ℵ₀)
  have ha : IsSuccLimit (succ (max c ℵ₀)).ord := isSuccLimit_ord hreg.aleph0_le
  set δ := deriv (fun o ↦ (ℶ_ o).ord) (succ (max c ℵ₀)).ord
  have hfix : (ℶ_ δ).ord = δ := deriv_fp isNormal_ord_beth _
  refine ⟨ℶ_ δ, ?_, isCutoff_of_beth_ord_eq (by rw [hfix]) ?_⟩
  · rw [← ord_lt_ord, hfix]
    exact (ord_strictMono ((le_max_left c ℵ₀).trans_lt (lt_succ _))).trans_le
      (isNormal_deriv _).strictMono.le_apply
  · rw [hfix, cof_map_of_isNormal (isNormal_deriv _) ha, hreg.cof_ord]
    exact (le_max_right c ℵ₀).trans_lt (lt_succ _)

end Cardinal
