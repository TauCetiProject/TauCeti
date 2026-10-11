/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import TauCeti.Order.Filter.AtTopBot
public import TauCeti.Topology.Semicontinuity.Basic

/-!
# Γ-convergence

A sequence of extended-real functionals `F n : X → EReal` on a topological space
*Γ-converges* to `f : X → EReal` if

* (liminf inequality) `f x ≤ liminf F n (u n)` along every sequence `u n → x`, and
* (recovery sequences) every `x` is the limit of a sequence `u n → x` with
  `limsup F n (u n) ≤ f x`.

This is the notion of convergence of functionals under which minimization passes to the limit:
on every topological space, cluster points of minimizers of `F n` minimize `f`; on a
first-countable space, under equicoercivity (`TauCeti.Equicoercive`: every sublevel `{F n ≤ t}`
lies in a compact set independent of `n`) the infima of `F n` converge to the infimum of `f`, which
is attained when the space is nonempty. Γ-convergence is stable under continuous perturbations,
which is how it is applied to penalized functionals such as `F n + d(·, x)² / (2τ)` in the
stability theory of resolvents and minimizing movements.

The *lower and upper Γ-limits* are defined through neighbourhoods,

`Γ-liminf F x = sup_{s ∈ 𝓝 x} liminf_n inf_{y ∈ s} F n y`,

and likewise with `limsup`. They are lower semicontinuous for every topology. On a first-countable
space they are attained by sequences, so the sequential definition above says exactly that both
Γ-limits equal `f` (`TauCeti.tendstoGamma_iff_gammaLiminf_eq_and_gammaLimsup_eq`). In particular,
on a first-countable space a Γ-limit is lower semicontinuous. Γ-convergence passes to
subsequences on every topological space.

## Main definitions

* `TauCeti.TendstoGamma F f`: the sequence `F` Γ-converges to `f`, in the sequential sense.
* `TauCeti.gammaLiminf F` and `TauCeti.gammaLimsup F`: the lower and upper Γ-limits.
* `TauCeti.Equicoercive F`: all sublevel sets `{F n ≤ t}` of a real level `t` lie in one compact
  set.

## Main results

* `TauCeti.tendstoGamma_iff_gammaLiminf_eq_and_gammaLimsup_eq`: on a first-countable space,
  sequential Γ-convergence is the equality of the two neighbourhood Γ-limits with `f`.
* `TauCeti.TendstoGamma.lowerSemicontinuous`: on a first-countable space, a Γ-limit is lower
  semicontinuous.
* `TauCeti.TendstoGamma.comp`: Γ-convergence passes to subsequences, on every topological space.
* `TauCeti.TendstoGamma.add_continuous`: Γ-convergence is stable under adding a continuous real
  function.
* `TauCeti.TendstoGamma.isMinOn_of_tendsto`: cluster points of minimizers are minimizers, on
  every topological space.
* `TauCeti.TendstoGamma.tendsto_iInf` and `TauCeti.TendstoGamma.exists_isMinOn`: the
  **fundamental theorem of Γ-convergence**: for an equicoercive sequence on a first-countable
  space, the infima converge to the infimum of the Γ-limit, and the latter is attained when the
  space is nonempty.

## References

* A. Braides, *Γ-convergence for Beginners*, Oxford University Press 2002, Chapter 1.
* G. Dal Maso, *An Introduction to Γ-Convergence*, Birkhäuser 1993, Chapters 4, 7 and 8.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {F : ℕ → X → EReal} {f : X → EReal} {x : X}
  {u : ℕ → X}

/-- A sequence of functionals `F n` *Γ-converges* to `f` if `f x ≤ liminf F n (u n)` along every
sequence `u n → x`, and every `x` has a *recovery sequence* `u n → x` with
`limsup F n (u n) ≤ f x`. -/
structure TendstoGamma (F : ℕ → X → EReal) (f : X → EReal) : Prop where
  /-- The liminf inequality. -/
  le_liminf ⦃x : X⦄ ⦃u : ℕ → X⦄ (hu : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (fun n ↦ F n (u n)) atTop
  /-- Every point has a recovery sequence. -/
  exists_tendsto_limsup_le (x : X) :
    ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ limsup (fun n ↦ F n (u n)) atTop ≤ f x

/-- The *lower Γ-limit* `sup_{s ∈ 𝓝 x} liminf_n inf_{y ∈ s} F n y` of a sequence of functionals. -/
def gammaLiminf (F : ℕ → X → EReal) (x : X) : EReal :=
  ⨆ s ∈ 𝓝 x, liminf (fun n ↦ ⨅ y ∈ s, F n y) atTop

/-- The *upper Γ-limit* `sup_{s ∈ 𝓝 x} limsup_n inf_{y ∈ s} F n y` of a sequence of functionals. -/
def gammaLimsup (F : ℕ → X → EReal) (x : X) : EReal :=
  ⨆ s ∈ 𝓝 x, limsup (fun n ↦ ⨅ y ∈ s, F n y) atTop

/-- A sequence of functionals is *equicoercive* if for every real level `t` the sublevel sets
`{F n ≤ t}` all lie in one compact set. -/
def Equicoercive (F : ℕ → X → EReal) : Prop :=
  ∀ t : ℝ, ∃ K, IsCompact K ∧ ∀ n x, F n x ≤ t → x ∈ K

/-- The defining formula of the lower Γ-limit. -/
theorem gammaLiminf_def (F : ℕ → X → EReal) (x : X) :
    gammaLiminf F x = ⨆ s ∈ 𝓝 x, liminf (fun n ↦ ⨅ y ∈ s, F n y) atTop :=
  (rfl)

/-- The defining formula of the upper Γ-limit. -/
theorem gammaLimsup_def (F : ℕ → X → EReal) (x : X) :
    gammaLimsup F x = ⨆ s ∈ 𝓝 x, limsup (fun n ↦ ⨅ y ∈ s, F n y) atTop :=
  (rfl)

/-- The defining property of an equicoercive sequence. -/
theorem equicoercive_def :
    Equicoercive F ↔ ∀ t : ℝ, ∃ K, IsCompact K ∧ ∀ n x, F n x ≤ t → x ∈ K :=
  Iff.rfl

/-- Equicoercivity passes to subsequences, and more generally to reindexings. -/
theorem Equicoercive.comp (hF : Equicoercive F) (φ : ℕ → ℕ) : Equicoercive fun k ↦ F (φ k) :=
  fun t ↦ (hF t).imp fun _ hK ↦ ⟨hK.1, fun k ↦ hK.2 (φ k)⟩

/-! ### The neighbourhood Γ-limits -/

/-- The lower Γ-limit is lower semicontinuous. -/
theorem lowerSemicontinuous_gammaLiminf (F : ℕ → X → EReal) :
    LowerSemicontinuous (gammaLiminf F) :=
  lowerSemicontinuous_iSup_nhds _

/-- The upper Γ-limit is lower semicontinuous. -/
theorem lowerSemicontinuous_gammaLimsup (F : ℕ → X → EReal) :
    LowerSemicontinuous (gammaLimsup F) :=
  lowerSemicontinuous_iSup_nhds _

/-- The lower Γ-limit is at most the upper Γ-limit. -/
theorem gammaLiminf_le_gammaLimsup (F : ℕ → X → EReal) (x : X) :
    gammaLiminf F x ≤ gammaLimsup F x :=
  iSup₂_mono fun _ _ ↦ liminf_le_limsup

/-- The lower Γ-limit at `x` is at most `liminf F n (u n)` along every sequence `u n → x`. -/
theorem gammaLiminf_le_liminf (hu : Tendsto u atTop (𝓝 x)) :
    gammaLiminf F x ≤ liminf (fun n ↦ F n (u n)) atTop :=
  iSup₂_le fun _ hs ↦ liminf_le_liminf <| (hu.eventually_mem hs).mono fun n hn ↦ iInf₂_le (u n) hn

/-- The upper Γ-limit at `x` is at most `limsup F n (u n)` along every sequence `u n → x`. -/
theorem gammaLimsup_le_limsup (hu : Tendsto u atTop (𝓝 x)) :
    gammaLimsup F x ≤ limsup (fun n ↦ F n (u n)) atTop :=
  iSup₂_le fun _ hs ↦ limsup_le_limsup <| (hu.eventually_mem hs).mono fun n hn ↦ iInf₂_le (u n) hn

/-- Passing to a subsequence can only increase the lower Γ-limit. -/
theorem gammaLiminf_le_gammaLiminf_comp {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    gammaLiminf F x ≤ gammaLiminf (fun k ↦ F (φ k)) x :=
  iSup₂_mono fun s _ ↦ hφ.liminf_le_liminf_comp (u := fun n ↦ ⨅ y ∈ s, F n y)

section FirstCountableTopology

variable [FirstCountableTopology X]

/-- On a first-countable space the lower Γ-limit is attained by a sequence: some `u n → x` has
`liminf F n (u n) ≤ Γ-liminf F x`. -/
theorem exists_tendsto_liminf_le_gammaLiminf (F : ℕ → X → EReal) (x : X) :
    ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ liminf (fun n ↦ F n (u n)) atTop ≤ gammaLiminf F x := by
  rcases eq_or_ne (gammaLiminf F x) ⊤ with hL | hL
  · exact ⟨fun _ ↦ x, tendsto_const_nhds, hL ▸ le_top⟩
  obtain ⟨s, hs⟩ := (𝓝 x).exists_antitone_basis
  obtain ⟨c, -, hcL, hc⟩ := exists_seq_strictAnti_tendsto' (lt_top_iff_ne_top.2 hL)
  -- For each `k`, infinitely many `F n` take a value `< c k` on `s k`; extract one such `n`
  -- for each `k` along a subsequence `φ`, and put the corresponding point at time `φ k`.
  have h : ∀ k, ∃ᶠ n in atTop, ∃ y ∈ s k, F n y < c k := fun k ↦
    (frequently_lt_of_liminf_lt (by isBoundedDefault) ((le_iSup₂ (f := fun s (_ : s ∈ 𝓝 x) ↦
      liminf (fun n ↦ ⨅ y ∈ s, F n y) atTop) (s k) (hs.mem k)).trans_lt (hcL k).1)).mono
      fun _ hn ↦ by simpa only [iInf_lt_iff, exists_prop] using hn
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_frequently h
  choose y hys hyc using hφP
  refine ⟨Function.extend φ y fun _ ↦ x, hs.1.tendsto_right_iff.2 fun k _ ↦ ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (φ k)] with n hn
    by_cases hn' : ∃ j, φ j = n
    · obtain ⟨j, rfl⟩ := hn'
      rw [hφ.injective.extend_apply]
      exact hs.antitone (hφ.le_iff_le.1 hn) (hys j)
    · rw [Function.extend_apply' _ _ _ hn']
      exact mem_of_mem_nhds (hs.mem k)
  · calc liminf (fun n ↦ F n (Function.extend φ y (fun _ ↦ x) n)) atTop
        ≤ liminf (fun k ↦ F (φ k) (y k)) atTop := by
          simpa only [Function.comp_def, hφ.injective.extend_apply] using
            hφ.tendsto_atTop.liminf_le_liminf_comp
              (u := fun n ↦ F n (Function.extend φ y (fun _ ↦ x) n))
      _ ≤ liminf c atTop := liminf_le_liminf (Eventually.of_forall fun k ↦ (hyc k).le)
      _ = gammaLiminf F x := hc.liminf_eq

/-- On a first-countable space the upper Γ-limit is attained by a sequence: some `u n → x` has
`limsup F n (u n) ≤ Γ-limsup F x`. -/
theorem exists_tendsto_limsup_le_gammaLimsup (F : ℕ → X → EReal) (x : X) :
    ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ limsup (fun n ↦ F n (u n)) atTop ≤ gammaLimsup F x := by
  rcases eq_or_ne (gammaLimsup F x) ⊤ with hL | hL
  · exact ⟨fun _ ↦ x, tendsto_const_nhds, hL ▸ le_top⟩
  obtain ⟨s, hs⟩ := (𝓝 x).exists_antitone_basis
  obtain ⟨c, hcanti, hcL, hc⟩ := exists_seq_strictAnti_tendsto' (lt_top_iff_ne_top.2 hL)
  -- For each `k`, all large `F n` take a value `< c k` on `s k`; follow these requirements for
  -- a slowly increasing index `κ n`.
  have h : ∀ k, ∀ᶠ n in atTop, ∃ y ∈ s k, F n y < c k := fun k ↦
    (eventually_lt_of_limsup_lt ((le_iSup₂ (f := fun s (_ : s ∈ 𝓝 x) ↦
      limsup (fun n ↦ ⨅ y ∈ s, F n y) atTop) (s k) (hs.mem k)).trans_lt (hcL k).1)).mono
      fun _ hn ↦ by simpa only [iInf_lt_iff, exists_prop] using hn
  obtain ⟨κ, hκ, hκP⟩ := exists_tendsto_atTop_of_forall_eventually h
  classical
  let v : ℕ → X := fun n ↦ if hn : ∃ y ∈ s (κ n), F n y < c (κ n) then hn.choose else x
  have hv : ∀ᶠ n in atTop, v n ∈ s (κ n) ∧ F n (v n) < c (κ n) := hκP.mono fun n hn ↦ by
    simp only [v, dite_eq_left hn]
    exact hn.choose_spec
  refine ⟨v, hs.1.tendsto_right_iff.2 fun k _ ↦ ?_, ?_⟩
  · filter_upwards [hv, hκ.eventually_ge_atTop k] with n hn hkn
    exact hs.antitone hkn hn.1
  · refine le_of_forall_gt fun d hd ↦ ?_
    obtain ⟨k, hk⟩ := (hc.eventually (gt_mem_nhds hd)).exists
    refine (limsup_le_of_le (h := ?_)).trans_lt hk
    filter_upwards [hv, hκ.eventually_ge_atTop k] with n hn hkn
    exact hn.2.le.trans (hcanti.antitone hkn)

/-- On a first-countable space, the liminf inequality for `f` along every sequence holds exactly
when `f` is bounded by the lower Γ-limit. -/
theorem le_gammaLiminf_iff : f ≤ gammaLiminf F ↔
    ∀ ⦃x : X⦄ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (fun n ↦ F n (u n)) atTop :=
  ⟨fun h _ _ hu ↦ (h _).trans (gammaLiminf_le_liminf hu), fun h x ↦ by
    obtain ⟨u, hu, hle⟩ := exists_tendsto_liminf_le_gammaLiminf F x
    exact (h hu).trans hle⟩

/-- On a first-countable space, every point has a recovery sequence for `f` exactly when the
upper Γ-limit is bounded by `f`. -/
theorem gammaLimsup_le_iff : gammaLimsup F ≤ f ↔
    ∀ x, ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ limsup (fun n ↦ F n (u n)) atTop ≤ f x :=
  ⟨fun h x ↦ (exists_tendsto_limsup_le_gammaLimsup F x).imp fun _ hu ↦ ⟨hu.1, hu.2.trans (h x)⟩,
    fun h x ↦ by
      obtain ⟨u, hu, hle⟩ := h x
      exact (gammaLimsup_le_limsup hu).trans hle⟩

/-- On a first-countable space, `F` Γ-converges to `f` exactly when the lower and the upper
Γ-limits of `F` both equal `f`. -/
theorem tendstoGamma_iff_gammaLiminf_eq_and_gammaLimsup_eq :
    TendstoGamma F f ↔ gammaLiminf F = f ∧ gammaLimsup F = f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨le_gammaLiminf_iff.1 h.1.ge, gammaLimsup_le_iff.1 h.2.le⟩⟩
  have h₁ := le_gammaLiminf_iff.2 h.le_liminf
  have h₂ := gammaLimsup_le_iff.2 h.exists_tendsto_limsup_le
  exact ⟨le_antisymm (fun x ↦ (gammaLiminf_le_gammaLimsup F x).trans (h₂ x)) h₁,
    le_antisymm h₂ (fun x ↦ (h₁ x).trans (gammaLiminf_le_gammaLimsup F x))⟩

namespace TendstoGamma

/-- On a first-countable space a Γ-limit is the lower Γ-limit. -/
theorem gammaLiminf_eq (h : TendstoGamma F f) : gammaLiminf F = f :=
  (tendstoGamma_iff_gammaLiminf_eq_and_gammaLimsup_eq.1 h).1

/-- On a first-countable space a Γ-limit is the upper Γ-limit. -/
theorem gammaLimsup_eq (h : TendstoGamma F f) : gammaLimsup F = f :=
  (tendstoGamma_iff_gammaLiminf_eq_and_gammaLimsup_eq.1 h).2

/-- On a first-countable space a Γ-limit is lower semicontinuous. -/
theorem lowerSemicontinuous (h : TendstoGamma F f) : LowerSemicontinuous f :=
  h.gammaLiminf_eq ▸ lowerSemicontinuous_gammaLiminf F

end TendstoGamma

end FirstCountableTopology

namespace TendstoGamma

/-- Γ-convergence passes to subsequences, and more generally to reindexings tending to
infinity. -/
theorem comp (h : TendstoGamma F f) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    TendstoGamma (fun k ↦ F (φ k)) f where
  le_liminf x u hu := by
    -- Along a strictly increasing reindexing `ψ`, padding the points with `x` gives a sequence
    -- converging to `x`, to which the liminf inequality for `F` applies.
    have key {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {v : ℕ → X} (hv : Tendsto v atTop (𝓝 x)) :
        f x ≤ liminf (fun j ↦ F (ψ j) (v j)) atTop := by
      have hw : Tendsto (Function.extend ψ v fun _ ↦ x) atTop (𝓝 x) := tendsto_def.2 fun U hU ↦ by
        obtain ⟨J, hJ⟩ := eventually_atTop.1 (hv.eventually_mem hU)
        filter_upwards [eventually_ge_atTop (ψ J)] with n hn
        by_cases hn' : ∃ j, ψ j = n
        · obtain ⟨j, rfl⟩ := hn'
          rw [mem_preimage, hψ.injective.extend_apply]
          exact hJ j (hψ.le_iff_le.1 hn)
        · rw [mem_preimage, Function.extend_apply' _ _ _ hn']
          exact mem_of_mem_nhds hU
      simpa only [Function.comp_def, hψ.injective.extend_apply] using
        (h.le_liminf hw).trans (hψ.tendsto_atTop.liminf_le_liminf_comp
          (u := fun n ↦ F n (Function.extend ψ v (fun _ ↦ x) n)))
    -- Otherwise infinitely many values lie below some `c < f x`; along them, `φ` can be made
    -- strictly increasing, which contradicts `key`.
    by_contra! hlt
    obtain ⟨c, hlc, hcf⟩ := exists_between hlt
    obtain ⟨ψ₁, hψ₁, hψ₁c⟩ :=
      extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hlc)
    obtain ⟨ψ₂, hψ₂, hφψ⟩ := strictMono_subseq_of_tendsto_atTop (hφ.comp hψ₁.tendsto_atTop)
    refine hcf.not_ge ((key hφψ (hu.comp (hψ₁.comp hψ₂).tendsto_atTop)).trans ?_)
    exact (liminf_le_liminf (Eventually.of_forall fun j ↦ (hψ₁c (ψ₂ j)).le)).trans_eq
      (liminf_const c)
  exists_tendsto_limsup_le x := by
    obtain ⟨u, hu, hle⟩ := h.exists_tendsto_limsup_le x
    exact ⟨u ∘ φ, hu.comp hφ, (hφ.limsup_comp_le_limsup (u := fun n ↦ F n (u n))).trans hle⟩

/-- Γ-convergence is stable under adding a continuous real function. -/
theorem add_continuous (h : TendstoGamma F f) {g : X → ℝ} (hg : Continuous g) :
    TendstoGamma (fun n x ↦ F n x + g x) (fun x ↦ f x + g x) := by
  have hlim {x : X} {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x)) :
      Tendsto (fun n ↦ (g (u n) : EReal)) atTop (𝓝 (g x : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp ((hg.tendsto x).comp hu)
  refine ⟨fun x u hu ↦ ?_, fun x ↦ ?_⟩
  · calc f x + g x
        ≤ liminf (fun n ↦ F n (u n)) atTop + liminf (fun n ↦ (g (u n) : EReal)) atTop := by
          rw [(hlim hu).liminf_eq]
          gcongr
          exact h.le_liminf hu
      _ ≤ liminf (fun n ↦ F n (u n) + g (u n)) atTop := EReal.le_liminf_add
  · obtain ⟨u, hu, hle⟩ := h.exists_tendsto_limsup_le x
    refine ⟨u, hu, ?_⟩
    calc limsup (fun n ↦ F n (u n) + g (u n)) atTop
        ≤ limsup (fun n ↦ F n (u n)) atTop + limsup (fun n ↦ (g (u n) : EReal)) atTop :=
          EReal.limsup_add_le (.inr (by simp [(hlim hu).limsup_eq]))
            (.inr (by simp [(hlim hu).limsup_eq]))
      _ ≤ f x + g x := by
          rw [(hlim hu).limsup_eq]
          gcongr

/-- A constant sequence of lower semicontinuous functionals Γ-converges to its value. -/
theorem _root_.LowerSemicontinuous.tendstoGamma_const {g : X → EReal}
    (hg : LowerSemicontinuous g) : TendstoGamma (fun _ ↦ g) g where
  le_liminf x u hu :=
    (hg.le_liminf x).trans (hu.liminf_le_liminf_comp (u := g))
  exists_tendsto_limsup_le x := ⟨fun _ ↦ x, tendsto_const_nhds, by simp⟩

/-- The upper limit of the infima of a Γ-converging sequence is at most the infimum of the
Γ-limit. -/
theorem limsup_iInf_le (h : TendstoGamma F f) :
    limsup (fun n ↦ ⨅ x, F n x) atTop ≤ ⨅ x, f x :=
  le_iInf fun x ↦ by
    obtain ⟨u, -, hle⟩ := h.exists_tendsto_limsup_le x
    exact (limsup_le_limsup (Eventually.of_forall fun n ↦ iInf_le _ (u n))).trans hle

/-- Cluster points of minimizers are minimizers: if `u n` minimizes `F n` and `u (φ k) → x₀`
along a subsequence, then `x₀` minimizes the Γ-limit `f`. -/
theorem isMinOn_of_tendsto (h : TendstoGamma F f) (hu : ∀ n, IsMinOn (F n) univ (u n))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {x₀ : X} (hx₀ : Tendsto (u ∘ φ) atTop (𝓝 x₀)) :
    IsMinOn f univ x₀ := fun y _ ↦ by
  obtain ⟨v, hv, hle⟩ := (h.comp hφ).exists_tendsto_limsup_le y
  calc f x₀ ≤ liminf (fun k ↦ F (φ k) (u (φ k))) atTop := (h.comp hφ).le_liminf hx₀
    _ ≤ liminf (fun k ↦ F (φ k) (v k)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k ↦ hu (φ k) (mem_univ (v k)))
    _ ≤ limsup (fun k ↦ F (φ k) (v k)) atTop := liminf_le_limsup
    _ ≤ f y := hle

variable [FirstCountableTopology X]

/-- A sequence of points of bounded energy for an equicoercive Γ-converging sequence has a
convergent subsequence, along which the liminf inequality bounds the Γ-limit at its limit. -/
theorem exists_tendsto_subseq (h : TendstoGamma F f) (hc : Equicoercive F) {t : ℝ}
    (hu : ∀ n, F n (u n) ≤ t) :
    ∃ (x₀ : X) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 x₀) ∧
      f x₀ ≤ liminf (fun i ↦ F (ψ i) (u (ψ i))) atTop := by
  obtain ⟨K, hK, hFK⟩ := hc t
  obtain ⟨x₀, -, ψ, hψ, hψx₀⟩ := hK.tendsto_subseq fun n ↦ hFK n (u n) (hu n)
  exact ⟨x₀, ψ, hψ, hψx₀, (h.comp hψ.tendsto_atTop).le_liminf hψx₀⟩

/-- The **fundamental theorem of Γ-convergence**, convergence of minimum values: for an
equicoercive Γ-converging sequence, the infima of `F n` converge to the infimum of the Γ-limit. -/
theorem tendsto_iInf (h : TendstoGamma F f) (hc : Equicoercive F) :
    Tendsto (fun n ↦ ⨅ x, F n x) atTop (𝓝 (⨅ x, f x)) := by
  refine tendsto_of_le_liminf_of_limsup_le (le_of_forall_lt fun c hc' ↦ ?_) h.limsup_iInf_le
  by_contra! hle
  -- Below the level `c`, infinitely many `F n` have points of value `< t` for a real `t < c`; a
  -- cluster point of these points has `f`-value at most `t`, below the infimum of `f`.
  obtain ⟨t, hlt, htc⟩ := EReal.lt_iff_exists_real_btwn.1 (hc'.trans_le' hle)
  have hfreq : ∃ᶠ n in atTop, ∃ y, F n y < t :=
    (frequently_lt_of_liminf_lt (by isBoundedDefault) hlt).mono fun _ hn ↦ iInf_lt_iff.1 hn
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
  choose y hy using hφP
  obtain ⟨x₀, ψ, -, -, hx₀⟩ :=
    (h.comp hφ.tendsto_atTop).exists_tendsto_subseq (hc.comp φ) fun k ↦ (hy k).le
  have : f x₀ ≤ t := hx₀.trans <|
    (liminf_le_liminf (Eventually.of_forall fun i ↦ (hy (ψ i)).le)).trans_eq (liminf_const _)
  exact htc.not_ge ((iInf_le f x₀).trans this)

/-- The **fundamental theorem of Γ-convergence**, existence of minimizers: the Γ-limit of an
equicoercive sequence on a nonempty first-countable space attains its infimum. -/
theorem exists_isMinOn [Nonempty X] (h : TendstoGamma F f) (hc : Equicoercive F) :
    ∃ x₀, IsMinOn f univ x₀ := by
  set m := ⨅ x, f x
  rcases eq_or_ne m ⊤ with hm | hm
  · obtain ⟨x₀⟩ := ‹Nonempty X›
    refine ⟨x₀, fun y _ ↦ ?_⟩
    -- Every value of `f` is at least its infimum `⊤`, so `f y = ⊤` and `f x₀ ≤ f y` trivially.
    have hfy : f y = ⊤ := eq_top_iff.2 (hm ▸ iInf_le f y)
    simp [hfy]
  -- Choose levels `c k ↓ m`, points `y k` with `F (φ k) (y k) < c k`, and a cluster point.
  obtain ⟨c, hcanti, hcm, hc_lim⟩ := exists_seq_strictAnti_tendsto' (lt_top_iff_ne_top.2 hm)
  have hev : ∀ k, ∀ᶠ n in atTop, ∃ y, F n y < c k := fun k ↦
    ((h.tendsto_iInf hc).eventually (gt_mem_nhds (hcm k).1)).mono fun _ hn ↦ iInf_lt_iff.1 hn
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually hev
  choose y hy using hφP
  have hc0 : c 0 ≠ ⊤ := (hcm 0).2.ne
  have hc0' : c 0 ≠ ⊥ := (hcm 0).1.ne_bot
  obtain ⟨x₀, ψ, hψ, -, hx₀⟩ := (h.comp hφ.tendsto_atTop).exists_tendsto_subseq (hc.comp φ)
    (t := (c 0).toReal) fun k ↦ by
      rw [EReal.coe_toReal hc0 hc0']
      exact (hy k).le.trans (hcanti.antitone (Nat.zero_le k))
  refine ⟨x₀, fun z _ ↦ le_trans (hx₀.trans ?_) (iInf_le f z)⟩
  calc liminf (fun i ↦ F (φ (ψ i)) (y (ψ i))) atTop ≤ liminf (fun i ↦ c (ψ i)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun i ↦ (hy (ψ i)).le)
    _ = m := (hc_lim.comp hψ.tendsto_atTop).liminf_eq

end TendstoGamma

end TauCeti
