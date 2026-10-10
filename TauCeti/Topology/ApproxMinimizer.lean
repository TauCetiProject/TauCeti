/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Stability of minimizers under approximate minimization

If a sequence `z k` lives in a compact set and each `z k` *approximately*
minimizes a continuous real function `F` — for every point `x`, `F (z k) ≤
F x + ε x k` with `ε x k → 0` — then a subsequence of `z k` converges to a
genuine global minimizer of `F`.

This is the elementary "recovery" half of the fundamental theorem of
Γ-convergence: a perturbed family of variational problems whose minimizers stay
in a fixed compact set has a limit point that solves the unperturbed problem.
The typical source of the approximate-minimizer hypothesis is a second family
`F k` with `z k ∈ argmin (F k)` and `F k → F` in a suitable uniform sense.

## Main results

* `TauCeti.exists_subseq_tendsto_forall_le_of_approxMin`
* `TauCeti.exists_subseq_tendsto_isMinOn_of_approxMinOn` — the variant where the
  approximate-minimization comparison ranges only over the compact set `K`, so the
  limit is a minimizer *on `K`* (`IsMinOn F K`) rather than a global one. This is
  the form the Berge maximum theorem consumes (the feasible set is constrained).

## Staging note

Staged for Tau Ceti, roadmap topic T22.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Topology/Order/Compact.lean` (companion
to `IsCompact.exists_isMinOn`), or a dedicated file alongside
`Mathlib/Topology/Sequences.lean`.
Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `72b913b`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/Topology/Order/Compact.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (rule 2 of
  `scripts/check_dependency_layers.py`); this module imports Mathlib only.
-/

public section

/-!
### Provenance

Moved from the retired `ForMathlib` staging tree into `ForTauCeti/Topology/`.
`ForMathlib` to `TauCeti` to match the destination package; declaration names,
statements and proofs are unchanged.

**FM-RETIRE was worked twice, and the two versions disagreed on the namespace.**
The reconciliation — why `TauCeti` won over `main`'s `ForMathlib`, and which pins
were updated to match — is recorded once, in `ForTauCeti/Topology/Berge.lean`.
-/

namespace TauCeti

open Filter Topology

/--
**Stability of minimizers under approximate minimization.**

Let `K` be a compact subset of a first-countable topological space, `F : X → ℝ`
continuous, and `z : ℕ → X` a sequence in `K` such that each `z k` approximately
minimizes `F`: for every `x`, `F (z k) ≤ F x + ε x k`, where `ε x k → 0` as
`k → ∞` (the error may depend on the comparison point `x`). Then there is a
strictly monotone `φ` and a point `ψ ∈ K` with `z ∘ φ → ψ` and `ψ` a global
minimizer of `F` (`∀ x, F ψ ≤ F x`).
-/
theorem exists_subseq_tendsto_forall_le_of_approxMin
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, (∀ x, F ψ ≤ F x) ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  obtain ⟨ψ, hψK, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq hz
  refine ⟨φ, hφ_mono, ψ, hψK, ?_, hφ_tendsto⟩
  intro x
  -- `F (z (φ t)) → F ψ` by continuity of `F`.
  have hcont : Tendsto (fun t => F (z (φ t))) atTop (𝓝 (F ψ)) :=
    (hF.tendsto ψ).comp hφ_tendsto
  -- `F x + ε x (φ t) → F x` since the (subsequenced) error vanishes.
  have hrhs : Tendsto (fun t => F x + ε x (φ t)) atTop (𝓝 (F x)) := by
    have hεφ : Tendsto (fun t => ε x (φ t)) atTop (𝓝 0) :=
      (hε x).comp hφ_mono.tendsto_atTop
    simpa using tendsto_const_nhds.add hεφ
  -- Pass the pointwise bound to the limit.
  exact le_of_tendsto_of_tendsto hcont hrhs
    (Eventually.of_forall fun t => happrox x (φ t))

/--
**Stability of constrained minimizers under approximate minimization.**

The constrained variant of `exists_subseq_tendsto_forall_le_of_approxMin`: the
approximate-minimization bound is only required to hold for comparison points `x`
*in the compact set* `K` (`F (z k) ≤ F x + ε x k` for `x ∈ K`), and the limit
point `ψ` is correspondingly a minimizer of `F` *on `K`* (`IsMinOn F K ψ`) rather
than a global minimizer.  This is the form consumed by the Berge maximum theorem,
where the feasible set is the fixed compact `K`.
-/
theorem exists_subseq_tendsto_isMinOn_of_approxMinOn
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x ∈ K, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x ∈ K, ∀ k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, IsMinOn F K ψ ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  obtain ⟨ψ, hψK, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq hz
  refine ⟨φ, hφ_mono, ψ, hψK, ?_, hφ_tendsto⟩
  rw [isMinOn_iff]
  intro x hx
  -- `F (z (φ t)) → F ψ` by continuity of `F`.
  have hcont : Tendsto (fun t => F (z (φ t))) atTop (𝓝 (F ψ)) :=
    (hF.tendsto ψ).comp hφ_tendsto
  -- `F x + ε x (φ t) → F x` since the (subsequenced) error vanishes.
  have hrhs : Tendsto (fun t => F x + ε x (φ t)) atTop (𝓝 (F x)) := by
    have hεφ : Tendsto (fun t => ε x (φ t)) atTop (𝓝 0) :=
      (hε x hx).comp hφ_mono.tendsto_atTop
    simpa using tendsto_const_nhds.add hεφ
  -- Pass the pointwise bound (valid for `x ∈ K`) to the limit.
  exact le_of_tendsto_of_tendsto hcont hrhs
    (Eventually.of_forall fun t => happrox x hx (φ t))

end TauCeti
