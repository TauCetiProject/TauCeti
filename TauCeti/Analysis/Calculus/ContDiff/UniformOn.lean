/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Uniformly smooth functions on a set

`TauCeti.UniformContDiffOn 𝕜 n G s` says that a function `G : X → Y` between normed spaces has a
chain of derivative families `G', G'', …` up to order `n`, each the derivative at every point of
`s` of the previous one, such that `G` and all these derivatives are uniformly continuous on `s`
and the derivatives of orders `1` to `n` are bounded on `s` (`G` itself need not be bounded). When
`s` is open, `G` is `C^n` on `s` (`UniformContDiffOn.contDiffOn`). The derivatives are carried
along as functions `X → (X →L[𝕜] ⋯ →L[𝕜] Y)` rather than as iterated Fréchet derivatives,
so a proof by induction on `n` applies the case `n` to the derivative of `G`. The domain and the
target lie in the same universe, because the recursion passes to the target `X →L[𝕜] Y`.

This is the regularity needed for superposition operators on bounded continuous functions: the
uniform control is what makes the derivative of `f ↦ G ∘ f` converge at all the points `f t` at
once.

## Main declarations

* `TauCeti.UniformContDiffOn`: the definition, with `TauCeti.uniformContDiffOn_zero_iff` and
  `TauCeti.uniformContDiffOn_succ_iff` unfolding it.
* `TauCeti.UniformContDiffOn.uniformContinuousOn`, `.continuousOn`, `.differentiableOn` and
  `.contDiffOn`: the relation to Mathlib's `ContDiffOn`.
* `TauCeti.UniformContDiffOn.mono` and `TauCeti.UniformContDiffOn.of_le`: shrinking the set and
  lowering the order.
* `ContDiff.uniformContDiffOn`: a `C^n` function is uniformly `C^n` on a compact set.
-/

public section

universe u

open Set

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {X : Type u} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- A function `G : X → Y` is **uniformly `C^n` on `s`** if it is uniformly continuous on `s`, and
for `n + 1` it also has a derivative `G' x` at every point `x` of `s`, bounded on `s`, such that
`G'` is uniformly `C^n` on `s`. -/
def UniformContDiffOn : (n : ℕ) → {Y : Type u} → [NormedAddCommGroup Y] → [NormedSpace 𝕜 Y] →
    (X → Y) → Set X → Prop
  | 0 => fun G s ↦ UniformContinuousOn G s
  | n + 1 => fun G s ↦ UniformContinuousOn G s ∧
    ∃ G' : X → X →L[𝕜] _, (∀ x ∈ s, HasFDerivAt G (G' x) x) ∧
      (∃ C, ∀ x ∈ s, ‖G' x‖ ≤ C) ∧ UniformContDiffOn n G' s

variable {𝕜} {s : Set X} {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y}

/-- Uniform `C^0` regularity is uniform continuity. -/
theorem uniformContDiffOn_zero_iff : UniformContDiffOn 𝕜 0 G s ↔ UniformContinuousOn G s :=
  Iff.rfl

/-- Uniform `C^{n+1}` regularity: uniform continuity, and a derivative that is bounded on `s` and
uniformly `C^n`. -/
theorem uniformContDiffOn_succ_iff {n : ℕ} :
    UniformContDiffOn 𝕜 (n + 1) G s ↔ UniformContinuousOn G s ∧
      ∃ G' : X → X →L[𝕜] Y, (∀ x ∈ s, HasFDerivAt G (G' x) x) ∧ (∃ C, ∀ x ∈ s, ‖G' x‖ ≤ C) ∧
        UniformContDiffOn 𝕜 n G' s :=
  Iff.rfl

/-- Uniform `C^n` regularity on `s` implies it on every subset of `s`. -/
theorem UniformContDiffOn.mono {t : Set X} (hts : t ⊆ s) :
    ∀ {n : ℕ} {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y},
      UniformContDiffOn 𝕜 n G s → UniformContDiffOn 𝕜 n G t := by
  intro n
  induction n with
  | zero => exact fun h ↦ UniformContinuousOn.mono h hts
  | succ n ih =>
    intro Y _ _ G h
    obtain ⟨hu, G', hG', ⟨C, hC⟩, hG'n⟩ := uniformContDiffOn_succ_iff.1 h
    exact uniformContDiffOn_succ_iff.2 ⟨hu.mono hts, G', fun x hx ↦ hG' x (hts hx),
      ⟨C, fun x hx ↦ hC x (hts hx)⟩, ih hG'n⟩

/-- Uniform `C^{n+1}` regularity implies uniform `C^n` regularity. -/
theorem UniformContDiffOn.of_succ :
    ∀ {n : ℕ} {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y},
      UniformContDiffOn 𝕜 (n + 1) G s → UniformContDiffOn 𝕜 n G s := by
  intro n
  induction n with
  | zero => exact fun h ↦ (uniformContDiffOn_succ_iff.1 h).1
  | succ n ih =>
    intro Y _ _ G h
    obtain ⟨hu, G', hG', hC, hG'n⟩ := uniformContDiffOn_succ_iff.1 h
    exact uniformContDiffOn_succ_iff.2 ⟨hu, G', hG', hC, ih hG'n⟩

/-- Uniform `C^n` regularity implies uniform `C^m` regularity for `m ≤ n`. -/
theorem UniformContDiffOn.of_le {m n : ℕ} (hmn : m ≤ n) (h : UniformContDiffOn 𝕜 n G s) :
    UniformContDiffOn 𝕜 m G s := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih h.of_succ

/-- A uniformly `C^n` function is uniformly continuous on `s`. -/
theorem UniformContDiffOn.uniformContinuousOn {n : ℕ} (h : UniformContDiffOn 𝕜 n G s) :
    UniformContinuousOn G s := by
  cases n with
  | zero => exact uniformContDiffOn_zero_iff.1 h
  | succ n => exact (uniformContDiffOn_succ_iff.1 h).1

/-- A uniformly `C^n` function is continuous on `s`. -/
theorem UniformContDiffOn.continuousOn {n : ℕ} (h : UniformContDiffOn 𝕜 n G s) :
    ContinuousOn G s :=
  h.uniformContinuousOn.continuousOn

/-- A uniformly `C^n` function with `1 ≤ n` is differentiable on `s`. -/
theorem UniformContDiffOn.differentiableOn {n : ℕ} (hn : 1 ≤ n) (h : UniformContDiffOn 𝕜 n G s) :
    DifferentiableOn 𝕜 G s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨-, G', hG', -⟩ := uniformContDiffOn_succ_iff.1 h
  exact fun x hx ↦ (hG' x hx).differentiableAt.differentiableWithinAt

/-- On an open set, a uniformly `C^n` function is `C^n`. -/
theorem UniformContDiffOn.contDiffOn (hs : IsOpen s) (n : ℕ) :
    ∀ {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y},
      UniformContDiffOn 𝕜 n G s → ContDiffOn 𝕜 n G s := by
  induction n with
  | zero =>
    intro Y _ _ G h
    exact contDiffOn_zero.2 h.continuousOn
  | succ n ih =>
    intro Y _ _ G h
    obtain ⟨-, G', hG', -, hG'n⟩ := uniformContDiffOn_succ_iff.1 h
    have hder : ∀ x ∈ s, fderiv 𝕜 G x = G' x := fun x hx ↦ (hG' x hx).fderiv
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    exact ⟨h.differentiableOn le_add_self, by simp, (ih hG'n).congr hder⟩

/-- **A smooth function is uniformly smooth on a compact set.** If `G` is `C^n` and `s` is compact,
then `G` is uniformly `C^n` on `s`: every derivative is continuous, hence bounded and uniformly
continuous on `s`. -/
theorem _root_.ContDiff.uniformContDiffOn (hs : IsCompact s) (n : ℕ) :
    ∀ {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y},
      ContDiff 𝕜 n G → UniformContDiffOn 𝕜 n G s := by
  induction n with
  | zero =>
    intro Y _ _ G hG
    exact uniformContDiffOn_zero_iff.2
      (hs.uniformContinuousOn_of_continuous hG.continuous.continuousOn)
  | succ n ih =>
    intro Y _ _ G hG
    have hdiff : Differentiable 𝕜 G := hG.differentiable (by simp)
    have hG' : ContDiff 𝕜 n (fderiv 𝕜 G) := hG.fderiv_right (m := n) (by simp)
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hG'.continuous.continuousOn
    exact uniformContDiffOn_succ_iff.2
      ⟨hs.uniformContinuousOn_of_continuous hG.continuous.continuousOn, fderiv 𝕜 G,
        fun x _ ↦ (hdiff x).hasFDerivAt, ⟨C, hC⟩, ih hG'⟩

end TauCeti
