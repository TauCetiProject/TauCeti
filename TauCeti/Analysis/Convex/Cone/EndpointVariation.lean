/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Convex.Cone.Basic

/-!
# Endpoint variations of a curve inside a cone

Let `γ : ℝ → E` be a curve in a real normed space and `σ : ℝ → E` a curve with `σ 0 = γ a`. The
family

`G s t = γ t + ((b - t) / (b - a)) • (σ s - σ 0)`

is a variation of `γ` whose curves start at `σ s` and end at `γ b`, and it is `C^n` along
`{0} × [a, b]` when `γ` and `σ` are `C^n`. Every point of `G s` is a point of `γ` translated by a
nonnegative multiple of the endpoint displacement `σ s - σ 0`. Hence if `γ` lies in a set `S` which
is stable under translation by the vectors of a convex cone `C`, and `σ s - σ 0 ∈ C`, then `G s`
lies in `S` as well. If `γ` lies in an open set `V`, so does `G s` for `s` close to `0`, by
compactness of `[a, b]`.

The two cases of interest are a translated convex cone `{y | y - σ 0 ∈ C}` and a halfspace
`{y | 0 ≤ L y}`: they describe, in a chart, a domain near a corner or near a smooth boundary
point. The resulting variations are the competitors of a curve that is constrained to such a
domain and whose initial point moves along a curve in the domain, for instance in the first
variation of length with a moving endpoint. The displacement condition is imposed only along a
filter `l ≤ 𝓝 0`, such as `𝓝[≥] 0`, for an endpoint curve that enters the cone in one direction
only.

## Main results

* `TauCeti.exists_contDiffAt_endpointVariation_of_add_mem`: the general statement, for a set `S`
  stable under translation by a convex cone `C`.
* `TauCeti.exists_contDiffAt_coneEndpointVariation`: the case of a translated convex cone.
* `TauCeti.exists_contDiffAt_halfspaceEndpointVariation`: the case of a halfspace.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞} {l : Filter ℝ}
  {γ σ : ℝ → E} {a b : ℝ} {V : Set E}

/-- **Endpoint variations inside a set stable under a cone.** Let `S` be stable under
translation by the vectors of a convex cone `C`, let `γ` be `C^n` on `[a, b]` with values in
`S ∩ V`, where `V` is open, and let `σ` be `C^n` at `0` with `σ 0 = γ a`. If `σ s - σ 0 ∈ C` for
`s` along a filter `l ≤ 𝓝 0`, there is a variation `G` of `γ`, `C^n` along `{0} × [a, b]`, such
that `G s` starts at `σ s` and ends at `γ b` for every `s`, and maps `[a, b]` into `S ∩ V` for `s`
along `l`. -/
theorem exists_contDiffAt_endpointVariation_of_add_mem (hl : l ≤ 𝓝 0) (hab : a < b) {S : Set E}
    {C : ConvexCone ℝ E} (hS : ∀ x ∈ S, ∀ v ∈ C, x + v ∈ S) (hV : IsOpen V)
    (hγ : ∀ t ∈ Icc a b, ContDiffAt ℝ n γ t) (hσ : ContDiffAt ℝ n σ 0) (hγσ : γ a = σ 0)
    (hγSV : MapsTo γ (Icc a b) (S ∩ V)) (hσC : ∀ᶠ s in l, σ s - σ 0 ∈ C) :
    ∃ G : ℝ → ℝ → E, G 0 = γ ∧
      (∀ t ∈ Icc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ s, G s a = σ s) ∧ (∀ s, G s b = γ b) ∧
      ∀ᶠ s in l, MapsTo (G s) (Icc a b) (S ∩ V) := by
  let G : ℝ → ℝ → E := fun s t ↦ γ t + ((b - t) / (b - a)) • (σ s - σ 0)
  have hzero : G 0 = γ := by
    funext t
    simp [G]
  have hG : ∀ t ∈ Icc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t) := fun t ht ↦
    ((hγ t ht).comp (0, t) contDiffAt_snd).add
      (((contDiffAt_const.sub contDiffAt_snd).div_const (b - a)).smul
        ((hσ.comp (0, t) contDiffAt_fst).sub contDiffAt_const))
  have hGV : ∀ᶠ s in 𝓝 0, ∀ t ∈ Icc a b, G s t ∈ V :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦
      (hG t ht).continuousAt.preimage_mem_nhds
        (hV.mem_nhds (by simpa only [hzero] using (hγSV ht).2))
  refine ⟨G, hzero, hG, fun s ↦ ?_, fun s ↦ by simp [G], ?_⟩
  · simp only [G, div_self (sub_ne_zero.2 hab.ne'), one_smul, hγσ, add_sub_cancel]
  · filter_upwards [hl hGV, hσC] with s hsV hsC t ht
    refine ⟨?_, hsV t ht⟩
    rcases ht.2.eq_or_lt with rfl | htb
    · simpa [G] using (hγSV ht).1
    · exact hS _ (hγSV ht).1 _ (C.smul_mem (div_pos (sub_pos.2 htb) (sub_pos.2 hab)) hsC)

/-- **Endpoint variations inside a translated convex cone.** A `C^n` curve `γ` on `[a, b]` with
values in `{y | y - σ 0 ∈ C} ∩ V`, where `C` is a convex cone and `V` is open, has a variation
`G`, `C^n` along `{0} × [a, b]`, whose curves start at `σ s` and end at `γ b`, and stay in
`{y | y - σ 0 ∈ C} ∩ V` for `s` along any filter `l ≤ 𝓝 0` on which `σ s - σ 0 ∈ C`. -/
theorem exists_contDiffAt_coneEndpointVariation (hl : l ≤ 𝓝 0) (hab : a < b)
    {C : ConvexCone ℝ E} (hV : IsOpen V) (hγ : ∀ t ∈ Icc a b, ContDiffAt ℝ n γ t)
    (hσ : ContDiffAt ℝ n σ 0) (hγσ : γ a = σ 0)
    (hγCV : MapsTo γ (Icc a b) ({y | y - σ 0 ∈ C} ∩ V)) (hσC : ∀ᶠ s in l, σ s - σ 0 ∈ C) :
    ∃ G : ℝ → ℝ → E, G 0 = γ ∧
      (∀ t ∈ Icc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ s, G s a = σ s) ∧ (∀ s, G s b = γ b) ∧
      ∀ᶠ s in l, MapsTo (G s) (Icc a b) ({y | y - σ 0 ∈ C} ∩ V) :=
  exists_contDiffAt_endpointVariation_of_add_mem hl hab
    (fun x hx v hv ↦ by simpa only [mem_ofPred_eq, add_sub_right_comm] using C.add_mem hx hv)
    hV hγ hσ hγσ hγCV hσC

/-- **Endpoint variations inside a halfspace.** A `C^n` curve `γ` on `[a, b]` with values
in `{y | 0 ≤ L y} ∩ V`, where `L` is a linear functional and `V` is open, has a variation `G`,
`C^n` along `{0} × [a, b]`, whose curves start at `σ s` and end at `γ b`, and stay in
`{y | 0 ≤ L y} ∩ V` for `s` along any filter `l ≤ 𝓝 0` on which `L (σ 0) ≤ L (σ s)`. This
includes an endpoint curve `σ` moving in a level set of `L`. -/
theorem exists_contDiffAt_halfspaceEndpointVariation (hl : l ≤ 𝓝 0) (hab : a < b)
    (L : E →ₗ[ℝ] ℝ) (hV : IsOpen V) (hγ : ∀ t ∈ Icc a b, ContDiffAt ℝ n γ t)
    (hσ : ContDiffAt ℝ n σ 0) (hγσ : γ a = σ 0)
    (hγLV : MapsTo γ (Icc a b) ({y | 0 ≤ L y} ∩ V)) (hσL : ∀ᶠ s in l, L (σ 0) ≤ L (σ s)) :
    ∃ G : ℝ → ℝ → E, G 0 = γ ∧
      (∀ t ∈ Icc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ s, G s a = σ s) ∧ (∀ s, G s b = γ b) ∧
      ∀ᶠ s in l, MapsTo (G s) (Icc a b) ({y | 0 ≤ L y} ∩ V) :=
  exists_contDiffAt_endpointVariation_of_add_mem hl hab
    (C := (ConvexCone.positive ℝ ℝ).comap L)
    (fun x hx v hv ↦ by
      simp only [mem_ofPred_eq, ConvexCone.mem_comap, ConvexCone.mem_positive] at hx hv ⊢
      rw [map_add]
      exact add_nonneg hx hv)
    hV hγ hσ hγσ hγLV (hσL.mono fun s hs ↦ by simpa [sub_nonneg] using hs)

end TauCeti
