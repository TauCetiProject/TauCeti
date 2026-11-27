/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Dynamics.Entropy.Equicontinuous
import TauCeti.Dynamics.TopologicalEntropy.Inverse

/-!
# Topological entropy of the time-`t` maps of a continuous flow

For a continuous real flow `ϕ` on a compact uniform space, the topological entropy of the
time-`t` map is proportional to `|t|`:
`coverEntropy (ϕ t) univ = |t| * coverEntropy (ϕ 1) univ`. In particular the entropy of a flow
depends on its time scale: the time change `t ↦ ϕ (c * t)` multiplies it by `c > 0`.

The proof compares Bowen balls at two positive times `s` and `t`. By uniform continuity of
`(u, x) ↦ ϕ u x` on the compact set `[0, s] × X`, every entourage `U` has an entourage `V` such
that `V`-close points stay `U`-close under `ϕ u` for all `u ∈ [0, s]`. Then two points that are
`V`-close along `N` steps of `ϕ s` are `U`-close along the whole flow segment of length `N * s`,
hence along `m` steps of `ϕ t` whenever `m * t ≤ N * s`. Taking `N = ⌈(t / s) * m⌉₊` gives
`coverEntropy (ϕ t) F ≤ (t / s) * coverEntropy (ϕ s) F` for every set `F`; exchanging `s` and `t`
gives equality. Negative times reduce to positive ones through the inverse homeomorphism, and
time `0` is the identity, of entropy `0`.

## Main results

* `TauCeti.flow_iterate`: `(ϕ s)^[k] = ϕ (k * s)`.
* `TauCeti.exists_mem_uniformity_forall_mem_Icc_flow_mem`: uniform equicontinuity of the time-`u`
  maps for `u` in a compact interval `[0, s]`.
* `TauCeti.dynEntourage_flow_subset`: the comparison of dynamical entourages of `ϕ s` and `ϕ t`.
* `TauCeti.coverEntropy_flow_le`, `TauCeti.coverEntropyInf_flow_le`: for `0 < s` and `0 < t`, the
  entropy of `ϕ t` on any set is at most `t / s` times that of `ϕ s`.
* `TauCeti.coverEntropy_flow_eq_div_mul`, `TauCeti.coverEntropyInf_flow_eq_div_mul`: equality.
* `TauCeti.coverEntropy_flow_of_pos`: `coverEntropy (ϕ t) F = t * coverEntropy (ϕ 1) F` for
  `t > 0`.
* `TauCeti.coverEntropy_flow_univ`: `coverEntropy (ϕ t) univ = |t| * coverEntropy (ϕ 1) univ` for
  every real `t`, on a nonempty compact space.

This is item 2 of §5.5 of the ClassicalErgodicTheory roadmap.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth Topology
open scoped Uniformity

variable {X : Type*}

section Iterate

variable [TopologicalSpace X]

/-- The iterates of a time-`s` map of a real flow are its time-`k * s` maps. -/
theorem flow_iterate (ϕ : Flow ℝ X) (s : ℝ) (k : ℕ) : (ϕ s)^[k] = ϕ (k * s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply', ih, ← ϕ.map_add]
    congr 1
    push_cast
    ring

/-- The time-`t` map of a real flow at a negative time `t` is the inverse of the time-`(-t)`
homeomorphism. -/
theorem flow_eq_toHomeomorph_symm (ϕ : Flow ℝ X) (t : ℝ) :
    ϕ t = ⇑(ϕ.toHomeomorph (-t)).symm := by
  funext x
  simp

end Iterate

section Comparison

variable [TopologicalSpace X]

/-- If `V`-close points stay `U`-close under `ϕ u` for `u ∈ [0, s]`, then points `V`-close along
`N` steps of `ϕ s` are `U`-close along `m` steps of `ϕ t` whenever `m * t ≤ N * s`. -/
theorem dynEntourage_flow_subset (ϕ : Flow ℝ X) {s t : ℝ} (ht : 0 < t) {U V : SetRel X X}
    (hV : ∀ x y, (x, y) ∈ V → ∀ u ∈ Icc 0 s, (ϕ u x, ϕ u y) ∈ U) {m N : ℕ}
    (hmN : m * t ≤ N * s) :
    dynEntourage (ϕ s) V N ⊆ dynEntourage (ϕ t) U m := by
  rintro ⟨x, y⟩ hxy
  rw [mem_dynEntourage] at hxy ⊢
  intro j hj
  have hjt : (j : ℝ) * t < N * s :=
    (mul_lt_mul_of_pos_right (by exact_mod_cast hj) ht).trans_le hmN
  have hs : 0 < s :=
    pos_of_mul_pos_right ((by positivity : (0 : ℝ) ≤ j * t).trans_lt hjt) N.cast_nonneg
  have hjt₀ : 0 ≤ (j : ℝ) * t / s := by positivity
  set k := ⌊(j : ℝ) * t / s⌋₊
  have hkN : k < N := (Nat.floor_lt hjt₀).2 ((div_lt_iff₀ hs).2 hjt)
  have hks : (k : ℝ) * s ≤ j * t := (le_div_iff₀ hs).1 (Nat.floor_le hjt₀)
  have hks' : (j : ℝ) * t < (k + 1) * s := (div_lt_iff₀ hs).1 (Nat.lt_floor_add_one _)
  have hu : (j : ℝ) * t - k * s ∈ Icc 0 s := ⟨by linarith, by linarith⟩
  have key : ∀ z, (ϕ t)^[j] z = ϕ (j * t - k * s) ((ϕ s)^[k] z) := by
    intro z
    rw [flow_iterate, flow_iterate, ← ϕ.map_add]
    congr 1
    ring
  rw [key, key]
  exact hV _ _ (hxy k hkN) _ hu

/-- Minimal covers for `ϕ t` at `m` steps are no larger than those for `ϕ s` at `N` steps, under
the hypotheses of `dynEntourage_flow_subset`. -/
theorem coverMincard_flow_le (ϕ : Flow ℝ X) {s t : ℝ} (ht : 0 < t) {U V : SetRel X X}
    (hV : ∀ x y, (x, y) ∈ V → ∀ u ∈ Icc 0 s, (ϕ u x, ϕ u y) ∈ U) (F : Set X) {m N : ℕ}
    (hmN : m * t ≤ N * s) :
    coverMincard (ϕ t) F U m ≤ coverMincard (ϕ s) F V N :=
  biInf_mono fun _ h ↦ h.mono_entourage (dynEntourage_flow_subset ϕ ht hV hmN)

/-- The step counts `⌈(t / s) * m⌉₊` grow at the linear rate `t / s`. -/
private theorem tendsto_natCeil_div (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ ((⌈a * n⌉₊ : ℕ) : EReal) / n) atTop (𝓝 (a : EReal)) := by
  have h := ((continuous_coe_real_ereal.tendsto a).comp
    ((tendsto_nat_ceil_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop))
  refine h.congr fun n ↦ ?_
  simp [Function.comp_def, EReal.coe_div]

private theorem le_natCeil_mul {s t : ℝ} (hs : 0 < s) (m : ℕ) :
    (m : ℝ) * t ≤ ⌈t / s * m⌉₊ * s := by
  have := Nat.le_ceil (t / s * m)
  calc (m : ℝ) * t = t / s * m * s := by field_simp
    _ ≤ ⌈t / s * m⌉₊ * s := mul_le_mul_of_nonneg_right this hs.le

/-- The entourage-level `limsup` comparison between `ϕ t` and `ϕ s`. -/
theorem coverEntropyEntourage_flow_le (ϕ : Flow ℝ X) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) {U V : SetRel X X}
    (hV : ∀ x y, (x, y) ∈ V → ∀ u ∈ Icc 0 s, (ϕ u x, ϕ u y) ∈ U) (F : Set X) :
    coverEntropyEntourage (ϕ t) F U ≤ ((t / s : ℝ) : EReal) * coverEntropyEntourage (ϕ s) F V := by
  have hts : (0 : ℝ) < t / s := div_pos ht hs
  calc coverEntropyEntourage (ϕ t) F U
      ≤ expGrowthSup ((fun N : ℕ ↦ (coverMincard (ϕ s) F V N : ENNReal)) ∘
          fun m : ℕ ↦ ⌈t / s * m⌉₊) :=
        expGrowthSup_monotone fun m ↦ ENat.toENNReal_mono
          (coverMincard_flow_le ϕ ht hV F (le_natCeil_mul hs m))
    _ = ((t / s : ℝ) : EReal) * coverEntropyEntourage (ϕ s) F V :=
        Monotone.expGrowthSup_comp
          (fun _ _ h ↦ ENat.toENNReal_mono (coverMincard_monotone_time _ F V h))
          (tendsto_natCeil_div _ hts.le) (EReal.coe_ne_zero.2 hts.ne') (EReal.coe_ne_top _)

/-- The entourage-level `liminf` comparison between `ϕ t` and `ϕ s`. -/
theorem coverEntropyInfEntourage_flow_le (ϕ : Flow ℝ X) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) {U V : SetRel X X}
    (hV : ∀ x y, (x, y) ∈ V → ∀ u ∈ Icc 0 s, (ϕ u x, ϕ u y) ∈ U) (F : Set X) :
    coverEntropyInfEntourage (ϕ t) F U ≤
      ((t / s : ℝ) : EReal) * coverEntropyInfEntourage (ϕ s) F V := by
  have hts : (0 : ℝ) < t / s := div_pos ht hs
  calc coverEntropyInfEntourage (ϕ t) F U
      ≤ expGrowthInf ((fun N : ℕ ↦ (coverMincard (ϕ s) F V N : ENNReal)) ∘
          fun m : ℕ ↦ ⌈t / s * m⌉₊) :=
        expGrowthInf_monotone fun m ↦ ENat.toENNReal_mono
          (coverMincard_flow_le ϕ ht hV F (le_natCeil_mul hs m))
    _ = ((t / s : ℝ) : EReal) * coverEntropyInfEntourage (ϕ s) F V :=
        Monotone.expGrowthInf_comp
          (fun _ _ h ↦ ENat.toENNReal_mono (coverMincard_monotone_time _ F V h))
          (tendsto_natCeil_div _ hts.le) (EReal.coe_ne_zero.2 hts.ne') (EReal.coe_ne_top _)

end Comparison

section Compact

variable [UniformSpace X] [CompactSpace X] (ϕ : Flow ℝ X)

/-- On a compact uniform space, the time-`u` maps of a real flow for `u` in a compact interval
`[0, s]` are uniformly equicontinuous: every entourage `U` has an entourage `V` whose pairs stay in
`U` under all of them. -/
theorem exists_mem_uniformity_forall_mem_Icc_flow_mem (s : ℝ)
    {U : SetRel X X} (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, ∀ x y, (x, y) ∈ V → ∀ u ∈ Icc 0 s, (ϕ u x, ϕ u y) ∈ U := by
  have hK : IsCompact (Icc (0 : ℝ) s ×ˢ (univ : Set X)) := isCompact_Icc.prod isCompact_univ
  have hc := hK.uniformContinuousOn_of_continuous ϕ.cont'.continuousOn
  have h := hc hU
  rw [mem_map, mem_inf_principal, uniformity_prod_eq_prod, mem_map, mem_prod_iff] at h
  obtain ⟨A, hA, B, hB, hAB⟩ := h
  refine ⟨B, hB, fun x y hxy u hu ↦ ?_⟩
  exact hAB (mk_mem_prod (refl_mem_uniformity hA) hxy) ⟨⟨hu, mem_univ x⟩, ⟨hu, mem_univ y⟩⟩

/-- For a continuous flow on a compact uniform space and `0 < s`, `0 < t`, the topological entropy
of `ϕ t` on any set is at most `t / s` times that of `ϕ s`. -/
theorem coverEntropy_flow_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (F : Set X) :
    coverEntropy (ϕ t) F ≤ ((t / s : ℝ) : EReal) * coverEntropy (ϕ s) F := by
  refine iSup₂_le fun U hU ↦ ?_
  obtain ⟨V, hV, hVU⟩ := exists_mem_uniformity_forall_mem_Icc_flow_mem ϕ s hU
  exact (coverEntropyEntourage_flow_le ϕ hs ht hVU F).trans <|
    mul_le_mul_of_nonneg_left (coverEntropyEntourage_le_coverEntropy _ F hV)
      (EReal.coe_nonneg.2 (div_pos ht hs).le)

/-- For a continuous flow on a compact uniform space and `0 < s`, `0 < t`, the `liminf`
topological entropy of `ϕ t` on any set is at most `t / s` times that of `ϕ s`. -/
theorem coverEntropyInf_flow_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (F : Set X) :
    coverEntropyInf (ϕ t) F ≤ ((t / s : ℝ) : EReal) * coverEntropyInf (ϕ s) F := by
  refine iSup₂_le fun U hU ↦ ?_
  obtain ⟨V, hV, hVU⟩ := exists_mem_uniformity_forall_mem_Icc_flow_mem ϕ s hU
  exact (coverEntropyInfEntourage_flow_le ϕ hs ht hVU F).trans <|
    mul_le_mul_of_nonneg_left (coverEntropyInfEntourage_le_coverEntropyInf _ F hV)
      (EReal.coe_nonneg.2 (div_pos ht hs).le)

/-- Reverse a comparison `b ≤ (s / t) * a` into `(t / s) * b ≤ a`, for positive reals `s`, `t`. -/
private theorem div_mul_le_of_le_div_mul {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {a b : EReal}
    (h : b ≤ ((s / t : ℝ) : EReal) * a) : ((t / s : ℝ) : EReal) * b ≤ a := by
  calc ((t / s : ℝ) : EReal) * b ≤ ((t / s : ℝ) : EReal) * (((s / t : ℝ) : EReal) * a) :=
        mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 (div_pos ht hs).le)
    _ = a := by
        rw [← mul_assoc, ← EReal.coe_mul, div_mul_div_cancel₀ hs.ne', div_self ht.ne',
          EReal.coe_one, one_mul]

/-- For a continuous flow on a compact uniform space and `0 < s`, `0 < t`, the topological entropy
of `ϕ t` on any set is `t / s` times that of `ϕ s`. -/
theorem coverEntropy_flow_eq_div_mul {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (F : Set X) :
    coverEntropy (ϕ t) F = ((t / s : ℝ) : EReal) * coverEntropy (ϕ s) F :=
  (coverEntropy_flow_le ϕ hs ht F).antisymm
    (div_mul_le_of_le_div_mul hs ht (coverEntropy_flow_le ϕ ht hs F))

/-- For a continuous flow on a compact uniform space and `0 < s`, `0 < t`, the `liminf`
topological entropy of `ϕ t` on any set is `t / s` times that of `ϕ s`. -/
theorem coverEntropyInf_flow_eq_div_mul {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (F : Set X) :
    coverEntropyInf (ϕ t) F = ((t / s : ℝ) : EReal) * coverEntropyInf (ϕ s) F :=
  (coverEntropyInf_flow_le ϕ hs ht F).antisymm
    (div_mul_le_of_le_div_mul hs ht (coverEntropyInf_flow_le ϕ ht hs F))

/-- For a continuous flow on a compact uniform space and `t > 0`, the topological entropy of the
time-`t` map on any set is `t` times that of the time-`1` map. -/
theorem coverEntropy_flow_of_pos {t : ℝ} (ht : 0 < t) (F : Set X) :
    coverEntropy (ϕ t) F = t * coverEntropy (ϕ 1) F := by
  simpa using coverEntropy_flow_eq_div_mul ϕ one_pos ht F

/-- For a continuous flow on a compact uniform space and `t > 0`, the `liminf` topological entropy
of the time-`t` map on any set is `t` times that of the time-`1` map. -/
theorem coverEntropyInf_flow_of_pos {t : ℝ} (ht : 0 < t) (F : Set X) :
    coverEntropyInf (ϕ t) F = t * coverEntropyInf (ϕ 1) F := by
  simpa using coverEntropyInf_flow_eq_div_mul ϕ one_pos ht F

/-- For a continuous flow on a nonempty compact uniform space, the topological entropy of the
time-`t` map is `|t|` times that of the time-`1` map, for every real `t`. -/
theorem coverEntropy_flow_univ [Nonempty X] (t : ℝ) :
    coverEntropy (ϕ t) univ = |t| * coverEntropy (ϕ 1) univ := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [abs_of_neg ht, ← coverEntropy_flow_of_pos ϕ (neg_pos.2 ht) univ,
      flow_eq_toHomeomorph_symm ϕ t, Homeomorph.coverEntropy_symm_univ]
    rfl
  · rw [Flow.map_zero, abs_zero, EReal.coe_zero, zero_mul]
    exact coverEntropy_id_eq_zero isCompact_univ.totallyBounded univ_nonempty
  · rw [abs_of_pos ht]
    exact coverEntropy_flow_of_pos ϕ ht univ

end Compact

end TauCeti
