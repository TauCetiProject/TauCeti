/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Topology.Order.Compact
import TauCeti.Dynamics.Flow.Basic
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Topology.Neighborhoods

/-!
# Lusternik–Schnirelmann bounds for flows with a Lyapunov function

Let `ϕ` be a flow of `ℝ` on a compact space `α`, and let `W : α → ℝ` be a continuous
**Lyapunov function** which strictly decreases along every nonconstant orbit:
`W (ϕ t x) < W x` whenever `t > 0` and `ϕ t x ≠ x`. The rest points of `ϕ` are the points `x` with
`ϕ t x = x` for all `t`. This file bounds their number from below by any **index** of `α` adapted
to the flow, in the sense of Lusternik and Schnirelmann: a function `ν : Set α → ℕ∞` which

* is monotone and vanishes on `∅`,
* is subadditive, `ν (A ∪ B) ≤ ν A + ν B`,
* does not increase under the flow, `ν (ϕ t ⁻¹' A) ≤ ν A` for `t ≥ 0`,
* is at most `1` on some neighbourhood of each rest point.

Then `ν univ` is at most the number of rest points (`Flow.index_univ_le_encard`), and more
precisely, for every level `b`, the index of the sublevel `{W ≤ b}` is at most the number of rest
points in it (`Flow.index_sublevel_le_encard`). An infinite set of rest points has count `⊤`.

The standard example is the Lusternik–Schnirelmann count of categorical open covers on a locally
contractible space, which gives `Flow.lsCategoryCount_univ_le_encard` and the cup-length bound
`Flow.lsCupLength_add_one_le_encard` for singular cohomology, in
`TauCeti.Topology.Homotopy.LusternikSchnirelmann.Flow`. The axioms above do not mention local
contractibility, so the bound also applies to indices, such as a Čech-cohomological index, on
compact spaces which are not locally contractible.

The proof is the Lusternik–Schnirelmann minimax argument, with the deformation lemma supplied by
the flow and compactness (`Flow.exists_pos_forall_apply_le_sub`): given a level `c` and an open set
`U` containing the rest points on that level, there are `ε > 0` and `T ≥ 0` such that the time-`T`
map of the flow carries every point of `{W ≤ c + ε}` outside `U` into `{W ≤ c - ε}`. Otherwise a
cluster point of counterexamples for `ε → 0`, `T → ∞` would be a point outside `U` on whose forward
orbit `W` stays equal to `c`, hence a rest point on the level `c`. So crossing a level `c` costs at
most the index of `U`, which is at most the number of rest points on the level. No metric,
separation axiom, local contractibility or smoothness is used.

## Main results

* `Flow.exists_pos_forall_apply_le_sub`: the deformation lemma across a level.
* `Flow.index_sublevel_le_encard`: the index of a sublevel is at most the number of rest points in
  it.
* `Flow.index_univ_le_encard`: the index of the space is at most the number of rest points.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49, the cup-length estimate for flows with a Lyapunov
  function.
* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, AMS, 2003, Chapter 1.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α} {W : α → ℝ}

/-- **The deformation lemma.** Let `W` be a continuous function on a compact space which strictly
decreases along every nonconstant orbit of the flow `ϕ`, and let `U` be an open set containing
every rest point on the level `W = c`. Then for some `ε > 0` and `T ≥ 0` the time-`T` map of the
flow carries every point of the sublevel `{W ≤ c + ε}` outside `U` into the sublevel
`{W ≤ c - ε}`. -/
theorem exists_pos_forall_apply_le_sub [CompactSpace α] (hWc : Continuous W)
    (hW : ∀ x t, 0 < t → ϕ t x ≠ x → W (ϕ t x) < W x) (c : ℝ) {U : Set α} (hU : IsOpen U)
    (hcU : ∀ x, (∀ t, ϕ t x = x) → W x = c → x ∈ U) :
    ∃ ε > 0, ∃ T, 0 ≤ T ∧ ∀ x, W x ≤ c + ε → x ∉ U → W (ϕ T x) ≤ c - ε := by
  by_contra! h
  -- Counterexamples `x n` for `ε = 1 / (n + 1)` and `T = n`, and a cluster point `y` of them.
  choose x hx using fun n : ℕ ↦ h (1 / (n + 1)) Nat.one_div_pos_of_nat n n.cast_nonneg
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace (map x atTop)
  have hy : MapClusterPt y atTop x := mapClusterPt_def.2 hy
  -- Eventually `1 / (n + 1)` is below any given `δ > 0`.
  have hsmall {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ := by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (Nat.one_div_le_one_div hn).trans hN.le
  have hyU : y ∉ U :=
    hU.isClosed_compl.mem_of_mapClusterPt hy (Eventually.of_forall fun n ↦ (hx n).2.1)
  -- `W y ≤ c`, as a limit of the values `W (x n) ≤ c + 1 / (n + 1)`.
  have hyc : W y ≤ c := le_of_forall_pos_le_add fun δ hδ ↦
    (isClosed_le hWc continuous_const).mem_of_mapClusterPt hy <| by
      filter_upwards [hsmall hδ] with n hn
      exact (hx n).1.trans (by linarith)
  -- `c ≤ W (ϕ t y)` for every `t`, since `W (ϕ t (x n)) ≥ W (ϕ n (x n)) > c - 1 / (n + 1)` for
  -- `n ≥ t`.
  have hcy (t : ℝ) : c ≤ W (ϕ t y) := le_of_forall_sub_le fun δ hδ ↦
    (isClosed_le continuous_const (hWc.comp (ϕ.continuous_toFun t))).mem_of_mapClusterPt hy <| by
      filter_upwards [hsmall hδ, eventually_ge_atTop ⌈t⌉₊] with n hn hnt
      have htn : t ≤ n := (Nat.le_ceil t).trans (Nat.cast_le.2 hnt)
      exact (by linarith [(hx n).2.2] : c - δ ≤ W (ϕ n (x n))).trans
        (antitone_apply_of_lt hW (x n) htn)
  -- So `W` is constant along the forward orbit of `y`, which is therefore a rest point on the
  -- level `c`, inside `U`.
  have hrest : ∀ t, ϕ t y = y := apply_eq_self_of_forall_pos fun t ht ↦ by
    by_contra hne
    linarith [hW y t ht hne, hcy t]
  have hWy : W y = c := le_antisymm hyc (by simpa [hrest 1] using hcy 1)
  exact hyU (hcU y hrest hWy)

section Index

variable {ν : Set α → ℕ∞}

/-- **The Lusternik–Schnirelmann bound on sublevels.** Let `W` be a continuous function on a
compact space which strictly decreases along every nonconstant orbit of the flow `ϕ`, and let `ν`
be an index on `α`: monotone, zero on `∅`, subadditive, not increased by the flow in forward time,
and at most `1` on some neighbourhood of each rest point. Then for every level `b` the index of the
sublevel `{W ≤ b}` is at most the number of rest points in it. -/
theorem index_sublevel_le_encard [CompactSpace α] (hWc : Continuous W)
    (hW : ∀ x t, 0 < t → ϕ t x ≠ x → W (ϕ t x) < W x) (hmono : Monotone ν) (hempty : ν ∅ = 0)
    (hunion : ∀ A B, ν (A ∪ B) ≤ ν A + ν B) (hflow : ∀ t, 0 ≤ t → ∀ A, ν (ϕ t ⁻¹' A) ≤ ν A)
    (hloc : ∀ x, (∀ t, ϕ t x = x) → ∃ V ∈ 𝓝 x, ν V ≤ 1) (b : ℝ) :
    ν {x | W x ≤ b} ≤ {x | (∀ t, ϕ t x = x) ∧ W x ≤ b}.encard := by
  -- Write `g a` for the index of `{W ≤ a}` and `h a` for the number of rest points in it.
  set g : ℝ → ℕ∞ := fun a ↦ ν {x | W x ≤ a} with hg
  set h : ℝ → ℕ∞ := fun a ↦ {x | (∀ t, ϕ t x = x) ∧ W x ≤ a}.encard
  -- `set` abstracts only the lambdas, not their beta-reduced applications at `b` in the goal, so
  -- fold those applications by hand.
  change g b ≤ h b
  -- The set `F` of levels `a ≤ b` at which the bound fails is bounded below, since `{W ≤ a}` is
  -- empty below the minimum of `W`. Let `s` be its infimum.
  by_contra hb
  set F := {a | a ≤ b ∧ ¬g a ≤ h a}
  obtain ⟨m, hm⟩ := (isCompact_range hWc).bddBelow
  have hFbdd : BddBelow F := ⟨m, fun a ha ↦ by
    by_contra! ham
    refine ha.2 ?_
    have : {x | W x ≤ a} = ∅ := eq_empty_of_forall_notMem fun x hx ↦
      (ham.trans_le (hm (mem_range_self x))).not_ge hx
    simp [hg, this, hempty]⟩
  have hFne : F.Nonempty := ⟨b, le_rfl, hb⟩
  set s := sInf F
  have hsb : s ≤ b := csInf_le hFbdd ⟨le_rfl, hb⟩
  have hbelow : ∀ a < s, g a ≤ h a := fun a ha ↦ by
    by_contra hna
    exact (csInf_le hFbdd ⟨ha.le.trans hsb, hna⟩).not_gt ha
  -- The rest points on the level `s` have an open neighbourhood `U` of index at most their number,
  -- and the deformation lemma crosses the level `s` outside `U`.
  set K := {x | (∀ t, ϕ t x = x) ∧ W x = s}
  obtain ⟨U, hUo, hKU, hU⟩ := K.exists_isOpen_superset_le_encard hmono hempty hunion
    fun x hx ↦ hloc x hx.1
  obtain ⟨ε, hε, T, hT, hdef⟩ :=
    exists_pos_forall_apply_le_sub hWc hW s hUo fun x hx hxs ↦ hKU ⟨hx, hxs⟩
  -- No level in `[s, s + ε]` fails, contradicting the choice of `s`.
  obtain ⟨a, haF, has⟩ := exists_lt_of_csInf_lt hFne (lt_add_of_pos_right s hε)
  have hsa : s ≤ a := csInf_le hFbdd haF
  refine haF.2 ?_
  have hsub : {x | W x ≤ a} ⊆ U ∪ ϕ T ⁻¹' {x | W x ≤ s - ε} := fun x hx ↦ by
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr (hdef x (le_trans hx has.le) hxU)
  have hdisj : Disjoint {x | (∀ t, ϕ t x = x) ∧ W x ≤ s - ε} K :=
    disjoint_left.2 fun x hx hxK ↦ by linarith [hx.2, hxK.2]
  calc g a ≤ ν U + ν (ϕ T ⁻¹' {x | W x ≤ s - ε}) := (hmono hsub).trans (hunion _ _)
    _ ≤ K.encard + h (s - ε) := add_le_add hU ((hflow T hT _).trans (hbelow _ (by linarith)))
    _ = ({x | (∀ t, ϕ t x = x) ∧ W x ≤ s - ε} ∪ K).encard := by
      rw [encard_union_eq hdisj, add_comm]
    _ ≤ h a := encard_le_encard <| union_subset (fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩)
      fun x hx ↦ ⟨hx.1, hx.2.trans_le hsa⟩

/-- **The Lusternik–Schnirelmann bound for flows.** Let `W` be a continuous function on a compact
space which strictly decreases along every nonconstant orbit of the flow `ϕ`, and let `ν` be an
index on `α`: monotone, zero on `∅`, subadditive, not increased by the flow in forward time, and
at most `1` on some neighbourhood of each rest point. Then the flow has at least `ν univ` rest
points. -/
theorem index_univ_le_encard [CompactSpace α] (hWc : Continuous W)
    (hW : ∀ x t, 0 < t → ϕ t x ≠ x → W (ϕ t x) < W x) (hmono : Monotone ν) (hempty : ν ∅ = 0)
    (hunion : ∀ A B, ν (A ∪ B) ≤ ν A + ν B) (hflow : ∀ t, 0 ≤ t → ∀ A, ν (ϕ t ⁻¹' A) ≤ ν A)
    (hloc : ∀ x, (∀ t, ϕ t x = x) → ∃ V ∈ 𝓝 x, ν V ≤ 1) :
    ν univ ≤ {x | ∀ t, ϕ t x = x}.encard := by
  obtain ⟨b, hb⟩ := (isCompact_range hWc).bddAbove
  have huniv : {x | W x ≤ b} = univ := eq_univ_of_forall fun x ↦ hb (mem_range_self x)
  have hrest : {x | (∀ t, ϕ t x = x) ∧ W x ≤ b} = {x | ∀ t, ϕ t x = x} :=
    Set.ext fun x ↦ and_iff_left (hb (mem_range_self x))
  simpa [huniv, hrest] using
    index_sublevel_le_encard hWc hW hmono hempty hunion hflow hloc b

end Index

end Flow
