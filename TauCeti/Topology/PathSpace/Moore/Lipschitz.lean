/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Topology.MetricSpace.CyclicDistanceCut
public import TauCeti.Topology.PathSpace.Moore.FreeLoop
import Mathlib.Topology.MetricSpace.Lipschitz
import TauCeti.Data.Fin.Basic

/-!
# Lipschitz Moore paths and their samples

A Moore path `γ` in a pseudometric space is a function `[0, ∞) → X`, so it makes sense to ask that
it be Lipschitz. Concatenation preserves this
(`TauCeti.MoorePath.lipschitzWith_trans`): the two halves meet at the junction time, where the
triangle inequality splits the distance between points on either side.

A `1`-Lipschitz free loop moves by at most `t - s` between the times `s ≤ t`. So its samples at
increasing times `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ m` up to its duration `L` lie in Abouzaid's distance cut
`TauCeti.cyclicDistanceCut δ` as soon as every gap `τ (i + 1) - τ i` is at most `δ (i + 1)` and the
closing gap `τ 0 + (L - τ m)`, which runs through the base point, is at most `δ 0`
(`TauCeti.MooreFreeLoopSpace.apply_mem_cyclicDistanceCut`). Call such times *sample times* for
the cut (`TauCeti.cyclicDistanceCutTimes`). They are stable under convex combinations
(`TauCeti.combo_mem_cyclicDistanceCutTimes`), which is how sampled vertices are slid along a loop
inside a distance cut. Two families of sample times are used for broken geodesics: the `m + 1`
equally spaced times, when the duration is at most `m + 1` times every cut-off
(`TauCeti.mul_div_mem_cyclicDistanceCutTimes`), and, for a tuple `q` of a distance cut, the partial
sums of its cyclic edges, with the first one repeated
(`TauCeti.partialSum_mem_cyclicDistanceCutTimes`), the times at which the closed broken geodesic
through `q` passes through its vertices.

## Main definitions

* `TauCeti.cyclicDistanceCutTimes`: the sample times for a distance cut.

## Main results

* `TauCeti.MoorePath.lipschitzWith_refl`, `TauCeti.MoorePath.lipschitzWith_trans`: constant paths
  are Lipschitz, and concatenation preserves the Lipschitz property.
* `TauCeti.MooreFreeLoopSpace.apply_mem_cyclicDistanceCut`: the samples of a `1`-Lipschitz free
  loop at sample times for a distance cut lie in the cut.
* `TauCeti.combo_mem_cyclicDistanceCutTimes`: convex combinations of sample times.
* `TauCeti.mul_div_mem_cyclicDistanceCutTimes`, `TauCeti.partialSum_mem_cyclicDistanceCutTimes`:
  equally spaced times and vertex times.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2.
-/

public section

open scoped NNReal

namespace TauCeti

namespace MoorePath

variable {X : Type*} [PseudoMetricSpace X]

/-- The constant Moore path of length zero is Lipschitz with every constant. -/
theorem lipschitzWith_refl (x : X) (K : ℝ≥0) : LipschitzWith K (refl x) := by
  have h : ⇑(refl x) = fun _ ↦ x := funext (refl_apply x)
  rw [h]
  exact LipschitzWith.const' x

/-- **Concatenation preserves the Lipschitz property.** If two Moore paths are `K`-Lipschitz, so is
their concatenation. -/
theorem lipschitzWith_trans {γ δ : MoorePath X} (h : γ.target = δ.source) {K : ℝ≥0}
    (hγ : LipschitzWith K γ) (hδ : LipschitzWith K δ) : LipschitzWith K (γ.trans δ h) := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, dist_comm s]
    exact this t s (le_of_not_ge hst)
  have hd : ∀ {a b : ℝ≥0}, a ≤ b → dist a b = (b : ℝ) - a := fun hab ↦ by
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hab))]
  rcases le_total t γ.length with ht | ht
  · rw [trans_apply_of_le _ _ _ (hst.trans ht), trans_apply_of_le _ _ _ ht]
    exact hγ.dist_le_mul s t
  rcases le_total γ.length s with hs | hs
  · -- Both times lie in the second path.
    rw [trans_apply_of_length_le _ _ _ hs, trans_apply_of_length_le _ _ _ ht]
    have hsub : dist (s - γ.length) (t - γ.length) = dist s t := by
      rw [hd (tsub_le_tsub_right hst _), hd hst, NNReal.coe_sub hs, NNReal.coe_sub ht]
      ring
    simpa only [hsub] using hδ.dist_le_mul (s - γ.length) (t - γ.length)
  · -- The times lie on either side of the junction, where the paths meet.
    rw [trans_apply_of_le _ _ _ hs, trans_apply_of_length_le _ _ _ ht]
    have hjoin : γ γ.length = δ 0 := by rw [← target_def, h, source_def]
    calc dist (γ s) (δ (t - γ.length))
        ≤ dist (γ s) (γ γ.length) + dist (δ 0) (δ (t - γ.length)) := by
          rw [← hjoin]
          exact dist_triangle _ _ _
      _ ≤ K * dist s γ.length + K * dist 0 (t - γ.length) :=
          add_le_add (hγ.dist_le_mul _ _) (hδ.dist_le_mul _ _)
      _ = K * dist s t := by
          rw [hd hs, hd zero_le, hd hst, NNReal.coe_sub ht, NNReal.coe_zero]
          ring

end MoorePath

variable {m : ℕ}

/-- **Sample times for a distance cut.** The times `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ m ≤ L` whose gaps
`τ (i + 1) - τ i` are at most `δ (i + 1)` and whose closing gap `τ 0 + (L - τ m)` is at most `δ 0`.
The samples of a `1`-Lipschitz free loop of duration `L` at these times lie in the distance cut
with cut-offs `δ` (`TauCeti.MooreFreeLoopSpace.apply_mem_cyclicDistanceCut`). -/
def cyclicDistanceCutTimes (L : ℝ≥0) (δ : Fin (m + 1) → ℝ) : Set (Fin (m + 1) → ℝ≥0) :=
  {τ | Monotone τ ∧ τ (Fin.last m) ≤ L ∧ (τ 0 : ℝ) + (L - τ (Fin.last m)) ≤ δ 0 ∧
    ∀ i : Fin m, (τ i.succ : ℝ) - τ i.castSucc ≤ δ i.succ}

@[simp]
theorem mem_cyclicDistanceCutTimes {L : ℝ≥0} {δ : Fin (m + 1) → ℝ} {τ : Fin (m + 1) → ℝ≥0} :
    τ ∈ cyclicDistanceCutTimes L δ ↔ Monotone τ ∧ τ (Fin.last m) ≤ L ∧
      (τ 0 : ℝ) + (L - τ (Fin.last m)) ≤ δ 0 ∧
      ∀ i : Fin m, (τ i.succ : ℝ) - τ i.castSucc ≤ δ i.succ :=
  Iff.rfl

/-- **Sample times for a distance cut are stable under convex combinations.** For times `a` and `b`
for the distance cut with cut-offs `δ` and `s ∈ [0, 1]`, so are the times `(1 - s) a + s b`. -/
theorem combo_mem_cyclicDistanceCutTimes {L : ℝ≥0} {δ : Fin (m + 1) → ℝ}
    {a b : Fin (m + 1) → ℝ≥0} (ha : a ∈ cyclicDistanceCutTimes L δ)
    (hb : b ∈ cyclicDistanceCutTimes L δ) (s : unitInterval) :
    (fun i ↦ unitInterval.toNNReal (unitInterval.symm s) * a i + unitInterval.toNNReal s * b i) ∈
      cyclicDistanceCutTimes L δ := by
  obtain ⟨ha, haL, ha₀, ha'⟩ := ha
  obtain ⟨hb, hbL, hb₀, hb'⟩ := hb
  -- A convex combination of two numbers below `c` is below `c`.
  have hcombo : ∀ {x y c : ℝ}, x ≤ c → y ≤ c → (1 - s) * x + s * y ≤ c := fun hx hy ↦ by
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.2 s.2.2),
      mul_le_mul_of_nonneg_left hy s.2.1]
  have hcoe : ∀ i, ((unitInterval.toNNReal (unitInterval.symm s) * a i +
      unitInterval.toNNReal s * b i : ℝ≥0) : ℝ) = (1 - s) * a i + s * b i := fun i ↦ by
    simp
  refine ⟨(ha.const_mul zero_le).add (hb.const_mul zero_le), ?_, ?_, fun i ↦ ?_⟩
  · rw [← NNReal.coe_le_coe, hcoe]
    exact hcombo (NNReal.coe_le_coe.2 haL) (NNReal.coe_le_coe.2 hbL)
  · rw [hcoe, hcoe]
    convert hcombo ha₀ hb₀ using 1
    ring
  · rw [hcoe, hcoe]
    convert hcombo (ha' i) (hb' i) using 1
    ring

/-- **Equally spaced sample times.** The `m + 1` times `L * (j / (m + 1))` are sample times for the
distance cut with cut-offs `δ` on a loop of duration `L` when `L ≤ (m + 1) * δ j` for every `j`:
all their gaps, including the closing one, are `L / (m + 1)`. -/
theorem mul_div_mem_cyclicDistanceCutTimes {L : ℝ≥0} {δ : Fin (m + 1) → ℝ}
    (h : ∀ j, (L : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * δ j) :
    (fun j : Fin (m + 1) ↦ L * ((j : ℕ) / (m + 1 : ℕ) : ℝ≥0)) ∈ cyclicDistanceCutTimes L δ := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hgap : ∀ j, (L : ℝ) / ((m : ℝ) + 1) ≤ δ j := fun j ↦ by
    rw [div_le_iff₀ hm, mul_comm]
    exact_mod_cast h j
  refine ⟨fun a b hab ↦ ?_, ?_, ?_, fun j ↦ ?_⟩
  · dsimp only
    gcongr
    exact_mod_cast hab
  · rw [← NNReal.coe_le_coe]
    push_cast
    exact mul_le_of_le_one_right L.2 ((div_le_one hm).2 (by linarith))
  · convert hgap 0 using 1
    push_cast [Fin.val_zero, Fin.val_last]
    field_simp
    ring
  · convert hgap j.succ using 1
    push_cast [Fin.val_succ, Fin.val_castSucc]
    field_simp
    ring

/-- **Vertex times with the first vertex repeated.** For a tuple `q` of the distance cut with
cut-offs `δ`, the partial sums `t i = d(q₀, q₁) + ⋯ + d(qᵢ₋₁, qᵢ)` of its cyclic edges, with `t 0`
repeated `k + 1` times, are sample times for the distance cut with cut-offs `δ'` on a loop whose
duration is the total `t (n + 1)` of the cyclic edges, when every `δ i` is at most every `δ' j`:
their gaps are `0` and the edges of `q`, and their closing gap is the closing edge of `q`. -/
theorem partialSum_mem_cyclicDistanceCutTimes {X : Type*} [PseudoMetricSpace X] {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} (h : ∀ i j, δ i ≤ δ' j)
    {q : Fin (n + 1) → X} (hq : q ∈ cyclicDistanceCut δ) :
    (fun j : Fin (n + k + 1) ↦ Fin.partialSum (fun i ↦ nndist (q i) (q (i + 1)))
        (Fin.castSucc ⟨j - k, by omega⟩)) ∈
      cyclicDistanceCutTimes (Fin.partialSum (fun i ↦ nndist (q i) (q (i + 1))) (Fin.last (n + 1)))
        δ' := by
  have hP : Monotone (Fin.partialSum fun i ↦ nndist (q i) (q (i + 1))) :=
    Fin.monotone_iff_le_succ.2 fun i ↦ by
      rw [Fin.partialSum_succ]
      exact le_self_add
  have hδ' : ∀ j, 0 ≤ δ' j := fun j ↦ (nonneg_of_mem_cyclicDistanceCut hq 0).trans (h 0 j)
  have hfirst : (⟨((0 : Fin (n + k + 1)) : ℕ) - k, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp)
  have hlast : (⟨(Fin.last (n + k) : ℕ) - k, by omega⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp)
  refine ⟨fun a b hab ↦ hP (Fin.castSucc_le_castSucc_iff.2 (Fin.mk_le_mk.2
    (Nat.sub_le_sub_right hab k))), ?_, ?_, fun j ↦ ?_⟩
  · exact hP (Fin.le_last _)
  · -- The closing gap is the closing edge `d(qₙ, q₀)`.
    dsimp only
    rw [hfirst, hlast, Fin.castSucc_zero, Fin.partialSum_zero, ← Fin.succ_last, Fin.partialSum_succ]
    have hq0 := mem_cyclicDistanceCut.1 hq 0
    rw [Fin.zero_sub_one_eq_last, dist_comm] at hq0
    simp only [NNReal.coe_add, NNReal.coe_zero, zero_add, add_sub_cancel_left, Fin.last_add_one,
      coe_nndist]
    exact hq0.trans (h 0 0)
  · dsimp only
    by_cases hj : (j : ℕ) < k
    · -- Between repeated copies of `q₀` the gap is zero.
      have he : (⟨(j.succ : ℕ) - k, by omega⟩ : Fin (n + 1)) = ⟨(j.castSucc : ℕ) - k, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      rw [he, sub_self]
      exact hδ' _
    · -- Otherwise the gap is the edge of `q` from `qᵢ` to `qᵢ₊₁`, where `i = j - k`.
      let i : Fin n := ⟨j - k, by omega⟩
      have hsucc : (⟨(j.succ : ℕ) - k, by omega⟩ : Fin (n + 1)) = i.succ :=
        Fin.ext (by simp only [Fin.val_succ, i]; omega)
      have hcast : (⟨(j.castSucc : ℕ) - k, by omega⟩ : Fin (n + 1)) = i.castSucc :=
        Fin.ext (by simp [i])
      have hi := mem_cyclicDistanceCut.1 hq i.succ
      rw [Fin.succ_sub_one_eq_castSucc, dist_comm] at hi
      rw [hsucc, hcast, ← Fin.succ_castSucc, Fin.partialSum_succ, NNReal.coe_add,
        add_sub_cancel_left]
      simp only [Fin.coeSucc_eq_succ, coe_nndist]
      exact hi.trans (h _ _)

namespace MooreFreeLoopSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- **Samples of a `1`-Lipschitz free loop at increasing times lie in a distance cut.** Let `γ` be a
free loop of duration `L` which is `1`-Lipschitz, and let `τ 0 ≤ ⋯ ≤ τ m ≤ L` be times. The samples
`γ (τ i)` lie in the distance cut with cut-offs `δ` when every gap `τ (i + 1) - τ i` is at most
`δ (i + 1)` and the closing gap `τ 0 + (L - τ m)`, from the last sample through the base point
back to the first, is at most `δ 0`. -/
theorem apply_mem_cyclicDistanceCut {γ : MooreFreeLoopSpace X}
    (hγ : LipschitzWith 1 γ.toMoorePath) {τ : Fin (m + 1) → ℝ≥0} {δ : Fin (m + 1) → ℝ}
    (hτ : τ ∈ cyclicDistanceCutTimes γ.length δ) :
    (fun i ↦ γ.toMoorePath (τ i)) ∈ cyclicDistanceCut δ := by
  obtain ⟨hτ, hlast, h₀, h⟩ := hτ
  have hdist : ∀ s t : ℝ≥0, s ≤ t →
      dist (γ.toMoorePath s) (γ.toMoorePath t) ≤ (t : ℝ) - s := fun s t hst ↦ by
    have := hγ.dist_le_mul s t
    rwa [NNReal.coe_one, one_mul, NNReal.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))] at this
  rw [mem_cyclicDistanceCut]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · -- The closing edge runs from the first sample back to the base point and on to the last.
    rw [Fin.zero_sub_one_eq_last]
    have hbase : γ.toMoorePath 0 = γ.toMoorePath γ.length := by
      rw [← MoorePath.source_def, ← length_toMoorePath, ← MoorePath.target_def,
        γ.target_eq_source]
    calc dist (γ.toMoorePath (τ 0)) (γ.toMoorePath (τ (Fin.last m)))
        ≤ dist (γ.toMoorePath 0) (γ.toMoorePath (τ 0)) +
            dist (γ.toMoorePath (τ (Fin.last m))) (γ.toMoorePath γ.length) := by
          rw [dist_comm (γ.toMoorePath 0), ← hbase, dist_comm (γ.toMoorePath (τ (Fin.last m)))]
          exact dist_triangle _ _ _
      _ ≤ ((τ 0 : ℝ) - (0 : ℝ≥0)) + ((γ.length : ℝ) - τ (Fin.last m)) :=
          add_le_add (hdist _ _ zero_le) (hdist _ _ hlast)
      _ ≤ δ 0 := by simpa only [NNReal.coe_zero, sub_zero] using h₀
  · rw [Fin.succ_sub_one_eq_castSucc, dist_comm]
    exact (hdist _ _ (hτ Fin.castSucc_lt_succ.le)).trans (h j)

end MooreFreeLoopSpace

end TauCeti
