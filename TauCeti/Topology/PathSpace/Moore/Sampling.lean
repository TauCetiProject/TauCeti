/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop
public import TauCeti.Topology.ContinuousMap.Ascoli
public import TauCeti.Topology.MetricSpace.CyclicDistanceCut
public import TauCeti.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz
import TauCeti.Algebra.Order.BigOperators.Fin
import TauCeti.Data.Fin.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Constructions

/-!
# Sampling compact families of Moore paths

`MoorePath.sample γ r` records the vertices `γ(0), γ(L/r), …, γ((r-1)L/r)`, where
`L` is the duration of `γ`. Sampling is continuous, including at paths of duration zero.

For a compact family of paths in a pseudometric space, every sufficiently fine subdivision
has uniformly small arcs: every point of an arc is close to its initial sampled vertex.
The same estimate holds for free loops, including the final arc back to the first vertex.
These estimates place the sampled vertices in distance cutoffs for broken geodesics and
control the original arcs during interpolation inside convex balls. In particular, for
cut-offs bounded below by a positive constant, every sufficiently fine sampling of a compact
family of free loops lies in Abouzaid's distance cut `TauCeti.cyclicDistanceCut`
(`TauCeti.MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut`): this is the threshold
`r(K)` of the compact-family approximation of the free loop space by broken geodesics.

The compact-family argument uses the existing continuous comparison `MoorePath.toUnitPath` and
the compact-family equicontinuity theorem `IsCompact.equicontinuous`. It concerns duration and
compact-open topology; no geometric-length bound or unit-speed parametrization is used.

A `1`-Lipschitz free loop moves by at most `t - s` between the times `s ≤ t`. So its samples at
increasing times `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ m` up to its duration `L` lie in the distance cut
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

* `TauCeti.MoorePath.sample`: the equally spaced vertices of a Moore path.
* `TauCeti.cyclicDistanceCutTimes`: the sample times for a distance cut.

## Main results

* `TauCeti.MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut`: compact families of free
  loops are sampled into the distance cuts.
* `TauCeti.MooreFreeLoopSpace.apply_mem_cyclicDistanceCut`: the samples of a `1`-Lipschitz free
  loop at sample times for a distance cut lie in the cut.
* `TauCeti.combo_mem_cyclicDistanceCutTimes`: convex combinations of sample times.
* `TauCeti.mul_div_mem_cyclicDistanceCutTimes`, `TauCeti.partialSum_mem_cyclicDistanceCutTimes`:
  equally spaced times and vertex times.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, §11.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public noncomputable section

open scoped NNReal unitInterval
open Set Topology

namespace TauCeti
namespace MoorePath

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The `r` equally spaced vertices of a Moore path, starting at time zero and omitting
the final endpoint. The time spacing is the duration divided by `r`. -/
def sample (γ : MoorePath X) (r : ℕ) : Fin r → X :=
  fun i ↦ γ (γ.length * ((i.val : ℝ≥0) / (r : ℝ≥0)))

/-- The defining evaluation formula for sampling a Moore path. -/
theorem sample_apply (γ : MoorePath X) (r : ℕ) (i : Fin r) :
    γ.sample r i = γ (γ.length * ((i.val : ℝ≥0) / (r : ℝ≥0))) :=
  (rfl)

/-- The first sampled vertex is the source. -/
@[simp]
theorem sample_zero (γ : MoorePath X) {r : ℕ} [NeZero r] :
    γ.sample r 0 = γ.source := by
  simp [sample_apply, source_def]

/-- Sampling a constant path gives a constant tuple, regardless of its duration. -/
@[simp]
theorem sample_constOfLength (x : X) (L : ℝ≥0) (r : ℕ) :
    (constOfLength x L).sample r = fun _ ↦ x := by
  funext i
  rw [sample_apply, constOfLength_apply]

/-- Sampling commutes with continuous maps of the target. -/
@[simp]
theorem sample_map (γ : MoorePath X) (f : C(X, Y)) (r : ℕ) :
    (γ.map f).sample r = fun i ↦ f (γ.sample r i) := by
  funext i
  simp [sample_apply]

/-- The vertices vary continuously with the Moore path and its duration. -/
@[fun_prop]
theorem continuous_sample (r : ℕ) : Continuous (fun γ : MoorePath X ↦ γ.sample r) := by
  refine continuous_pi fun i ↦ ?_
  simp only [sample_apply]
  exact continuous_id.moorePath_eval (continuous_length.mul continuous_const)

/-- The `i`-th sampled vertex is the start `i / r` of the `i`-th of the `r` equal arcs of the
path reparametrized to the unit interval. -/
theorem sample_eq_toUnitPath_arcPoint (γ : MoorePath X) {r : ℕ} (i : Fin r) :
    γ.sample r i = γ.toUnitPath (unitInterval.arcPoint r i 0) := by
  rw [sample_apply, toUnitPath_apply]
  congr 2
  apply NNReal.coe_injective
  rw [unitInterval.coe_toNNReal, unitInterval.coe_arcPoint i.isLt]
  simp

variable {X : Type*} [PseudoMetricSpace X]

/-- In a compact family of Moore paths, all sufficiently fine subdivisions have uniformly
small arcs. Every point in the `i`th arc is within `ε` of its initial sampled vertex.
The subdivision threshold is uniform in the path, the arc, and the point of the arc. -/
theorem exists_sample_arc_dist_lt {K : Set (MoorePath X)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ r ≥ N, ∀ γ ∈ K, ∀ i : Fin r, ∀ t : I,
      (i.val : ℝ) / r ≤ t → (t : ℝ) ≤ (i.val + 1 : ℝ) / r →
      dist (γ.sample r i) (γ.toUnitPath t) < ε := by
  have hequi := (hK.image continuous_toUnitPath).equicontinuous
  have huniform := CompactSpace.uniformEquicontinuous_of_equicontinuous hequi
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformEquicontinuous_iff.mp huniform ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, by omega, fun r hr γ hγ i t ht₀ ht₁ ↦ ?_⟩
  let s : I := unitInterval.arcPoint r i 0
  have hs : (s : ℝ) = (i.val : ℝ) / r := by
    rw [unitInterval.coe_arcPoint i.isLt, Set.Icc.coe_zero, add_zero]
  have hmesh : 1 / (r : ℝ) < δ :=
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hr)).trans_lt hn
  have hst : dist s t < δ := by
    rw [Subtype.dist_eq, hs, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht₀)]
    have ht : (t : ℝ) - (i.val : ℝ) / r ≤ 1 / r := by
      rw [add_div] at ht₁
      linarith
    exact ht.trans_lt hmesh
  rw [sample_eq_toUnitPath_arcPoint]
  exact hclose s t hst ⟨γ.toUnitPath, ⟨γ, hγ, rfl⟩⟩

end MoorePath

/-! ### Sample times for a distance cut -/

section CutTimes

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
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.2 s.property.2),
      mul_le_mul_of_nonneg_left hy s.property.1]
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
    exact mul_le_of_le_one_right L.property ((div_le_one hm).2 (by linarith))
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
duration is the total `t (n + 1)` of the cyclic edges, when `δ (j - k) ≤ δ' j` for every `j`:
their gaps are `0` and the edges of `q`, and their closing gap is the closing edge of `q`. -/
theorem partialSum_mem_cyclicDistanceCutTimes {X : Type*} [PseudoMetricSpace X] {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ}
    (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    {q : Fin (n + 1) → X} (hq : q ∈ cyclicDistanceCut δ) :
    (fun j : Fin (n + k + 1) ↦ Fin.partialSum (fun i ↦ nndist (q i) (q (i + 1)))
        (Fin.castSucc ⟨j - k, by omega⟩)) ∈
      cyclicDistanceCutTimes (Fin.partialSum (fun i ↦ nndist (q i) (q (i + 1))) (Fin.last (n + 1)))
        δ' := by
  have hP : Monotone (Fin.partialSum fun i ↦ nndist (q i) (q (i + 1))) :=
    Fin.monotone_partialSum fun _ ↦ zero_le
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
    have h0 := h 0
    rw [hfirst] at h0
    simp only [NNReal.coe_add, NNReal.coe_zero, zero_add, add_sub_cancel_left, Fin.last_add_one,
      coe_nndist]
    exact hq0.trans h0
  · dsimp only
    by_cases hj : (j : ℕ) < k
    · -- Between repeated copies of `q₀` the gap is zero.
      have he : (⟨(j.succ : ℕ) - k, by omega⟩ : Fin (n + 1)) = ⟨(j.castSucc : ℕ) - k, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      rw [he, sub_self]
      exact (nonneg_of_mem_cyclicDistanceCut hq _).trans (h _)
    · -- Otherwise the gap is the edge of `q` from `qᵢ` to `qᵢ₊₁`, where `i = j - k`.
      let i : Fin n := ⟨j - k, by omega⟩
      have hsucc : (⟨(j.succ : ℕ) - k, by omega⟩ : Fin (n + 1)) = i.succ :=
        Fin.ext (by simp only [Fin.val_succ, i]; omega)
      have hcast : (⟨(j.castSucc : ℕ) - k, by omega⟩ : Fin (n + 1)) = i.castSucc :=
        Fin.ext (by simp [i])
      have hi := mem_cyclicDistanceCut.1 hq i.succ
      rw [Fin.succ_sub_one_eq_castSucc, dist_comm] at hi
      have hj' := h j.succ
      rw [hsucc] at hj'
      rw [hsucc, hcast, ← Fin.succ_castSucc, Fin.partialSum_succ, NNReal.coe_add,
        add_sub_cancel_left]
      simp only [Fin.coeSucc_eq_succ, coe_nndist]
      exact hi.trans hj'

end CutTimes

namespace MooreFreeLoopSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- In a compact family of free Moore loops, sufficiently fine sampling has uniformly
small cyclic edges. Addition in `Fin (r + 1)` includes the closing edge to the first vertex. -/
theorem exists_sample_dist_add_one_lt {K : Set (MooreFreeLoopSpace X)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r ≥ N, ∀ γ ∈ K, ∀ i : Fin (r + 1),
      dist (γ.toMoorePath.sample (r + 1) i)
        (γ.toMoorePath.sample (r + 1) (i + 1)) < ε := by
  obtain ⟨N, _, h⟩ := MoorePath.exists_sample_arc_dist_lt
    (hK.image continuous_toMoorePath) hε
  refine ⟨N, fun r hr γ hγ i ↦ ?_⟩
  have harc := h (r + 1) (by omega) γ.toMoorePath ⟨γ, hγ, rfl⟩ i
  have hrpos : 0 < (r + 1 : ℝ) := by positivity
  by_cases hi : i.val + 1 < r + 1
  · have hj : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt' hi
    let t : I := ⟨(i.val + 1 : ℝ) / (r + 1), by positivity,
      (div_le_one hrpos).mpr (by exact_mod_cast hi.le)⟩
    have hsample : γ.toMoorePath.sample (r + 1) (i + 1) = γ.toMoorePath.toUnitPath t := by
      rw [MoorePath.sample_apply, MoorePath.toUnitPath_apply, hj]
      congr 2
      apply NNReal.coe_injective
      rw [unitInterval.coe_toNNReal]
      simp [t]
    rw [hsample]
    apply harc t
    · dsimp [t]
      simp only [Nat.cast_add, Nat.cast_one]
      exact div_le_div_of_nonneg_right (by linarith) hrpos.le
    · simp [t]
  · have hi' : i.val + 1 = r + 1 := by omega
    have hj : i + 1 = (0 : Fin (r + 1)) := by
      ext
      simp [Fin.val_add, hi']
    rw [hj, MoorePath.sample_zero]
    have hiReal : (i.val : ℝ) + 1 = (r : ℝ) + 1 := by exact_mod_cast hi'
    have hdist := harc 1 (by
      simp only [Set.Icc.coe_one, Nat.cast_add, Nat.cast_one]
      exact (div_le_one hrpos).mpr (by exact_mod_cast i.isLt.le)) (by
        simp only [Set.Icc.coe_one, Nat.cast_add, Nat.cast_one, hiReal,
          div_self hrpos.ne', le_refl])
    simpa only [MoorePath.toUnitPath_one, target_toMoorePath, source_toMoorePath] using hdist

/-- **Compact families of free loops are sampled into the distance cuts.** For a compact family
`K` of free Moore loops and cut-offs bounded below by `ε > 0`, every sufficiently fine sampling
of `K` lies in the distance cut: there is `N` such that for every `r ≥ N` and all cut-offs
`δ : Fin (r + 1) → ℝ` with `ε ≤ δ i` for every `i`, the `r + 1` sampled vertices of each loop of
`K` lie in `cyclicDistanceCut δ`. The threshold is uniform in the cut-offs. -/
theorem exists_mapsTo_sample_cyclicDistanceCut {K : Set (MooreFreeLoopSpace X)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r ≥ N, ∀ δ : Fin (r + 1) → ℝ, (∀ i, ε ≤ δ i) →
      MapsTo (fun γ : MooreFreeLoopSpace X ↦ γ.toMoorePath.sample (r + 1)) K
        (cyclicDistanceCut δ) := by
  obtain ⟨N, hN⟩ := exists_sample_dist_add_one_lt hK hε
  refine ⟨N, fun r hr δ hδ γ hγ ↦ mem_cyclicDistanceCut.2 fun i ↦ ?_⟩
  -- The edge ending at the vertex `i` is the edge starting at the vertex `i - 1`.
  have hi := hN r hr γ hγ (i - 1)
  rw [sub_add_cancel, dist_comm] at hi
  exact hi.le.trans (hδ i)

/-- **Samples of a `1`-Lipschitz free loop at increasing times lie in a distance cut.** Let `γ` be a
free loop of duration `L` which is `1`-Lipschitz, and let `τ 0 ≤ ⋯ ≤ τ m ≤ L` be times. The samples
`γ (τ i)` lie in the distance cut with cut-offs `δ` when every gap `τ (i + 1) - τ i` is at most
`δ (i + 1)` and the closing gap `τ 0 + (L - τ m)`, from the last sample through the base point
back to the first, is at most `δ 0`. -/
theorem apply_mem_cyclicDistanceCut {m : ℕ} {γ : MooreFreeLoopSpace X}
    (hγ : LipschitzWith 1 γ.toMoorePath) {τ : Fin (m + 1) → ℝ≥0} {δ : Fin (m + 1) → ℝ}
    (hτ : τ ∈ cyclicDistanceCutTimes γ.length δ) :
    (fun i ↦ γ.toMoorePath (τ i)) ∈ cyclicDistanceCut δ := by
  obtain ⟨hτ, hlast, h₀, h⟩ := hτ
  have hdist : ∀ s t : ℝ≥0, s ≤ t →
      dist (γ.toMoorePath s) (γ.toMoorePath t) ≤ (t : ℝ) - s := fun s t hst ↦ by
    simpa only [NNReal.coe_one, one_mul, NNReal.dist_eq_sub_of_le hst] using hγ.dist_le_mul s t
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
