/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop
public import TauCeti.Topology.ContinuousMap.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Sampling compact families of Moore paths

`MoorePath.sample γ r` records the vertices `γ(0), γ(L/r), …, γ((r-1)L/r)`, where
`L` is the duration of `γ`. Sampling is continuous, including at paths of duration zero.

For a compact family of paths in a pseudometric space, every sufficiently fine subdivision
has uniformly small arcs: every point of an arc is close to its initial sampled vertex.
The same estimate holds for free loops, including the final arc back to the first vertex.
These estimates place the sampled vertices in distance cutoffs for broken geodesics and
control the original arcs during interpolation inside convex balls.

The argument uses the existing continuous comparison `MoorePath.toUnitPath` and the
compact-family equicontinuity theorem `IsCompact.equicontinuous`. It concerns duration
and compact-open topology; no geometric-length bound or unit-speed parametrization is used.

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
  have hrnat : 0 < r := by omega
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hrnat
  have hi : (i.val : ℝ) ≤ r := by exact_mod_cast i.isLt.le
  let s : I := ⟨(i.val : ℝ) / r, div_nonneg (Nat.cast_nonneg _) hrpos.le,
    (div_le_one hrpos).mpr hi⟩
  have hmesh : 1 / (r : ℝ) < δ :=
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hr)).trans_lt hn
  have hst : dist s t < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht₀)]
    have ht : (t : ℝ) - (i.val : ℝ) / r ≤ 1 / r := by
      rw [add_div] at ht₁
      linarith
    exact ht.trans_lt hmesh
  have hsample : γ.sample r i = γ.toUnitPath s := by
    rw [sample_apply, toUnitPath_apply]
    congr 2
  rw [hsample]
  exact hclose s t hst ⟨γ.toUnitPath, ⟨γ, hγ, rfl⟩⟩

end MoorePath

namespace MooreFreeLoopSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- In a compact family of free Moore loops, sufficiently fine sampling has uniformly
small cyclic edges. Addition in `Fin (r + 1)` includes the closing edge to the first vertex. -/
theorem exists_sample_dist_add_one_lt {K : Set (MooreFreeLoopSpace X)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r ≥ N, ∀ γ ∈ K, ∀ i : Fin (r + 1),
      dist (γ.toMoorePath.sample (r + 1) i)
        (γ.toMoorePath.sample (r + 1) (i + 1)) < ε := by
  obtain ⟨N, hN, h⟩ := MoorePath.exists_sample_arc_dist_lt
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

end MooreFreeLoopSpace
end TauCeti
