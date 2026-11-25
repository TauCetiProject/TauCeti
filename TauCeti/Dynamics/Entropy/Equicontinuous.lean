/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuous maps and isometries have zero topological entropy

If the iterates `T^[n]` of a map `T` of a uniform space form a uniformly equicontinuous family,
then for every entourage `U` there is one entourage `V` with `V ⊆ dynEntourage T U n` for all `n`.
A totally bounded set `F` is covered by finitely many `V`-balls, so the minimal dynamical covers
of `F` have bounded cardinality and the topological entropy of `T` on `F` is at most `0`
(`TauCeti.coverEntropy_nonpos_of_uniformEquicontinuous`), and equal to `0` when `F` is nonempty.

The iterates of an isometry are isometries, hence uniformly equicontinuous: an isometry of a
compact pseudo-emetric space has topological entropy `0`
(`TauCeti.coverEntropy_univ_eq_zero_of_isometry`). This covers the identity and the rotations
of the circle.

## Main results

* `TauCeti.coverEntropy_nonpos_of_uniformEquicontinuous`,
  `TauCeti.coverEntropy_eq_zero_of_uniformEquicontinuous`: zero entropy on totally bounded sets
  for uniformly equicontinuous iterates.
* `TauCeti.uniformEquicontinuous_iterate_of_isometry`: the iterates of an isometry are uniformly
  equicontinuous.
* `TauCeti.coverEntropy_univ_eq_zero_of_isometry`: an isometry of a nonempty compact
  pseudo-emetric space has topological entropy `0`.
* `TauCeti.coverEntropy_id_eq_zero`, `TauCeti.coverEntropy_addCircle_add_right_eq_zero`: the
  identity and the rotations of the circle have topological entropy `0`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped Uniformity ENNReal

variable {X : Type*} [UniformSpace X] {T : X → X} {F : Set X}

/-- If the iterates of `T` are uniformly equicontinuous and `F` is totally bounded, the minimal
dynamical covers of `F` at an entourage of `X` have bounded cardinality. -/
theorem exists_coverMincard_le_of_uniformEquicontinuous
    (hT : UniformEquicontinuous fun n : ℕ ↦ T^[n]) (hF : TotallyBounded F) {U : SetRel X X}
    (hU : U ∈ 𝓤 X) : ∃ b : ℕ, ∀ n, coverMincard T F U n ≤ b := by
  classical
  obtain ⟨t, ht, hFt⟩ := hF _ (hT U hU)
  refine ⟨ht.toFinset.card, fun n ↦ IsDynCoverOf.coverMincard_le_card fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hFt hx)
  exact ⟨y, by simpa using hy, mem_dynEntourage.2 fun k _ ↦ hxy k⟩

/-- If the iterates of `T` are uniformly equicontinuous, the cover entropy of `T` at an entourage
on a totally bounded set is at most `0`. -/
theorem coverEntropyEntourage_nonpos_of_uniformEquicontinuous
    (hT : UniformEquicontinuous fun n : ℕ ↦ T^[n]) (hF : TotallyBounded F) {U : SetRel X X}
    (hU : U ∈ 𝓤 X) : coverEntropyEntourage T F U ≤ 0 := by
  obtain ⟨b, hb⟩ := exists_coverMincard_le_of_uniformEquicontinuous hT hF hU
  calc coverEntropyEntourage T F U ≤ expGrowthSup fun _ ↦ (1 : ℝ≥0∞) :=
        expGrowthSup_le_of_eventually_le (b := b) (ENNReal.natCast_ne_top b)
          (Eventually.of_forall fun n ↦ by simpa using ENat.toENNReal_le.2 (hb n))
    _ = 0 := expGrowthSup_const one_ne_zero ENNReal.one_ne_top

/-- If the iterates of `T` are uniformly equicontinuous, the topological entropy of `T` on a
totally bounded set is at most `0`. It is `⊥` on the empty set. -/
theorem coverEntropy_nonpos_of_uniformEquicontinuous
    (hT : UniformEquicontinuous fun n : ℕ ↦ T^[n]) (hF : TotallyBounded F) :
    coverEntropy T F ≤ 0 :=
  iSup₂_le fun _ hU ↦ coverEntropyEntourage_nonpos_of_uniformEquicontinuous hT hF hU

/-- If the iterates of `T` are uniformly equicontinuous, the topological entropy of `T` on a
nonempty totally bounded set is `0`. -/
theorem coverEntropy_eq_zero_of_uniformEquicontinuous
    (hT : UniformEquicontinuous fun n : ℕ ↦ T^[n]) (hF : TotallyBounded F) (hne : F.Nonempty) :
    coverEntropy T F = 0 :=
  (coverEntropy_nonpos_of_uniformEquicontinuous hT hF).antisymm (coverEntropy_nonneg T hne)

/-- If the iterates of `T` are uniformly equicontinuous, the `liminf` topological entropy of `T`
on a nonempty totally bounded set is `0`. -/
theorem coverEntropyInf_eq_zero_of_uniformEquicontinuous
    (hT : UniformEquicontinuous fun n : ℕ ↦ T^[n]) (hF : TotallyBounded F) (hne : F.Nonempty) :
    coverEntropyInf T F = 0 :=
  ((coverEntropyInf_le_coverEntropy T F).trans
    (coverEntropy_nonpos_of_uniformEquicontinuous hT hF)).antisymm (coverEntropyInf_nonneg T hne)

/-- The iterates of an isometry are uniformly equicontinuous. -/
theorem uniformEquicontinuous_iterate_of_isometry {Y : Type*} [PseudoEMetricSpace Y]
    {S : Y → Y} (hS : Isometry S) : UniformEquicontinuous fun n : ℕ ↦ S^[n] := by
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := mem_uniformity_edist.1 hU
  filter_upwards [edist_mem_uniformity hε] with p hp n
  refine hεU ?_
  have hn : Isometry S^[n] := by
    induction n with
    | zero => exact isometry_id
    | succ n ih => rw [Function.iterate_succ]; exact ih.comp hS
  rw [hn.edist_eq]
  exact hp

/-- An isometry of a nonempty compact pseudo-emetric space has topological entropy `0`. -/
theorem coverEntropy_univ_eq_zero_of_isometry {Y : Type*} [PseudoEMetricSpace Y] [CompactSpace Y]
    [Nonempty Y] {S : Y → Y} (hS : Isometry S) : coverEntropy S univ = 0 :=
  coverEntropy_eq_zero_of_uniformEquicontinuous (uniformEquicontinuous_iterate_of_isometry hS)
    isCompact_univ.totallyBounded univ_nonempty

/-- The identity has topological entropy `0` on every nonempty totally bounded set. -/
theorem coverEntropy_id_eq_zero (hF : TotallyBounded F) (hne : F.Nonempty) :
    coverEntropy (id : X → X) F = 0 := by
  refine coverEntropy_eq_zero_of_uniformEquicontinuous (fun U hU ↦ ?_) hF hne
  filter_upwards [hU] with p hp n
  simpa using hp

/-- Every rotation `x ↦ x + a` of the circle `AddCircle p`, `p > 0`, has topological entropy
`0`. -/
theorem coverEntropy_addCircle_add_right_eq_zero {p : ℝ} [Fact (0 < p)] (a : AddCircle p) :
    coverEntropy (· + a) (univ : Set (AddCircle p)) = 0 :=
  coverEntropy_univ_eq_zero_of_isometry (IsometryEquiv.addRight a).isometry

end TauCeti
