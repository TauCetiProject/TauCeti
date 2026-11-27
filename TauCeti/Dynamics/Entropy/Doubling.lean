/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Analysis.Asymptotics.ExpGrowth
import Mathlib.Dynamics.TopologicalEntropy.Semiconj
import TauCeti.Analysis.Normed.Group.AddCircle
import TauCeti.Dynamics.Circle.BinaryExpansion
import TauCeti.Dynamics.Entropy.FullShift

/-!
# Topological entropy of the doubling map

The doubling map `x ↦ 2 • x` of `UnitAddCircle` has topological entropy `log 2`
(`TauCeti.coverEntropy_two_nsmul_unitAddCircle`).

* Upper bound: binary expansion `TauCeti.binaryExpansion` is a uniformly continuous surjection
  from the one-sided full shift on `Fin 2` onto the circle which semiconjugates the shift to the
  doubling map, so the entropy is at most that of the full shift, `log 2`
  (`TauCeti.coverEntropy_shift_nat`).
* Lower bound: the `2^n` points `j / 2^n`, the image of `ZMod.toAddCircle` on `ZMod (2^n)`, form
  a dynamical net at scale `1/8` and time `n`. For
  `d ≠ 0` with `2^n • d = 0`, some `2^k • d` with `k < n` has norm at least `1/4`
  (`AddCircle.exists_le_norm_two_pow_nsmul`), since doubling a point of norm less than `1/4`
  doubles its norm.

## Main results

* `TauCeti.coverEntropy_two_nsmul_unitAddCircle`,
  `TauCeti.coverEntropyInf_two_nsmul_unitAddCircle`: the doubling map has entropy `log 2`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal

/-- The discrete uniform structure on `Fin n`, whose topology is Mathlib's discrete topology on
`Fin n`. -/
private abbrev finUniformSpace (n : ℕ) : UniformSpace (Fin n) := ⊥

attribute [local instance] finUniformSpace

private lemma uniformContinuous_binaryExpansion : UniformContinuous binaryExpansion := by
  refine CompactSpace.uniformContinuous_of_continuous ?_
  -- The topology of the discrete uniformity on `Fin 2` is Mathlib's discrete topology on `Fin 2`,
  -- so `continuous_binaryExpansion` applies to the product of these topologies.
  have hFin : (finUniformSpace 2).toTopologicalSpace = instTopologicalSpaceFin :=
    UniformSpace.toTopologicalSpace_bot
  have h : @Continuous _ _
      (Pi.topologicalSpace (t₂ := fun _ ↦ (finUniformSpace 2).toTopologicalSpace)) _
      binaryExpansion := by
    rw [hFin]
    exact continuous_binaryExpansion
  exact h

/-- Distinct points `a / 2^n`, `b / 2^n` of the circle (images of `ZMod.toAddCircle`) are
`1/4`-separated by some iterate of the doubling map before time `n`. -/
private lemma exists_le_dist_toAddCircle {n : ℕ} {a b : ZMod (2 ^ n)} (hab : a ≠ b) :
    ∃ k < n, 1 / 4 ≤
      dist ((fun z : UnitAddCircle ↦ 2 • z)^[k] (ZMod.toAddCircle a))
        ((fun z : UnitAddCircle ↦ 2 • z)^[k] (ZMod.toAddCircle b)) := by
  have hd : ZMod.toAddCircle (a - b) ≠ 0 := by
    rwa [Ne, ZMod.toAddCircle_eq_zero, sub_eq_zero]
  have hn : 2 ^ n • ZMod.toAddCircle (a - b) = 0 := by
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  obtain ⟨k, hk, hle⟩ := AddCircle.exists_le_norm_two_pow_nsmul hd hn
  rw [abs_one] at hle
  refine ⟨k, hk, ?_⟩
  rwa [smul_iterate_apply, smul_iterate_apply, dist_eq_norm, ← smul_sub, ← map_sub]

/-- The `2^n` points `j / 2^n` of the circle form a dynamical net at scale `1/8` and time `n`. -/
private lemma pow_le_netMaxcard (n : ℕ) :
    (2 : ℕ∞) ^ n ≤ netMaxcard (fun z : UnitAddCircle ↦ 2 • z) univ
      {p | dist p.1 p.2 < 1 / 8} n := by
  classical
  let s : Finset UnitAddCircle := Finset.univ.image (ZMod.toAddCircle (N := 2 ^ n))
  have hcard : s.card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ (ZMod.toAddCircle_injective _), Finset.card_univ,
      ZMod.card]
  have hnet : IsDynNetIn (fun z : UnitAddCircle ↦ 2 • z) univ {p | dist p.1 p.2 < 1 / 8} n
      (s : Set UnitAddCircle) := by
    refine ⟨subset_univ _, ?_⟩
    rintro _ hx _ hy hxy
    simp only [s, Finset.coe_image, Finset.coe_univ, image_univ, mem_range] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hab : a ≠ b := fun h ↦ hxy (h ▸ rfl)
    obtain ⟨k, hk, hle⟩ := exists_le_dist_toAddCircle hab
    refine Set.disjoint_left.mpr fun z hza hzb ↦ ?_
    simp only [SetRel.mem_ball, SetRel.mem_inv, mem_dynEntourage, mem_ofPred_eq] at hza hzb
    have h1 := hza k hk
    have h2 := hzb k hk
    have := dist_triangle_left ((fun z : UnitAddCircle ↦ 2 • z)^[k] (ZMod.toAddCircle a))
      ((fun z : UnitAddCircle ↦ 2 • z)^[k] (ZMod.toAddCircle b))
      ((fun z : UnitAddCircle ↦ 2 • z)^[k] z)
    rw [dist_comm] at h1 h2
    linarith
  have := hnet.card_le_netMaxcard
  rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at this

/-- The doubling map of the circle has topological entropy at least `log 2`. -/
private lemma log_two_le_netEntropyInfEntourage :
    ENNReal.log 2 ≤ netEntropyInfEntourage (fun z : UnitAddCircle ↦ 2 • z) univ
      {p | dist p.1 p.2 < 1 / 8} := by
  rw [← expGrowthInf_pow]
  exact expGrowthInf_monotone fun n ↦ by
    simpa using ENat.toENNReal_le.2 (pow_le_netMaxcard n)

private lemma mem_uniformity_dist_lt_eighth :
    {p : UnitAddCircle × UnitAddCircle | dist p.1 p.2 < 1 / 8} ∈ uniformity UnitAddCircle :=
  Metric.dist_mem_uniformity (by norm_num)

/-- **Check.** The doubling map `x ↦ 2 • x` of the circle has topological entropy `log 2`. -/
theorem coverEntropy_two_nsmul_unitAddCircle :
    coverEntropy (fun z : UnitAddCircle ↦ 2 • z) univ = ENNReal.log 2 := by
  refine le_antisymm ?_ ?_
  · calc coverEntropy (fun z : UnitAddCircle ↦ 2 • z) univ =
          coverEntropy (fun z : UnitAddCircle ↦ 2 • z) (binaryExpansion '' univ) := by
          rw [image_univ, surjective_binaryExpansion.range_eq]
      _ ≤ coverEntropy (SymbolicDynamics.FullShift.shift (1 : ℕ)) (univ : Set (ℕ → Fin 2)) :=
          coverEntropy_image_le_of_uniformContinuous semiconj_binaryExpansion
            uniformContinuous_binaryExpansion univ
      _ = ENNReal.log 2 := by rw [coverEntropy_shift_nat, Fintype.card_fin, Nat.cast_ofNat]
  · exact log_two_le_netEntropyInfEntourage.trans <|
      (netEntropyInfEntourage_le_coverEntropyInf _ _ mem_uniformity_dist_lt_eighth).trans
        (coverEntropyInf_le_coverEntropy _ _)

/-- **Check.** The `liminf` topological entropy of the doubling map of the circle is `log 2`. -/
theorem coverEntropyInf_two_nsmul_unitAddCircle :
    coverEntropyInf (fun z : UnitAddCircle ↦ 2 • z) univ = ENNReal.log 2 :=
  (coverEntropyInf_eq_coverEntropy _ (mapsTo_univ _ _)).trans coverEntropy_two_nsmul_unitAddCircle

end TauCeti
