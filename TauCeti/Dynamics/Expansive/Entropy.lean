/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import TauCeti.Analysis.Asymptotics.ExpGrowth
public import TauCeti.Dynamics.Expansive.FiniteWindow

/-!
# Topological entropy of expansive maps

An expansive homeomorphism `T` of a compact metric space, with expansive constant `δ`, has finite
topological entropy, and its entropy is computed at any single scale `0 < ε ≤ δ`: it is the growth
rate of the largest `(n, ε)`-separated sets (in Mathlib's form, dynamical nets for the closed
entourage `{p | dist p.1 p.2 ≤ ε}`). The same holds for positively expansive continuous maps.

The proof compares scales through the finite-window form of expansiveness
(`TauCeti.IsExpansive.exists_window`): for `η > 0` there is `N` such that points `ε`-close at all
times `|i| ≤ N` are `η`-close. Shifting a dynamical net for `{dist < η}` of length `n` back by
`T ^ N` gives a dynamical net for `{dist ≤ ε}` of length `n + 2 N`
(`TauCeti.netMaxcard_le_netMaxcard_add_of_window`), and a shift of the time does not change the
exponential growth rate (`Monotone.expGrowthSup_comp_add`).

## Main results

* `TauCeti.IsExpansive.coverEntropy_eq_netEntropyEntourage`: for an expansive homeomorphism and
  `0 < ε ≤ δ`, `coverEntropy T univ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε}`;
* `TauCeti.IsExpansive.coverEntropy_lt_top`: an expansive homeomorphism has finite entropy;
* `TauCeti.IsPositivelyExpansive.coverEntropy_eq_netEntropyEntourage`,
  `TauCeti.IsPositivelyExpansive.coverEntropy_lt_top`: the same for positively expansive maps.
-/

public section

namespace TauCeti

open Dynamics ExpGrowth Filter Set
open scoped ENNReal Uniformity

variable {X : Type*}

/-- **Comparison of scales through a two-sided window.** Let `T` be a permutation and `U`, `V`
relations such that a pair is `U`-related as soon as its images under `T ^ i` are `V`-related for
all `|i| ≤ N`. Then a `(U, n)`-dynamical net of the whole space is carried by `T ^ (-N)` to a
`(V, n + 2 N)`-dynamical net, so `netMaxcard T univ U n ≤ netMaxcard T univ V (n + 2 N)`. -/
theorem netMaxcard_le_netMaxcard_add_of_window (T : Equiv.Perm X) {U V : SetRel X X} {N : ℕ}
    (hwin : ∀ x y, (∀ i : ℤ, |i| ≤ N → ((T ^ i) x, (T ^ i) y) ∈ V) → (x, y) ∈ U) (n : ℕ) :
    netMaxcard T univ U n ≤ netMaxcard T univ V (n + 2 * N) := by
  classical
  refine iSup₂_le fun s hs ↦ ?_
  have hinj : Function.Injective (T ^ (-(N : ℤ))) := Equiv.injective _
  rw [← Finset.card_image_of_injective s hinj]
  refine IsDynNetIn.card_le_netMaxcard ⟨subset_univ _, ?_⟩
  -- iterates of `T` are powers of `T`
  have hit (k : ℕ) (x : X) : T^[k] x = (T ^ (k : ℤ)) x := by
    rw [zpow_natCast, Equiv.Perm.iterate_eq_pow]
  intro a ha b hb hab
  simp only [Finset.coe_image, mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxy : x ≠ y := fun h ↦ hab (h ▸ rfl)
  refine Set.disjoint_left.2 fun z hzx hzy ↦ ?_
  -- the point `w = T ^ N z` lies in the `(U, n)`-balls of both `x` and `y`
  have key : ∀ x, z ∈ (dynEntourage T V (n + 2 * N)).inv.ball ((T ^ (-(N : ℤ))) x) →
      (T ^ (N : ℤ)) z ∈ (dynEntourage T U n).inv.ball x := by
    intro x hz
    simp only [SetRel.mem_ball, SetRel.mem_inv, mem_dynEntourage] at hz ⊢
    intro j hj
    refine hwin _ _ fun i hi ↦ ?_
    have hk : 0 ≤ i + j + N := by
      have := neg_abs_le i
      omega
    obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
    have hkn : k < n + 2 * N := by
      have := le_abs_self i
      omega
    have h := hz k hkn
    rw [hit, hit] at h
    rw [hit, hit]
    have e₁ : (T ^ i) ((T ^ (j : ℤ)) x) = (T ^ (k : ℤ)) ((T ^ (-(N : ℤ))) x) := by
      simp only [← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    have e₂ : (T ^ i) ((T ^ (j : ℤ)) ((T ^ (N : ℤ)) z)) = (T ^ (k : ℤ)) z := by
      simp only [← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    rwa [e₁, e₂]
  exact hs.2 hx hy hxy |>.ne_of_mem (key x hzx) (key y hzy) rfl

/-- **Comparison of scales through a forward window.** Let `T` be a map and `U`, `V` relations
such that a pair is `U`-related as soon as its images under `T^[i]` are `V`-related for all
`i ≤ N`. Then every `(U, n)`-dynamical net is a `(V, n + N)`-dynamical net, so
`netMaxcard T F U n ≤ netMaxcard T F V (n + N)`. -/
theorem netMaxcard_le_netMaxcard_add_of_forward_window (T : X → X) (F : Set X)
    {U V : SetRel X X} {N : ℕ}
    (hwin : ∀ x y, (∀ i ≤ N, (T^[i] x, T^[i] y) ∈ V) → (x, y) ∈ U) (n : ℕ) :
    netMaxcard T F U n ≤ netMaxcard T F V (n + N) := by
  refine iSup₂_le fun s hs ↦ IsDynNetIn.card_le_netMaxcard ⟨hs.1, fun x hx y hy hxy ↦ ?_⟩
  refine Set.disjoint_left.2 fun z hzx hzy ↦ ?_
  have key : ∀ x, z ∈ (dynEntourage T V (n + N)).inv.ball x →
      z ∈ (dynEntourage T U n).inv.ball x := by
    intro x hz
    simp only [SetRel.mem_ball, SetRel.mem_inv, mem_dynEntourage] at hz ⊢
    intro j hj
    refine hwin _ _ fun i hi ↦ ?_
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
    exact hz _ (by omega)
  exact (hs.2 hx hy hxy).ne_of_mem (key x hzx) (key y hzy) rfl

variable [PseudoMetricSpace X] [CompactSpace X]

/-- **Entropy of an expansive homeomorphism at a single scale.** If `T` is an expansive
homeomorphism of a compact metric space with constant `δ`, then for every `0 < ε ≤ δ` its
topological entropy is the growth rate of the largest dynamical nets for the closed entourage
`{p | dist p.1 p.2 ≤ ε}`. -/
theorem IsExpansive.coverEntropy_eq_netEntropyEntourage {T : Equiv.Perm X} {δ ε : ℝ}
    (h : IsExpansive T δ) (hT : Continuous T) (hT' : Continuous T.symm) (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    coverEntropy T univ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε} := by
  have hV : {p : X × X | dist p.1 p.2 ≤ ε} ∈ 𝓤 X := Metric.uniformity_basis_dist_le.mem_of_mem hε
  refine le_antisymm ?_ ((netEntropyEntourage_le_coverEntropy T univ hV))
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage Metric.uniformity_basis_dist T univ]
  refine iSup₂_le fun η hη ↦ ?_
  obtain ⟨N, hN⟩ := (h.mono hεδ).exists_window hT hT' hη
  calc netEntropyEntourage T univ {p | dist p.1 p.2 < η}
      ≤ expGrowthSup fun n ↦ (netMaxcard T univ {p | dist p.1 p.2 ≤ ε} (n + 2 * N) : ℝ≥0∞) :=
        expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono
          (netMaxcard_le_netMaxcard_add_of_window T hN n)
    _ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε} :=
        (ENat.toENNReal_mono.comp (netMaxcard_monotone_time T univ _)).expGrowthSup_comp_add _

/-- **Expansive homeomorphisms have finite entropy.** An expansive homeomorphism of a compact
metric space with a positive expansive constant has finite topological entropy. -/
theorem IsExpansive.coverEntropy_lt_top {T : Equiv.Perm X} {δ : ℝ} (h : IsExpansive T δ)
    (hT : Continuous T) (hT' : Continuous T.symm) (hδ : 0 < δ) :
    coverEntropy T univ < ⊤ := by
  rw [h.coverEntropy_eq_netEntropyEntourage hT hT' hδ le_rfl]
  exact (netEntropyEntourage_le_coverEntropyEntourage T univ).trans_lt
    (coverEntropyEntourage_finite_of_isCompact_invariant isCompact_univ (mapsTo_univ _ _)
      (Metric.uniformity_basis_dist_le.mem_of_mem hδ))

/-- **Entropy of a positively expansive map at a single scale.** If a continuous map `T` of a
compact metric space is positively expansive with constant `δ`, then for every `0 < ε ≤ δ` its
topological entropy is the growth rate of the largest dynamical nets for the closed entourage
`{p | dist p.1 p.2 ≤ ε}`. -/
theorem IsPositivelyExpansive.coverEntropy_eq_netEntropyEntourage {T : X → X} {δ ε : ℝ}
    (h : IsPositivelyExpansive T δ) (hT : Continuous T) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    coverEntropy T univ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε} := by
  have hV : {p : X × X | dist p.1 p.2 ≤ ε} ∈ 𝓤 X := Metric.uniformity_basis_dist_le.mem_of_mem hε
  refine le_antisymm ?_ ((netEntropyEntourage_le_coverEntropy T univ hV))
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage Metric.uniformity_basis_dist T univ]
  refine iSup₂_le fun η hη ↦ ?_
  obtain ⟨N, hN⟩ := (h.mono hεδ).exists_window hT hη
  calc netEntropyEntourage T univ {p | dist p.1 p.2 < η}
      ≤ expGrowthSup fun n ↦ (netMaxcard T univ {p | dist p.1 p.2 ≤ ε} (n + N) : ℝ≥0∞) :=
        expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono
          (netMaxcard_le_netMaxcard_add_of_forward_window T univ hN n)
    _ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε} :=
        (ENat.toENNReal_mono.comp (netMaxcard_monotone_time T univ _)).expGrowthSup_comp_add _

/-- **Positively expansive maps have finite entropy.** A continuous positively expansive map of a
compact metric space with a positive expansive constant has finite topological entropy. -/
theorem IsPositivelyExpansive.coverEntropy_lt_top {T : X → X} {δ : ℝ}
    (h : IsPositivelyExpansive T δ) (hT : Continuous T) (hδ : 0 < δ) :
    coverEntropy T univ < ⊤ := by
  rw [h.coverEntropy_eq_netEntropyEntourage hT hδ le_rfl]
  exact (netEntropyEntourage_le_coverEntropyEntourage T univ).trans_lt
    (coverEntropyEntourage_finite_of_isCompact_invariant isCompact_univ (mapsTo_univ _ _)
      (Metric.uniformity_basis_dist_le.mem_of_mem hδ))

end TauCeti
