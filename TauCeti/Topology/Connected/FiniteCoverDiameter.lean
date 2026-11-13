/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Oscillation and diameter bounds from finite covers

For a continuous function on a preconnected space, a finite cover with uniformly bounded
oscillation bounds the total oscillation by the number of covering sets times that bound.
The cover sets need not be open. In a preconnected pseudometric space, a finite cover by
sets of bounded diameter gives the corresponding global distance bound. In particular,
the covering sets can be preimages of ambient balls under an arbitrary map.

## References

* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Function

/-- A continuous function on a preconnected space has total oscillation at most
the number of covering sets times their uniform oscillation bound. -/
theorem Continuous.sub_le_nat_card_mul_of_finite_cover
    {X ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace X] [PreconnectedSpace X] [Finite ι]
    {h : X → 𝕜} (hh : Continuous h) (U : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ U i) {D : 𝕜}
    (hosc : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, |h x - h y| ≤ D)
    (x y : X) : h y - h x ≤ Nat.card ι * D := by
  classical
  -- Choose one point on each of `N + 1` equally spaced intermediate levels.
  let N := Nat.card ι
  obtain ⟨i₀, hi₀⟩ := hcover x
  have hD : 0 ≤ D := by simpa using hosc i₀ x hi₀ x hi₀
  let : Nonempty ι := ⟨i₀⟩
  have hN : 0 < N := Nat.card_pos
  have hNr : (0 : 𝕜) < N := by exact_mod_cast hN
  by_contra! hlarge
  let r := (h y - h x) / N
  have hrD : D < r := by
    apply (lt_div_iff₀ hNr).mpr
    simpa only [mul_comm] using hlarge
  have hr : 0 < r := hD.trans_lt hrD
  have hNr_eq : (N : 𝕜) * r = h y - h x := by dsimp only [r]; field_simp
  have hpoints (i : Fin (N + 1)) : ∃ z : X, h z = h x + (i.val : 𝕜) * r := by
    have hi : (i.val : 𝕜) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have himem : h x + (i.val : 𝕜) * r ∈ Icc (h x) (h y) := by
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hr.le)
      · nlinarith
    obtain ⟨z, _, hz⟩ := isPreconnected_univ.intermediate_value
      (mem_univ x) (mem_univ y) hh.continuousOn himem
    exact ⟨z, hz⟩
  choose z hz using hpoints
  choose index hindex using fun i ↦ hcover (z i)
  -- Two levels cannot lie in the same covering set, contradicting its cardinality.
  have hne (i j : Fin (N + 1)) (hlt : i.val < j.val) : index i ≠ index j := by
    intro hij
    have hosc' := hosc (index j) (z i) (hij ▸ hindex i) (z j) (hindex j)
    rw [hz i, hz j] at hosc'
    have hstep : (i.val : 𝕜) + 1 ≤ j.val := by exact_mod_cast hlt
    have hdiff : 0 ≤ h x + (j.val : 𝕜) * r - (h x + (i.val : 𝕜) * r) := by
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg hdiff] at hosc'
    nlinarith
  have hinj : Injective index := by
    intro i j hij
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact (hne i j hlt hij).elim
    · exact Fin.ext heq
    · exact (hne j i hgt hij.symm).elim
  have hcard := Nat.card_le_card_of_injective index hinj
  rw [Nat.card_fin] at hcard
  omega

/-- A finite cover of a preconnected pseudometric space by sets of diameter at most `D`
bounds every distance by the number of covering sets times `D`. -/
theorem TauCeti.dist_le_nat_card_mul_of_finite_cover
    {X ι : Type*} [PseudoMetricSpace X] [PreconnectedSpace X] [Finite ι]
    (U : ι → Set X) (hcover : ∀ x, ∃ i, x ∈ U i) {D : ℝ}
    (hlocal : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, dist x y ≤ D)
    (x y : X) : dist x y ≤ Nat.card ι * D := by
  have hosc : ∀ i, ∀ z ∈ U i, ∀ w ∈ U i, |dist x z - dist x w| ≤ D := by
    intro i z hz w hw
    have hrev : |dist x z - dist x w| ≤ dist z w := by
      simpa only [dist_comm] using abs_dist_sub_le z w x
    exact hrev.trans (hlocal i z hz w hw)
  have h := Continuous.sub_le_nat_card_mul_of_finite_cover (h := dist x)
    (continuous_const.dist continuous_id) U hcover hosc x y
  simpa only [dist_self, sub_zero] using h

/-- If the preimages of the balls `ball (q i) r` cover `X` and any two points in the
same preimage are within `D` of each other, then any two points of `X` are within
`Nat.card ι * D`. No continuity of the map `f` is required. -/
theorem TauCeti.dist_le_nat_card_mul_of_image_ball_cover
    {X Y ι : Type*} [PseudoMetricSpace X] [PreconnectedSpace X]
    [PseudoMetricSpace Y] [Finite ι]
    (f : X → Y) (q : ι → Y) {r D : ℝ}
    (hcover : ∀ x : X, ∃ i, dist (f x) (q i) < r)
    (hlocal : ∀ i, ∀ x ∈ f ⁻¹' Metric.ball (q i) r,
      ∀ y ∈ f ⁻¹' Metric.ball (q i) r, dist x y ≤ D)
    (x y : X) : dist x y ≤ Nat.card ι * D :=
  TauCeti.dist_le_nat_card_mul_of_finite_cover
    (fun i ↦ f ⁻¹' Metric.ball (q i) r) hcover hlocal x y
