/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup
public import TauCeti.Topology.MetricSpace.Lipschitz.Parametrizable

/-!
# Counting points of a discrete subgroup near a dilated Lipschitz-parametrizable set

Let `L` be a discrete additive subgroup of a proper normed real vector space `E`, and let `S ⊆ E` be
Lipschitz parametrizable in dimension `d`, that is, covered by finitely many Lipschitz images of
the unit `d`-cube.  Dilating `S` by a factor `c ≥ 1` and thickening it by a fixed bounded set `B`
produces a region that carries `O(c ^ d)` points of `L`.

This is the quantitative half of Lipschitz parametrizability.  When `d` is strictly smaller than
the ambient dimension, as in the codimension-one boundary application, it is a genuinely smaller
order than the `c ^ (dim E)` points carried by a dilated body and hence gives a power-saving error
term in a lattice-point count.  The thickening by `B` is what the application needs: the lattice
cells `x + F` that meet a dilated region `c • S` are exactly the `x ∈ L` lying in
`c • S + (-F)`, so a count of cells meeting the boundary of a dilated body is a count of the
points of `L` in such a region.

The proof subdivides the unit cube into `m ^ d` subcubes of side `1 / m`, with `m` of size
`c`, so that each chart maps a subcube into a set of diameter at most one after dilating by `c`.
Translation invariance bounds the number of points of `L` in any set of bounded diameter by a
constant, so the total count is at most a constant times the number `m ^ d` of subcubes.

## Main results

* `TauCeti.IsLipschitzParametrizable.finite_smul_add_inter`: a bounded thickening of a dilated
  Lipschitz-parametrizable set meets a discrete subgroup in a finite set.
* `TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le`: the explicit bound
  `#((c • S + B) ∩ L) ≤ A * c ^ d` for `c ≥ 1`, with `A` independent of `c`.
* `TauCeti.IsLipschitzParametrizable.isBigO_ncard_smul_add_inter`: the same bound as an
  asymptotic statement, `#((c • S + B) ∩ L) = O(c ^ d)` as `c → ∞`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
-/

public section

open Asymptotics Bornology Filter Metric Set
open scoped Pointwise Topology

namespace TauCeti.IsLipschitzParametrizable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A bounded thickening of a dilated Lipschitz-parametrizable set meets a discrete subgroup in a
finite set. -/
theorem finite_smul_add_inter {d : ℕ} {S : Set E}
    (hS : IsLipschitzParametrizable d S) (L : AddSubgroup E) [DiscreteTopology L]
    {B : Set E} (hB : IsBounded B) (c : ℝ) :
    ((c • S + B) ∩ (L : Set E)).Finite := by
  obtain ⟨n, C, f, hf, hcov⟩ := isLipschitzParametrizable_iff.1 hS
  apply L.finite_inter
  apply isBounded_add
  · exact ((Bornology.isBounded_iUnion.2 fun i ↦
      ((isCompact_Icc.image_of_continuousOn (hf i).continuousOn).isBounded)).subset hcov).smul₀ c
  · exact hB

omit [ProperSpace E] in
/-- Dilating a set `T` of diameter at most `C / m` by `c` with `c * C / m ≤ 1` and adding a set of
points within `r` of the origin gives a set of diameter at most `1 + 2 * r`. -/
private theorem dist_smul_add_le {T B : Set E} {c C r : ℝ} {m : ℕ} (hc : 0 ≤ c)
    (hcm : c * C / m ≤ 1) (hT : ∀ w ∈ T, ∀ w' ∈ T, dist w w' ≤ C / m)
    (hrB : ∀ x ∈ B, dist x 0 ≤ r) :
    ∀ u ∈ c • T + B, ∀ v ∈ c • T + B, dist u v ≤ 1 + 2 * r := by
  intro u hu v hv
  rw [Set.mem_add] at hu hv
  obtain ⟨a, ⟨w, hw, rfl⟩, b, hb, rfl⟩ := hu
  obtain ⟨a', ⟨w', hw', rfl⟩, b', hb', rfl⟩ := hv
  have hchart : dist (c • w) (c • w') ≤ 1 := by
    rw [dist_smul₀, Real.norm_of_nonneg hc]
    calc c * dist w w' ≤ c * (C / m) := by gcongr; exact hT w hw w' hw'
      _ = c * C / m := by ring
      _ ≤ 1 := hcm
  calc dist (c • w + b) (c • w' + b')
      ≤ dist (c • w) (c • w') + dist b b' := dist_add_add_le _ _ _ _
    _ ≤ 1 + (dist b 0 + dist 0 b') := by gcongr; exact dist_triangle _ _ _
    _ ≤ 1 + (r + r) := by
        gcongr
        exacts [hrB b hb, dist_comm (0 : E) b' ▸ hrB b' hb']
    _ = 1 + 2 * r := by ring

/-- There is a number `m` of pieces, positive, with `c * C / m ≤ 1` and `m ≤ c * (C + 2)` when
`1 ≤ c`. -/
private theorem exists_nat_pieces {c C : ℝ} (hc : 1 ≤ c) (hC : 0 ≤ C) :
    ∃ m : ℕ, 0 < m ∧ c * C / m ≤ 1 ∧ (m : ℝ) ≤ c * (C + 2) := by
  have h₀ := Nat.le_ceil (c * C)
  have h₁ : ((⌈c * C⌉₊ : ℕ) : ℝ) < c * C + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine ⟨⌈c * C⌉₊ + 1, Nat.succ_pos _, ?_, ?_⟩
  · refine (div_le_one (by positivity)).2 ?_
    push_cast
    linarith
  · push_cast
    nlinarith

/-- **The boundary count.**  If `S` is Lipschitz parametrizable in dimension `d` and `B` is
bounded, then for `c ≥ 1` the thickened dilate `c • S + B` contains at most `A * c ^ d` points of
a discrete subgroup `L`, with the constant `A` independent of `c`.

With `B = -F` for a bounded fundamental domain `F` of `L`, the left-hand side counts the cells of
`L` that meet `c • S`; taking `S` to be the frontier of a body and `d` its codimension-one
parametrization dimension is what produces a power-saving error in a lattice-point count. -/
theorem exists_ncard_smul_add_inter_le {d : ℕ} {S : Set E}
    (hS : IsLipschitzParametrizable d S) (L : AddSubgroup E) [DiscreteTopology L]
    {B : Set E} (hB : IsBounded B) :
    ∃ A ≥ (0 : ℝ), ∀ c : ℝ, 1 ≤ c →
      (((c • S + B) ∩ (L : Set E)).ncard : ℝ) ≤ A * c ^ d := by
  obtain ⟨n, C, f, hf, hcov⟩ := isLipschitzParametrizable_iff.1 hS
  obtain ⟨r, hr⟩ := hB.subset_closedBall 0
  have hrB : ∀ x ∈ B, dist x 0 ≤ r := fun x hx ↦ mem_closedBall.1 (hr hx)
  set N : ℕ := (closedBall (0 : E) (1 + 2 * r) ∩ (L : Set E)).ncard
  refine ⟨n * ((C : ℝ) + 2) ^ d * N, by positivity, fun c hc ↦ ?_⟩
  -- Cut each edge of the unit cube into `m` pieces, so that each of the `m ^ d` subcubes has
  -- image of diameter at most `c * C / m ≤ 1` after dilating by `c`.
  obtain ⟨m, hm0, hcm, hmc⟩ := exists_nat_pieces hc C.2
  choose T hTcov hTdist using fun i ↦ (hf i).exists_cover_image_unitCube hm0
  -- The thickened dilates of the pieces cover `c • S + B`.
  have hPcov : c • S + B ⊆ ⋃ p : Fin n × (Fin d → Fin m), c • T p.1 p.2 + B := by
    rintro u hu
    rw [Set.mem_add] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := hu
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hs)
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hTcov i hi)
    exact mem_iUnion.2 ⟨(i, k), Set.mem_add.2
      ⟨c • s, Set.smul_mem_smul_set hk, b, hb, rfl⟩⟩
  have hcount := L.ncard_inter_le_card_mul_ncard_closedBall_inter _ hPcov fun p ↦
    dist_smul_add_le (one_pos.trans_le hc).le hcm (hTdist p.1 p.2) hrB
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Finset.prod_const,
    Finset.card_univ] at hcount
  calc (((c • S + B) ∩ (L : Set E)).ncard : ℝ)
      ≤ ((n * m ^ d * N : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = (n : ℝ) * (m : ℝ) ^ d * N := by push_cast; ring
    _ ≤ (n : ℝ) * (c * ((C : ℝ) + 2)) ^ d * N := by gcongr; exact hmc
    _ = (n * ((C : ℝ) + 2) ^ d * N) * c ^ d := by rw [mul_pow]; ring

/-- The boundary count as an asymptotic statement: if `S` is Lipschitz parametrizable in
dimension `d` and `B` is bounded, the number of points of a discrete subgroup `L` in the
thickened dilate `c • S + B` is `O(c ^ d)` as `c → ∞`. -/
theorem isBigO_ncard_smul_add_inter {d : ℕ} {S : Set E}
    (hS : IsLipschitzParametrizable d S) (L : AddSubgroup E) [DiscreteTopology L]
    {B : Set E} (hB : IsBounded B) :
    (fun c : ℝ ↦ (((c • S + B) ∩ (L : Set E)).ncard : ℝ)) =O[atTop] fun c : ℝ ↦ c ^ d := by
  obtain ⟨A, -, hA⟩ := hS.exists_ncard_smul_add_inter_le L hB
  refine isBigO_iff.2 ⟨A, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) d)]
  exact hA c hc

end TauCeti.IsLipschitzParametrizable
