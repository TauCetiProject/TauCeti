/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Basic
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.Valuation.RootMonic
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Continuity of valuations over the invariants of a finite group

Let a finite group `G` act on a topological ring `A` by continuous ring automorphisms, and let
`R → A` be an inducing ring map whose image contains every invariant (`Algebra.IsInvariant R A G`),
for instance the inclusion of the fixed subring `Aᴳ` with the subspace topology. This file shows
that a valuation `v` on `A` is continuous as soon as its restriction to `R` is
(`Valuation.isContinuous_of_isContinuous_comap_of_isInvariant`). Nothing is assumed about the
order of `G` or the characteristic of `A`.

Each `x ∈ A` is a root of its orbit polynomial `∏_{g ∈ G} (X - g • x)`, of degree `n = #G`, whose
coefficients are invariant, so come from `R`, and depend continuously on `x`. Fix `a` with
`v a ≠ 0`. A lower bound for `v a` by values on `R` comes from the orbit polynomial of `a`: for
two of its coefficients `c = ι r` and `d = ι s` and some `k ≥ 1`, `0 ≠ v c ≤ v d * v a ^ k`
(`Valuation.exists_map_coeff_le_mul_pow_of_root`). If `v a ≤ v x`, then some coefficient `e` of
the orbit polynomial of `x` has `v x ^ (n - l) ≤ v e` for some `l < n`
(`Valuation.exists_pow_le_map_coeff_of_root_monic`), hence
`v c ^ (n - l) ≤ v (e ^ k * d ^ (n - l))`. Continuity of the restriction to `R` makes the reverse
strict inequality an open condition on `x`, true at `x = 0`, so `{x | v x < v a}` contains a
neighbourhood of `0`, and hence is open.

## Main results

* `Valuation.isContinuous_of_isContinuous_comap_of_isInvariant`: a valuation on `A` whose
  restriction to the invariants is continuous is continuous.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), proof of
  Theorem 3.1, Step 1, on continuous valuations of `A` and of `Aᴳ`.
-/

public section

open Polynomial Topology

namespace Valuation

section Charpoly

variable {A : Type*} [CommRing A] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- If `v c ≤ v d * v a ^ k` and `v a ≤ v x`, then some coefficient `e` of index `l < #G` of the
orbit polynomial of `x` has `v c ^ (#G - l) ≤ v e ^ k * v d ^ (#G - l)`. -/
private theorem exists_pow_le_map_coeff_charpoly {v : Valuation A Γ₀} {a c d x : A} {k : ℕ}
    (hle : v c ≤ v d * v a ^ k) (hax : v a ≤ v x) :
    ∃ l < Fintype.card G, v c ^ (Fintype.card G - l) ≤
      v ((MulSemiringAction.charpoly G x).coeff l) ^ k * v d ^ (Fintype.card G - l) := by
  have : Nontrivial A := ⟨0, 1, fun h ↦ (zero_ne_one : (0 : Γ₀) ≠ 1) (by simpa using congrArg v h)⟩
  obtain ⟨l, hl, hxl⟩ := v.exists_pow_le_map_coeff_of_root_monic
    (MulSemiringAction.monic_charpoly G x) (MulSemiringAction.eval_charpoly G x)
  rw [TauCeti.MulSemiringAction.natDegree_charpoly] at hl hxl
  refine ⟨l, hl, ?_⟩
  calc v c ^ (Fintype.card G - l) ≤ (v d * v a ^ k) ^ (Fintype.card G - l) := by gcongr
    _ = (v a ^ (Fintype.card G - l)) ^ k * v d ^ (Fintype.card G - l) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm]
    _ ≤ (v x ^ (Fintype.card G - l)) ^ k * v d ^ (Fintype.card G - l) := by gcongr
    _ ≤ v ((MulSemiringAction.charpoly G x).coeff l) ^ k * v d ^ (Fintype.card G - l) := by
        gcongr

end Charpoly

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace R]
  [TopologicalSpace A] [IsTopologicalRing A] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G A] [ContinuousConstSMul G A] [Algebra.IsInvariant R A G]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

include G in
/-- If the restriction of `v` to the invariants is continuous, then `{x | v x < v a}` is a
neighbourhood of `0` for every `a` with `v a ≠ 0`. -/
private theorem setOf_lt_mem_nhds_zero (hι : Topology.IsInducing (algebraMap R A))
    {v : Valuation A Γ₀} (hv : (v.comap (algebraMap R A)).IsContinuous) {a : A} (ha : v a ≠ 0) :
    {x | v x < v a} ∈ 𝓝 (0 : A) := by
  classical
  cases nonempty_fintype G
  set ι := algebraMap R A
  set P : A → A[X] := MulSemiringAction.charpoly G
  set n := Fintype.card G
  -- the coefficients of the orbit polynomial `P x` come from `R` and are continuous in `x`
  have hcoeff (x : A) (l : ℕ) : ∃ r : R, ι r = (P x).coeff l :=
    Algebra.IsInvariant.isInvariant _ (MulSemiringAction.smul_coeff_charpoly x l)
  have hcont (l : ℕ) : Continuous fun x ↦ (P x).coeff l := by
    simp_rw [P, MulSemiringAction.charpoly_eq]
    exact (TauCeti.Polynomial.continuous_coeff_prod_X_sub_C _ l).comp
      (continuous_pi fun g ↦ continuous_const_smul g)
  have hzero {l : ℕ} (hl : l < n) : (P 0).coeff l = 0 := by
    simp [P, MulSemiringAction.charpoly_eq, coeff_X_pow, hl.ne, n]
  -- continuity on `R`: each `{s | v (ι s) < v (ι r)}` is cut out by an open subset of `A`
  have hopen (r : R) : ∃ O : Set A, IsOpen O ∧ ι ⁻¹' O = {s | v (ι s) < v (ι r)} :=
    hι.isOpen_iff.mp (by simpa using isContinuous_def.mp hv r)
  choose O hO hpre using hopen
  -- a lower bound `0 ≠ v c ≤ v d * v a ^ k` with `c`, `d` coming from `R` and `k ≥ 1`
  obtain ⟨i, j, hij, hi, hle⟩ := v.exists_map_coeff_le_mul_pow_of_root
    (MulSemiringAction.eval_charpoly G a) ha
    ⟨_, by rw [(MulSemiringAction.monic_charpoly G a).coeff_natDegree, map_one]; exact one_ne_zero⟩
  obtain ⟨rc, hrc⟩ := hcoeff a i
  obtain ⟨rd, hrd⟩ := hcoeff a j
  set k := j - i
  have hk : k ≠ 0 := Nat.sub_ne_zero_of_lt hij
  -- the open set `U` on which `v (e ^ k * d ^ (n - l)) < v c ^ (n - l)` for the coefficients `e`
  -- of index `l < n`, which contains `0`
  set U := ⋂ l ∈ Finset.range n,
    (fun x ↦ (P x).coeff l ^ k * (P a).coeff j ^ (n - l)) ⁻¹' O (rc ^ (n - l))
  have hUo : IsOpen U :=
    isOpen_biInter_finset fun l _ ↦ (hO _).preimage (((hcont l).pow k).mul continuous_const)
  have h0U : (0 : A) ∈ U := by
    refine Set.mem_iInter₂.mpr fun l hl ↦ ?_
    have h0 : (0 : R) ∈ ι ⁻¹' O (rc ^ (n - l)) := by
      rw [hpre, Set.mem_ofPred_eq, map_zero, map_zero, map_pow, map_pow, hrc]
      exact pos_iff_ne_zero.mpr (pow_ne_zero _ hi)
    simpa [hzero (Finset.mem_range.mp hl), zero_pow hk] using h0
  -- on `U`, `v x < v a`: otherwise the upper bound for `v x` contradicts the lower one for `v a`
  refine Filter.mem_of_superset (hUo.mem_nhds h0U) fun x hx ↦ not_le.mp fun hax ↦ ?_
  obtain ⟨l, hl, hle'⟩ := exists_pow_le_map_coeff_charpoly G hle hax
  obtain ⟨s, hs⟩ := hcoeff x l
  have hmem : ι (s ^ k * rd ^ (n - l)) ∈ O (rc ^ (n - l)) := by
    rw [map_mul, map_pow, map_pow, hs, hrd]
    exact Set.mem_iInter₂.mp hx l (Finset.mem_range.mpr hl)
  rw [← Set.mem_preimage, hpre, Set.mem_ofPred_eq] at hmem
  simp only [map_mul, map_pow, hs, hrd, hrc] at hmem
  exact hmem.not_ge hle'

include G in
/-- **A valuation is continuous when its restriction to the invariants is.** Let a finite group
`G` act on a topological ring `A` by continuous ring automorphisms, and let `R → A` be an
inducing ring map such that every `G`-invariant element of `A` comes from `R`. If the restriction
of a valuation `v` on `A` to `R` is continuous, then `v` is continuous. -/
theorem isContinuous_of_isContinuous_comap_of_isInvariant
    (hι : Topology.IsInducing (algebraMap R A)) {v : Valuation A Γ₀}
    (hv : (v.comap (algebraMap R A)).IsContinuous) : v.IsContinuous := by
  rw [isContinuous_iff_forall_ne_zero]
  intro a ha
  -- `{x | v x < v a}` contains the translate of a neighbourhood of `0` around each of its points
  refine isOpen_iff_mem_nhds.mpr fun x₀ hx₀ ↦ ?_
  have hmem : {x | v (x - x₀) < v a} ∈ 𝓝 x₀ :=
    (continuous_sub_right x₀).continuousAt.preimage_mem_nhds
      (by rw [sub_self]; exact setOf_lt_mem_nhds_zero G hι hv ha)
  filter_upwards [hmem] with x hx
  rw [← sub_add_cancel x x₀]
  exact v.map_add_lt hx hx₀

end Valuation
