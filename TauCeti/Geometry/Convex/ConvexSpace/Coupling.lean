/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.ConvexSpace.PrefixSum
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

import Mathlib.Order.Fin.Prod
import TauCeti.Algebra.Order.Group.MinMax

/-!
# Comonotone coupling of barycentric weights on finite standard simplices

Given points `s : StdSimplex R (Fin m)` and `t : StdSimplex R (Fin n)` over a linearly ordered
additive group or strict ordered ring `R`, their **comonotone** (or **Fréchet–Hoeffding**) coupling
`Convexity.StdSimplex.coupling s t : StdSimplex R (Fin m × Fin n)` assigns to `(i, j)` the overlap
length `Convexity.StdSimplex.couplingWeights s t (i, j)` of the `i`-th cumulative-weight interval
`[s₀ + ⋯ + s_{i-1}, s₀ + ⋯ + s_i]` of `s` with the `j`-th cumulative-weight interval
`[t₀ + ⋯ + t_{j-1}, t₀ + ⋯ + t_j]` of `t`.

Summing these weights over any lower rectangle `Finset.Iic (i, j)` telescopes in both coordinates to
`min (TauCeti.prefixSum (i + 1) s.weights) (TauCeti.prefixSum (j + 1) t.weights)`
(`Convexity.StdSimplex.sum_Iic_coupling`). From this cumulative-distribution identity it follows
that:

* `s.coupling t` has marginals `s` and `t` (`Convexity.StdSimplex.map_fst_coupling`,
  `Convexity.StdSimplex.map_snd_coupling`), and any pair of monotone maps `f : Fin k → Fin m`,
  `g : Fin k → Fin n` pushes `w : StdSimplex R (Fin k)` forward to `(w.map f).coupling (w.map g)`
  (`Convexity.StdSimplex.map_prodMk_eq_coupling`);
* the support of `s.coupling t` is a chain in `Fin m × Fin n`
  (`Convexity.StdSimplex.isChain_support_coupling`);
* over an order-closed topological ring, `s.coupling t` depends continuously on `(s, t)`
  (`Convexity.StdSimplex.continuous_coupling`).

## Main definitions

* `Convexity.StdSimplex.couplingWeights`: the overlap-length weight function on `Fin m × Fin n`.
* `Convexity.StdSimplex.coupling`: the comonotone coupling in `StdSimplex R (Fin m × Fin n)`.

## Main results

* `Convexity.StdSimplex.couplingWeights_eq_zero_iff`,
  `Convexity.StdSimplex.couplingWeights_ne_zero_iff`: vanishing and positivity of a coupling weight
  in terms of cumulative-interval overlap.
* `Convexity.StdSimplex.sum_couplingWeights_lt`, `Convexity.StdSimplex.sum_Iic_coupling`:
  rectangular cumulative sums of `s.coupling t`.
* `Convexity.StdSimplex.isChain_support_coupling`: the support of `s.coupling t` is a chain.
* `Convexity.StdSimplex.map_fst_coupling`, `Convexity.StdSimplex.map_snd_coupling`,
  `Convexity.StdSimplex.map_prodMk_eq_coupling`: marginals and pushforward along monotone pairs.
* `Convexity.StdSimplex.continuous_couplingWeights`, `Convexity.StdSimplex.continuous_coupling`:
  joint continuity of `couplingWeights` and `coupling`.

## References

* M. Fréchet, *Sur les tableaux de corrélation dont les marges sont données*, Ann. Univ. Lyon
  Sect. A (3) 14 (1951), 53–77.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953), 200–204.
-/

public section

namespace Convexity.StdSimplex

section OrderedAddCommGroup

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [One R] {m n : ℕ}

/-- The comonotone coupling weights on `Fin m × Fin n` associated to barycentric coordinates
`s : StdSimplex R (Fin m)` and `t : StdSimplex R (Fin n)`: the overlap length of the `i`-th
cumulative-weight interval of `s` with the `j`-th cumulative-weight interval of `t`. -/
noncomputable def couplingWeights (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (x : Fin m × Fin n) : R :=
  max 0 (min (TauCeti.prefixSum (x.1.val + 1) s.weights)
      (TauCeti.prefixSum (x.2.val + 1) t.weights) -
    max (TauCeti.prefixSum x.1.val s.weights) (TauCeti.prefixSum x.2.val t.weights))

/-- Swapping the two simplex factors swaps the coordinates of `couplingWeights`. -/
theorem couplingWeights_swap (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (x : Fin n × Fin m) :
    s.couplingWeights t x.swap = t.couplingWeights s x := by
  simp only [couplingWeights, Prod.fst_swap, Prod.snd_swap, min_comm, max_comm]

variable [IsOrderedAddMonoid R]

/-- The coupling weight at `x` vanishes precisely when the cumulative-weight intervals at `x.1` and
`x.2` have nonpositive overlap. -/
@[simp]
theorem couplingWeights_eq_zero_iff (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (x : Fin m × Fin n) :
    s.couplingWeights t x = 0 ↔
      min (TauCeti.prefixSum (x.1.val + 1) s.weights)
        (TauCeti.prefixSum (x.2.val + 1) t.weights) ≤
      max (TauCeti.prefixSum x.1.val s.weights) (TauCeti.prefixSum x.2.val t.weights) := by
  rw [couplingWeights, max_eq_left_iff, sub_nonpos]

/-- The coupling weight at `x` is nonzero precisely when the cumulative-weight intervals at `x.1`
and `x.2` overlap in a nondegenerate interval. -/
theorem couplingWeights_ne_zero_iff (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (x : Fin m × Fin n) :
    s.couplingWeights t x ≠ 0 ↔
      max (TauCeti.prefixSum x.1.val s.weights) (TauCeti.prefixSum x.2.val t.weights) <
        min (TauCeti.prefixSum (x.1.val + 1) s.weights)
          (TauCeti.prefixSum (x.2.val + 1) t.weights) :=
  (s.couplingWeights_eq_zero_iff t x).not.trans not_le

private lemma couplingWeights_eq_sub (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (i : Fin m) (j : Fin n) :
    s.couplingWeights t (i, j) =
      (min (TauCeti.prefixSum (i.val + 1) s.weights) (TauCeti.prefixSum (j.val + 1) t.weights) -
        min (TauCeti.prefixSum i.val s.weights) (TauCeti.prefixSum (j.val + 1) t.weights)) -
      (min (TauCeti.prefixSum (i.val + 1) s.weights) (TauCeti.prefixSum j.val t.weights) -
        min (TauCeti.prefixSum i.val s.weights) (TauCeti.prefixSum j.val t.weights)) := by
  have h := TauCeti.max_zero_min_sub_max
    (TauCeti.monotone_prefixSum s.nonneg (Nat.le_succ i.val))
    (TauCeti.monotone_prefixSum t.nonneg (Nat.le_succ j.val))
  rw [couplingWeights, h]
  grind

/-- Summing `s.couplingWeights t` over a lower rectangle `{i | i < K} × {j | j < L}` telescopes in
both coordinates to `min (TauCeti.prefixSum K s.weights) (TauCeti.prefixSum L t.weights)`. -/
theorem sum_couplingWeights_lt (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) (K L : ℕ) :
    (∑ i : Fin m with i.val < K, ∑ j : Fin n with j.val < L, s.couplingWeights t (i, j)) =
      min (TauCeti.prefixSum K s.weights) (TauCeti.prefixSum L t.weights) := by
  have hinner (i : Fin m) :
      (∑ j : Fin n with j.val < L, s.couplingWeights t (i, j)) =
        min (TauCeti.prefixSum (i.val + 1) s.weights) (TauCeti.prefixSum L t.weights) -
          min (TauCeti.prefixSum i.val s.weights) (TauCeti.prefixSum L t.weights) := by
    simp_rw [couplingWeights_eq_sub]
    rw [TauCeti.sum_sub_prefixSum
      (fun v ↦ min (TauCeti.prefixSum (i.val + 1) s.weights) v -
        min (TauCeti.prefixSum i.val s.weights) v)
      L t.weights]
    simp [min_eq_right (s.prefixSum_weights_nonneg _)]
  simp_rw [hinner]
  rw [TauCeti.sum_sub_prefixSum (fun u ↦ min u (TauCeti.prefixSum L t.weights)) K s.weights]
  simp [min_eq_left (t.prefixSum_weights_nonneg _)]

private lemma filter_val_lt_eq_univ (k : ℕ) :
    (Finset.univ.filter fun i : Fin k ↦ i.val < k) = Finset.univ :=
  Finset.filter_true_of_mem fun i _ ↦ i.isLt

private lemma sum_couplingWeights_lt_univ_right (s : StdSimplex R (Fin m))
    (t : StdSimplex R (Fin n)) (K : ℕ) :
    (∑ i : Fin m with i.val < K, ∑ j : Fin n, s.couplingWeights t (i, j)) =
      TauCeti.prefixSum K s.weights := by
  have h := s.sum_couplingWeights_lt t K n
  simp_rw [filter_val_lt_eq_univ n] at h
  have htot : ∑ j : Fin n, t.weights j = 1 := by simpa [Finsupp.sum_fintype] using t.total
  rwa [TauCeti.prefixSum_of_le le_rfl, htot, min_eq_left (s.prefixSum_weights_le_one K)] at h

private lemma sum_couplingWeights (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) :
    ∑ x, s.couplingWeights t x = 1 := by
  have h := sum_couplingWeights_lt_univ_right s t m
  have htot : ∑ i : Fin m, s.weights i = 1 := by simpa [Finsupp.sum_fintype] using s.total
  rw [filter_val_lt_eq_univ m, TauCeti.prefixSum_of_le le_rfl, htot] at h
  rwa [Fintype.sum_prod_type]

/-- The comonotone coupling of `s : StdSimplex R (Fin m)` and `t : StdSimplex R (Fin n)` as a point
of `StdSimplex R (Fin m × Fin n)`. -/
noncomputable def coupling (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) :
    StdSimplex R (Fin m × Fin n) where
  weights := Finsupp.equivFunOnFinite.symm (s.couplingWeights t)
  nonneg _ := le_max_left 0 _
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact sum_couplingWeights s t

/-- The barycentric weights of `s.coupling t` are `s.couplingWeights t`. -/
@[simp]
theorem coupling_weights (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (x : Fin m × Fin n) :
    (s.coupling t).weights x = s.couplingWeights t x :=
  (rfl)

/-- The sum of the weights of `s.coupling t` over the lower rectangle `Finset.Iic u` equals
`min (TauCeti.prefixSum (u.1 + 1) s.weights) (TauCeti.prefixSum (u.2 + 1) t.weights)`. -/
theorem sum_Iic_coupling (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n))
    (u : Fin m × Fin n) :
    (∑ x ∈ Finset.Iic u, (s.coupling t).weights x) =
      min (TauCeti.prefixSum (u.1.val + 1) s.weights)
        (TauCeti.prefixSum (u.2.val + 1) t.weights) := by
  rw [← s.sum_couplingWeights_lt t (u.1.val + 1) (u.2.val + 1), ← Finset.sum_product']
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_Iic, Prod.le_def, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.le_def]
  omega

/-- If two overlapping cumulative-weight intervals separate in one coordinate (`v₁ < u₁`), then they
are ordered in the same direction in the other coordinate (`v₂ ≤ u₂`). -/
private lemma coord_le_of_lt {s : StdSimplex R (Fin m)} {t : StdSimplex R (Fin n)}
    {u₁ v₁ : Fin m} {u₂ v₂ : Fin n}
    (hu : max (TauCeti.prefixSum u₁.val s.weights) (TauCeti.prefixSum u₂.val t.weights) <
      min (TauCeti.prefixSum (u₁.val + 1) s.weights) (TauCeti.prefixSum (u₂.val + 1) t.weights))
    (hv : max (TauCeti.prefixSum v₁.val s.weights) (TauCeti.prefixSum v₂.val t.weights) <
      min (TauCeti.prefixSum (v₁.val + 1) s.weights) (TauCeti.prefixSum (v₂.val + 1) t.weights))
    (h₁ : v₁ < u₁) : v₂ ≤ u₂ := by
  have hstep : TauCeti.prefixSum (v₁.val + 1) s.weights ≤ TauCeti.prefixSum u₁.val s.weights :=
    TauCeti.monotone_prefixSum s.nonneg (Nat.succ_le_of_lt h₁)
  have hlt : TauCeti.prefixSum v₂.val t.weights < TauCeti.prefixSum (u₂.val + 1) t.weights :=
    calc TauCeti.prefixSum v₂.val t.weights
      _ ≤ max (TauCeti.prefixSum v₁.val s.weights) (TauCeti.prefixSum v₂.val t.weights) :=
        le_max_right _ _
      _ < min (TauCeti.prefixSum (v₁.val + 1) s.weights)
          (TauCeti.prefixSum (v₂.val + 1) t.weights) := hv
      _ ≤ TauCeti.prefixSum (v₁.val + 1) s.weights := min_le_left _ _
      _ ≤ TauCeti.prefixSum u₁.val s.weights := hstep
      _ ≤ max (TauCeti.prefixSum u₁.val s.weights) (TauCeti.prefixSum u₂.val t.weights) :=
        le_max_left _ _
      _ < min (TauCeti.prefixSum (u₁.val + 1) s.weights)
          (TauCeti.prefixSum (u₂.val + 1) t.weights) := hu
      _ ≤ TauCeti.prefixSum (u₂.val + 1) t.weights := min_le_right _ _
  by_contra! h₂
  exact not_le_of_gt hlt (TauCeti.monotone_prefixSum t.nonneg (Nat.succ_le_of_lt h₂))

/-- The support of `s.coupling t` is a chain in `Fin m × Fin n`. -/
theorem isChain_support_coupling (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) :
    IsChain (· ≤ ·) ((s.coupling t).weights.support : Set (Fin m × Fin n)) := by
  intro u hu v hv _
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, coupling_weights,
    couplingWeights_ne_zero_iff] at hu hv
  by_cases hle : u ≤ v
  · exact Or.inl hle
  · refine Or.inr ?_
    rw [Prod.le_def, not_and_or] at hle
    rcases hle with h₁ | h₂
    · exact ⟨(not_le.1 h₁).le, coord_le_of_lt hu hv (not_le.1 h₁)⟩
    · refine ⟨coord_le_of_lt (s := t) (t := s) ?_ ?_ (not_le.1 h₂), (not_le.1 h₂).le⟩
      · rwa [max_comm, min_comm]
      · rwa [max_comm, min_comm]

end OrderedAddCommGroup

section StrictOrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {k m n : ℕ}

/-- Swapping coordinates sends `t.coupling s` to `s.coupling t`. -/
theorem map_swap_coupling (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) :
    (t.coupling s).map Prod.swap = s.coupling t := by
  rw [← weights_inj]
  ext x
  have hinj : Function.Injective (Prod.swap : Fin n × Fin m → Fin m × Fin n) :=
    Prod.swap_injective
  rw [← Prod.swap_swap x, weights_map_apply_of_injective hinj, coupling_weights, coupling_weights,
    couplingWeights_swap, Prod.swap_swap]

/-- The first marginal of `s.coupling t` is `s`. -/
@[simp]
theorem map_fst_coupling (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) :
    (s.coupling t).map Prod.fst = s := by
  rw [← weights_inj, DFunLike.ext_iff, ← funext_iff]
  refine TauCeti.eq_of_forall_prefixSum_eq fun K ↦ ?_
  rw [TauCeti.prefixSum_def, sum_filter_weights_map Prod.fst (s.coupling t) (fun i ↦ i.val < K)]
  have h : (Finset.univ.filter fun x : Fin m × Fin n ↦ x.1.val < K) =
      (Finset.univ.filter fun i : Fin m ↦ i.val < K) ×ˢ Finset.univ := by
    ext ⟨i, j⟩
    simp
  rw [h, Finset.sum_product]
  exact sum_couplingWeights_lt_univ_right s t K

/-- The second marginal of `s.coupling t` is `t`. -/
@[simp]
theorem map_snd_coupling (s : StdSimplex R (Fin m)) (t : StdSimplex R (Fin n)) :
    (s.coupling t).map Prod.snd = t := by
  rw [← s.map_swap_coupling t, map_map]
  exact t.map_fst_coupling s

/-- Any pair of monotone maps `f : Fin k → Fin m` and `g : Fin k → Fin n` pushes a simplex point
`w : StdSimplex R (Fin k)` forward to the comonotone coupling of its two coordinate marginals. -/
theorem map_prodMk_eq_coupling (w : StdSimplex R (Fin k)) {f : Fin k → Fin m} {g : Fin k → Fin n}
    (hf : Monotone f) (hg : Monotone g) :
    w.map (fun i ↦ (f i, g i)) = (w.map f).coupling (w.map g) := by
  have hzero : (fun u ↦ (w.map (fun i ↦ (f i, g i))).weights u -
      ((w.map f).coupling (w.map g)).weights u) = 0 :=
    TauCeti.eq_zero_of_forall_sum_Iic_eq_zero fun u ↦ by
      simp only [Finset.sum_sub_distrib, sub_eq_zero]
      rw [sum_Iic_coupling]
      obtain ⟨a, ha, hpa⟩ := w.exists_lt_iff_and_prefixSum_weights_map hf (u.1.val + 1)
      obtain ⟨b, hb, hpb⟩ := w.exists_lt_iff_and_prefixSum_weights_map hg (u.2.val + 1)
      have hIic : Finset.Iic u = Finset.univ.filter (fun z : Fin m × Fin n ↦ z ≤ u) := by
        ext z
        simp
      rw [hIic, sum_filter_weights_map (fun i ↦ (f i, g i)) w (fun z ↦ z ≤ u), hpa, hpb,
        ← (TauCeti.monotone_prefixSum w.nonneg).map_min, TauCeti.prefixSum_def]
      refine Finset.sum_congr (Finset.filter_congr fun i _ ↦ ?_) fun _ _ ↦ rfl
      simp only [Prod.le_def, Fin.le_def, lt_min_iff]
      exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨(ha i).1 (Nat.lt_succ_of_le h₁), (hb i).1 (Nat.lt_succ_of_le h₂)⟩,
        fun ⟨h₁, h₂⟩ ↦ ⟨Nat.le_of_lt_succ ((ha i).2 h₁), Nat.le_of_lt_succ ((hb i).2 h₂)⟩⟩
  ext u
  exact sub_eq_zero.1 (congrFun hzero u)

end StrictOrderedRing

section Topology

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [OrderClosedTopology R] {m n : ℕ}

/-- Each coordinate weight `s.couplingWeights t x` depends continuously on `(s, t)`. -/
@[fun_prop]
theorem continuous_couplingWeights (x : Fin m × Fin n) :
    Continuous fun z : StdSimplex R (Fin m) × StdSimplex R (Fin n) ↦ z.1.couplingWeights z.2 x := by
  unfold couplingWeights
  fun_prop

/-- The comonotone coupling `s.coupling t` depends continuously on `(s, t)`. -/
@[fun_prop]
theorem continuous_coupling :
    Continuous fun z : StdSimplex R (Fin m) × StdSimplex R (Fin n) ↦ z.1.coupling z.2 := by
  rw [(isEmbedding_toFun_comp_weights R (Fin m × Fin n)).continuous_iff]
  exact continuous_pi fun x ↦ continuous_couplingWeights x

end Topology

end Convexity.StdSimplex
