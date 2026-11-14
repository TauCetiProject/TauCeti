/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import TauCeti.Topology.Algebra.InfiniteSum.Sigma

/-!
# Periodic points of all periods through orbit representatives

Let `f : α → α` and let `x : ι → α` be a family of **orbit representatives** of the periodic points
of `f`: every `x i` is periodic, and every periodic point lies on the forward orbit of exactly one
`x i`. Write `d i` for the least period of `x i`. A periodic point `y` of positive period `n` lies
on the orbit of a unique `x i`, as `y = f^[j] (x i)` for a unique phase `j < d i`, and `d i`
divides `n`. Hence the pairs `(n, y)` with `n > 0` and `f^[n] y = y` correspond exactly to the
triples `(i, k, j)` with `k ∈ ℕ` and `j < d i`, through

`(i, k, j) ↦ (d i * (k + 1), f^[j] (x i))`

(`Function.sigmaMinimalPeriodEquiv`). Under this correspondence a sum over the fixed points of all
iterates of `f` regroups into a sum over the periodic orbits and their iterates, each orbit of least
period `d` contributing its `d` points to every period `d * (k + 1)`
(`Function.hasSum_of_hasSum_sum_sigmaMinimalPeriodEquiv`).

This is the bookkeeping between the two forms of the dynamical zeta function of a map: the orbit
form `exp (∑_γ ∑_k ε_γ(k) e^(k γ) / k)`, a sum over primitive periodic orbits and their iterates,
and the fixed-point form `exp (∑_n ∑_{f^[n] y = y} ε_n(y) e^(γ_n(y)) / n)`, a sum over the fixed
points of the iterates, whose inner sums are the signed fixed-point counts of the Lefschetz
fixed-point formula.

## Main results

* `Function.injective_of_existsUnique_iterate_eq`: orbit representatives are distinct.
* `Function.tendsto_minimalPeriod_cofinite`: if each iterate has finitely many fixed points, the
  least periods of distinct periodic points tend to infinity.
* `Function.sigmaMinimalPeriodEquiv`: the correspondence `(i, k, j) ↦ (d i * (k + 1), f^[j] (x i))`.
* `Function.hasSum_of_hasSum_sum_sigmaMinimalPeriodEquiv`: a summable family on the fixed points of
  the iterates sums to `a` when its orbit sums sum to `a`.

## References

* D. Fried, *Lefschetz formulas for flows*, Contemp. Math. 58, Part III (1987), 19–69.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, Section 1.3.
-/

public section

open Filter Set

namespace Function

variable {α ι : Type*} {f : α → α} {x : ι → α}

/-- If every periodic point of `f` lies on the forward orbit of exactly one `x i`, and every `x i`
is periodic, then the family `x` is injective. -/
theorem injective_of_existsUnique_iterate_eq (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) : Injective x := fun i _ h ↦
  (hrep (x i) (hx i)).unique ⟨0, rfl⟩ ⟨0, h.symm⟩

/-- If each positive iterate of `f` has only finitely many fixed points, the least periods of a
family of distinct periodic points tend to infinity along the cofinite filter. -/
theorem tendsto_minimalPeriod_cofinite (hfin : ∀ n, 0 < n → (ptsOfPeriod f n).Finite)
    (hx : ∀ i, x i ∈ periodicPts f) (hinj : Injective x) :
    Tendsto (fun i ↦ minimalPeriod f (x i)) cofinite atTop := by
  refine tendsto_atTop.2 fun N ↦ eventually_cofinite.2 ?_
  -- A point of least period below `N` is a fixed point of some `f^[n]` with `0 < n < N`.
  have hN : {n | 0 < n ∧ n < N}.Finite := (finite_Iio N).subset fun _ hn ↦ hn.2
  refine ((hN.biUnion fun n hn ↦ hfin n hn.1).preimage hinj.injOn).subset fun i hi ↦
    mem_preimage.2 <| mem_biUnion
      ⟨minimalPeriod_pos_of_mem_periodicPts (hx i), (not_le.1 hi : minimalPeriod f (x i) < N)⟩
      (isPeriodicPt_minimalPeriod f (x i))

/-- The map `(i, k, j) ↦ (d i * (k + 1), f^[j] (x i))`, with `d i` the least period of `x i`,
from triples with `j < d i` to the periodic points of positive period. -/
private noncomputable def sigmaMinimalPeriodMap (hx : ∀ i, x i ∈ periodicPts f)
    (t : Σ p : ι × ℕ, Fin (minimalPeriod f (x p.1))) :
    {q : ℕ × α // 0 < q.1 ∧ IsPeriodicPt f q.1 q.2} :=
  ⟨(minimalPeriod f (x t.1.1) * (t.1.2 + 1), f^[t.2] (x t.1.1)),
    Nat.mul_pos (minimalPeriod_pos_of_mem_periodicPts (hx t.1.1)) t.1.2.succ_pos,
    ((isPeriodicPt_minimalPeriod f (x t.1.1)).mul_const _).apply_iterate _⟩

private theorem bijective_sigmaMinimalPeriodMap (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) :
    Bijective (sigmaMinimalPeriodMap hx) := by
  constructor
  · rintro ⟨⟨i, k⟩, j⟩ ⟨⟨i', k'⟩, j'⟩ h
    simp only [sigmaMinimalPeriodMap, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨hn, hy⟩ := h
    -- The two points lie on the orbits of `x i` and `x i'`, so `i = i'`.
    obtain rfl : i = i' := (hrep _ (mk_mem_periodicPts (minimalPeriod_pos_of_mem_periodicPts (hx i))
      ((isPeriodicPt_minimalPeriod f (x i)).apply_iterate j))).unique ⟨j, rfl⟩ ⟨j', hy.symm⟩
    -- Both phases are below the least period, so they agree.
    obtain rfl : j = j' := Fin.ext (iterate_injOn_Iio_minimalPeriod j.2 j'.2 hy)
    obtain rfl : k = k' := by
      have := Nat.eq_of_mul_eq_mul_left (minimalPeriod_pos_of_mem_periodicPts (hx i)) hn
      omega
    rfl
  · rintro ⟨⟨n, y⟩, hn, hy⟩
    have hyp : y ∈ periodicPts f := mk_mem_periodicPts hn hy
    obtain ⟨i, ⟨j, rfl⟩, -⟩ := hrep y hyp
    -- The period `n` is a multiple `d * m` of the least period `d` of the orbit, with `m > 0`.
    obtain ⟨m, rfl⟩ : minimalPeriod f (x i) ∣ n := by
      simpa [minimalPeriod_apply_iterate (hx i)] using hy.minimalPeriod_dvd
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    refine ⟨⟨⟨i, m - 1⟩, ⟨j % minimalPeriod f (x i),
      Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts (hx i))⟩⟩, ?_⟩
    simp only [sigmaMinimalPeriodMap, Subtype.mk.injEq, Prod.mk.injEq, iterate_mod_minimalPeriod_eq,
      and_true]
    rw [Nat.sub_add_cancel hm]

variable (f) in
/-- **Periodic points of all periods through orbit representatives.** For a family `x` of orbit
representatives of the periodic points of `f`, with least periods `d i`, the triples `(i, k, j)`
with `k ∈ ℕ` and `j < d i` correspond to the pairs `(n, y)` with `n > 0` and `f^[n] y = y`, through
`(i, k, j) ↦ (d i * (k + 1), f^[j] (x i))`. -/
noncomputable def sigmaMinimalPeriodEquiv (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) :
    (Σ p : ι × ℕ, Fin (minimalPeriod f (x p.1))) ≃
      {q : ℕ × α // 0 < q.1 ∧ IsPeriodicPt f q.1 q.2} :=
  .ofBijective _ (bijective_sigmaMinimalPeriodMap hx hrep)

@[simp]
theorem sigmaMinimalPeriodEquiv_apply (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y)
    (t : Σ p : ι × ℕ, Fin (minimalPeriod f (x p.1))) :
    sigmaMinimalPeriodEquiv f hx hrep t =
      ⟨(minimalPeriod f (x t.1.1) * (t.1.2 + 1), f^[t.2] (x t.1.1)),
        Nat.mul_pos (minimalPeriod_pos_of_mem_periodicPts (hx t.1.1)) t.1.2.succ_pos,
        ((isPeriodicPt_minimalPeriod f (x t.1.1)).mul_const _).apply_iterate _⟩ :=
  (rfl)

theorem coe_sigmaMinimalPeriodEquiv_apply (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y)
    (t : Σ p : ι × ℕ, Fin (minimalPeriod f (x p.1))) :
    (sigmaMinimalPeriodEquiv f hx hrep t : ℕ × α) =
      (minimalPeriod f (x t.1.1) * (t.1.2 + 1), f^[t.2] (x t.1.1)) :=
  (rfl)

/-- **Regrouping a sum over the fixed points of the iterates by orbits.** Let `x` be a family of
orbit representatives of the periodic points of `f`, with least periods `d i`, and let `g` be a
summable family indexed by the pairs `(n, y)` with `n > 0` and `f^[n] y = y`. If, for each orbit
`i` and each `k`, the `d i` terms of `g` at the points of the `i`-th orbit in period
`d i * (k + 1)` add up to `F (i, k)`, and `F` sums to `a`, then `g` sums to `a`. -/
theorem hasSum_of_hasSum_sum_sigmaMinimalPeriodEquiv {V : Type*} [AddCommMonoid V]
    [TopologicalSpace V] [R1Space V]
    (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y)
    {g : {q : ℕ × α // 0 < q.1 ∧ IsPeriodicPt f q.1 q.2} → V} (hg : Summable g)
    {F : ι × ℕ → V} {a : V} (hF : HasSum F a)
    (hgF : ∀ p, ∑ j, g (sigmaMinimalPeriodEquiv f hx hrep ⟨p, j⟩) = F p) : HasSum g a := by
  obtain ⟨s, hs⟩ := hg
  -- Sum the reindexed family first over the phases `j` of each orbit, then over the orbits.
  have hσ : HasSum F s := by
    simpa only [comp_apply, hgF] using
      ((sigmaMinimalPeriodEquiv f hx hrep).hasSum_iff.2 hs).sigma_of_finite
  -- The two limits of `F` are inseparable, so `g` also sums to `a`.
  unfold HasSum at hs hσ hF ⊢
  rwa [(tendsto_nhds_unique_inseparable hσ hF).nhds_eq] at hs

end Function
