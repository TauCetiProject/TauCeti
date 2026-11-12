/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Link

/-!
# The `Sym(3)` coboundary constant of `K_k`

The coboundary constant `h₁(K_k)` itself, the star-gauge lower bound `k/3 ≤ h₁(K_k)`, and the
value `h₁(K_4) = 4/3`.

`Sym3.Basic` proves, for the `k = 4` seed, its defect `N`, that no gauge costs less than `D`,
and that `D` is attained. This file defines the quantities that seed is about:

* `gaugeDist α`: the minimum of `cost α β` over every gauge `β : Fin k → Sym(3)`, the distance of
  `α` from the coboundaries, with `gaugeDist α = 0` exactly when `α` is a coboundary;
* `h1 k`: the infimum of `N/D = defect α / gaugeDist α` over every non-coboundary `α`.

It then proves both halves of `h₁(K_k) = k/3`:

* the upper bound `h1 4 ≤ 4/3`, from the witness `w4` of `Sym3.Basic`;
* the lower bound `k/3 ≤ h1 k` for every `k` (given a non-coboundary exists), by the star-gauge
  double count of Proposition 1 of the paper, which is Chapman–Lubotzky [Stability of
  homomorphisms, coverings and cocycles II, Adv. Math. 463 (2025) 110117, arXiv:2311.06706]
  Proposition 3.2: the star gauges `β_x` (`x` a vertex) cost `3N` in total, so the cheapest
  costs at most `3N/k`.

All counts are moved-point (Hamming) counts in the same degree convention as `Basic`, with
`Sym(3)` values on the cochain and the gauge.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

open Equiv Finset
open TauCeti.TwoComplex

variable {k : ℕ}

/-! ## The Hamming count -/

/-- Only the identity moves no point (`movedNorm` is a group norm). -/
theorem moved_eq_zero_iff (σ : S3) : moved σ = 0 ↔ σ = 1 := by
  rw [← map_eq_zero_iff_eq_one (Perm.movedNorm (Fin 3)), ← moved_eq_movedNorm]
  exact_mod_cast Iff.rfl

/-- A permutation and its inverse move the same points (`movedNorm` is a group norm). -/
theorem moved_inv (σ : S3) : moved σ⁻¹ = moved σ := by
  have h := map_inv_eq_map (Perm.movedNorm (Fin 3)) σ
  rw [← moved_eq_movedNorm, ← moved_eq_movedNorm] at h
  exact_mod_cast h

theorem moved_one : moved (1 : S3) = 0 := by decide

/-! ## Gauge distance and the coboundary constant -/

/-- The **gauge distance** of a cochain: the minimum of `cost α β` over every gauge
`β : Fin k → Sym(3)`. This is the paper's `D` (Section 1), the Hamming distance of `α` from
the `Sym(3)`-valued coboundaries. -/
def gaugeDist (α : Fin k → Fin k → S3) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (cost α)

/-- No gauge costs less than the gauge distance. -/
theorem gaugeDist_le (α : Fin k → Fin k → S3) (β : Fin k → S3) : gaugeDist α ≤ cost α β :=
  Finset.inf'_le _ (Finset.mem_univ β)

/-- The gauge distance is attained by some gauge. -/
theorem exists_cost_eq_gaugeDist (α : Fin k → Fin k → S3) :
    ∃ β : Fin k → S3, cost α β = gaugeDist α := by
  obtain ⟨β, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (cost α)
  exact ⟨β, h.symm⟩

/-- A lower bound for every gauge is a lower bound for the gauge distance. -/
theorem le_gaugeDist {α : Fin k → Fin k → S3} {D : ℕ} (h : ∀ β, D ≤ cost α β) :
    D ≤ gaugeDist α :=
  Finset.le_inf' _ _ fun β _ => h β

/-- A cost attained and a matching lower bound for every gauge pin the gauge distance. -/
theorem gaugeDist_eq_of {α : Fin k → Fin k → S3} {D : ℕ} (hlow : ∀ β, D ≤ cost α β)
    (β₀ : Fin k → S3) (hβ₀ : cost α β₀ = D) : gaugeDist α = D :=
  le_antisymm ((gaugeDist_le α β₀).trans hβ₀.le) (le_gaugeDist hlow)

/-! ### Cost and defect as sums over vertices -/

/-- A sum over the edges `u < v` as a double sum over vertices. -/
private theorem sum_edges (g : Fin k → Fin k → ℕ) :
    ((edges k).map fun e => g e.1 e.2).sum =
      ∑ u : Fin k, ∑ v : Fin k, if u < v then g u v else 0 := by
  unfold edges
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  simp [Fin.sum_univ_def, List.sum_map_ite, Function.comp_def]

/-- A sum over the triangles `u < v < w` as a triple sum over vertices. -/
private theorem sum_triangles (g : Fin k → Fin k → Fin k → ℕ) :
    ((triangles k).map fun t => g t.1 t.2.1 t.2.2).sum =
      ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k, if u < v ∧ v < w then g u v w else 0 := by
  unfold triangles
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  rw [Function.comp_apply, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map,
    Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
  simp [Fin.sum_univ_def, List.sum_map_ite, Function.comp_def]

theorem cost_eq_sum (α : Fin k → Fin k → S3) (β : Fin k → S3) :
    cost α β = ∑ u : Fin k, ∑ v : Fin k,
      if u < v then moved ((β u)⁻¹ * α u v * β v) else 0 :=
  sum_edges fun u v => moved ((β u)⁻¹ * α u v * β v)

/-- The holonomy of `α` around the triangle `a → b → c → a`. -/
@[expose] def hol (α : Fin k → Fin k → S3) (a b c : Fin k) : S3 :=
  val α a b * val α b c * val α c a

@[simp] theorem hol_apply (α : Fin k → Fin k → S3) (a b c : Fin k) :
    hol α a b c = val α a b * val α b c * val α c a :=
  rfl

theorem defect_eq_sum (α : Fin k → Fin k → S3) :
    defect α = ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k,
      if u < v ∧ v < w then moved (hol α u v w) else 0 :=
  sum_triangles fun u v w => moved (hol α u v w)

/-- Reading a bare function through `val` changes neither its defect nor its gauge distance. -/
theorem val_congr {f g : Fin k → Fin k → S3} (h : ∀ u v, u < v → f u v = g u v) {u v : Fin k}
    (huv : u ≠ v) : val f u v = val g u v := by
  rcases huv.lt_or_gt with huv | huv <;> simp [val, huv, not_lt.mpr huv.le, h]

/-- The defect only reads the values on `u < v`. -/
theorem defect_congr {f g : Fin k → Fin k → S3} (h : ∀ u v, u < v → f u v = g u v) :
    defect f = defect g := by
  rw [defect_eq_sum, defect_eq_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun w _ => ?_
  split_ifs with h'
  · obtain ⟨huv, hvw⟩ := h'
    simp only [hol, val_congr h huv.ne, val_congr h hvw.ne, val_congr h (huv.trans hvw).ne']
  · rfl

/-- The costs only read the values on `u < v`. -/
theorem cost_congr {f g : Fin k → Fin k → S3} (h : ∀ u v, u < v → f u v = g u v) (β : Fin k → S3) :
    cost f β = cost g β := by
  rw [cost_eq_sum, cost_eq_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h'
  · rw [h u v h']
  · rfl

/-- The gauge distance only reads the values on `u < v`. -/
theorem gaugeDist_congr {f g : Fin k → Fin k → S3} (h : ∀ u v, u < v → f u v = g u v) :
    gaugeDist f = gaugeDist g := by
  unfold gaugeDist
  simp only [cost_congr h]

/-! ### What `gaugeDist α = 0` means -/

/-- A gauge costs nothing exactly when it writes `α` as a coboundary. -/
theorem cost_eq_zero_iff (α : Fin k → Fin k → S3) (β : Fin k → S3) :
    cost α β = 0 ↔ ∀ u v, u < v → α u v = β u * (β v)⁻¹ := by
  rw [cost_eq_sum]
  constructor
  · intro h u v huv
    have h1 := (Finset.sum_eq_zero_iff.mp h) u (Finset.mem_univ u)
    have h2 : (if u < v then moved ((β u)⁻¹ * α u v * β v) else 0) = 0 :=
      (Finset.sum_eq_zero_iff.mp h1) v (Finset.mem_univ v)
    rw [ite_eq_left huv, moved_eq_zero_iff] at h2
    calc α u v = β u * ((β u)⁻¹ * α u v * β v) * (β v)⁻¹ := by group
      _ = β u * (β v)⁻¹ := by rw [h2, mul_one]
  · intro h
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
    -- The summand at `u`, `v`, beta-reduced, so that `ite_eq_left` applies.
    change (if u < v then moved ((β u)⁻¹ * α u v * β v) else 0) = 0
    by_cases huv : u < v
    · rw [ite_eq_left huv, moved_eq_zero_iff, h u v huv]
      group
    · rw [ite_eq_right huv]

/-- **The definition means what it says.** The gauge distance of `α` is zero exactly when `α`
is a `Sym(3)`-valued coboundary, `α(u,v) = β(u) β(v)⁻¹` on every edge `u < v`. -/
theorem gaugeDist_eq_zero_iff (α : Fin k → Fin k → S3) :
    gaugeDist α = 0 ↔ ∃ β : Fin k → S3, ∀ u v, u < v → α u v = β u * (β v)⁻¹ := by
  constructor
  · intro h
    obtain ⟨β, hβ⟩ := exists_cost_eq_gaugeDist α
    exact ⟨β, (cost_eq_zero_iff α β).mp (hβ.trans h)⟩
  · rintro ⟨β, hβ⟩
    exact le_antisymm ((gaugeDist_le α β).trans ((cost_eq_zero_iff α β).mpr hβ).le)
      (Nat.zero_le _)

/-- The **coboundary constant** `h₁(K_k)` in the counting normalisation of the paper: the
infimum of the counting ratio `N/D = defect α / gaugeDist α` over every `Sym(3)`-valued 1-cochain
`α` on `K_k` that is not a coboundary (`0 < gaugeDist α`, see `gaugeDist_eq_zero_iff`), where
`D` is the minimum over `Sym(3)`-valued gauges. Only the values `α u v` with `u < v` enter `N`
and `D`, so ranging over all functions `Fin k → Fin k → Sym(3)` ranges over all cochains. When
no non-coboundary exists the set is empty and the value is `0` by Mathlib's convention. -/
@[expose] noncomputable def h1 (k : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ α : Fin k → Fin k → S3, 0 < gaugeDist α ∧
    r = (defect α : ℝ) / (gaugeDist α : ℝ)}

theorem h1_def (k : ℕ) :
    h1 k = sInf {r : ℝ | ∃ α : Fin k → Fin k → S3, 0 < gaugeDist α ∧
      r = (defect α : ℝ) / (gaugeDist α : ℝ)} :=
  rfl

/-- The coboundary constant is nonnegative. -/
theorem h1_nonneg (k : ℕ) : 0 ≤ h1 k := by
  apply Real.sInf_nonneg
  rintro r ⟨α, -, rfl⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every non-coboundary bounds the constant from above by its own ratio `N/D`. -/
theorem h1_le_of_pos {α : Fin k → Fin k → S3} (h : 0 < gaugeDist α) :
    h1 k ≤ (defect α : ℝ) / (gaugeDist α : ℝ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨β, -, rfl⟩
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact ⟨α, h, rfl⟩

/-! ## The upper bound at `k = 4` from the seed -/

/-- The `k = 4` witness has gauge distance exactly `6`. -/
theorem gaugeDist_w4 : gaugeDist w4 = 6 := gaugeDist_eq_of witness_k4.2.1 _ witness_k4.2.2.1

/-- **Theorem 4, upper half, k = 4.** `h₁(K_4) ≤ 4/3`, from the witness `w4` (`N = 8`,
`D = 6`). -/
theorem h1_le_k4 : h1 4 ≤ 4 / 3 := by
  have h := h1_le_of_pos (α := w4) (by rw [gaugeDist_w4]; norm_num)
  rw [gaugeDist_w4, witness_k4.1] at h
  calc h1 4 ≤ ((8 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) := h
    _ = 4 / 3 := by norm_num

/-! ## The lower bound: the star-gauge double count

Proposition 1 of the paper, which is Chapman–Lubotzky [Stability of homomorphisms, coverings and
cocycles II, Adv. Math. 463 (2025) 110117, arXiv:2311.06706] Proposition 3.2. The star gauge at
`x` makes every edge at `x` free, and the term of an edge `u < v` away from `x` is the holonomy
of the triangle `x → u → v → x`. Every triangle is met once from each of its three vertices, and
`moved` of a holonomy does not depend on where the triangle is entered or in which direction it
is run, so the star gauges cost `3N` in total. -/

/-- Reversing an edge inverts its value. -/
theorem val_swap (α : Fin k → Fin k → S3) {u v : Fin k} (h : u ≠ v) :
    val α v u = (val α u v)⁻¹ := by
  unfold val
  rcases lt_trichotomy u v with huv | huv | huv
  · rw [ite_eq_right (not_lt.mpr huv.le), ite_eq_left huv]
  · exact absurd huv h
  · rw [ite_eq_left huv, ite_eq_right (not_lt.mpr huv.le), inv_inv]

/-- Entering a triangle at another vertex conjugates the holonomy. -/
theorem moved_hol_rot (α : Fin k → Fin k → S3) (a b c : Fin k) :
    moved (hol α b c a) = moved (hol α a b c) := by
  have h : hol α b c a = (val α a b)⁻¹ * hol α a b c * val α a b := by
    unfold hol
    group
  rw [h, moved_conj]

/-- Running a triangle backwards inverts the holonomy. -/
theorem moved_hol_rev (α : Fin k → Fin k → S3) {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c)
    (hca : c ≠ a) : moved (hol α a c b) = moved (hol α a b c) := by
  have h : hol α a c b = (hol α a b c)⁻¹ := by
    unfold hol
    rw [val_swap α hca, val_swap α hbc, val_swap α hab]
    group
  rw [h, moved_inv]

/-- Swapping the first two vertices of a triangle leaves `moved` of the holonomy unchanged. -/
theorem moved_hol_swap (α : Fin k → Fin k → S3) {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c)
    (hca : c ≠ a) : moved (hol α b a c) = moved (hol α a b c) :=
  (moved_hol_rot α c b a).trans ((moved_hol_rev α hca hab hbc).trans (moved_hol_rot α c a b).symm)

/-- The **star gauge** at `x`: `β(x) = 1` and `β(u) = α(u,x)` (oriented) otherwise. -/
def starGauge (α : Fin k → Fin k → S3) (x u : Fin k) : S3 :=
  if u = x then 1 else val α u x

/-- Away from `x`, the star-gauge term of an edge is the holonomy of its triangle with `x`. -/
private theorem star_hol (α : Fin k → Fin k → S3) {x u v : Fin k} (huv : u < v) (hxu : x ≠ u)
    (hxv : x ≠ v) : (starGauge α x u)⁻¹ * α u v * starGauge α x v = hol α x u v := by
  have hval : val α u v = α u v := ite_eq_left huv
  unfold starGauge hol
  rw [ite_eq_right (Ne.symm hxu), ite_eq_right (Ne.symm hxv), val_swap α hxu, inv_inv, hval]

/-- An edge leaving `x` is free under the star gauge at `x`. -/
private theorem star_left (α : Fin k → Fin k → S3) {u v : Fin k} (huv : u < v) :
    (starGauge α u u)⁻¹ * α u v * starGauge α u v = 1 := by
  have hval : val α u v = α u v := ite_eq_left huv
  unfold starGauge
  rw [ite_eq_left (rfl : u = u), ite_eq_right huv.ne', val_swap α huv.ne, hval]
  group

/-- An edge entering `x` is free under the star gauge at `x`. -/
private theorem star_right (α : Fin k → Fin k → S3) {u v : Fin k} (huv : u < v) :
    (starGauge α v u)⁻¹ * α u v * starGauge α v v = 1 := by
  have hval : val α u v = α u v := ite_eq_left huv
  unfold starGauge
  rw [ite_eq_right huv.ne, ite_eq_left (rfl : v = v), hval]
  group

/-- The unique increasing enumeration of a 2-element set. -/
private theorem eq_ordered_pair {u v u' v' : Fin k}
    (huv : u < v) (huv' : u' < v')
    (he : ({u', v'} : Finset (Fin k)) = {u, v}) : u' = u ∧ v' = v := by
  have hmin {a b x : Fin k} (hab : a < b)
      (hx : x ∈ ({a, b} : Finset (Fin k))) : a ≤ x := by
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hab.le]
  have hmax {a b x : Fin k} (hab : a < b)
      (hx : x ∈ ({a, b} : Finset (Fin k))) : x ≤ b := by
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hab.le]
  exact ⟨le_antisymm (hmin huv' (by rw [he]; simp)) (hmin huv (by rw [← he]; simp)),
    le_antisymm (hmax huv (by rw [← he]; simp)) (hmax huv' (by rw [he]; simp))⟩

/-- The unique increasing enumeration of a 3-element set. -/
private theorem eq_ordered_of_finset {u v w u' v' w' : Fin k}
    (huv : u < v) (hvw : v < w) (huv' : u' < v') (hvw' : v' < w')
    (he : ({u', v', w'} : Finset (Fin k)) = {u, v, w}) :
    u' = u ∧ v' = v ∧ w' = w := by
  have hmin {a b c x : Fin k} (hab : a < b) (hbc : b < c)
      (hx : x ∈ ({a, b, c} : Finset (Fin k))) : a ≤ x := by
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_rfl
    · exact hab.le
    · exact (hab.trans hbc).le
  have hmax {a b c x : Fin k} (hab : a < b) (hbc : b < c)
      (hx : x ∈ ({a, b, c} : Finset (Fin k))) : x ≤ c := by
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hab.trans hbc).le
    · exact hbc.le
    · exact le_rfl
  have hu : u' = u := le_antisymm (hmin huv' hvw' (by rw [he]; simp))
    (hmin huv hvw (by rw [← he]; simp))
  have hw : w' = w := le_antisymm (hmax huv hvw (by rw [← he]; simp))
    (hmax huv' hvw' (by rw [he]; simp))
  have hv : v' ∈ ({u, v, w} : Finset (Fin k)) := he ▸ by simp
  simp only [mem_insert, mem_singleton] at hv
  refine ⟨hu, ?_, hw⟩
  rcases hv with hv | rfl | hv
  · exact (huv'.ne (hu.trans hv.symm)).elim
  · rfl
  · exact (hvw'.ne (hv.trans hw.symm)).elim

/-- Moved-point holonomy of a 3-set, read in increasing order, or `0` if it is not a
triple. -/
private def movedHol (α : Fin k → Fin k → S3) (t : Finset (Fin k)) : ℕ :=
  ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k,
    if u < v ∧ v < w ∧ ({u, v, w} : Finset (Fin k)) = t then
      moved (hol α u v w) else 0

private theorem movedHol_eq (α : Fin k → Fin k → S3) {u v w : Fin k}
    (huv : u < v) (hvw : v < w) :
    movedHol α {u, v, w} = moved (hol α u v w) := by
  unfold movedHol
  rw [Fintype.sum_eq_single u, Fintype.sum_eq_single v, Fintype.sum_eq_single w]
  · simp [huv, hvw]
  · intro w' hw'
    by_cases h : u < v ∧ v < w' ∧ ({u, v, w'} : Finset (Fin k)) = {u, v, w}
    · exact (hw' (eq_ordered_of_finset huv hvw h.1 h.2.1 h.2.2).2.2).elim
    · simp [h]
  · intro v' hv'
    refine Fintype.sum_eq_zero _ fun w' => ?_
    by_cases h : u < v' ∧ v' < w' ∧ ({u, v', w'} : Finset (Fin k)) = {u, v, w}
    · exact (hv' (eq_ordered_of_finset huv hvw h.1 h.2.1 h.2.2).2.1).elim
    · simp [h]
  · intro u' hu'
    refine Fintype.sum_eq_zero _ fun v' => Fintype.sum_eq_zero _ fun w' => ?_
    by_cases h : u' < v' ∧ v' < w' ∧ ({u', v', w'} : Finset (Fin k)) = {u, v, w}
    · exact (hu' (eq_ordered_of_finset huv hvw h.1 h.2.1 h.2.2).1).elim
    · simp [h]

private theorem sum_swap_triangles (F : Finset (Fin k) → Fin k → Fin k → Fin k → ℕ) :
    ∑ t ∈ (complete (Fin k)).triangles, ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k, F t u v w =
      ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k, ∑ t ∈ (complete (Fin k)).triangles,
        F t u v w := by
  rw [sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [sum_comm]

private theorem defect_eq_sum_movedHol (α : Fin k → Fin k → S3) :
    defect α = ∑ t ∈ (complete (Fin k)).triangles, movedHol α t := by
  rw [defect_eq_sum]
  unfold movedHol
  rw [sum_swap_triangles]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
  by_cases huv : u < v
  · by_cases hvw : v < w
    · have h : u < v ∧ v < w := ⟨huv, hvw⟩
      have ht : ({u, v, w} : Finset (Fin k)) ∈ (complete (Fin k)).triangles :=
        triple_mem_triangles_complete h.1.ne (h.1.trans h.2).ne h.2.ne
      simp [h, ht]
    · simp [hvw]
  · simp [huv]

private theorem sum_complete_edges (g : Finset (Fin k) → ℕ) :
    ∑ e ∈ (complete (Fin k)).edges, g e =
      ∑ u : Fin k, ∑ v : Fin k, if u < v then g {u, v} else 0 := by
  have hbij :
      ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin k × Fin k => p.1 < p.2),
        g ({p.1, p.2} : Finset (Fin k)) =
      ∑ e ∈ (complete (Fin k)).edges, g e := by
    refine sum_bij (fun p _ => ({p.1, p.2} : Finset (Fin k))) ?_ ?_ ?_ ?_
    · intro p hp
      exact (mem_edges_complete _).2 (card_pair (mem_filter.mp hp).2.ne)
    · intro p hp p' hp' heq
      exact Prod.ext_iff.2
        (eq_ordered_pair (mem_filter.mp hp').2 (mem_filter.mp hp).2 heq)
    · intro e he
      obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp ((mem_edges_complete _).1 he)
      rcases huv.lt_or_gt with h | h
      · exact ⟨(u, v), by simp [h], rfl⟩
      · exact ⟨(v, u), by simp [h], Finset.pair_comm _ _⟩
    · intros; rfl
  rw [← hbij, sum_filter, sum_product]

/-- The star-gauge cost of an edge is zero at `x` and otherwise the holonomy of its
triangle with `x`. -/
private theorem star_term (α : Fin k → Fin k → S3) (x u v : Fin k) (huv : u < v) :
    moved ((starGauge α x u)⁻¹ * α u v * starGauge α x v) =
      if x ∈ ({u, v} : Finset (Fin k)) then 0
        else movedHol α (insert x {u, v}) := by
  by_cases hxu : x = u
  · subst hxu
    rw [star_left α huv, moved_one]
    simp
  · by_cases hxv : x = v
    · subst hxv
      rw [star_right α huv, moved_one]
      simp
    · have hx : x ∉ ({u, v} : Finset (Fin k)) := by simp [hxu, hxv]
      have hxu' : x ≠ u := hxu
      have hxv' : x ≠ v := hxv
      rw [ite_eq_right hx, star_hol α huv hxu' hxv']
      have hins : insert x ({u, v} : Finset (Fin k)) = {x, u, v} := by ext; simp
      rw [hins]
      rcases lt_trichotomy x u with hxlt | hxe | hxgt
      · exact (movedHol_eq α hxlt huv).symm
      · exact (hxu hxe).elim
      · rcases lt_trichotomy x v with hylt | hye | hygt
        · have hset : ({x, u, v} : Finset (Fin k)) = {u, x, v} := by
            ext a; simp; tauto
          rw [hset, movedHol_eq α hxgt hylt,
            moved_hol_swap α hxgt.ne' huv.ne hylt.ne']
        · exact (hxv hye).elim
        · have hset : ({x, u, v} : Finset (Fin k)) = {u, v, x} := by
            ext a; simp; tauto
          rw [hset, movedHol_eq α huv hygt, moved_hol_rot α x u v]

private theorem cost_starGauge_eq (α : Fin k → Fin k → S3) (x : Fin k) :
    cost α (starGauge α x) =
      ∑ e ∈ (complete (Fin k)).edges,
        (if x ∈ e then 0 else movedHol α (insert x e)) := by
  rw [cost_eq_sum, sum_complete_edges]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  by_cases huv : u < v
  · simp only [huv, ↓reduceIte]
    exact star_term α x u v huv
  · simp only [huv, ↓reduceIte]

/-- **The double count.** The star gauges at the `k` vertices cost `3N` in total: each
triangle is counted once from each of its three vertices. This is the
`Sym(3)`-valued form of `TwoComplex.sum_vertex_edges_complete`, itself the complete
complex case of `TwoComplex.sum_vertex_linkEdges`. -/
theorem star_gauge_sum (α : Fin k → Fin k → S3) :
    ∑ x, cost α (starGauge α x) = 3 * defect α := by
  simp_rw [cost_starGauge_eq]
  rw [sum_vertex_edges_complete (movedHol α), nsmul_eq_mul, Nat.cast_id,
    defect_eq_sum_movedHol]

/-- **The cheapest gauge costs at most the average star gauge**: `k · D ≤ 3 · N` for every
`Sym(3)`-valued cochain on `K_k`. This is Proposition 1 of the paper, which is Chapman–Lubotzky
[Stability of homomorphisms, coverings and cocycles II, Adv. Math. 463 (2025) 110117,
arXiv:2311.06706] Proposition 3.2, in the counting convention of this file. -/
theorem gaugeDist_mul_le (α : Fin k → Fin k → S3) : k * gaugeDist α ≤ 3 * defect α := by
  rw [← star_gauge_sum α]
  calc k * gaugeDist α = ∑ _x : Fin k, gaugeDist α := by simp
    _ ≤ ∑ x, cost α (starGauge α x) := Finset.sum_le_sum fun x _ => gaugeDist_le α _

/-- **Proposition 1 (lower bound).** `k/3 ≤ h₁(K_k)` whenever `K_k` carries a `Sym(3)`-valued
non-coboundary. Proposition 1 of the paper, which is Chapman–Lubotzky [Stability of
homomorphisms, coverings and cocycles II, Adv. Math. 463 (2025) 110117, arXiv:2311.06706]
Proposition 3.2, here for `Sym(3)` values in the counting convention. -/
theorem k_div_three_le_h1 (hne : ∃ α : Fin k → Fin k → S3, 0 < gaugeDist α) :
    (k : ℝ) / 3 ≤ h1 k := by
  apply le_csInf
  · obtain ⟨α, hα⟩ := hne
    exact ⟨_, α, hα, rfl⟩
  · rintro r ⟨α, hα, rfl⟩
    have hD : (0 : ℝ) < (gaugeDist α : ℝ) := by exact_mod_cast hα
    have h' : (k : ℝ) * (gaugeDist α : ℝ) ≤ 3 * (defect α : ℝ) := by
      exact_mod_cast gaugeDist_mul_le α
    rw [le_div_iff₀ hD]
    linarith

/-! ## The value at `k = 4` -/

/-- Each of the four star gauges of the seed costs exactly `6`. -/
theorem cost_starGauge_w4 : ∀ x, cost w4 (starGauge w4 x) = 6 := by decide +kernel

/-- **Theorem 4, k = 4.** `h₁(K_4) = 4/3`. -/
theorem h1_eq_k4 : h1 4 = 4 / 3 := by
  apply le_antisymm h1_le_k4
  have h := k_div_three_le_h1 (k := 4) ⟨w4, by rw [gaugeDist_w4]; norm_num⟩
  exact_mod_cast h

end TauCeti.CoboundaryExpansion.Sym3
