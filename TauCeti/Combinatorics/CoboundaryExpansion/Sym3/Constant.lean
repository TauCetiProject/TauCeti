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

open Equiv

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
@[expose] def gaugeDist (α : Fin k → Fin k → S3) : ℕ :=
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

private theorem lsum_flatMap {ι κ : Type*} (l : List ι) (f : ι → List κ) (g : κ → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      ih]

private theorem lsum_filter {ι : Type*} (l : List ι) (p : ι → Bool) (f : ι → ℕ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a = true then f a else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hp : p a = true
    · simp only [List.filter_cons_of_pos hp, List.map_cons, List.sum_cons, ih, ite_eq_left hp]
    · simp only [List.filter_cons_of_neg hp, List.map_cons, List.sum_cons, ih, ite_eq_right hp,
        zero_add]

/-- A sum over the edges `u < v` as a double sum over vertices. -/
private theorem sum_edges (g : Fin k → Fin k → ℕ) :
    ((edges k).map fun e => g e.1 e.2).sum =
      ∑ u : Fin k, ∑ v : Fin k, if u < v then g u v else 0 := by
  unfold edges
  rw [lsum_flatMap, Fin.sum_univ_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u _
  rw [List.map_map, lsum_filter, Fin.sum_univ_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  simp

/-- A sum over the triangles `u < v < w` as a triple sum over vertices. -/
private theorem sum_triangles (g : Fin k → Fin k → Fin k → ℕ) :
    ((triangles k).map fun t => g t.1 t.2.1 t.2.2).sum =
      ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k, if u < v ∧ v < w then g u v w else 0 := by
  unfold triangles
  rw [lsum_flatMap, Fin.sum_univ_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u _
  rw [lsum_flatMap, Fin.sum_univ_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  rw [List.map_map, lsum_filter, Fin.sum_univ_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  simp

theorem cost_eq_sum (α : Fin k → Fin k → S3) (β : Fin k → S3) :
    cost α β = ∑ u : Fin k, ∑ v : Fin k,
      if u < v then moved ((β u)⁻¹ * α u v * β v) else 0 :=
  sum_edges fun u v => moved ((β u)⁻¹ * α u v * β v)

/-- The holonomy of `α` around the triangle `a → b → c → a`. -/
@[expose] def hol (α : Fin k → Fin k → S3) (a b c : Fin k) : S3 := val α a b * val α b c * val α c a

theorem defect_eq_sum (α : Fin k → Fin k → S3) :
    defect α = ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k,
      if u < v ∧ v < w then moved (hol α u v w) else 0 :=
  sum_triangles fun u v w => moved (hol α u v w)

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
@[expose] def starGauge (α : Fin k → Fin k → S3) (x u : Fin k) : S3 :=
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

/-- The star-gauge term of one edge, split by where `x` sits relative to `u < v`. -/
private theorem star_point (α : Fin k → Fin k → S3) (x u v : Fin k) :
    (if u < v then moved ((starGauge α x u)⁻¹ * α u v * starGauge α x v) else 0) =
      (if x < u ∧ u < v then moved (hol α x u v) else 0) +
      (if u < x ∧ x < v then moved (hol α u x v) else 0) +
      (if u < v ∧ v < x then moved (hol α u v x) else 0) := by
  by_cases huv : u < v
  · rcases lt_trichotomy x u with hxu | hxu | hxu
    · have hxv : x < v := hxu.trans huv
      rw [star_hol α huv hxu.ne hxv.ne]
      simp only [ite_eq_left huv, ite_eq_left (And.intro hxu huv),
        ite_eq_right (fun h : u < x ∧ x < v => lt_asymm hxu h.1),
        ite_eq_right (fun h : u < v ∧ v < x => lt_asymm hxv h.2), add_zero]
    · rw [hxu, star_left α huv]
      simp only [ite_eq_left huv, moved_one,
        ite_eq_right (fun h : u < u ∧ u < v => lt_irrefl u h.1),
        ite_eq_right (fun h : u < v ∧ v < u => lt_asymm huv h.2), add_zero]
    · rcases lt_trichotomy x v with hxv | hxv | hxv
      · rw [star_hol α huv hxu.ne' hxv.ne, moved_hol_swap α hxu.ne' huv.ne hxv.ne']
        simp only [ite_eq_left huv, ite_eq_right (fun h : x < u ∧ u < v => lt_asymm hxu h.1),
          ite_eq_left (And.intro hxu hxv), ite_eq_right (fun h : u < v ∧ v < x => lt_asymm hxv h.2),
          zero_add, add_zero]
      · rw [hxv, star_right α huv]
        simp only [ite_eq_left huv, moved_one,
          ite_eq_right (fun h : v < u ∧ u < v => lt_asymm huv h.1),
          ite_eq_right (fun h : u < v ∧ v < v => lt_irrefl v h.2), add_zero]
      · rw [star_hol α huv hxu.ne' hxv.ne', moved_hol_rot α x u v]
        simp only [ite_eq_left huv, ite_eq_right (fun h : x < u ∧ u < v => lt_asymm hxu h.1),
          ite_eq_right (fun h : u < x ∧ x < v => lt_asymm hxv h.2), ite_eq_left (And.intro huv hxv),
          zero_add]
  · simp only [ite_eq_right huv, ite_eq_right (fun h : x < u ∧ u < v => huv h.2),
      ite_eq_right (fun h : u < x ∧ x < v => huv (h.1.trans h.2)),
      ite_eq_right (fun h : u < v ∧ v < x => huv h.1), add_zero]

/-- **The double count.** The star gauges at the `k` vertices cost `3N` in total: each triangle
is counted once from each of its three vertices. -/
theorem star_gauge_sum (α : Fin k → Fin k → S3) :
    ∑ x, cost α (starGauge α x) = 3 * defect α := by
  have hA : ∑ x : Fin k, ∑ u : Fin k, ∑ v : Fin k,
      (if x < u ∧ u < v then moved (hol α x u v) else 0) = defect α :=
    (defect_eq_sum α).symm
  have hB : ∑ x : Fin k, ∑ u : Fin k, ∑ v : Fin k,
      (if u < x ∧ x < v then moved (hol α u x v) else 0) = defect α := by
    rw [defect_eq_sum]
    exact Finset.sum_comm
  have hC : ∑ x : Fin k, ∑ u : Fin k, ∑ v : Fin k,
      (if u < v ∧ v < x then moved (hol α u v x) else 0) = defect α := by
    rw [defect_eq_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact Finset.sum_comm
  calc ∑ x, cost α (starGauge α x)
      = ∑ x : Fin k, ∑ u : Fin k, ∑ v : Fin k,
          ((if x < u ∧ u < v then moved (hol α x u v) else 0) +
           (if u < x ∧ x < v then moved (hol α u x v) else 0) +
           (if u < v ∧ v < x then moved (hol α u v x) else 0)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [cost_eq_sum]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        exact star_point α x u v
    _ = defect α + defect α + defect α := by
        simp only [Finset.sum_add_distrib, hA, hB, hC]
    _ = 3 * defect α := by ring

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

/-- README 6.1 check: each of the four star gauges of the seed costs exactly `6`. -/
theorem cost_starGauge_w4 : ∀ x, cost w4 (starGauge w4 x) = 6 := by decide +kernel

/-- **Theorem 4, k = 4.** `h₁(K_4) = 4/3`. -/
theorem h1_eq_k4 : h1 4 = 4 / 3 := by
  apply le_antisymm h1_le_k4
  have h := k_div_three_le_h1 (k := 4) ⟨w4, by rw [gaugeDist_w4]; norm_num⟩
  exact_mod_cast h

end TauCeti.CoboundaryExpansion.Sym3
