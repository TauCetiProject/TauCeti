/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cheeger
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The star-gauge identity and star bound on the complete two-complex

For a cochain `α` on `TwoComplex.complete V` and a vertex `x : V`, the star gauge
`α.starGauge x : u ↦ α u x` trivializes every edge incident to `x` (where `α x x = 1` gives
`(α u x)⁻¹ * α u x * 1 = 1`), and turns every opposite edge `(u, v)` into the triangle holonomy
`(α u x)⁻¹ * α u v * α v x = α x u * α u v * α v x`.

When `ℓ : GroupNorm G` is conjugation invariant (`ℓ.toGroupSeminorm.IsConjInvariant`), every
triangle `{x, u, v}` contributes `ℓ (α.holonomy u v w)` once at each of its three vertices, giving
the exact star-gauge identity

* `Cochain.sum_cost_starGauge`: `∑ x : V, α.cost ℓ (α.starGauge x) = 3 * α.defect ℓ`.

Comparing each star-gauge cost against `α.gaugeDist ℓ` yields the general star lower bounds and
their equality case:

* `card_mul_gaugeDist_le`: `(Fintype.card V : ℝ) * α.gaugeDist ℓ ≤ 3 * α.defect ℓ`;
* `card_div_three_le_h1`: `(Fintype.card V : ℝ) / 3 ≤ h1 (TwoComplex.complete V) ℓ` whenever some
  cochain has positive gauge distance;
* `card_div_sub_two_le_h1Norm`:
  `(Fintype.card V : ℝ) / (Fintype.card V - 2) ≤ h1Norm (TwoComplex.complete V) ℓ` for
  `3 ≤ Fintype.card V`;
* `defect_div_gaugeDist_eq_card_div_three_iff`: for `0 < α.gaugeDist ℓ`, equality holds iff every
  star gauge `α.starGauge x` attains `α.gaugeDist ℓ`;
* `exists_gaugeDist_pos_complete`, `card_div_three_le_h1_of_nontrivial`, and
  `card_div_three_le_h1Sym`: for `3 ≤ Fintype.card V` and any nontrivial group `G` (finite when
  conjugation invariance is not assumed, or arbitrary when `ℓ` is conjugation invariant),
  single-edge non-identity cochains witness `0 < α.gaugeDist ℓ`, discharging the positivity
  hypothesis.

## References

* Julien Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for
  Every k ≥ 4*, Proposition 1
* Michael Chapman and Alex Lubotzky, *Stability of homomorphisms, coverings and cocycles II:
  Examples, applications and open problems*, Proposition 3.2
-/

public section

open Finset

namespace TauCeti

namespace Cochain

section StarGauge

variable {V G : Type*} [Group G] {X : TwoComplex V}

/-- The star gauge of `α` centered at vertex `x`, sending `u` to `α u x`. Because `α x x = 1`, it
takes value `1` at `x` without case splitting. -/
def starGauge (α : Cochain X G) (x : V) : V → G :=
  fun u => α u x

/-- Evaluating `α.starGauge x` at `u` returns `α u x`. -/
@[simp]
theorem starGauge_apply (α : Cochain X G) (x u : V) : α.starGauge x u = α u x := by
  rfl

/-- The star gauge at `x` takes value `1` at `x` itself. -/
theorem starGauge_self (α : Cochain X G) (x : V) : α.starGauge x x = 1 :=
  α.apply_self x

/-- At the left endpoint `u` of an edge `(u, v)`, the star gauge `α.starGauge u` trivializes the
edge term. -/
theorem starGauge_mul_left (α : Cochain X G) {u v : V} (hadj : X.Adj u v) :
    (α.starGauge u u)⁻¹ * α u v * α.starGauge u v = 1 := by
  rw [starGauge_apply, starGauge_apply, apply_self, α.map_symm hadj]
  group

/-- At the right endpoint `v` of a pair `(u, v)`, the star gauge `α.starGauge v` trivializes the
edge term. -/
theorem starGauge_mul_right (α : Cochain X G) (u v : V) :
    (α.starGauge v u)⁻¹ * α u v * α.starGauge v v = 1 := by
  rw [starGauge_apply, starGauge_apply, apply_self]
  group

/-- Whenever `x` is adjacent to `u`, the edge term of `α.starGauge x` on `(u, v)` is the holonomy
`α.holonomy x u v`. -/
theorem starGauge_mul_eq_holonomy (α : Cochain X G) {x u v : V} (hxu : X.Adj x u) :
    (α.starGauge x u)⁻¹ * α u v * α.starGauge x v = α.holonomy x u v := by
  rw [starGauge_apply, starGauge_apply, holonomy_def, α.map_symm hxu, inv_inv]

/-- **Star-gauge identity** (Beasley, Proposition 1; Chapman–Lubotzky II, Proposition 3.2): on the
complete two-complex and under a conjugation-invariant group norm, summing the costs of all star
gauges yields three times the triangle defect. -/
theorem sum_cost_starGauge [Fintype V] [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain (TwoComplex.complete V) G) :
    ∑ x : V, α.cost ℓ (α.starGauge x) = 3 * α.defect ℓ := by
  simp_rw [cost_def, TwoComplex.orderedEdges_complete]
  rw [sum_comm]
  have hpoint : ∀ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
      (∑ x : V, ℓ ((α.starGauge x p.1)⁻¹ * α p.1 p.2 * α.starGauge x p.2)) =
        (∑ x : V, if x < p.1 then ℓ (α.holonomy x p.1 p.2) else 0) +
        (∑ x : V, if p.1 < x ∧ x < p.2 then ℓ (α.holonomy p.1 x p.2) else 0) +
        (∑ x : V, if p.2 < x then ℓ (α.holonomy p.1 p.2 x) else 0) := by
    intro ⟨u, v⟩ hp
    have huv : u < v := (mem_filter.mp hp).2
    have hadj_uv : (TwoComplex.complete V).Adj u v := (TwoComplex.adj_complete_iff u v).mpr huv.ne
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rcases lt_trichotomy x u with hxu | rfl | hux
    · have hxv : ¬ (v < x) := asymm (hxu.trans huv)
      have hux' : ¬ (u < x) := asymm hxu
      have hadj_xu : (TwoComplex.complete V).Adj x u :=
        (TwoComplex.adj_complete_iff x u).mpr hxu.ne
      rw [α.starGauge_mul_eq_holonomy hadj_xu]
      simp [hxu, hux', hxv]
    · rw [α.starGauge_mul_left hadj_uv, map_one_eq_zero]
      simp [asymm huv]
    · rcases lt_trichotomy x v with hxv | rfl | hvx
      · have hxu' : ¬ (x < u) := asymm hux
        have hvx' : ¬ (v < x) := asymm hxv
        have hadj_xu : (TwoComplex.complete V).Adj x u :=
          (TwoComplex.adj_complete_iff x u).mpr hux.ne'
        have ht : ({u, x, v} : Finset V) ∈ (TwoComplex.complete V).triangles := by
          rw [TwoComplex.mem_triangles_complete, card_insert_of_notMem, card_pair hxv.ne]
          simp [hux.ne, huv.ne]
        have hswap : ℓ (α.holonomy x u v) = ℓ (α.holonomy u x v) := by
          calc
            ℓ (α.holonomy x u v) = ℓ (α.holonomy v x u) :=
              α.norm_holonomy_rotate hℓ v x u
            _ = ℓ (α.holonomy v u x) :=
              α.norm_holonomy_swap_right ℓ ht (by simp) (by simp) (by simp) huv.ne' hux.ne hxv.ne
            _ = ℓ (α.holonomy u x v) := (α.norm_holonomy_rotate hℓ v u x).symm
        rw [α.starGauge_mul_eq_holonomy hadj_xu, hswap]
        simp [hxu', hux, hxv, hvx']
      · rw [α.starGauge_mul_right u x, map_one_eq_zero]
        simp [asymm huv]
      · have hxu' : ¬ (x < u) := asymm (huv.trans hvx)
        have hxv' : ¬ (x < v) := asymm hvx
        have hadj_xu : (TwoComplex.complete V).Adj x u :=
          (TwoComplex.adj_complete_iff x u).mpr (huv.trans hvx).ne'
        have hrot : ℓ (α.holonomy x u v) = ℓ (α.holonomy u v x) :=
          (α.norm_holonomy_rotate hℓ x u v).symm
        rw [α.starGauge_mul_eq_holonomy hadj_xu, hrot]
        simp [hxu', hxv', hvx]
  rw [sum_congr rfl hpoint, sum_add_distrib, sum_add_distrib]
  have hdef : α.defect ℓ =
      ∑ a : V, ∑ b : V, ∑ c : V, if a < b ∧ b < c then ℓ (α.holonomy a b c) else 0 := by
    rw [defect_def, TwoComplex.orderedTriangles_complete, sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
  have hS1 :
      (∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
          ∑ x : V, if x < p.1 then ℓ (α.holonomy x p.1 p.2) else 0) = α.defect ℓ := by
    rw [sum_filter, Fintype.sum_prod_type, hdef]
    calc
      (∑ u : V, ∑ v : V, if u < v then ∑ x : V, (if x < u then ℓ (α.holonomy x u v) else 0) else 0)
        = ∑ u : V, ∑ v : V, ∑ x : V, if x < u ∧ u < v then ℓ (α.holonomy x u v) else 0 := by
          refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
          by_cases huv : u < v <;> simp [huv]
      _ = ∑ u : V, ∑ x : V, ∑ v : V, if x < u ∧ u < v then ℓ (α.holonomy x u v) else 0 :=
          sum_congr rfl fun u _ => sum_comm
      _ = ∑ x : V, ∑ u : V, ∑ v : V, if x < u ∧ u < v then ℓ (α.holonomy x u v) else 0 :=
          sum_comm
  have hS2 :
      (∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
          ∑ x : V, if p.1 < x ∧ x < p.2 then ℓ (α.holonomy p.1 x p.2) else 0) = α.defect ℓ := by
    rw [sum_filter, Fintype.sum_prod_type, hdef]
    calc
      (∑ u : V, ∑ v : V,
          if u < v then ∑ x : V, (if u < x ∧ x < v then ℓ (α.holonomy u x v) else 0) else 0)
        = ∑ u : V, ∑ v : V, ∑ x : V, if u < x ∧ x < v then ℓ (α.holonomy u x v) else 0 := by
          refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
          by_cases huv : u < v
          · simp [huv]
          · simp only [huv, ↓reduceIte]
            symm
            refine sum_eq_zero fun x _ => ?_
            simp only [ite_eq_right_iff, and_imp]
            intro hux hxv
            exact absurd (hux.trans hxv) huv
      _ = ∑ u : V, ∑ x : V, ∑ v : V, if u < x ∧ x < v then ℓ (α.holonomy u x v) else 0 :=
          sum_congr rfl fun u _ => sum_comm
  have hS3 :
      (∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
          ∑ x : V, if p.2 < x then ℓ (α.holonomy p.1 p.2 x) else 0) = α.defect ℓ := by
    rw [sum_filter, Fintype.sum_prod_type, hdef]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    by_cases huv : u < v <;> simp [huv]
  rw [hS1, hS2, hS3]
  ring

end StarGauge

end Cochain

section StarBound

variable {V G : Type*} [Group G]

/-- **Star bound** (Beasley, Proposition 1; Chapman–Lubotzky II, Proposition 3.2), in additive
counting form: for any conjugation-invariant group norm `ℓ` and any cochain `α` on
`TwoComplex.complete V`, `|V| · α.gaugeDist ℓ ≤ 3 · α.defect ℓ`. -/
theorem card_mul_gaugeDist_le [Fintype V] [LinearOrder V] (ℓ : GroupNorm G)
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain (TwoComplex.complete V) G) :
    (Fintype.card V : ℝ) * α.gaugeDist ℓ ≤ 3 * α.defect ℓ := by
  calc
    (Fintype.card V : ℝ) * α.gaugeDist ℓ
      = ∑ _x : V, α.gaugeDist ℓ := by simp
    _ ≤ ∑ x : V, α.cost ℓ (α.starGauge x) :=
        sum_le_sum fun x _ => α.gaugeDist_le_cost ℓ (α.starGauge x)
    _ = 3 * α.defect ℓ := α.sum_cost_starGauge hℓ

/-- Pointwise ratio form of the star bound for any cochain at positive gauge distance on
`TwoComplex.complete V`. -/
theorem card_div_three_le_defect_div_gaugeDist [Fintype V] [LinearOrder V] (ℓ : GroupNorm G)
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) {α : Cochain (TwoComplex.complete V) G}
    (hα : 0 < α.gaugeDist ℓ) :
    (Fintype.card V : ℝ) / 3 ≤ α.defect ℓ / α.gaugeDist ℓ := by
  rw [div_le_div_iff₀ (by norm_num) hα]
  linarith [card_mul_gaugeDist_le ℓ hℓ α]

/-- **Star bound on `h1`** (Beasley, Proposition 1; Chapman–Lubotzky II, Proposition 3.2):
whenever some cochain on `TwoComplex.complete V` has positive gauge distance, the coboundary
Cheeger constant is at least `Fintype.card V / 3`. -/
theorem card_div_three_le_h1 [Fintype V] [LinearOrder V] (ℓ : GroupNorm G)
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hne : ∃ α : Cochain (TwoComplex.complete V) G, 0 < α.gaugeDist ℓ) :
    (Fintype.card V : ℝ) / 3 ≤ h1 (TwoComplex.complete V) ℓ :=
  le_h1 hne fun _ hα => card_div_three_le_defect_div_gaugeDist ℓ hℓ hα

/-- Normalized star bound: for `3 ≤ Fintype.card V` and any conjugation-invariant group norm `ℓ`
admitting a cochain at positive gauge distance,
`Fintype.card V / (Fintype.card V - 2) ≤ h1Norm (TwoComplex.complete V) ℓ`. -/
theorem card_div_sub_two_le_h1Norm [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V)
    (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hne : ∃ α : Cochain (TwoComplex.complete V) G, 0 < α.gaugeDist ℓ) :
    (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 2) ≤ h1Norm (TwoComplex.complete V) ℓ := by
  rw [h1Norm_complete hV]
  have hk3 : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hsub_pos : 0 < (Fintype.card V : ℝ) - 2 := by linarith
  have hfac_nonneg : 0 ≤ 3 / ((Fintype.card V : ℝ) - 2) := div_nonneg (by norm_num) hsub_pos.le
  calc
    (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 2)
      = 3 / ((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) / 3) := by
          field_simp [hsub_pos.ne']
    _ ≤ 3 / ((Fintype.card V : ℝ) - 2) * h1 (TwoComplex.complete V) ℓ :=
        mul_le_mul_of_nonneg_left (card_div_three_le_h1 ℓ hℓ hne) hfac_nonneg

/-! ### Equality case of the star bound -/

/-- Additive equality characterization for the star bound: `|V| · α.gaugeDist ℓ = 3 · α.defect ℓ`
iff every star gauge `α.starGauge x` attains `α.gaugeDist ℓ`. -/
theorem card_mul_gaugeDist_eq_three_mul_defect_iff [Fintype V] [LinearOrder V]
    (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain (TwoComplex.complete V) G) :
    (Fintype.card V : ℝ) * α.gaugeDist ℓ = 3 * α.defect ℓ ↔
      ∀ x : V, α.cost ℓ (α.starGauge x) = α.gaugeDist ℓ := by
  rw [← α.sum_cost_starGauge hℓ]
  have hcard : (Fintype.card V : ℝ) * α.gaugeDist ℓ = ∑ _x : V, α.gaugeDist ℓ := by simp
  rw [hcard]
  have hdiff :
      (∑ _x : V, α.gaugeDist ℓ) = (∑ x : V, α.cost ℓ (α.starGauge x)) ↔
        ∑ x : V, (α.cost ℓ (α.starGauge x) - α.gaugeDist ℓ) = 0 := by
    rw [sum_sub_distrib]
    exact ⟨fun h => by linarith, fun h => by linarith⟩
  rw [hdiff, sum_eq_zero_iff_of_nonneg fun x _ => sub_nonneg.mpr (α.gaugeDist_le_cost ℓ _)]
  simp [sub_eq_zero]

/-- **Equality case of the star bound**: a cochain at positive gauge distance on
`TwoComplex.complete V` attains the star ratio `Fintype.card V / 3` iff every star gauge is an
optimal gauge for `α`. -/
theorem defect_div_gaugeDist_eq_card_div_three_iff [Fintype V] [LinearOrder V]
    (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    {α : Cochain (TwoComplex.complete V) G} (hα : 0 < α.gaugeDist ℓ) :
    α.defect ℓ / α.gaugeDist ℓ = (Fintype.card V : ℝ) / 3 ↔
      ∀ x : V, α.cost ℓ (α.starGauge x) = α.gaugeDist ℓ := by
  rw [div_eq_div_iff hα.ne' (by norm_num), ← card_mul_gaugeDist_eq_three_mul_defect_iff ℓ hℓ α]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-! ### Discharging the positive-gauge-distance hypothesis -/

/-- On any two-complex with at least one triangle and any nontrivial coefficient group `G`, placing
a non-identity element on a single edge of an ordered triangle yields a cochain with non-identity
holonomy. -/
theorem exists_holonomy_ne_one_of_triangles_nonempty [LinearOrder V] [Nontrivial G]
    {X : TwoComplex V} (hX : X.triangles.Nonempty) :
    ∃ (α : Cochain X G) (u v w : V),
      u < v ∧ v < w ∧ ({u, v, w} : Finset V) ∈ X.triangles ∧ α.holonomy u v w ≠ 1 := by
  obtain ⟨t, ht⟩ := hX
  have hc := X.triangle_card t ht
  let iso := t.orderEmbOfFin hc
  let u := iso 0
  let v := iso 1
  let w := iso 2
  have huv : u < v := iso.strictMono (by decide)
  have hvw : v < w := iso.strictMono (by decide)
  have huw : u < w := huv.trans hvw
  have hu : u ∈ t := orderEmbOfFin_mem t hc 0
  have hv : v ∈ t := orderEmbOfFin_mem t hc 1
  have hw : w ∈ t := orderEmbOfFin_mem t hc 2
  have hsub : ({u, v, w} : Finset V) ⊆ t :=
    insert_subset_iff.mpr ⟨hu, insert_subset_iff.mpr ⟨hv, singleton_subset_iff.mpr hw⟩⟩
  have hcard : ({u, v, w} : Finset V).card = 3 := by
    rw [card_insert_of_notMem, card_pair hvw.ne]
    simp [huv.ne, huw.ne]
  have ht' : ({u, v, w} : Finset V) ∈ X.triangles := by
    rwa [eq_of_subset_of_card_le hsub (by rw [hc, hcard])]
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangles ht hu hv huv.ne
  have hadj_vw : X.Adj v w := X.adj_of_mem_triangles ht hv hw hvw.ne
  have hadj_wu : X.Adj w u := X.adj_of_mem_triangles ht hw hu huw.ne'
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  let α : Cochain X G := Cochain.ofLt X fun a b => if a = u ∧ b = v then g else 1
  refine ⟨α, u, v, w, huv, hvw, ht', ?_⟩
  have h1 : α u v = g := by
    rw [Cochain.ofLt_apply_of_lt _ huv hadj_uv]
    simp
  have h2 : α v w = 1 := by
    rw [Cochain.ofLt_apply_of_lt _ hvw hadj_vw]
    simp [huv.ne']
  have h3 : α w u = 1 := by
    rw [Cochain.ofLt_apply_of_gt _ huw hadj_wu]
    simp [hvw.ne']
  rw [Cochain.holonomy_def, h1, h2, h3, mul_one, mul_one]
  exact hg

/-- On any two-complex with at least one triangle and any nontrivial coefficient group `G`, there
exists a cochain that is not a coboundary. -/
theorem exists_not_isCoboundary_of_triangles_nonempty [LinearOrder V] [Nontrivial G]
    {X : TwoComplex V} (hX : X.triangles.Nonempty) :
    ∃ α : Cochain X G, ¬ α.IsCoboundary := by
  obtain ⟨α, u, v, w, huv, hvw, ht, hhol⟩ :=
    exists_holonomy_ne_one_of_triangles_nonempty (G := G) hX
  exact ⟨α, α.not_isCoboundary_of_holonomy_ne_one ht (by simp) (by simp) (by simp)
    huv.ne hvw.ne (huv.trans hvw).ne' hhol⟩

/-- Under a conjugation-invariant group norm `ℓ` on any nontrivial group `G` (finite or infinite),
any two-complex with at least one triangle carries a cochain at strictly positive gauge distance. -/
theorem exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant
    [LinearOrder V] [Nontrivial G] {X : TwoComplex V} (hX : X.triangles.Nonempty)
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ := by
  obtain ⟨α, u, v, w, huv, hvw, ht, hhol⟩ :=
    exists_holonomy_ne_one_of_triangles_nonempty (G := G) hX
  have hpos : 0 < ℓ (α.holonomy u v w) :=
    lt_of_le_of_ne (apply_nonneg ℓ _) fun h0 => hhol (eq_one_of_map_eq_zero ℓ h0.symm)
  exact ⟨α, hpos.trans_le (α.norm_holonomy_le_gaugeDist_of_lt hℓ huv hvw ht)⟩

/-- On any two-complex with at least one triangle and any finite nontrivial group `G`, some
cochain has strictly positive gauge distance (even without conjugation invariance). -/
theorem exists_gaugeDist_pos_of_triangles_nonempty [LinearOrder V] [Finite G] [Nontrivial G]
    {X : TwoComplex V} (hX : X.triangles.Nonempty) (ℓ : GroupNorm G) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ := by
  obtain ⟨α, hα⟩ := exists_not_isCoboundary_of_triangles_nonempty (G := G) hX
  exact ⟨α, (α.gaugeDist_pos_iff ℓ).mpr hα⟩

/-- For `3 ≤ Fintype.card V` and a finite nontrivial group `G`, `TwoComplex.complete V` carries a
cochain at strictly positive gauge distance. -/
theorem exists_gaugeDist_pos_complete [Fintype V] [LinearOrder V] [Finite G] [Nontrivial G]
    (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G) :
    ∃ α : Cochain (TwoComplex.complete V) G, 0 < α.gaugeDist ℓ :=
  exists_gaugeDist_pos_of_triangles_nonempty (TwoComplex.triangles_complete_nonempty hV) ℓ

/-- Unconditional star bound on `h1 (TwoComplex.complete V) ℓ` for `3 ≤ Fintype.card V` and any
nontrivial group `G` equipped with a conjugation-invariant group norm `ℓ`. -/
theorem card_div_three_le_h1_of_nontrivial [Fintype V] [LinearOrder V] [Nontrivial G]
    (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    (Fintype.card V : ℝ) / 3 ≤ h1 (TwoComplex.complete V) ℓ :=
  card_div_three_le_h1 ℓ hℓ
    (exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant
      (TwoComplex.triangles_complete_nonempty hV) hℓ)

/-- Unconditional normalized star bound on `h1Norm (TwoComplex.complete V) ℓ` for
`3 ≤ Fintype.card V` and any nontrivial group `G` equipped with a conjugation-invariant group
norm `ℓ`. -/
theorem card_div_sub_two_le_h1Norm_of_nontrivial [Fintype V] [LinearOrder V] [Nontrivial G]
    (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 2) ≤ h1Norm (TwoComplex.complete V) ℓ :=
  card_div_sub_two_le_h1Norm hV ℓ hℓ
    (exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant
      (TwoComplex.triangles_complete_nonempty hV) hℓ)

/-- Unconditional permutation star bound: for `3 ≤ Fintype.card V`, the same-degree permutation
Cheeger constant `h1Sym (TwoComplex.complete V)` is at least `Fintype.card V / 3`. -/
theorem card_div_three_le_h1Sym [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Sym (TwoComplex.complete V) :=
  le_h1Sym fun n =>
    card_div_three_le_h1_of_nontrivial hV (Equiv.Perm.movedNorm (Fin (n + 2)))
      Equiv.Perm.isConjInvariant_movedNorm

end StarBound

end TauCeti
