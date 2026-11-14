/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Link
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The star bound on the complete two-complex

For a 1-cochain `α` on `X` and a vertex `x : V`, the star gauge `α.starGauge x` sends each vertex
`u` to `α u x` (and in particular pins `x` to `α x x = 1`). On the complete two-complex
`complete V`:

* every edge containing `x` has zero cost under `α.starGauge x`;
* every edge `{u, v}` avoiding `x` has cost equal to the holonomy norm of the triangle
  `{x, u, v}` whenever `ℓ` is conjugation invariant.

Summing over `x : V` via `TwoComplex.sum_vertex_edges_complete` yields the star identity
`∑ x : V, α.cost ℓ (α.starGauge x) = 3 * α.defect ℓ` (Jeromie Beasley, *The Permutation Coboundary
Constant of the Complete Complex Is k/3 for Every k≥4*, Proposition 1; for permutation
coefficients, M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II*,
Proposition 3.2).

Because each star gauge has cost at least `α.gaugeDist ℓ`, it follows that:

* `(Fintype.card V : ℝ) * α.gaugeDist ℓ ≤ 3 * α.defect ℓ` (`TauCeti.card_mul_gaugeDist_le`),
  with equality if and only if every star gauge is optimal (Beasley, Corollary 2);
* `(Fintype.card V : ℝ) / 3 ≤ h1 (complete V) ℓ` (`TauCeti.card_div_three_le_h1`) and
  `(Fintype.card V : ℝ) / (Fintype.card V - 2) ≤ h1Norm (complete V) ℓ` whenever a cochain at
  positive gauge distance exists;
* when `3 ≤ Fintype.card V` and `G` is any nontrivial group, a single-edge cochain around a filled
  triangle witnesses positive gauge distance under conjugation invariance, discharging that
  hypothesis unconditionally and giving `(Fintype.card V : ℝ) / 3 ≤ h1Sym (complete V)`
  (`TauCeti.card_div_three_le_h1Sym`).

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.23245792, version 7, Proposition 1 and Corollary 2.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117,
  Proposition 3.2.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

/-! ### Star gauges and the star identity -/

namespace Cochain

section StarGauge

variable {V G : Type*} [Group G] {X : TwoComplex V}

/-- The star gauge of `α` centered at vertex `x`, sending `u` to `α u x`. Because `α x x = 1`, this
pins `x` to `1` without requiring `DecidableEq V`. -/
def starGauge (α : Cochain X G) (x : V) : V → G := fun u => α u x

@[simp, grind =]
theorem starGauge_apply (α : Cochain X G) (x u : V) : α.starGauge x u = α u x := (rfl)

theorem starGauge_self (α : Cochain X G) (x : V) : α.starGauge x x = 1 := α.apply_self x

/-- On `complete V` under a conjugation-invariant norm, the edge cost of `α.starGauge x` on an edge
`e` vanishes when `x ∈ e` and equals `α.triangleDefect ℓ (insert x e)` when `x ∉ e`. -/
theorem edgeCost_starGauge_complete [Fintype V] [DecidableEq V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain (complete V) G) (x : V) {e : Finset V}
    (he : e ∈ (complete V).edges) :
    α.edgeCost ℓ (α.starGauge x) e = if x ∈ e then 0 else α.triangleDefect ℓ (insert x e) := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp ((mem_edges_complete e).mp he)
  rw [α.edgeCost_of_mem_edges ℓ (α.starGauge x) he huv (by simp) (by simp)]
  by_cases hx : x ∈ ({u, v} : Finset V)
  · simp only [hx, ↓reduceIte]
    rcases mem_insert.mp hx with rfl | hx'
    · simp [α.apply_swap x v]
    · rw [mem_singleton.mp hx']; simp
  · simp only [hx, ↓reduceIte]
    have ht : insert x ({u, v} : Finset V) ∈ (complete V).triangles := by
      rw [mem_triangles_complete, card_insert_of_notMem hx, card_pair huv]
    rw [α.triangleDefect_triple hℓ ht]
    simp [starGauge_apply, holonomy_def, (α.apply_swap u x).symm]

/-- The star identity on the complete two-complex (Beasley, Proposition 1; Chapman–Lubotzky II,
Proposition 3.2): under a conjugation-invariant group norm, summing the costs of all star gauges
gives three times the triangle defect. -/
theorem sum_cost_starGauge [Fintype V] [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain (complete V) G) :
    ∑ x : V, α.cost ℓ (α.starGauge x) = 3 * α.defect ℓ := by
  simp_rw [α.cost_eq_sum_edges ℓ]
  have h := sum_vertex_edges_complete (V := V) (α.triangleDefect ℓ)
  rw [nsmul_eq_mul, Nat.cast_ofNat, ← α.defect_eq_sum_triangles hℓ] at h
  rw [← h]
  exact sum_congr rfl fun x _ => sum_congr rfl fun e he => α.edgeCost_starGauge_complete hℓ x he

end StarGauge

end Cochain

/-! ### The star bound and its equality case -/

section StarBound

variable {V G : Type*} [Fintype V] [LinearOrder V] [Group G]

/-- The star bound in counting form (Beasley, Proposition 1; Chapman–Lubotzky II, Proposition 3.2):
for every cochain on `complete V` and every conjugation-invariant group norm `ℓ`,
`card V * gaugeDist α ≤ 3 * defect α`. -/
theorem card_mul_gaugeDist_le (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain (complete V) G) :
    (Fintype.card V : ℝ) * α.gaugeDist ℓ ≤ 3 * α.defect ℓ := by
  calc (Fintype.card V : ℝ) * α.gaugeDist ℓ
      = ∑ _x : V, α.gaugeDist ℓ := by simp
    _ ≤ ∑ x : V, α.cost ℓ (α.starGauge x) :=
        sum_le_sum fun x _ => α.gaugeDist_le_cost ℓ (α.starGauge x)
    _ = 3 * α.defect ℓ := α.sum_cost_starGauge hℓ

/-- Pointwise ratio form of the star bound for a cochain at positive gauge distance. -/
theorem Cochain.card_div_three_le_defect_div_gaugeDist {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) {α : Cochain (complete V) G}
    (hα : 0 < α.gaugeDist ℓ) :
    (Fintype.card V : ℝ) / 3 ≤ α.defect ℓ / α.gaugeDist ℓ := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα, mul_comm _ (3 : ℝ)]
  exact card_mul_gaugeDist_le ℓ hℓ α

/-- The star bound as a lower bound on the counting Cheeger constant `h1 (complete V) ℓ`, whenever
some cochain on `complete V` has positive gauge distance. -/
theorem card_div_three_le_h1 (ℓ : GroupNorm G) (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hne : ∃ α : Cochain (complete V) G, 0 < α.gaugeDist ℓ) :
    (Fintype.card V : ℝ) / 3 ≤ h1 (complete V) ℓ :=
  le_h1_of_forall hne fun _ hα => Cochain.card_div_three_le_defect_div_gaugeDist hℓ hα

/-- Normalized form of the star bound on `complete V` for `3 ≤ Fintype.card V`. -/
theorem card_div_card_sub_two_le_h1Norm (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G)
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hne : ∃ α : Cochain (complete V) G, 0 < α.gaugeDist ℓ) :
    (Fintype.card V : ℝ) / (Fintype.card V - 2) ≤ h1Norm (complete V) ℓ := by
  rw [h1Norm_complete hV ℓ]
  have hk3 : (3 : ℝ) ≤ Fintype.card V := Nat.ofNat_le_cast.mpr hV
  have hpos : 0 < 3 / ((Fintype.card V : ℝ) - 2) := div_pos (by norm_num) (by linarith)
  calc
    (Fintype.card V : ℝ) / (Fintype.card V - 2)
        = (3 / ((Fintype.card V : ℝ) - 2)) * ((Fintype.card V : ℝ) / 3) := by ring
    _ ≤ (3 / ((Fintype.card V : ℝ) - 2)) * h1 (complete V) ℓ :=
        mul_le_mul_of_nonneg_left (card_div_three_le_h1 ℓ hℓ hne) hpos.le

/-- Equality holds in `card_mul_gaugeDist_le` if and only if every star gauge is optimal for `α`
(Beasley, Corollary 2). -/
theorem Cochain.three_mul_defect_eq_card_mul_gaugeDist_iff {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain (complete V) G) :
    3 * α.defect ℓ = (Fintype.card V : ℝ) * α.gaugeDist ℓ ↔
      ∀ x : V, α.cost ℓ (α.starGauge x) = α.gaugeDist ℓ := by
  have hsum : (Fintype.card V : ℝ) * α.gaugeDist ℓ = ∑ _x : V, α.gaugeDist ℓ := by simp
  rw [← α.sum_cost_starGauge hℓ, hsum, eq_comm,
    sum_eq_sum_iff_of_le fun x _ => α.gaugeDist_le_cost ℓ (α.starGauge x)]
  simp [eq_comm]

/-- A cochain on `complete V` at positive gauge distance attains the star ratio `card V / 3` if and
only if every star gauge is an optimal gauge for `α` (Beasley, Corollary 2). -/
theorem Cochain.defect_div_gaugeDist_eq_card_div_three_iff {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) {α : Cochain (complete V) G}
    (hα : 0 < α.gaugeDist ℓ) :
    α.defect ℓ / α.gaugeDist ℓ = (Fintype.card V : ℝ) / 3 ↔
      ∀ x : V, α.cost ℓ (α.starGauge x) = α.gaugeDist ℓ := by
  rw [div_eq_div_iff hα.ne' (by norm_num : (3 : ℝ) ≠ 0), mul_comm _ (3 : ℝ),
    α.three_mul_defect_eq_card_mul_gaugeDist_iff hℓ]

end StarBound

/-! ### Unconditional star bounds -/

section Unconditional

/-- For `3 ≤ Fintype.card V` and any nontrivial group `G` equipped with a conjugation-invariant
norm `ℓ`, `card V / 3 ≤ h1 (complete V) ℓ`. -/
theorem card_div_three_le_h1_of_nontrivial {V G : Type*} [Fintype V] [LinearOrder V]
    [Group G] [Nontrivial G] (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G)
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    (Fintype.card V : ℝ) / 3 ≤ h1 (complete V) ℓ :=
  card_div_three_le_h1 ℓ hℓ (exists_gaugeDist_pos_complete_of_isConjInvariant hV hℓ)

/-- Normalized star bound on `complete V` for `3 ≤ Fintype.card V` and any nontrivial group `G`
equipped with a conjugation-invariant norm `ℓ`. -/
theorem card_div_card_sub_two_le_h1Norm_of_nontrivial {V G : Type*} [Fintype V] [LinearOrder V]
    [Group G] [Nontrivial G] (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G)
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    (Fintype.card V : ℝ) / (Fintype.card V - 2) ≤ h1Norm (complete V) ℓ :=
  card_div_card_sub_two_le_h1Norm hV ℓ hℓ (exists_gaugeDist_pos_complete_of_isConjInvariant hV hℓ)

/-- For `3 ≤ Fintype.card V`, every permutation degree `n + 2 ≥ 2` has a nontrivial symmetric group,
so the star bound yields `card V / 3 ≤ h1Sym (complete V)`. -/
theorem card_div_three_le_h1Sym {V : Type*} [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Sym (complete V) :=
  (le_h1Sym_iff (complete V)).mpr fun _ =>
    card_div_three_le_h1_of_nontrivial hV _ Equiv.Perm.isConjInvariant_movedNorm

end Unconditional

end TauCeti

end
