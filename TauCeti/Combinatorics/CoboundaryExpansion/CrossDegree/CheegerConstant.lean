/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Cochain

/-!
# The Chapman–Lubotzky cross-degree Cheeger constant `h1Err`

This file defines the Chapman–Lubotzky cross-degree coboundary Cheeger constant `TauCeti.h1Err`
for any `TwoComplex V`, without ambient `Fintype` or `LinearOrder` assumptions on `V`:

* `TauCeti.h1Err`: the infimum over all cochain degrees `n + 2 ≥ 2` and all cochains `α` with
  `0 < α.gaugeDistErr` of
  `(∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2) / α.gaugeDistErr`.
* **Existence of positive-distance cochains** (`TauCeti.exists_gaugeDistErr_pos_complete`): on
  `complete V` with `3 ≤ Fintype.card V` and `2 ≤ n`, some degree-`n` cochain has strictly
  positive cross-degree gauge distance.
* **Relabelling invariance and basic bounds** (`TauCeti.h1Err_nonneg`, `TauCeti.h1Err_le_div`,
  `TauCeti.le_h1Err_iff`, `TauCeti.h1Err_lt_iff`, `TauCeti.h1Err_relabel`,
  `TauCeti.h1Err_complete_congr`, and `TauCeti.h1Err_complete_eq_of_card_eq`).
* **Ordered-defect comparison** (`TauCeti.h1Err_eq_sInf_defect`, `TauCeti.h1Err_le_defect_div`,
  `TauCeti.le_h1Err_iff_defect`, `TauCeti.h1Err_lt_iff_defect`, and
  `TauCeti.le_h1Err_of_forall_defect`): whenever `[Fintype V]` and `[LinearOrder V]` are present,
  `h1Err X` agrees with the infimum using ordered `Cochain.defect`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2,
  equations (2.8)–(2.9) and the display after (2.9), pp. 6–7.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Zenodo, doi:10.5281/zenodo.23245792, Section 2 and Proposition 10.
-/

public section

open Finset

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

section CrossDegreeCheeger

variable {V W : Type*}

/-- On `complete V` with `3 ≤ Fintype.card V` and `2 ≤ n`, some degree-`n` cochain has strictly
positive cross-degree gauge distance. -/
theorem exists_gaugeDistErr_pos_complete [Fintype V] (hV : 3 ≤ Fintype.card V)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ α : Cochain (complete V) (Perm (Fin n)), 0 < α.gaugeDistErr := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨α, hα⟩ := exists_not_isCoboundary_complete (V := V) (G := Perm (Fin (k + 2))) hV
  exact ⟨α, (α.gaugeDistErr_pos_iff_not_isCoboundary hn).mpr hα⟩

/-- The Chapman–Lubotzky cross-degree Cheeger constant of `X`: the infimum over all cochain degrees
`n + 2 ≥ 2` and all cochains `α` with `0 < α.gaugeDistErr` of
`(∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2) / α.gaugeDistErr`.
-/
noncomputable def h1Err (X : TwoComplex V) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
    r = (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
      α.gaugeDistErr}

theorem h1Err_def (X : TwoComplex V) :
    h1Err X = sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
        α.gaugeDistErr} := (rfl)

private theorem bddBelow_setOf_triangleDefect_div_gaugeDistErr (X : TwoComplex V) :
    BddBelow {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
        α.gaugeDistErr} :=
  ⟨0, by
    rintro r ⟨n, α, hα, rfl⟩
    exact div_nonneg
      (div_nonneg (sum_nonneg fun t _ => α.triangleDefect_nonneg _ t) (Nat.cast_nonneg _))
      hα.le⟩

/-- The cross-degree Cheeger constant is nonnegative. -/
theorem h1Err_nonneg (X : TwoComplex V) : 0 ≤ h1Err X :=
  Real.sInf_nonneg fun _ ⟨_, α, hα, hr⟩ =>
    hr ▸ div_nonneg
      (div_nonneg (sum_nonneg fun t _ => α.triangleDefect_nonneg _ t) (Nat.cast_nonneg _))
      hα.le

/-- Every cochain of degree `n + 2 ≥ 2` at positive `gaugeDistErr` gives an upper bound on
`h1Err X`. -/
theorem h1Err_le_div {X : TwoComplex V} {n : ℕ} {α : Cochain X (Perm (Fin (n + 2)))}
    (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤
      (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
        α.gaugeDistErr :=
  csInf_le (bddBelow_setOf_triangleDefect_div_gaugeDistErr X) ⟨n, α, hα, rfl⟩

/-- When some cochain of degree `n + 2 ≥ 2` has positive `gaugeDistErr`, `c ≤ h1Err X` holds iff
`c` bounds every cross-degree expansion ratio from below. -/
theorem le_h1Err_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    c ≤ h1Err X ↔
      ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
        c ≤ (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
          α.gaugeDistErr := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, le_csInf_iff (bddBelow_setOf_triangleDefect_div_gaugeDistErr X)
    ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun h n α hα => h _ ⟨n, α, hα, rfl⟩, fun h _ ⟨n, α, hα, hr⟩ => hr ▸ h n α hα⟩

/-- When some cochain of degree `n + 2 ≥ 2` has positive `gaugeDistErr`, `h1Err X < c` holds iff
some admissible cochain has cross-degree expansion ratio strictly below `c`. -/
theorem h1Err_lt_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    h1Err X < c ↔
      ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
        (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
          α.gaugeDistErr < c := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, csInf_lt_iff (bddBelow_setOf_triangleDefect_div_gaugeDistErr X)
    ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun ⟨_, ⟨n, α, hα, hr⟩, hlt⟩ => ⟨n, α, hα, hr ▸ hlt⟩,
    fun ⟨n, α, hα, hlt⟩ => ⟨_, ⟨n, α, hα, rfl⟩, hlt⟩⟩

/-- Lower-bound criterion for `h1Err X` in the presence of a cochain at positive `gaugeDistErr`. -/
theorem le_h1Err_of_forall {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ}
    (hc : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
      c ≤ (∑ t ∈ X.triangles, α.triangleDefect (movedNorm (Fin (n + 2))) t) / (n + 2 : ℕ) /
        α.gaugeDistErr) :
    c ≤ h1Err X :=
  (le_h1Err_iff hne).mpr hc

/-- Relabelling `X` along `e : V ≃ W` preserves `h1Err`. -/
@[simp] theorem h1Err_relabel (X : TwoComplex V) (e : V ≃ W) : h1Err (X.relabel e) = h1Err X := by
  rw [h1Err_def, h1Err_def]; congr 1; ext r
  refine exists_congr fun n => ?_
  exact ((Cochain.relabelEquiv X e).exists_congr fun α => by
    rw [Cochain.relabelEquiv_apply, α.gaugeDistErr_relabel e, X.sum_triangles_relabel e]
    simp_rw [α.triangleDefect_relabel_map isConjInvariant_movedNorm e]).symm

/-- `h1Err` on the complete complex is preserved along any bijection `V ≃ W`. -/
theorem h1Err_complete_congr [Fintype V] [Fintype W]
    (e : V ≃ W) : h1Err (complete V) = h1Err (complete W) := by
  rw [← relabel_complete e, h1Err_relabel (complete V) e]

/-- `h1Err (complete V)` depends on `V` only through `Fintype.card V`. -/
theorem h1Err_complete_eq_of_card_eq [Fintype V] [Fintype W]
    (hcard : Fintype.card V = Fintype.card W) : h1Err (complete V) = h1Err (complete W) :=
  h1Err_complete_congr (Fintype.equivOfCardEq hcard)

section OrderedComparison

variable [Fintype V] [LinearOrder V]

/-- With `[Fintype V]` and `[LinearOrder V]`, `h1Err X` agrees with the infimum using ordered
`Cochain.defect`. -/
theorem h1Err_eq_sInf_defect (X : TwoComplex V) :
    h1Err X = sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} := by
  rw [h1Err_def]
  congr 1; ext r
  exact exists_congr fun n => exists_congr fun α => by
    rw [Cochain.defect_eq_sum_triangles isConjInvariant_movedNorm α]

/-- Ordered-`defect` upper bound on `h1Err X`. -/
theorem h1Err_le_defect_div {X : TwoComplex V} {n : ℕ} {α : Cochain X (Perm (Fin (n + 2)))}
    (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr := by
  rw [Cochain.defect_eq_sum_triangles isConjInvariant_movedNorm α]
  exact h1Err_le_div hα

/-- Ordered-`defect` iff characterization of `c ≤ h1Err X`. -/
theorem le_h1Err_iff_defect {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    c ≤ h1Err X ↔
      ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
        c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr := by
  simp_rw [Cochain.defect_eq_sum_triangles isConjInvariant_movedNorm]
  exact le_h1Err_iff hne

/-- Ordered-`defect` iff characterization of `h1Err X < c`. -/
theorem h1Err_lt_iff_defect {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    h1Err X < c ↔
      ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
        α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr < c := by
  simp_rw [Cochain.defect_eq_sum_triangles isConjInvariant_movedNorm]
  exact h1Err_lt_iff hne

/-- Ordered-`defect` lower-bound criterion for `h1Err X`. -/
theorem le_h1Err_of_forall_defect {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ}
    (hc : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
      c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr) :
    c ≤ h1Err X :=
  (le_h1Err_iff_defect hne).mpr hc

end OrderedComparison

end CrossDegreeCheeger

end TauCeti

end
