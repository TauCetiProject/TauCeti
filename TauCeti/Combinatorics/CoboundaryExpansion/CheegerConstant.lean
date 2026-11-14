/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Invariance
public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# First coboundary Cheeger constants of a two-complex

Given a two-complex `X` on a finite linearly ordered vertex type `V` and a group norm `ℓ` on `G`,
this file defines the three first coboundary expansion constants studied by Chapman and Lubotzky
(*Stability of homomorphisms, coverings and cocycles I, II*) and Jeromie Beasley (*The Permutation
Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*):

* `TauCeti.h1 X ℓ`: the counting coboundary Cheeger constant, defined as the infimum of
  `α.defect ℓ / α.gaugeDist ℓ` over 1-cochains `α` at strictly positive gauge distance. When no
  such cochain exists, the ratio set is empty and `Real.sInf_empty` gives `0`.
* `TauCeti.h1Norm X ℓ`: the normalized Cheeger constant `(#X.edges / #X.triangles) * h1 X ℓ`. On
  the complete complex `complete V` with `3 ≤ Fintype.card V`, the normalizing factor simplifies to
  `3 / (Fintype.card V - 2)`.
* `TauCeti.h1Sym X`: the same-degree permutation Cheeger constant, defined as the infimum of
  `h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))` over all degrees `n + 2 ≥ 2` (Chapman–Lubotzky II,
  §2.2, eq. (2.8)). Degree `1` is excluded because `Equiv.Perm (Fin 1)` is trivial, where `h1`
  vanishes identically.

We establish nonnegativity, finite-group attainment of the infimum when a positive-gauge-distance
cochain exists, invariance under positive rescaling of the norm, independence of the vertex linear
order and invariance under vertex relabelling when `ℓ` is conjugation invariant, and the degree-2
comparison `h1Sym X ≤ h1 X (Equiv.Perm.movedNorm (Fin 2))`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles I: equivalence*,
  arXiv:2310.17474v2, Eur. J. Math. 11 (2025), art. 13, §5.1.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2,
  eq. (2.8), footnote 2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.23245792, version 7.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

/-! ### The counting Cheeger constant `h1` -/

section Counting

variable {V W G : Type*} [Group G]

/-- The first coboundary Cheeger constant of `X` with respect to `ℓ` in the counting convention:
the infimum of `α.defect ℓ / α.gaugeDist ℓ` over cochains at strictly positive gauge distance. -/
noncomputable def h1 [Fintype V] [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  sInf {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ}

theorem h1_def [Fintype V] [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    h1 X ℓ =
      sInf {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ} :=
  (rfl)

section FixedOrder

variable [Fintype V] [LinearOrder V]

private theorem bddBelow_ratioSet (X : TwoComplex V) (ℓ : GroupNorm G) :
    BddBelow {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ} := by
  refine ⟨0, ?_⟩
  rintro r ⟨α, hα, rfl⟩
  exact div_nonneg (α.defect_nonneg ℓ) hα.le

/-- The counting Cheeger constant is nonnegative. -/
theorem h1_nonneg (X : TwoComplex V) (ℓ : GroupNorm G) : 0 ≤ h1 X ℓ := by
  rw [h1_def]
  refine Real.sInf_nonneg ?_
  rintro r ⟨α, hα, rfl⟩
  exact div_nonneg (α.defect_nonneg ℓ) hα.le

/-- Every cochain at positive gauge distance gives an upper bound on `h1 X ℓ`. -/
theorem h1_le_div {X : TwoComplex V} {ℓ : GroupNorm G} {α : Cochain X G}
    (hα : 0 < α.gaugeDist ℓ) : h1 X ℓ ≤ α.defect ℓ / α.gaugeDist ℓ :=
  csInf_le (bddBelow_ratioSet X ℓ) ⟨α, hα, rfl⟩

/-- When some cochain has positive gauge distance, `c ≤ h1 X ℓ` holds iff `c` bounds every
expansion ratio from below. -/
theorem le_h1_iff {X : TwoComplex V} {ℓ : GroupNorm G}
    (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ) {c : ℝ} :
    c ≤ h1 X ℓ ↔ ∀ α : Cochain X G, 0 < α.gaugeDist ℓ → c ≤ α.defect ℓ / α.gaugeDist ℓ := by
  obtain ⟨α₀, hα₀⟩ := hne
  rw [h1_def, le_csInf_iff (bddBelow_ratioSet X ℓ) ⟨α₀.defect ℓ / α₀.gaugeDist ℓ, α₀, hα₀, rfl⟩]
  constructor
  · exact fun h α hα => h _ ⟨α, hα, rfl⟩
  · rintro h _ ⟨α, hα, rfl⟩
    exact h α hα

/-- Lower-bound criterion for `h1 X ℓ` in the presence of a cochain at positive gauge distance. -/
theorem le_h1_of_forall {X : TwoComplex V} {ℓ : GroupNorm G}
    (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ) {c : ℝ}
    (hc : ∀ α : Cochain X G, 0 < α.gaugeDist ℓ → c ≤ α.defect ℓ / α.gaugeDist ℓ) :
    c ≤ h1 X ℓ :=
  (le_h1_iff hne).mpr hc

/-- When every cochain has gauge distance zero, the ratio set is empty and `h1 X ℓ = 0`. -/
theorem h1_eq_zero_of_forall_gaugeDist_eq_zero {X : TwoComplex V} {ℓ : GroupNorm G}
    (h : ∀ α : Cochain X G, α.gaugeDist ℓ = 0) : h1 X ℓ = 0 := by
  have hempty :
      {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨α, hpos, _⟩ => hpos.ne' (h α)
  rw [h1_def, hempty, Real.sInf_empty]

/-- Over a trivial coefficient group every cochain is trivial, so `h1 X ℓ = 0`. -/
@[simp]
theorem h1_subsingleton [Subsingleton G] (X : TwoComplex V) (ℓ : GroupNorm G) : h1 X ℓ = 0 := by
  refine h1_eq_zero_of_forall_gaugeDist_eq_zero fun α => ?_
  have hα : α = 1 := Subsingleton.elim α 1
  simp [hα]

/-- When `G` is finite and some cochain has positive gauge distance, the infimum defining `h1 X ℓ`
is attained by a cochain. -/
theorem exists_div_eq_h1 [Finite G] {X : TwoComplex V} {ℓ : GroupNorm G}
    (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ α.defect ℓ / α.gaugeDist ℓ = h1 X ℓ := by
  obtain ⟨α₀, hα₀⟩ := hne
  let S := {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ}
  have hSne : S.Nonempty := ⟨α₀.defect ℓ / α₀.gaugeDist ℓ, α₀, hα₀, rfl⟩
  have hSfin : S.Finite :=
    (Set.finite_range fun α : Cochain X G => α.defect ℓ / α.gaugeDist ℓ).subset
      fun _ ⟨α, _, hr⟩ => ⟨α, hr.symm⟩
  obtain ⟨α, hα, hmem⟩ := hSne.csInf_mem hSfin
  exact ⟨α, hα, hmem.symm⟩

/-! ### Invariance under norm scaling, vertex ordering, and relabelling -/

/-- Multiplying a group norm by a positive real leaves `h1` unchanged. -/
@[simp]
theorem h1_smulOfPos (X : TwoComplex V) (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) :
    h1 X (ℓ.smulOfPos hr) = h1 X ℓ := by
  rw [h1_def, h1_def]
  congr 1
  ext x
  refine exists_congr fun α => ?_
  rw [α.gaugeDist_smulOfPos ℓ hr, α.defect_smulOfPos ℓ hr,
    mul_pos_iff_of_pos_left hr, mul_div_mul_left _ _ hr.ne']

end FixedOrder

/-- Under a conjugation-invariant norm, `h1 X ℓ` does not depend on the `LinearOrder` chosen on
`V`. -/
theorem h1_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (X : TwoComplex V)
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    @h1 V G _ _ l₁ X ℓ = @h1 V G _ _ l₂ X ℓ := by
  simp only [@h1_def V G _ _ l₁ X ℓ, @h1_def V G _ _ l₂ X ℓ,
    Cochain.gaugeDist_congr_linearOrder l₁ l₂ ℓ, Cochain.defect_congr_linearOrder l₁ l₂ hℓ]

/-- Under a conjugation-invariant norm, relabelling `X` along `e : V ≃ W` preserves `h1`. -/
@[simp]
theorem h1_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W] (X : TwoComplex V)
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (e : V ≃ W) :
    h1 (X.relabel e) ℓ = h1 X ℓ := by
  rw [h1_def, h1_def]
  congr 1
  ext r
  exact ((Cochain.relabelEquiv X e).exists_congr fun α => by simp [α.defect_relabel hℓ e]).symm

/-- Under a conjugation-invariant norm, `h1` on the complete complex is preserved along any
bijection `V ≃ W`. -/
theorem h1_complete_congr [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (e : V ≃ W) :
    h1 (complete V) ℓ = h1 (complete W) ℓ := by
  rw [← relabel_complete e, h1_relabel (complete V) hℓ e]

/-- Under a conjugation-invariant norm, `h1 (complete V) ℓ` depends on `V` only through
`Fintype.card V`. -/
theorem h1_complete_eq_of_card_eq [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hcard : Fintype.card V = Fintype.card W) :
    h1 (complete V) ℓ = h1 (complete W) ℓ :=
  h1_complete_congr hℓ (Fintype.equivOfCardEq hcard)

end Counting

/-! ### The normalized Cheeger constant `h1Norm` -/

section Normalized

variable {V W G : Type*} [Group G]

/-- The first coboundary Cheeger constant in the normalized convention: `h1 X ℓ` multiplied by
`#X.edges / #X.triangles`. When `X` has no triangles this evaluates to `0` via division by zero in
`ℝ`; theorems about `h1Norm` assume at least one triangle (`3 ≤ Fintype.card V` on `complete V`). -/
noncomputable def h1Norm [Fintype V] [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  (X.edges.card / X.triangles.card : ℝ) * h1 X ℓ

theorem h1Norm_def [Fintype V] [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    h1Norm X ℓ = (X.edges.card / X.triangles.card : ℝ) * h1 X ℓ := (rfl)

theorem h1Norm_nonneg [Fintype V] [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    0 ≤ h1Norm X ℓ :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (h1_nonneg X ℓ)

/-- Over a trivial coefficient group every cochain is trivial, so `h1Norm X ℓ = 0`. -/
@[simp]
theorem h1Norm_subsingleton [Subsingleton G] [Fintype V] [LinearOrder V] (X : TwoComplex V)
    (ℓ : GroupNorm G) : h1Norm X ℓ = 0 := by
  simp [h1Norm_def]

@[simp]
theorem h1Norm_smulOfPos [Fintype V] [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G)
    {r : ℝ} (hr : 0 < r) : h1Norm X (ℓ.smulOfPos hr) = h1Norm X ℓ := by
  simp [h1Norm_def]

theorem h1Norm_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (X : TwoComplex V)
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    @h1Norm V G _ _ l₁ X ℓ = @h1Norm V G _ _ l₂ X ℓ := by
  rw [@h1Norm_def V G _ _ l₁ X ℓ, @h1Norm_def V G _ _ l₂ X ℓ, h1_congr_linearOrder l₁ l₂ X hℓ]

@[simp]
theorem h1Norm_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W] (X : TwoComplex V)
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (e : V ≃ W) :
    h1Norm (X.relabel e) ℓ = h1Norm X ℓ := by
  simp [h1Norm_def, h1_relabel X hℓ e]

/-- On `complete V` with `3 ≤ Fintype.card V`, `h1Norm` equals `(3 / (Fintype.card V - 2)) * h1`. -/
theorem h1Norm_complete [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V)
    (ℓ : GroupNorm G) :
    h1Norm (complete V) ℓ = (3 / (Fintype.card V - 2 : ℝ)) * h1 (complete V) ℓ := by
  rw [h1Norm_def, card_edges_div_card_triangles_complete hV]

/-- Under a conjugation-invariant norm, `h1Norm (complete V) ℓ` depends on `V` only through
`Fintype.card V`. -/
theorem h1Norm_complete_eq_of_card_eq [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hcard : Fintype.card V = Fintype.card W) :
    h1Norm (complete V) ℓ = h1Norm (complete W) ℓ := by
  simp only [h1Norm_def, card_edges_complete, card_triangles_complete, hcard,
    h1_complete_eq_of_card_eq hℓ hcard]

end Normalized

/-! ### The same-degree permutation Cheeger constant `h1Sym` -/

section Symmetric

variable {V W : Type*}

/-- The same-degree permutation Cheeger constant of `X`: the infimum of
`h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))` over all degrees `n + 2 ≥ 2`. -/
noncomputable def h1Sym [Fintype V] [LinearOrder V] (X : TwoComplex V) : ℝ :=
  ⨅ n : ℕ, h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))

theorem h1Sym_def [Fintype V] [LinearOrder V] (X : TwoComplex V) :
    h1Sym X = ⨅ n : ℕ, h1 X (Equiv.Perm.movedNorm (Fin (n + 2))) := (rfl)

theorem bddBelow_range_h1_movedNorm [Fintype V] [LinearOrder V] (X : TwoComplex V) :
    BddBelow (Set.range fun n : ℕ => h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact h1_nonneg X _⟩

theorem h1Sym_nonneg [Fintype V] [LinearOrder V] (X : TwoComplex V) : 0 ≤ h1Sym X :=
  Real.iInf_nonneg fun _ => h1_nonneg X _

theorem h1Sym_le_h1_movedNorm_add_two [Fintype V] [LinearOrder V] (X : TwoComplex V) (n : ℕ) :
    h1Sym X ≤ h1 X (Equiv.Perm.movedNorm (Fin (n + 2))) :=
  ciInf_le (bddBelow_range_h1_movedNorm X) n

/-- Every permutation degree `m ≥ 2` bounds `h1Sym X` from above. -/
theorem h1Sym_le_h1_movedNorm [Fintype V] [LinearOrder V] (X : TwoComplex V) {m : ℕ}
    (hm : 2 ≤ m) : h1Sym X ≤ h1 X (Equiv.Perm.movedNorm (Fin m)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact h1Sym_le_h1_movedNorm_add_two X n

/-- Specialization of `h1Sym_le_h1_movedNorm` to degree `2` (`Sym(2) ≅ 𝔽₂`): the permutation
Cheeger constant is at most the `𝔽₂` Cheeger constant (Chapman–Lubotzky II, footnote 2). -/
theorem h1Sym_le_h1_movedNorm_fin_two [Fintype V] [LinearOrder V] (X : TwoComplex V) :
    h1Sym X ≤ h1 X (Equiv.Perm.movedNorm (Fin 2)) :=
  h1Sym_le_h1_movedNorm_add_two X 0

theorem le_h1Sym_iff [Fintype V] [LinearOrder V] (X : TwoComplex V) {c : ℝ} :
    c ≤ h1Sym X ↔ ∀ n : ℕ, c ≤ h1 X (Equiv.Perm.movedNorm (Fin (n + 2))) :=
  le_ciInf_iff (bddBelow_range_h1_movedNorm X)

/-- Degree `1` has trivial permutation group, so `h1 X (movedNorm (Fin 1)) = 0`. -/
theorem h1_movedNorm_fin_one [Fintype V] [LinearOrder V] (X : TwoComplex V) :
    h1 X (Equiv.Perm.movedNorm (Fin 1)) = 0 :=
  h1_subsingleton X _

theorem h1Sym_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (X : TwoComplex V) :
    @h1Sym V _ l₁ X = @h1Sym V _ l₂ X := by
  simp only [@h1Sym_def V _ l₁ X, @h1Sym_def V _ l₂ X]
  congr 1
  ext n
  exact h1_congr_linearOrder l₁ l₂ X Equiv.Perm.isConjInvariant_movedNorm

@[simp]
theorem h1Sym_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W] (X : TwoComplex V)
    (e : V ≃ W) : h1Sym (X.relabel e) = h1Sym X := by
  simp only [h1Sym_def]
  congr 1
  ext n
  exact h1_relabel X Equiv.Perm.isConjInvariant_movedNorm e

theorem h1Sym_complete_eq_of_card_eq [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (hcard : Fintype.card V = Fintype.card W) :
    h1Sym (complete V) = h1Sym (complete W) := by
  simp only [h1Sym_def]
  congr 1
  ext n
  exact h1_complete_eq_of_card_eq Equiv.Perm.isConjInvariant_movedNorm hcard

end Symmetric

end TauCeti

end
