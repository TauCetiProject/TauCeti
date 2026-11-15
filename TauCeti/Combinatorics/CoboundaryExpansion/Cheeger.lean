/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain
public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Coboundary Cheeger constants of finite two-complexes

For a finite 2-complex `X : TwoComplex V` and a group norm `ℓ : GroupNorm G`, this module defines
three variants of the first coboundary expansion (Cheeger) constant:

* `h1 X ℓ`: the counting constant, defined as the infimum of `α.defect ℓ / α.gaugeDist ℓ` over all
  cochains `α : Cochain X G` with `0 < α.gaugeDist ℓ` (evaluating to `0` via `sInf ∅ = 0` when
  every cochain has gauge distance `0`);
* `h1Norm X ℓ`: the normalized constant `(#X.edges / #X.triangles) * h1 X ℓ`, which rescales sums
  over edges and triangles to expectations and equals `3 / (|V| - 2) * h1 (complete V) ℓ` on
  `TwoComplex.complete V` when `3 ≤ Fintype.card V`;
* `h1Sym X`: the same-degree permutation constant `⨅ n : ℕ, h1 X (movedNorm (Fin (n + 2)))`, taking
  the infimum over finite symmetric groups of degree `m ≥ 2`.

We prove nonnegativity, upper and lower bound characterizations, attainment for `[Finite G]`,
invariance under positive rescaling of `ℓ`, order-independence and vertex-relabelling invariance
under conjugation-invariant group norms (implying that `h1 (complete V) ℓ` and `h1Sym (complete V)`
depend on `V` only through `Fintype.card V`), and the comparison
`h1Sym X ≤ h1 X (movedNorm (Fin 2))` with binary expansion.

## References

* Michael Chapman and Alex Lubotzky, *Stability of homomorphisms, coverings and cocycles II:
  Examples, applications and open problems*
* Julien Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for
  Every k ≥ 4*
* Dmitry N. Kozlov, *Threshold functions for vanishing of ℤ₂-cohomology of random 2-complexes*
-/

public section

open Finset

namespace TauCeti

section Counting

variable {V W G : Type*} [Group G]

/-- The first coboundary Cheeger constant in the counting convention: the infimum of
`α.defect ℓ / α.gaugeDist ℓ` over cochains at strictly positive gauge distance. When no cochain
has positive gauge distance, the ratio set is empty and `sInf ∅ = 0`. -/
noncomputable def h1 [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  sInf {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ}

/-- Unfold `h1` as `sInf` over expansion ratios at positive gauge distance. -/
theorem h1_def [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    h1 X ℓ =
      sInf {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ} := by
  rfl

/-- The set of expansion ratios defining `h1 X ℓ` is bounded below by `0`. -/
theorem bddBelow_h1_ratios [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    BddBelow {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨α, hpos, rfl⟩
  exact div_nonneg (α.defect_nonneg ℓ) hpos.le

/-- The coboundary Cheeger constant `h1 X ℓ` is nonnegative. -/
theorem h1_nonneg [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) : 0 ≤ h1 X ℓ := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨α, hpos, rfl⟩
  exact div_nonneg (α.defect_nonneg ℓ) hpos.le

/-- Every cochain at positive gauge distance bounds `h1 X ℓ` from above by its ratio
`defect / gaugeDist`. -/
theorem h1_le_defect_div_gaugeDist [LinearOrder V] {X : TwoComplex V} {ℓ : GroupNorm G}
    {α : Cochain X G} (hα : 0 < α.gaugeDist ℓ) :
    h1 X ℓ ≤ α.defect ℓ / α.gaugeDist ℓ :=
  csInf_le (bddBelow_h1_ratios X ℓ) ⟨α, hα, rfl⟩

/-- The Cheeger inequality `h1 X ℓ * α.gaugeDist ℓ ≤ α.defect ℓ` holds unconditionally for every
cochain `α`, including coboundaries and complexes where `h1 X ℓ = 0`. -/
theorem h1_mul_gaugeDist_le_defect [LinearOrder V] {X : TwoComplex V} (ℓ : GroupNorm G)
    (α : Cochain X G) :
    h1 X ℓ * α.gaugeDist ℓ ≤ α.defect ℓ := by
  rcases (α.gaugeDist_nonneg ℓ).eq_or_lt with hzero | hpos
  · rw [← hzero, mul_zero]
    exact α.defect_nonneg ℓ
  · exact (le_div_iff₀ hpos).mp (h1_le_defect_div_gaugeDist hpos)

/-- Whenever some cochain has positive gauge distance, `c ≤ h1 X ℓ` iff `c` bounds every positive
expansion ratio from below. -/
theorem le_h1_iff [LinearOrder V] {X : TwoComplex V} {ℓ : GroupNorm G} {c : ℝ}
    (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ) :
    c ≤ h1 X ℓ ↔ ∀ α : Cochain X G, 0 < α.gaugeDist ℓ → c ≤ α.defect ℓ / α.gaugeDist ℓ := by
  obtain ⟨α₀, hα₀⟩ := hne
  rw [h1, le_csInf_iff (bddBelow_h1_ratios X ℓ) ⟨α₀.defect ℓ / α₀.gaugeDist ℓ, α₀, hα₀, rfl⟩]
  exact ⟨fun h α hα => h _ ⟨α, hα, rfl⟩, by rintro h _ ⟨α, hα, rfl⟩; exact h α hα⟩

/-- Lower bound criterion for `h1 X ℓ` when at least one cochain has positive gauge distance. -/
theorem le_h1 [LinearOrder V] {X : TwoComplex V} {ℓ : GroupNorm G} {c : ℝ}
    (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ)
    (h : ∀ α : Cochain X G, 0 < α.gaugeDist ℓ → c ≤ α.defect ℓ / α.gaugeDist ℓ) :
    c ≤ h1 X ℓ :=
  (le_h1_iff hne).mpr h

/-- When every cochain has gauge distance `0`, the ratio set is empty and `h1 X ℓ = 0`. -/
theorem h1_eq_zero_of_forall_gaugeDist_eq_zero [LinearOrder V] {X : TwoComplex V}
    {ℓ : GroupNorm G} (h : ∀ α : Cochain X G, α.gaugeDist ℓ = 0) :
    h1 X ℓ = 0 := by
  have hempty :
      {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro α hpos
    exact absurd (h α) hpos.ne'
  rw [h1, hempty, Real.sInf_empty]

/-- Over a subsingleton (trivial) coefficient group, every cochain has gauge distance `0`, so
`h1 X ℓ = 0`. -/
@[simp]
theorem h1_of_subsingleton [LinearOrder V] [Subsingleton G] (X : TwoComplex V)
    (ℓ : GroupNorm G) : h1 X ℓ = 0 := by
  refine h1_eq_zero_of_forall_gaugeDist_eq_zero fun α => ?_
  have hα : α = 1 := by ext u v; exact Subsingleton.elim _ _
  rw [hα, Cochain.gaugeDist_one]

/-- On a complex with no triangles, every defect is `0` and hence `h1 X ℓ = 0`. -/
theorem h1_of_triangles_eq_empty [LinearOrder V] {X : TwoComplex V} (hX : X.triangles = ∅)
    (ℓ : GroupNorm G) : h1 X ℓ = 0 := by
  refine le_antisymm ?_ (h1_nonneg X ℓ)
  by_cases hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ
  · obtain ⟨α, hα⟩ := hne
    have hdef : α.defect ℓ = 0 := α.defect_of_triangles_eq_empty hX ℓ
    exact (h1_le_defect_div_gaugeDist hα).trans_eq (by rw [hdef, zero_div])
  · push Not at hne
    exact (h1_eq_zero_of_forall_gaugeDist_eq_zero fun α =>
      le_antisymm (hne α) (α.gaugeDist_nonneg ℓ)).le

/-- When `G` is finite and some cochain has positive gauge distance, the infimum defining
`h1 X ℓ` is attained by a cochain. -/
theorem exists_defect_div_gaugeDist_eq_h1 [LinearOrder V] [Finite G]
    {X : TwoComplex V} {ℓ : GroupNorm G}
    (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ α.defect ℓ / α.gaugeDist ℓ = h1 X ℓ := by
  let S := {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ}
  have hS_fin : S.Finite := by
    refine (Set.finite_range fun α : Cochain X G => α.defect ℓ / α.gaugeDist ℓ).subset ?_
    rintro _ ⟨α, _, rfl⟩
    exact ⟨α, rfl⟩
  obtain ⟨α₀, hα₀⟩ := hne
  have hS_ne : S.Nonempty := ⟨α₀.defect ℓ / α₀.gaugeDist ℓ, α₀, hα₀, rfl⟩
  obtain ⟨α, hpos, hEq⟩ := hS_ne.csInf_mem hS_fin
  exact ⟨α, hpos, hEq.symm⟩

/-! ### Invariance of `h1` -/

/-- Under a conjugation-invariant group norm, `h1 X ℓ` is independent of the `LinearOrder` chosen
on `V`. -/
theorem h1_congr_linearOrder (l₁ l₂ : LinearOrder V) {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (X : TwoComplex V) :
    @h1 V G _ l₁ X ℓ = @h1 V G _ l₂ X ℓ := by
  simp only [h1, Cochain.gaugeDist_congr_linearOrder l₁ l₂,
    Cochain.defect_congr_linearOrder l₁ l₂ hℓ]

/-- Rescaling the group norm by a positive real number cancels in every ratio `defect / gaugeDist`
and therefore leaves `h1` unchanged. -/
@[simp]
theorem h1_smulOfPos [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) :
    h1 X (ℓ.smulOfPos hr) = h1 X ℓ := by
  rw [h1, h1]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Cochain.gaugeDist_smulOfPos, Cochain.defect_smulOfPos,
    mul_pos_iff_of_pos_left hr, mul_div_mul_left _ _ hr.ne']

/-- Under a conjugation-invariant group norm, relabelling vertices along `e : V ≃ W` preserves
`h1`. -/
theorem h1_relabel [LinearOrder V] [LinearOrder W] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (X : TwoComplex V) (e : V ≃ W) :
    h1 (X.relabel e) ℓ = h1 X ℓ := by
  rw [h1, h1]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun ⟨α', hpos, hr⟩ => ?_, fun ⟨α, hpos, hr⟩ => ?_⟩
  · exact ⟨(α'.relabel e.symm).cast (by simp), by simpa using hpos,
      by simpa [Cochain.defect_relabel hℓ] using hr⟩
  · exact ⟨α.relabel e, by rwa [α.gaugeDist_relabel ℓ e],
      by rw [α.defect_relabel hℓ e, α.gaugeDist_relabel ℓ e, hr]⟩

/-- Under a conjugation-invariant group norm, any bijection `V ≃ W` identifies the Cheeger
constants of `TwoComplex.complete V` and `TwoComplex.complete W`. -/
theorem h1_complete_congr [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (e : V ≃ W) :
    h1 (TwoComplex.complete V) ℓ = h1 (TwoComplex.complete W) ℓ := by
  rw [← TwoComplex.relabel_complete e, h1_relabel hℓ]

/-- Under a conjugation-invariant group norm, `h1 (TwoComplex.complete V) ℓ` depends on the finite
vertex type `V` only through `Fintype.card V`. -/
theorem h1_complete_eq_of_card_eq [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hcard : Fintype.card V = Fintype.card W) :
    h1 (TwoComplex.complete V) ℓ = h1 (TwoComplex.complete W) ℓ :=
  h1_complete_congr hℓ (Fintype.equivOfCardEq hcard)

/-! ### The normalized Cheeger constant `h1Norm` -/

/-- The coboundary Cheeger constant in the normalized convention, converting sums over edges and
triangles into expectations by multiplying `h1 X ℓ` by `#X.edges / #X.triangles`. When `X` has no
triangles, Lean's division by zero gives `0`. -/
noncomputable def h1Norm [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  (X.edges.card / X.triangles.card : ℝ) * h1 X ℓ

/-- Unfold `h1Norm` into `(#X.edges / #X.triangles) * h1 X ℓ`. -/
theorem h1Norm_def [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    h1Norm X ℓ = (X.edges.card / X.triangles.card : ℝ) * h1 X ℓ := by
  rfl

/-- The normalized Cheeger constant `h1Norm X ℓ` is nonnegative. -/
theorem h1Norm_nonneg [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G) :
    0 ≤ h1Norm X ℓ :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (h1_nonneg X ℓ)

/-- On a complex with no triangles, `h1Norm X ℓ = 0`. -/
theorem h1Norm_of_triangles_eq_empty [LinearOrder V] {X : TwoComplex V} (hX : X.triangles = ∅)
    (ℓ : GroupNorm G) : h1Norm X ℓ = 0 := by
  simp [h1Norm, hX]

/-- On `TwoComplex.complete V` with `3 ≤ Fintype.card V`, the ratio of edge count to triangle
count is `3 / (Fintype.card V - 2)`. -/
theorem card_edges_div_card_triangles_complete [Fintype V] (hV : 3 ≤ Fintype.card V) :
    ((TwoComplex.complete V).edges.card : ℝ) / ((TwoComplex.complete V).triangles.card : ℝ) =
      3 / ((Fintype.card V : ℝ) - 2) := by
  rw [TwoComplex.natCast_card_edges_complete, TwoComplex.natCast_card_triangles_complete]
  have hk3 : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hk0 : (Fintype.card V : ℝ) ≠ 0 := by linarith
  have hk1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
  have hk2 : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- On `TwoComplex.complete V` with `3 ≤ Fintype.card V`, `h1Norm` equals
`3 / (Fintype.card V - 2) * h1`. -/
theorem h1Norm_complete [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V)
    (ℓ : GroupNorm G) :
    h1Norm (TwoComplex.complete V) ℓ =
      3 / ((Fintype.card V : ℝ) - 2) * h1 (TwoComplex.complete V) ℓ := by
  rw [h1Norm, card_edges_div_card_triangles_complete hV]

/-- Under a conjugation-invariant group norm, `h1Norm X ℓ` is independent of the `LinearOrder`
chosen on `V`. -/
theorem h1Norm_congr_linearOrder (l₁ l₂ : LinearOrder V) {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (X : TwoComplex V) :
    @h1Norm V G _ l₁ X ℓ = @h1Norm V G _ l₂ X ℓ := by
  simp only [h1Norm, h1_congr_linearOrder l₁ l₂ hℓ]

/-- Rescaling the group norm by a positive real number leaves `h1Norm` unchanged. -/
@[simp]
theorem h1Norm_smulOfPos [LinearOrder V] (X : TwoComplex V) (ℓ : GroupNorm G)
    {r : ℝ} (hr : 0 < r) :
    h1Norm X (ℓ.smulOfPos hr) = h1Norm X ℓ := by
  simp [h1Norm]

/-- Under a conjugation-invariant group norm, relabelling vertices preserves `h1Norm`. -/
theorem h1Norm_relabel [LinearOrder V] [LinearOrder W] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (X : TwoComplex V) (e : V ≃ W) :
    h1Norm (X.relabel e) ℓ = h1Norm X ℓ := by
  simp [h1Norm, h1_relabel hℓ]

/-- Under a conjugation-invariant group norm, `h1Norm (TwoComplex.complete V) ℓ` depends on `V`
only through `Fintype.card V`. -/
theorem h1Norm_complete_eq_of_card_eq [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (hcard : Fintype.card V = Fintype.card W) :
    h1Norm (TwoComplex.complete V) ℓ = h1Norm (TwoComplex.complete W) ℓ := by
  rw [← TwoComplex.relabel_complete (Fintype.equivOfCardEq hcard), h1Norm_relabel hℓ]

/-! ### The same-degree permutation Cheeger constant `h1Sym` -/

/-- The permutation coboundary Cheeger constant: the infimum of the same-degree constants
`h1 X (movedNorm (Fin m))` over all degrees `m ≥ 2`. Degree `1` is excluded because `Perm (Fin 1)`
is subsingleton, where `h1 = 0` trivially on every complex. -/
noncomputable def h1Sym [LinearOrder V] (X : TwoComplex V) : ℝ :=
  ⨅ n : ℕ, h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))

/-- Unfold `h1Sym` as the infimum over degrees `n + 2`. -/
theorem h1Sym_def [LinearOrder V] (X : TwoComplex V) :
    h1Sym X = ⨅ n : ℕ, h1 X (Equiv.Perm.movedNorm (Fin (n + 2))) := by
  rfl

/-- The family of degree-`(n + 2)` permutation Cheeger constants is bounded below by `0`. -/
theorem bddBelow_range_h1_movedNorm [LinearOrder V] (X : TwoComplex V) :
    BddBelow (Set.range fun n : ℕ => h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact h1_nonneg X _⟩

/-- The permutation Cheeger constant `h1Sym X` is nonnegative. -/
theorem h1Sym_nonneg [LinearOrder V] (X : TwoComplex V) : 0 ≤ h1Sym X :=
  Real.iInf_nonneg fun n => h1_nonneg X (Equiv.Perm.movedNorm (Fin (n + 2)))

/-- For every degree `m ≥ 2`, `h1Sym X` is at most the degree-`m` constant
`h1 X (movedNorm (Fin m))`. -/
theorem h1Sym_le_of_two_le [LinearOrder V] (X : TwoComplex V) {m : ℕ} (hm : 2 ≤ m) :
    h1Sym X ≤ h1 X (Equiv.Perm.movedNorm (Fin m)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact ciInf_le (bddBelow_range_h1_movedNorm X) n

/-- The permutation Cheeger constant is bounded above by the binary (`Sym(2) ≅ ℤ/2ℤ`) constant
(Chapman–Lubotzky II, footnote 2, in unnormalized counting scale where `movedNorm (Fin 2)` takes
values `0` and `2`, cancelling in `h1`). -/
theorem h1Sym_le_movedNorm_fin_two [LinearOrder V] (X : TwoComplex V) :
    h1Sym X ≤ h1 X (Equiv.Perm.movedNorm (Fin 2)) :=
  h1Sym_le_of_two_le X le_rfl

/-- Lower bound criterion for `h1Sym X`. -/
theorem le_h1Sym [LinearOrder V] {X : TwoComplex V} {c : ℝ}
    (h : ∀ n : ℕ, c ≤ h1 X (Equiv.Perm.movedNorm (Fin (n + 2)))) :
    c ≤ h1Sym X :=
  le_ciInf h

/-- `h1Sym X` is independent of the `LinearOrder` chosen on `V`. -/
theorem h1Sym_congr_linearOrder (l₁ l₂ : LinearOrder V) (X : TwoComplex V) :
    @h1Sym V l₁ X = @h1Sym V l₂ X :=
  iInf_congr fun _ => h1_congr_linearOrder l₁ l₂ Equiv.Perm.isConjInvariant_movedNorm X

/-- Relabelling vertices along `e : V ≃ W` preserves `h1Sym`. -/
@[simp]
theorem h1Sym_relabel [LinearOrder V] [LinearOrder W] (X : TwoComplex V) (e : V ≃ W) :
    h1Sym (X.relabel e) = h1Sym X := by
  simp only [h1Sym, h1_relabel Equiv.Perm.isConjInvariant_movedNorm]

/-- Any bijection `V ≃ W` identifies `h1Sym (complete V)` and `h1Sym (complete W)`. -/
theorem h1Sym_complete_congr [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) :
    h1Sym (TwoComplex.complete V) = h1Sym (TwoComplex.complete W) := by
  rw [← TwoComplex.relabel_complete e, h1Sym_relabel]

/-- `h1Sym (TwoComplex.complete V)` depends on the finite vertex type `V` only through
`Fintype.card V`. -/
theorem h1Sym_complete_eq_of_card_eq [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    (hcard : Fintype.card V = Fintype.card W) :
    h1Sym (TwoComplex.complete V) = h1Sym (TwoComplex.complete W) :=
  h1Sym_complete_congr (Fintype.equivOfCardEq hcard)

end Counting

end TauCeti
