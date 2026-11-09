/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Grading
public import TauCeti.RingTheory.GradedAlgebra.DegreeFiltration

/-!
# Degree filtrations on graded universal enveloping algebras

The word description of the enveloping grading shows that nonnegative support of the Lie
algebra implies nonnegative support of its enveloping algebra, without a basis assumption.
Every strictly positive degree ideal lies in the augmentation ideal. Conversely,
the degree filtration contains the powers of the augmentation ideal when the Lie
algebra is supported in strictly positive degrees.

## Attribution

Adapted from `Mei/Algebra/Lie/UniversalEnveloping/DegreeFiltration.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). Original copyright and author credit
are retained.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)

private theorem word_eq_zero_of_degree_neg
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (l : List (Σ i, ℒ i))
    (hl : d (l.map Sigma.fst).sum < 0) :
    (l.map (fun x => ι R (x.2 : L))).prod = 0 := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases ha : d a.1 < 0
    · have ha0 : (a.2 : L) = 0 := by simpa only [hneg a.1 ha, Submodule.mem_bot] using a.2.property
      simp only [List.map_cons, List.prod_cons, ha0, map_zero, zero_mul]
    · by_cases ht : d (l.map Sigma.fst).sum < 0
      · simp only [List.map_cons, List.prod_cons, ih ht, mul_zero]
      · simp only [List.map_cons, List.sum_cons, map_add] at hl
        omega

/-- A negative-degree enveloping piece vanishes when all negative-degree Lie pieces vanish. -/
theorem homogeneousSubmodule_eq_bot_of_degree_neg
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {n : Γ} (hn : d n < 0) :
    homogeneousSubmodule ℒ n = ⊥ := by
  apply le_antisymm _ bot_le
  rw [homogeneousSubmodule_def, Submodule.span_le]
  rintro a ⟨l, hl, rfl⟩
  exact (Submodule.mem_bot R).mpr
    (word_eq_zero_of_degree_neg ℒ d hneg l (by simpa only [hl] using hn))

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

/-- The decreasing total-degree filtration on the enveloping algebra. -/
noncomputable def degreeFiltration (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    TauCeti.AlgFiltration (_root_.UniversalEnvelopingAlgebra R L) :=
  TauCeti.GradedAlgebra.degreeFiltration (homogeneousSubmodule ℒ) d
    (fun _ hn => homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hn)

/-- The enveloping degree filtration consists of the corresponding degree ideals. -/
@[simp]
theorem degreeFiltration_ideal (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k =
      TauCeti.GradedAlgebra.degreeIdeal (homogeneousSubmodule ℒ) d
        (fun _ hn => homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hn) k := by
  rw [degreeFiltration, TauCeti.GradedAlgebra.degreeFiltration_ideal]

/-- An enveloping element has filtration order at least `k` exactly when its homogeneous
components of degree below `k` vanish. -/
theorem mem_degreeFiltration_ideal_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {k : ℕ}
    {a : _root_.UniversalEnvelopingAlgebra R L} :
    a ∈ (degreeFiltration ℒ d hneg).ideal k ↔
      ∀ n, d n < k → (DirectSum.decompose (homogeneousSubmodule ℒ) a n :
        _root_.UniversalEnvelopingAlgebra R L) = 0 := by
  rw [degreeFiltration_ideal, TauCeti.GradedAlgebra.mem_degreeIdeal_iff,
    TauCeti.DirectSum.mem_degreeTail_iff]

/-- Homogeneous generators of degree at least `k` lie in filtration order `k`. -/
theorem ι_mem_degreeFiltration (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {n : Γ} {x : L} (hx : x ∈ ℒ n) {k : ℕ} (hn : (k : ℤ) ≤ d n) :
    ι R x ∈ (degreeFiltration ℒ d hneg).ideal k := by
  rw [degreeFiltration, TauCeti.GradedAlgebra.degreeFiltration_ideal]
  exact TauCeti.GradedAlgebra.le_degreeIdeal (homogeneousSubmodule ℒ) d _ hn _
    (ι_mem_homogeneousSubmodule ℒ hx)

/-- Every strictly positive degree ideal is contained in the augmentation ideal,
even when the Lie algebra has a degree-zero part. -/
theorem degreeFiltration_le_augmentation (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {k : ℕ} (hk : 0 < k) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (TauCeti.HopfIdeal.augmentation R (_root_.UniversalEnvelopingAlgebra R L)).toIdeal := by
  rw [degreeFiltration_ideal, TauCeti.GradedAlgebra.degreeIdeal_le_iff]
  intro n hn
  apply (homogeneousSubmodule_le_iff ℒ n
    ((TauCeti.HopfIdeal.augmentation R
      (_root_.UniversalEnvelopingAlgebra R L)).toIdeal.restrictScalars R)).mpr
  intro l hl
  cases l with
  | nil =>
    simp only [List.map_nil, List.sum_nil] at hl
    subst n
    simp at hn
    omega
  | cons a l =>
    exact Ideal.mul_mem_right _ _
      (TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation R L (a.2 : L))

/-- A strictly positive Lie grading puts every Lie generator in filtration order one. -/
theorem ι_mem_degreeFiltration_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x : L) :
    ι R x ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 := by
  have hneg : ∀ n, d n < 0 → ℒ n = ⊥ := fun n hn => hpos n hn.le
  induction x using _root_.DirectSum.Decomposition.inductionOn ℒ with
  | zero => simpa only [map_zero] using ((degreeFiltration ℒ d hneg).ideal 1).zero_mem
  | add x y hx hy => simpa only [map_add] using Ideal.add_mem _ hx hy
  | @homogeneous n x =>
    by_cases hn : (1 : ℤ) ≤ d n
    · exact ι_mem_degreeFiltration ℒ d hneg x.property hn
    · have hx0 : (x : L) = 0 := by
        simpa only [hpos n (by omega), Submodule.mem_bot] using x.property
      simp only [hx0, map_zero, Ideal.zero_mem]

/-- The augmentation ideal lies in filtration order one for a positive Lie grading. -/
theorem augmentation_le_degreeFiltration_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    (TauCeti.HopfIdeal.augmentation R (_root_.UniversalEnvelopingAlgebra R L)).toIdeal ≤
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 := by
  rw [TauCeti.UniversalEnvelopingAlgebra.augmentation_toIdeal_eq_span_range_ι, Ideal.span_le]
  rintro _ ⟨x, rfl⟩
  exact ι_mem_degreeFiltration_one ℒ d hpos x

/-- Powers of the augmentation ideal have at least their corresponding total degree. -/
theorem augmentation_pow_le_degreeFiltration (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (k : ℕ) :
    (TauCeti.HopfIdeal.augmentation R (_root_.UniversalEnvelopingAlgebra R L)).toIdeal ^ k ≤
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal k := by
  have hneg : ∀ n, d n < 0 → ℒ n = ⊥ := fun n hn => hpos n hn.le
  induction k with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, TauCeti.AlgFiltration.ideal_zero,
      le_refl]
  | succ k ih =>
    rw [Ideal.IsTwoSided.pow_succ, Ideal.mul_le]
    intro x hx y hy
    simpa only [Nat.add_comm 1 k] using (degreeFiltration ℒ d hneg).mul_mem
      (augmentation_le_degreeFiltration_one ℒ d hpos hx) (ih hy)

end TauCeti.UniversalEnvelopingAlgebra
