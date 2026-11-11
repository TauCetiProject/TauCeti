/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Grading
public import TauCeti.RingTheory.GradedAlgebra.Degree.Filtration

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

/-- Homogeneous enveloping elements of degree at least `k` lie in filtration order `k`. -/
theorem mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {n : Γ} {a : _root_.UniversalEnvelopingAlgebra R L}
    (ha : a ∈ homogeneousSubmodule ℒ n) {k : ℕ} (hn : (k : ℤ) ≤ d n) :
    a ∈ (degreeFiltration ℒ d hneg).ideal k := by
  rw [degreeFiltration_ideal]
  exact TauCeti.GradedAlgebra.le_degreeIdeal _ d _ hn a ha

/-- Homogeneous generators of degree at least `k` lie in filtration order `k`. -/
theorem ι_mem_degreeFiltration (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {n : Γ} {x : L} (hx : x ∈ ℒ n) {k : ℕ} (hn : (k : ℤ) ≤ d n) :
    ι R x ∈ (degreeFiltration ℒ d hneg).ideal k :=
  mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg
    (ι_mem_homogeneousSubmodule ℒ hx) hn

/-- To contain a filtration ideal, it suffices to contain the homogeneous enveloping pieces of
degree at least `k`. -/
theorem degreeFiltration_ideal_le_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ)
    (K : Ideal (_root_.UniversalEnvelopingAlgebra R L)) :
    (degreeFiltration ℒ d hneg).ideal k ≤ K ↔
      ∀ n, (k : ℤ) ≤ d n → ∀ a ∈ homogeneousSubmodule ℒ n, a ∈ K := by
  rw [degreeFiltration_ideal]
  exact TauCeti.GradedAlgebra.degreeIdeal_le_iff _ d _ k K

/-- The enveloping degree filtration is separated. -/
theorem iInf_degreeFiltration_ideal_eq_bot (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (⨅ k : ℕ, (degreeFiltration ℒ d hneg).ideal k) = ⊥ := by
  simp only [degreeFiltration_ideal]
  exact TauCeti.GradedAlgebra.iInf_degreeIdeal_eq_bot _ d _

/-- Every strictly positive degree ideal is contained in the augmentation ideal,
even when the Lie algebra has a degree-zero part. -/
theorem degreeFiltration_le_augmentation (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {k : ℕ} (hk : 0 < k) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (TauCeti.HopfIdeal.augmentation R (_root_.UniversalEnvelopingAlgebra R L)).toIdeal := by
  rw [degreeFiltration_ideal_le_iff]
  intro n hn
  have hle := (homogeneousSubmodule_le_iff ℒ n
    ((TauCeti.HopfIdeal.augmentation R
      (_root_.UniversalEnvelopingAlgebra R L)).toIdeal.restrictScalars R)).mpr (by
    intro l hl
    cases l with
    | nil =>
      simp only [List.map_nil, List.sum_nil] at hl
      subst n
      rw [map_zero] at hn
      omega
    | cons a l =>
      rw [List.map_cons, List.prod_cons]
      exact (Submodule.restrictScalars_mem R _ _).mpr <| Ideal.mul_mem_right _ _
        (HopfIdeal.mem_toIdeal.mpr
          (TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation R L (a.2 : L))))
  exact fun a ha => (Submodule.restrictScalars_mem R _ _).mp (hle ha)

/-- A strictly positive Lie grading puts every Lie generator in filtration order one. -/
theorem ι_mem_degreeFiltration_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x : L) :
    ι R x ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 := by
  have hneg : ∀ n, d n < 0 → ℒ n = ⊥ := fun n hn => hpos n hn.le
  induction x using _root_.DirectSum.Decomposition.inductionOn ℒ with
  | zero => simpa only [map_zero] using ((degreeFiltration ℒ d hneg).ideal 1).zero_mem
  | add x y hx hy => simpa only [map_add] using Ideal.add_mem _ hx hy
  | @homogeneous n x =>
    by_cases hn : (1 : ℤ) ≤ d n
    · exact ι_mem_degreeFiltration ℒ d hneg x.property (by exact_mod_cast hn)
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
  exact (Ideal.pow_right_mono (augmentation_le_degreeFiltration_one ℒ d hpos) k).trans
    ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal_one_pow_le k)

end TauCeti.UniversalEnvelopingAlgebra
