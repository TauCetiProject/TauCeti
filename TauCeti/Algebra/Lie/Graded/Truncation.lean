/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Quotient
public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.PositiveDegrees.Grading
public import Mathlib.Algebra.Lie.Nilpotent

/-!
# Degree ideals and nilpotent truncations

For a positively graded Lie algebra, the sum of the homogeneous pieces above a degree cutoff is a
homogeneous Lie ideal `PositiveDegrees.degreeIdeal`. Bracketing adds degrees, so the lower central
series lies in these ideals and every degree truncation `PositiveDegrees.truncatedLie` is
nilpotent. The truncations inherit a positive grading, and the surjective transitions between
cutoffs are the quotient maps `LieIdeal.factor`.

The transition from order `k + 1` to order `k` has central kernel, equal to the sum of the
surviving pieces of degree exactly `k + 1`. Each stage of the tower of truncations is therefore a
central extension of the previous one.

No freeness, finite rank, or assumption on the coefficient ring beyond commutativity is needed.

## Main definitions

* `TauCeti.PositiveDegrees.degreeIdeal`: the homogeneous Lie ideal of terms of degree above `k`.
* `TauCeti.PositiveDegrees.truncatedLie`: the quotient by the degree ideal.
* `TauCeti.PositiveDegrees.truncatedGrading`: the images of the homogeneous pieces in the
  truncation, which is again a graded Lie algebra.
* `TauCeti.PositiveDegrees.truncationMap`: the transition between truncations.

## Main results

* `TauCeti.PositiveDegrees.lowerCentralSeries_le_degreeIdeal`: the `k`-th term of the lower
  central series lies in the degree ideal of cutoff `k`.
* `TauCeti.PositiveDegrees.ker_truncationMap_eq_iSup`: the kernel of a transition is the sum of
  the surviving pieces with degrees in the interval between the two cutoffs.
* `TauCeti.PositiveDegrees.ker_truncationMap_succ_le_center`: the kernel of the transition from
  order `k + 1` to order `k` is central.

Adapted from `Mei/Algebra/Lie/Graded/Truncation/{Basic,Transition}.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
-/

public section

namespace TauCeti.PositiveDegrees

variable {N : Type} [AddCommMonoid N] {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)

/-- Bracketing terms above cutoffs `k` and `l` gives terms above `k + l + 1`. -/
theorem lie_mem_degreeSubmodule [SetLike.GradedBracket ℒ ℒ] {k l : ℕ} {x y : L}
    (hx : x ∈ d.degreeSubmodule ℒ k) (hy : y ∈ d.degreeSubmodule ℒ l) :
    ⁅x, y⁆ ∈ d.degreeSubmodule ℒ (k + l + 1) := by
  rw [degreeSubmodule_def] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x, y⁆ ∈ d.degreeSubmodule ℒ (k + l + 1))
    hx (fun n x hx => ?_) (by simp) (fun x z hx hz => by simpa [add_lie] using add_mem hx hz)
  refine Submodule.iSup_induction _ (motive := fun y => ⁅x, y⁆ ∈ d.degreeSubmodule ℒ (k + l + 1))
    hy (fun m y hy => ?_) (by simp) (fun y z hy hz => by simpa [lie_add] using add_mem hy hz)
  refine d.le_degreeSubmodule ℒ (n := n.val + m.val) ?_ ?_
  · have := n.property
    have := m.property
    rw [map_add]
    omega
  · simpa only [vadd_eq_add] using SetLike.GradedBracket.bracket_mem hx hy

variable [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The homogeneous Lie ideal of terms of degree above `k`, denoted `F^{k+1}` in the literature. -/
def degreeIdeal (k : ℕ) : LieIdeal R L where
  toSubmodule := d.degreeSubmodule ℒ k
  lie_mem := by
    intro x y hy
    have hx : x ∈ d.degreeSubmodule ℒ 0 := by simp
    exact d.degreeSubmodule_antitone ℒ (by omega : k ≤ 0 + k + 1)
      (d.lie_mem_degreeSubmodule ℒ hx hy)

@[simp]
theorem degreeIdeal_toSubmodule (k : ℕ) :
    (d.degreeIdeal ℒ k).toSubmodule = d.degreeSubmodule ℒ k := (rfl)

/-- Every homogeneous piece above the cutoff lies in the degree ideal. -/
theorem le_degreeIdeal {n : N} {k : ℕ} (hn : (k : ℤ) < d.degree n) :
    ℒ n ≤ (d.degreeIdeal ℒ k).toSubmodule :=
  d.le_degreeSubmodule ℒ hn

/-- Degree-ideal membership is characterized by the vanishing of the low-degree components. -/
theorem mem_degreeIdeal_iff {x : L} {k : ℕ} :
    x ∈ d.degreeIdeal ℒ k ↔ ∀ n, d.degree n ≤ k → (DirectSum.decompose ℒ x n : L) = 0 :=
  d.mem_degreeSubmodule_iff ℒ

/-- The degree ideal is graded. -/
theorem degreeIdeal_isGraded (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous ℒ (d.degreeIdeal ℒ k).toSubmodule :=
  d.degreeSubmodule_isHomogeneous ℒ k

/-- Degree ideals decrease as the cutoff increases. -/
theorem degreeIdeal_antitone : Antitone (d.degreeIdeal ℒ) :=
  d.degreeSubmodule_antitone ℒ

/-- The ideal of terms above order zero is the whole positively graded Lie algebra. -/
@[simp]
theorem degreeIdeal_zero : d.degreeIdeal ℒ 0 = ⊤ := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Brackets add filtration orders. -/
theorem lie_degreeIdeal_le (k l : ℕ) :
    ⁅d.degreeIdeal ℒ k, d.degreeIdeal ℒ l⁆ ≤ d.degreeIdeal ℒ (k + l + 1) :=
  (LieSubmodule.lie_le_iff _ _ _).mpr fun _ hx _ hy => d.lie_mem_degreeSubmodule ℒ hx hy

/-- Mathlib's zero-based lower central series lies in the degree ideal of the same cutoff. -/
theorem lowerCentralSeries_le_degreeIdeal (k : ℕ) :
    LieModule.lowerCentralSeries R L L k ≤ d.degreeIdeal ℒ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ, ← d.degreeIdeal_zero ℒ]
    exact (LieSubmodule.mono_lie le_rfl ih).trans (by simpa using d.lie_degreeIdeal_le ℒ 0 k)

/-- The order-`k` Lie truncation, retaining the homogeneous degrees at most `k`. -/
abbrev truncatedLie (k : ℕ) := L ⧸ d.degreeIdeal ℒ k

/-- The `k`-th lower central term of the order-`k` truncation vanishes. -/
theorem lowerCentralSeries_truncatedLie_eq_bot (k : ℕ) :
    LieModule.lowerCentralSeries R (d.truncatedLie ℒ k) (d.truncatedLie ℒ k) k = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq k (d.degreeIdeal ℒ k).surjective_mkQ,
    LieIdeal.map_eq_bot_iff, LieIdeal.mkQ_ker]
  exact d.lowerCentralSeries_le_degreeIdeal ℒ k

/-- Every finite degree truncation is nilpotent. -/
instance truncatedLie_isNilpotent (k : ℕ) : LieRing.IsNilpotent (d.truncatedLie ℒ k) :=
  LieModule.IsNilpotent.mk _ (d.lowerCentralSeries_truncatedLie_eq_bot ℒ k)

/-- The order-zero truncation is trivial: every degree is strictly positive. -/
instance truncatedLie_zero_subsingleton : Subsingleton (d.truncatedLie ℒ 0) :=
  subsingleton_of_forall_eq 0 fun x => by
    obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ 0).surjective_mkQ x
    exact (d.degreeIdeal ℒ 0).mkQ_eq_zero.mpr (by simp)

/-- The order-one truncation is abelian: brackets of positive degrees have order at least two. -/
instance truncatedLie_one_isLieAbelian : IsLieAbelian (d.truncatedLie ℒ 1) :=
  (LieModule.trivial_iff_lower_central_eq_bot R _ _).mpr
    (d.lowerCentralSeries_truncatedLie_eq_bot ℒ 1)

/-- The degree-`n` piece of the truncation is the image of the degree-`n` piece of `L`. -/
def truncatedGrading (k : ℕ) (n : N) : Submodule R (d.truncatedLie ℒ k) :=
  (ℒ n).map (d.degreeIdeal ℒ k).toSubmodule.mkQ

/-- Each truncated homogeneous piece is the image of the original piece. -/
theorem truncatedGrading_eq (k : ℕ) (n : N) :
    d.truncatedGrading ℒ k n = (ℒ n).map (d.degreeIdeal ℒ k).toSubmodule.mkQ := (rfl)

/-- An element of the truncation has degree `n` exactly when it has a representative of degree
`n`. -/
theorem mem_truncatedGrading_iff {k : ℕ} {n : N} {y : d.truncatedLie ℒ k} :
    y ∈ d.truncatedGrading ℒ k n ↔ ∃ x ∈ ℒ n, LieSubmodule.Quotient.mk x = y :=
  Submodule.mem_map

/-- The truncated pieces form a Lie grading of the truncation. -/
noncomputable instance instGradedLieAlgebraTruncatedGrading (k : ℕ) :
    GradedLieAlgebra (d.truncatedGrading ℒ k) := by
  have : SetLike.GradedBracket (InternalGrading.ofDecomposition ℒ).piece
      (InternalGrading.ofDecomposition ℒ).piece := by
    rw [InternalGrading.ofDecomposition_piece]
    infer_instance
  have hpieces : d.truncatedGrading ℒ k =
      ((InternalGrading.ofDecomposition ℒ).quotient (d.degreeIdeal ℒ k).toSubmodule
        ((InternalGrading.isHomogeneous_ofDecomposition_piece_iff ℒ _).mpr
          (d.degreeIdeal_isGraded ℒ k))).piece :=
    funext fun n => by
      simp only [InternalGrading.quotient_piece, InternalGrading.ofDecomposition_piece,
        truncatedGrading_eq, LinearMap.restrictScalars_self]
  rw [hpieces]
  exact LieIdeal.instGradedLieAlgebraQuotient (d.degreeIdeal ℒ k) _ _

/-- Truncating a positive grading preserves positivity. -/
instance truncatedGrading_isPositiveGrading (k : ℕ) :
    IsPositiveGrading d (d.truncatedGrading ℒ k) where
  eq_bot n hn := by
    rw [truncatedGrading_eq, IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n hn, Submodule.map_bot]

/-- Homogeneous projection in the truncation commutes with the quotient map. -/
@[simp]
theorem decompose_truncatedGrading_mk (k : ℕ) (n : N) (x : L) :
    (DirectSum.decompose (d.truncatedGrading ℒ k) (Submodule.Quotient.mk x) n :
      d.truncatedLie ℒ k) = Submodule.Quotient.mk (DirectSum.decompose ℒ x n : L) :=
  (DirectSum.map_decompose_shift ℒ (d.truncatedGrading ℒ k)
    (d.degreeIdeal ℒ k).mkQ.toLinearMap.toAddMonoidHom id Function.injective_id
    (fun _ x hx => (d.mem_truncatedGrading_iff ℒ).mpr ⟨x, hx, rfl⟩) n x).symm

/-- Pieces above the cutoff vanish in the truncation. -/
@[simp]
theorem truncatedGrading_eq_bot {k : ℕ} {n : N} (hn : (k : ℤ) < d.degree n) :
    d.truncatedGrading ℒ k n = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact (d.degreeIdeal ℒ k).mkQ_eq_zero.mpr (d.le_degreeIdeal ℒ hn hy)

/-- The surjective transition from the truncation of order `l` to the truncation of order
`k ≤ l`. -/
def truncationMap {k l : ℕ} (h : k ≤ l) : d.truncatedLie ℒ l →ₗ⁅R⁆ d.truncatedLie ℒ k :=
  LieIdeal.factor (d.degreeIdeal_antitone ℒ h)

/-- A truncation transition sends the class of a representative to the class of the same
representative. -/
@[simp]
theorem truncationMap_mk {k l : ℕ} (h : k ≤ l) (x : L) :
    d.truncationMap ℒ h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x :=
  LieIdeal.factor_apply _ _

/-- The transition at the same order is the identity. -/
@[simp]
theorem truncationMap_refl (k : ℕ) : d.truncationMap ℒ (le_refl k) = LieHom.id :=
  LieIdeal.factor_refl _

/-- Successive transitions compose to the direct transition. -/
@[simp]
theorem truncationMap_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (d.truncationMap ℒ hkl).comp (d.truncationMap ℒ hlm) =
      d.truncationMap ℒ (hkl.trans hlm) :=
  LieIdeal.factor_comp _ _

/-- Transitions are surjective. -/
theorem truncationMap_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (d.truncationMap ℒ h) :=
  LieIdeal.factor_surjective _

/-- Only the degrees in `(k, l]` survive in the kernel of the transition from order `l` to
order `k`. -/
theorem ker_truncationMap_eq_iSup {k l : ℕ} (h : k ≤ l) :
    (d.truncationMap ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n ∧ d.degree n ≤ l}, d.truncatedGrading ℒ l n := by
  have hle : d.degreeIdeal ℒ l ≤ (d.degreeIdeal ℒ k).mkQ.ker := by
    simpa only [LieIdeal.mkQ_ker] using d.degreeIdeal_antitone ℒ h
  have hlift := (d.degreeIdeal ℒ l).eq_liftQ (g := d.truncationMap ℒ h) (h := hle)
    (d.truncationMap_mk ℒ h)
  have hpieces : (d.truncationMap ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n}, d.truncatedGrading ℒ l n := by
    rw [hlift, LieIdeal.ker_liftQ_mkQ,
      LieIdeal.coe_map_of_surjective (d.degreeIdeal ℒ l).surjective_mkQ,
      degreeIdeal_toSubmodule, degreeSubmodule_def, Submodule.map_iSup]
    simp only [truncatedGrading_eq]
    exact iSup_congr fun n => by rw [LieIdeal.coe_mkQ]
  rw [hpieces]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    by_cases hn : d.degree n ≤ l
    · exact le_iSup_of_le ⟨n, n.property, hn⟩ le_rfl
    · rw [d.truncatedGrading_eq_bot ℒ (lt_of_not_ge hn)]
      exact bot_le
  · exact iSup_le fun n => le_iSup_of_le ⟨n, n.property.1⟩ le_rfl

/-- A truncation transition maps each homogeneous piece onto the corresponding piece. -/
theorem map_truncationMap_truncatedGrading {k l : ℕ} (h : k ≤ l) (n : N) :
    (d.truncatedGrading ℒ l n).map (d.truncationMap ℒ h).toLinearMap =
      d.truncatedGrading ℒ k n := by
  rw [truncatedGrading_eq, truncatedGrading_eq, ← Submodule.map_comp]
  congr 1
  ext x
  exact d.truncationMap_mk ℒ h x

/-- The kernel of the transition from order `k + 1` to order `k` is exactly the sum of the pieces
of the newly retained degree `k + 1`. -/
theorem ker_truncationMap_succ (k : ℕ) :
    (d.truncationMap ℒ (Nat.le_succ k)).ker.toSubmodule =
      ⨆ n : {n : N // d.degree n = (k : ℤ) + 1}, d.truncatedGrading ℒ (k + 1) n := by
  rw [ker_truncationMap_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun n => le_iSup_of_le ⟨n, ?_⟩ le_rfl
    have := n.property
    push_cast at this
    omega
  · refine iSup_le fun n => le_iSup_of_le ⟨n, ?_⟩ le_rfl
    have := n.property
    constructor <;> omega

/-- Successive truncations are central extensions: the kernel of the transition from order `k + 1`
to order `k` is central. -/
theorem ker_truncationMap_succ_le_center (k : ℕ) :
    (d.truncationMap ℒ (Nat.le_succ k)).ker ≤ LieAlgebra.center R (d.truncatedLie ℒ (k + 1)) := by
  rw [truncationMap, LieIdeal.ker_factor_le_center_iff]
  simpa only [degreeIdeal_zero, zero_add] using d.lie_degreeIdeal_le ℒ 0 k

/-- The kernel of the transition from order `k + 1` to order `k` is abelian. -/
instance isLieAbelian_ker_truncationMap_succ (k : ℕ) :
    IsLieAbelian (d.truncationMap ℒ (Nat.le_succ k)).ker :=
  LieAlgebra.abelian_of_le_center R _ _ (d.ker_truncationMap_succ_le_center ℒ k)

end TauCeti.PositiveDegrees
