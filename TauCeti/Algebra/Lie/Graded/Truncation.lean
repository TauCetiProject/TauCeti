/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.Nilpotent
public import TauCeti.Algebra.Lie.Graded.Quotient
public import TauCeti.Algebra.PositiveDegrees.Basic
import TauCeti.Algebra.DirectSum.Internal

/-!
# Degree ideals and truncations of positively graded Lie algebras

Let `d` be positive degree data on `N`, with allowed monoid `P` and degree `δ`. A family of
submodules `ℒ n` is a positive grading for `d` (`TauCeti.IsPositiveGrading`) when `ℒ n = 0`
unless `n` is a nonzero element of `P`. For a positively graded Lie algebra `L`, the degree ideal
`TauCeti.degreeIdeal d ℒ k` is the sum of the homogeneous pieces `ℒ n` with `δ n > k`, and the
quotient `L ⧸ degreeIdeal d ℒ k` is the truncation of `L` retaining the degrees at most `k`.

The degree ideals form a decreasing, multiplicative filtration by homogeneous Lie ideals, starting
with `L` itself. Consequently each term of the lower central series lies in the corresponding
degree ideal, the truncations are nilpotent, and the kernel of the transition from the order
`k + 1` truncation to the order `k` truncation is central and spanned by the image of the pieces of
degree exactly `k + 1`. No finiteness or freeness hypothesis is needed: the statements hold over
every commutative ring.

## Main definitions

* `TauCeti.IsPositiveGrading`: the pieces outside the nonzero allowed degrees vanish.
* `TauCeti.degreeIdeal`: the Lie ideal spanned by the pieces of degree greater than `k`.

## Main results

* `TauCeti.mem_degreeIdeal_iff`: membership in a degree ideal by vanishing of the low-degree
  components.
* `TauCeti.isHomogeneous_degreeIdeal`: degree ideals are homogeneous, so the truncations inherit
  the Lie grading through `LieIdeal.instGradedLieAlgebraQuotient`.
* `TauCeti.lie_degreeIdeal_le`: the degree filtration is multiplicative.
* `TauCeti.lowerCentralSeries_le_degreeIdeal` and
  `TauCeti.lowerCentralSeries_quotient_degreeIdeal_eq_bot`: the order `k` truncation has
  nilpotency class at most `k`; in particular it is nilpotent.
* `TauCeti.map_mkQ_degreeIdeal_le_center` and `TauCeti.map_mkQ_degreeIdeal_toSubmodule`: the
  kernel of the order `k + 1` truncation onto the order `k` truncation is central, and is the image
  of the pieces of degree `k + 1`.
* `TauCeti.IsPositiveGrading.quotient` and `TauCeti.quotient_piece_degreeIdeal_eq_bot`: the
  order `k` truncation is positively graded, with no pieces of degree greater than `k`.

## References

* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, Algebraic
  Geometry 4 (2017), §2.1, arXiv:1603.00416.
-/

public section

open DirectSum

namespace TauCeti

section Grading

variable {N R M : Type*} [AddCommMonoid N] [Semiring R] [AddCommMonoid M] [Module R M]

/-- A family of submodules indexed by `N` is a positive grading for the positive degree data `d`
when its pieces vanish outside the nonzero allowed degrees, that is, unless the index lies in
`d.monoid` and is nonzero. -/
class IsPositiveGrading (d : PositiveDegrees N) (ℳ : N → Submodule R M) : Prop where
  /-- The pieces indexed outside the allowed monoid vanish. -/
  eq_bot_of_notMem : ∀ ⦃n⦄, n ∉ d.monoid → ℳ n = ⊥
  /-- The piece of degree zero vanishes. -/
  eq_bot_zero : ℳ 0 = ⊥

variable (d : PositiveDegrees N) (ℳ : N → Submodule R M) [IsPositiveGrading d ℳ]

/-- A nonzero homogeneous element of a positive grading has strictly positive degree. -/
theorem IsPositiveGrading.degree_pos {n : N} {x : M} (hx : x ∈ ℳ n) (hx0 : x ≠ 0) :
    0 < d.degree n := by
  by_cases hn : n ∈ d.monoid
  · refine d.degree_pos hn fun hn0 ↦ hx0 ?_
    rw [hn0, IsPositiveGrading.eq_bot_zero (d := d) (ℳ := ℳ)] at hx
    exact (Submodule.mem_bot R).1 hx
  · rw [IsPositiveGrading.eq_bot_of_notMem (d := d) (ℳ := ℳ) hn] at hx
    exact absurd ((Submodule.mem_bot R).1 hx) hx0

/-- A homogeneous element of a positive grading whose degree is not positive vanishes. -/
theorem IsPositiveGrading.eq_zero_of_degree_nonpos {n : N} {x : M} (hx : x ∈ ℳ n)
    (hn : d.degree n ≤ 0) : x = 0 := by
  by_contra hx0
  exact absurd (IsPositiveGrading.degree_pos d ℳ hx hx0) (not_lt.2 hn)

end Grading

section DegreeIdeal

variable {N R L : Type*} [AddCommMonoid N] [DecidableEq N] [CommRing R] [LieRing L]
  [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L)

/-- The bracket of an element whose components vanish in degrees at most `a` with one whose
components vanish in degrees at most `b` lies in the sum of the pieces of degree greater than
`a + b + 1`. -/
private theorem lie_mem_biSup_degree_lt [GradedLieAlgebra ℒ] {a b : ℤ} {x y : L}
    (hx : ∀ m, d.degree m ≤ a → (decompose ℒ x m : L) = 0)
    (hy : ∀ n, d.degree n ≤ b → (decompose ℒ y n : L) = 0) :
    ⁅x, y⁆ ∈ ⨆ (n) (_ : a + b + 1 < d.degree n), ℒ n := by
  classical
  rw [← sum_support_decompose ℒ x, ← sum_support_decompose ℒ y, sum_lie]
  refine Submodule.sum_mem _ fun m _ ↦ ?_
  rw [lie_sum]
  refine Submodule.sum_mem _ fun n _ ↦ ?_
  by_cases hm : d.degree m ≤ a
  · rw [hx m hm, zero_lie]
    exact Submodule.zero_mem _
  by_cases hn : d.degree n ≤ b
  · rw [hy n hn, lie_zero]
    exact Submodule.zero_mem _
  refine Submodule.mem_iSup_of_mem (m + n) (Submodule.mem_iSup_of_mem ?_ ?_)
  · rw [map_add]
    omega
  · exact SetLike.GradedBracket.bracket_mem (decompose ℒ x m).2 (decompose ℒ y n).2

variable [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The degree ideal `F^{k+1}` of a positively graded Lie algebra: the sum of the homogeneous
pieces of degree greater than `k`. The quotient by it is the truncation of the Lie algebra
retaining the degrees at most `k`. -/
def degreeIdeal (k : ℕ) : LieIdeal R L where
  toSubmodule := ⨆ (n) (_ : (k : ℤ) < d.degree n), ℒ n
  lie_mem {x y} hy := by
    -- Every element has vanishing components in degrees at most zero, by positivity.
    have hx (m : N) (hm : d.degree m ≤ 0) : (decompose ℒ x m : L) = 0 :=
      IsPositiveGrading.eq_zero_of_degree_nonpos d ℒ (decompose ℒ x m).2 hm
    have hy' := (mem_biSup_iff_decompose_eq_zero ℒ _).1 hy
    have hxy := lie_mem_biSup_degree_lt d ℒ hx (b := k) fun n hn ↦ hy' n (not_lt.2 hn)
    refine (iSup₂_mono' fun n hn ↦ ⟨n, ?_, le_rfl⟩ :
      ⨆ (n) (_ : 0 + (k : ℤ) + 1 < d.degree n), ℒ n ≤ _) hxy
    omega

/-- The degree ideal is the sum of the homogeneous pieces of degree greater than `k`. -/
theorem degreeIdeal_toSubmodule (k : ℕ) :
    (degreeIdeal d ℒ k).toSubmodule = ⨆ (n) (_ : (k : ℤ) < d.degree n), ℒ n :=
  (rfl)

/-- An element lies in the degree ideal `F^{k+1}` exactly when its components of degree at most
`k` vanish. -/
theorem mem_degreeIdeal_iff {k : ℕ} {x : L} :
    x ∈ degreeIdeal d ℒ k ↔ ∀ n, d.degree n ≤ k → (decompose ℒ x n : L) = 0 := by
  rw [← LieSubmodule.mem_toSubmodule, degreeIdeal_toSubmodule,
    mem_biSup_iff_decompose_eq_zero]
  simp only [not_lt]

/-- A homogeneous piece of degree greater than `k` lies in the degree ideal `F^{k+1}`. -/
theorem piece_le_degreeIdeal {k : ℕ} {n : N} (hn : (k : ℤ) < d.degree n) :
    ℒ n ≤ (degreeIdeal d ℒ k).toSubmodule := by
  rw [degreeIdeal_toSubmodule]
  exact le_iSup₂_of_le n hn le_rfl

/-- Degree ideals are homogeneous: the components of an element of a degree ideal lie in it. -/
theorem isHomogeneous_degreeIdeal (k : ℕ) :
    SetLike.IsHomogeneous ℒ (degreeIdeal d ℒ k).toSubmodule := by
  intro n x hx
  by_cases hn : (k : ℤ) < d.degree n
  · exact piece_le_degreeIdeal d ℒ hn (decompose ℒ x n).2
  · rw [(mem_degreeIdeal_iff d ℒ).1 hx n (not_lt.1 hn)]
    exact Submodule.zero_mem _

/-- The degree ideals decrease as the truncation order grows. -/
theorem degreeIdeal_antitone : Antitone (degreeIdeal d ℒ) := by
  intro k l hkl
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, degreeIdeal_toSubmodule,
    degreeIdeal_toSubmodule]
  exact iSup₂_mono' fun n hn ↦ ⟨n, lt_of_le_of_lt (by exact_mod_cast hkl) hn, le_rfl⟩

/-- The degree ideal `F^1` is the whole Lie algebra, since every piece has positive degree. -/
@[simp]
theorem degreeIdeal_zero : degreeIdeal d ℒ 0 = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ (mem_degreeIdeal_iff d ℒ).2 fun n hn ↦ ?_
  exact IsPositiveGrading.eq_zero_of_degree_nonpos d ℒ (decompose ℒ x n).2 (by exact_mod_cast hn)

/-- The degree filtration is multiplicative: `⁅F^{j+1}, F^{k+1}⁆ ≤ F^{j+k+2}`. -/
theorem lie_degreeIdeal_le (j k : ℕ) :
    ⁅degreeIdeal d ℒ j, degreeIdeal d ℒ k⁆ ≤ degreeIdeal d ℒ (j + k + 1) := by
  rw [LieSubmodule.lie_le_iff]
  intro x hx y hy
  have hxy := lie_mem_biSup_degree_lt d ℒ ((mem_degreeIdeal_iff d ℒ).1 hx)
    ((mem_degreeIdeal_iff d ℒ).1 hy)
  rw [← LieSubmodule.mem_toSubmodule, degreeIdeal_toSubmodule]
  push_cast
  exact hxy

/-- Bracketing with any element raises the degree filtration by one:
`⁅L, F^{k+1}⁆ ≤ F^{k+2}`. -/
theorem lie_top_degreeIdeal_le (k : ℕ) :
    ⁅(⊤ : LieIdeal R L), degreeIdeal d ℒ k⁆ ≤ degreeIdeal d ℒ (k + 1) := by
  have h := lie_degreeIdeal_le d ℒ 0 k
  rwa [degreeIdeal_zero, zero_add] at h

/-- The `k`-th term of the lower central series (numbered from zero) lies in the degree ideal
`F^{k+1}`. -/
theorem lowerCentralSeries_le_degreeIdeal (k : ℕ) :
    LieModule.lowerCentralSeries R L L k ≤ degreeIdeal d ℒ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ]
    exact (LieSubmodule.mono_lie le_rfl ih).trans (lie_top_degreeIdeal_le d ℒ k)

/-- The truncation of order `k` has nilpotency class at most `k`: the `k`-th term of its lower
central series vanishes. -/
theorem lowerCentralSeries_quotient_degreeIdeal_eq_bot (k : ℕ) :
    LieModule.lowerCentralSeries R (L ⧸ degreeIdeal d ℒ k) (L ⧸ degreeIdeal d ℒ k) k = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq k (LieIdeal.surjective_mkQ _),
    LieIdeal.map_eq_bot_iff, LieIdeal.mkQ_ker]
  exact lowerCentralSeries_le_degreeIdeal d ℒ k

/-- The truncations of a positively graded Lie algebra are nilpotent. -/
instance isNilpotent_quotient_degreeIdeal (k : ℕ) :
    LieRing.IsNilpotent (L ⧸ degreeIdeal d ℒ k) :=
  (LieModule.isNilpotent_iff R _ _).2 ⟨k, lowerCentralSeries_quotient_degreeIdeal_eq_bot d ℒ k⟩

/-- The degree ideal `F^{k+1}` is spanned by the pieces of degree exactly `k + 1` together with
the next degree ideal `F^{k+2}`. -/
theorem degreeIdeal_toSubmodule_eq_sup (k : ℕ) :
    (degreeIdeal d ℒ k).toSubmodule =
      (⨆ (n) (_ : d.degree n = k + 1), ℒ n) ⊔ (degreeIdeal d ℒ (k + 1)).toSubmodule := by
  refine le_antisymm ?_ (sup_le (iSup₂_le fun n hn ↦ piece_le_degreeIdeal d ℒ (by omega))
    (degreeIdeal_antitone d ℒ k.le_succ))
  rw [degreeIdeal_toSubmodule]
  refine iSup₂_le fun n hn ↦ ?_
  by_cases hnk : d.degree n = k + 1
  · exact le_sup_of_le_left (le_iSup₂_of_le n hnk le_rfl)
  · exact le_sup_of_le_right (piece_le_degreeIdeal d ℒ (by push_cast; omega))

/-- The image `F^{k+1} / F^{k+2}` of the degree ideal `F^{k+1}` in the truncation of order
`k + 1` is central. By `LieIdeal.ker_liftQ_mkQ`, this image is the kernel of the transition from
the truncation of order `k + 1` onto the truncation of order `k`. -/
theorem map_mkQ_degreeIdeal_le_center (k : ℕ) :
    (degreeIdeal d ℒ k).map (degreeIdeal d ℒ (k + 1)).mkQ ≤
      LieAlgebra.center R (L ⧸ degreeIdeal d ℒ (k + 1)) := by
  intro y hy
  obtain ⟨⟨x, hx⟩, rfl⟩ := LieIdeal.mem_map_of_surjective (LieIdeal.surjective_mkQ _) hy
  rw [LieModule.mem_maxTrivSubmodule]
  intro z
  obtain ⟨w, rfl⟩ := LieIdeal.surjective_mkQ _ z
  rw [← LieHom.map_lie, LieIdeal.mkQ_eq_zero]
  exact lie_top_degreeIdeal_le d ℒ k (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top w) hx)

/-- The image `F^{k+1} / F^{k+2}` of the degree ideal `F^{k+1}` in the truncation of order
`k + 1`, which is the kernel of the transition onto the truncation of order `k`, is the image of
the pieces of degree exactly `k + 1`. -/
theorem map_mkQ_degreeIdeal_toSubmodule (k : ℕ) :
    ((degreeIdeal d ℒ k).map (degreeIdeal d ℒ (k + 1)).mkQ).toSubmodule =
      (⨆ (n) (_ : d.degree n = k + 1), ℒ n).map
        ((degreeIdeal d ℒ (k + 1)).mkQ : L →ₗ[R] L ⧸ degreeIdeal d ℒ (k + 1)) := by
  rw [LieIdeal.coe_map_of_surjective (LieIdeal.surjective_mkQ _), degreeIdeal_toSubmodule_eq_sup,
    Submodule.map_sup, sup_eq_left]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  rw [LieHom.coe_toLinearMap, (LieIdeal.mkQ_eq_zero _).2 hx]
  exact Submodule.zero_mem _

end DegreeIdeal

section InternalGrading

variable {N : Type} {R M : Type*} [AddCommMonoid N] [DecidableEq N] (d : PositiveDegrees N)

/-- The internal grading carried by a positive decomposition is positive. -/
instance IsPositiveGrading.ofDecomposition [Semiring R] [AddCommMonoid M] [Module R M]
    (ℳ : N → Submodule R M) [Decomposition ℳ] [IsPositiveGrading d ℳ] :
    IsPositiveGrading d (InternalGrading.ofDecomposition ℳ).piece := by
  rwa [InternalGrading.ofDecomposition_piece]

variable {S : Type*} [Ring R] [Ring S] [SMul R S] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

/-- The quotient of a positive grading by a homogeneous submodule is positive. In particular,
the truncations of a positively graded Lie algebra are positively graded. -/
instance IsPositiveGrading.quotient (G : InternalGrading R M N) [IsPositiveGrading d G.piece]
    (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U) :
    IsPositiveGrading d (G.quotient U hU).piece where
  eq_bot_of_notMem n hn := by
    rw [InternalGrading.quotient_piece,
      IsPositiveGrading.eq_bot_of_notMem (d := d) (ℳ := G.piece) hn, Submodule.map_bot]
  eq_bot_zero := by
    rw [InternalGrading.quotient_piece, IsPositiveGrading.eq_bot_zero (d := d) (ℳ := G.piece),
      Submodule.map_bot]

end InternalGrading

section Truncation

variable {N : Type} {R L : Type*} [AddCommMonoid N] [DecidableEq N] [CommRing R] [LieRing L]
  [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ]

/-- The truncation of order `k` has no homogeneous pieces of degree greater than `k`. -/
theorem quotient_piece_degreeIdeal_eq_bot {k : ℕ} {n : N} (hn : (k : ℤ) < d.degree n)
    (hI : SetLike.IsHomogeneous (InternalGrading.ofDecomposition ℒ).piece
      (degreeIdeal d ℒ k).toSubmodule) :
    ((InternalGrading.ofDecomposition ℒ).quotient (degreeIdeal d ℒ k).toSubmodule hI).piece n =
      ⊥ := by
  rw [InternalGrading.quotient_piece, InternalGrading.ofDecomposition_piece, eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  simpa using piece_le_degreeIdeal d ℒ hn hx

end Truncation

end TauCeti
