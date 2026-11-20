/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Truncated
public import TauCeti.Algebra.SkewPolynomial.Algebraic

/-!
# Algebraic Frobenius over truncated Witt vectors

In characteristic `p`, Witt Frobenius descends to each finite length. A module with an
invertible semilinear Frobenius is algebraic when every element admits a monic annihilator
for the skew polynomial action. Invertibility is required of the operator, not of the module.
This is the finite-length condition in Bhatt–Lurie, *A Riemann–Hilbert correspondence in
positive characteristic*, Proposition 9.5.1.
-/

public section

namespace TruncatedWittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

/-- Witt Frobenius descended to length `n` over a characteristic-`p` ring. -/
noncomputable def frobenius (n : ℕ) : TruncatedWittVector p n R →+* TruncatedWittVector p n R :=
  (WittVector.truncate n).liftOfSurjective (WittVector.truncate_surjective p n R)
    ⟨(WittVector.truncate n).comp WittVector.frobenius, fun x hx ↦ by
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker,
        WittVector.mem_ker_truncate]
      intro i hi
      rw [WittVector.coeff_frobenius_charP, (WittVector.mem_ker_truncate n x).mp hx i hi,
        zero_pow (Fact.out : p.Prime).ne_zero]⟩

/-- Truncation intertwines full and finite-length Frobenius. -/
@[simp]
theorem frobenius_truncate (n : ℕ) (x : WittVector p R) :
    frobenius n (WittVector.truncate n x) = WittVector.truncate n (WittVector.frobenius x) := by
  simp only [frobenius, ← RingHom.comp_apply, RingHom.liftOfSurjective_comp]

/-- In Witt coordinates in characteristic `p`, Frobenius raises each entry to the `p`-th power. -/
@[simp]
theorem coeff_frobenius {n : ℕ} (x : TruncatedWittVector p n R) (i : Fin n) :
    (frobenius n x).coeff i = x.coeff i ^ p := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.coeff_frobenius_charP]

end TruncatedWittVector

namespace TauCeti

variable {p n : ℕ} [Fact p.Prime] {R M : Type*} [CommRing R] [CharP R p]
  [AddCommGroup M] [Module (TruncatedWittVector p n R) M]

local notation "A" => TruncatedWittVector p n R
local notation "σ" => (TruncatedWittVector.frobenius n : A →+* A)

/-- A Frobenius on a module over finite-length Witt vectors is algebraic when it is bijective
and every vector is killed by a monic skew polynomial in that operator. -/
def IsAlgebraicWittFrobenius (F : M →ₛₗ[σ] M) : Prop :=
  letI := RingHom.iterateMulSemiringAction σ
  Function.Bijective F ∧ F.withIterateTwist.IsOrbitAlgebraic

/-- Separate invertibility from pointwise algebraicity for a finite-length Witt Frobenius. -/
theorem isAlgebraicWittFrobenius_iff (F : M →ₛₗ[σ] M) :
    IsAlgebraicWittFrobenius F ↔
      letI := RingHom.iterateMulSemiringAction σ
      Function.Bijective F ∧ F.withIterateTwist.IsOrbitAlgebraic := Iff.rfl

/-- A Frobenius is algebraic if every element is fixed by some positive iterate. -/
theorem isAlgebraicWittFrobenius_of_periodic (F : M →ₛₗ[σ] M)
    (h : ∀ x, ∃ d : ℕ, 0 < d ∧ F^[d] x = x) : IsAlgebraicWittFrobenius F := by
  let := RingHom.iterateMulSemiringAction σ
  refine (isAlgebraicWittFrobenius_iff F).mpr ⟨⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨_ | d, hd, hx⟩ := h (x - y)
    · omega
    have hzero : F (x - y) = 0 := by simp [hxy]
    rw [Function.iterate_succ_apply, hzero, iterate_map_zero] at hx
    exact sub_eq_zero.mp hx.symm
  · intro x
    obtain ⟨_ | d, hd, hx⟩ := h x
    · omega
    exact ⟨F^[d] x, by simpa only [Function.iterate_succ_apply'] using hx⟩
  · have hcoe : (F.withIterateTwist : M → M) = F := funext F.withIterateTwist_apply
    exact LinearMap.isOrbitAlgebraic_of_periodic (by simpa only [hcoe] using h)

end TauCeti
