/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.WittVector.Truncated.Teichmuller

import Mathlib.RingTheory.Localization.Integer

/-!
# Principal localization of truncated Witt vectors

Finite p-typical Witt vectors commute with principal localization: the coefficient map from
`Wₙ(A)` to `Wₙ(A[1/s])` localizes at the Teichmüller representative of `s`. Multiplication by
this representative scales coordinate `i` by `s ^ p ^ i`. Finitely many coordinates allow a
single power to clear all denominators, including over rings with zero divisors.

The localization theorem uses the algebra structure induced by the coefficient map.
Use `IsLocalization.algEquiv` for the canonical comparison with any other localization.

## References

* A. Langer and T. Zink, *De Rham–Witt cohomology for a proper and smooth morphism*,
  Appendix A.1, p. 92. https://www.math.uni-bielefeld.de/~zink/dRW.pdf
-/

public section

namespace TruncatedWittVector

variable {p : ℕ} [Fact p.Prime]
variable {A B : Type*} [CommRing A] [CommRing B]

/-- Finite Witt vectors commute with localization away from one element, for the algebra
structure induced by the coefficient map. No regularity assumption on the element is needed. -/
theorem isLocalization_away_teichmuller (n : ℕ) (s : A) [Algebra A B] [IsLocalization.Away s B] :
    letI := (map (p := p) n (algebraMap A B)).toAlgebra
    IsLocalization.Away (teichmuller p n s) (TruncatedWittVector p n B) := by
  classical
  let _ := (map (p := p) n (algebraMap A B)).toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [RingHom.algebraMap_toAlgebra, map_teichmuller]
    exact (IsLocalization.Away.algebraMap_isUnit s).map (teichmuller p n)
  · intro x
    obtain ⟨⟨_, N, rfl⟩, hdenom⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers s) x.coeff
    choose a ha using hdenom
    simp only [Algebra.smul_def, map_pow] at ha
    have hN (i : Fin n) : N ≤ N * p ^ i.val :=
      Nat.le_mul_of_pos_right _ (pow_pos (Fact.out : p.Prime).pos _)
    refine ⟨N, mk p (fun i => a i * s ^ (N * p ^ i.val - N)), ?_⟩
    rw [RingHom.algebraMap_toAlgebra, map_teichmuller, ← map_pow]
    apply ext
    intro i
    rw [mul_comm x, teichmuller_mul_coeff, map_coeff, coeff_mk, ← pow_mul, map_mul, map_pow]
    calc
      (algebraMap A B s) ^ (N * p ^ i.val) * x.coeff i =
          ((algebraMap A B s) ^ N * x.coeff i) *
            (algebraMap A B s) ^ (N * p ^ i.val - N) := by
        rw [mul_right_comm ((algebraMap A B s) ^ N), ← pow_add,
          Nat.add_sub_of_le (hN i)]
      _ = _ := by rw [← ha i]
  · intro x y hxy
    rw [RingHom.algebraMap_toAlgebra] at hxy
    have hi (i : Fin n) : algebraMap A B (x.coeff i) = algebraMap A B (y.coeff i) := by
      simpa only [map_coeff] using
        congrArg (fun z : TruncatedWittVector p n B => z.coeff i) hxy
    choose k hk using fun i : Fin n => IsLocalization.Away.exists_of_eq s (hi i)
    let N := Finset.univ.sup k
    have hN (i : Fin n) : k i ≤ N * p ^ i.val := by
      exact (Finset.le_sup (Finset.mem_univ i)).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (Fact.out : p.Prime).pos _))
    refine ⟨N, ?_⟩
    rw [← map_pow]
    apply ext
    intro i
    simp only [teichmuller_mul_coeff, ← pow_mul]
    have hi := congrArg (fun z => s ^ (N * p ^ i.val - k i) * z) (hk i)
    simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN i)] using hi

end TruncatedWittVector
