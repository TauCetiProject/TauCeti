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
# Localization of truncated Witt vectors

Finite p-typical Witt vectors commute with localization at any submonoid `M`: the coefficient
map localizes at the image of `M` under the Teichmüller map. Multiplication by a representative
of `s` scales coordinate `i` by `s ^ p ^ i`. Finitely many coordinates allow a common
denominator, including over rings with zero divisors.

In particular, the coefficient map from `Wₙ(A)` to `Wₙ(A[1/s])` localizes at the
Teichmüller representative of `s`.

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

/-- Finite Witt vectors commute with localization at a submonoid, for the algebra structure
induced by the coefficient map. No regularity assumption on the submonoid is needed. -/
theorem isLocalization_teichmuller (n : ℕ) (M : Submonoid A) [Algebra A B]
    [IsLocalization M B] :
    letI := (map (p := p) n (algebraMap A B)).toAlgebra
    IsLocalization (M.map (teichmuller p n)) (TruncatedWittVector p n B) := by
  classical
  let _ := (map (p := p) n (algebraMap A B)).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_teichmuller]
    exact (IsLocalization.map_units B (⟨s, hs⟩ : M)).map (teichmuller p n)
  · intro x
    obtain ⟨s, hdenom⟩ := IsLocalization.exist_integer_multiples_of_finite M x.coeff
    choose a ha using hdenom
    simp only [Algebra.smul_def] at ha
    refine ⟨⟨mk p (fun i => a i * (s : A) ^ (p ^ i.val - 1)),
      ⟨teichmuller p n s, Submonoid.mem_map_of_mem _ s.property⟩⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, map_teichmuller]
    apply ext
    intro i
    rw [mul_comm x, teichmuller_mul_coeff, map_coeff, coeff_mk, map_mul, map_pow]
    calc
      (algebraMap A B s) ^ p ^ i.val * x.coeff i =
          ((algebraMap A B s) * x.coeff i) *
            (algebraMap A B s) ^ (p ^ i.val - 1) := by
        rw [mul_right_comm (algebraMap A B s), ← pow_succ',
          Nat.sub_add_cancel (pow_pos (Fact.out : p.Prime).pos _)]
      _ = _ := by rw [← ha i]
  · intro x y hxy
    rw [RingHom.algebraMap_toAlgebra] at hxy
    have hi (i : Fin n) : algebraMap A B (x.coeff i) = algebraMap A B (y.coeff i) := by
      simpa only [map_coeff] using
        congrArg (fun z : TruncatedWittVector p n B => z.coeff i) hxy
    choose c hc using fun i : Fin n => IsLocalization.exists_of_eq (M := M) (hi i)
    let s : M := ∏ i, c i
    refine ⟨⟨teichmuller p n s, Submonoid.mem_map_of_mem _ s.property⟩, ?_⟩
    apply ext
    intro i
    simp only [teichmuller_mul_coeff]
    obtain ⟨t, ht⟩ := (Finset.dvd_prod_of_mem c (Finset.mem_univ i)).pow
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    have hfactor : (s : A) ^ p ^ i.val = (c i : A) * t := congrArg Subtype.val ht
    simp only [hfactor, mul_right_comm (c i : A) (t : A), hc i]

/-- Finite Witt vectors commute with localization away from one element, for the algebra
structure induced by the coefficient map. No regularity assumption on the element is needed. -/
theorem isLocalization_away_teichmuller (n : ℕ) (s : A) [Algebra A B] [IsLocalization.Away s B] :
    letI := (map (p := p) n (algebraMap A B)).toAlgebra
    IsLocalization.Away (teichmuller p n s) (TruncatedWittVector p n B) := by
  simpa only [Submonoid.map_powers] using
    (isLocalization_teichmuller (p := p) (B := B) n (Submonoid.powers s))

end TruncatedWittVector
