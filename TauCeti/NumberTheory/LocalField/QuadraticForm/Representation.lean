/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Isotropy

/-!
# Units represented by a quadratic form over a local field

Let `K` be a nonarchimedean local field in which `2` is invertible, and let `q` be a regular
quadratic form over `K` of rank `n`, plain discriminant `d` and local Hasse invariant `s`. The
units represented by `q` are determined by `(n, d, s)`:

* `n = 1`: `q` represents `c` exactly when `[c] = d`, over every field
  (`QuadraticForm.mem_unitValueSet_iff_squareClass_eq_discr_of_finrank_eq_one`);
* `n = 2`: `q` represents `c` exactly when `(c, -d)_K = s`
  (`QuadraticForm.mem_unitValueSet_iff_hilbertSymbol_eq_localHasse_of_finrank_eq_two`);
* `n = 3`: `q` represents `c` exactly when `[c] ≠ -d`, or `[c] = -d` and `s = (-1, -d)_K`;
* `n ≥ 4`: `q` represents every unit.

In rank three the condition `s = (-1, -d)_K` is the isotropy of `q`, so a ternary form represents
every unit outside the square class `-d`, and it represents the units of that class exactly when
it is isotropic.

Each case follows from the isotropy list by the criterion that `q` represents `c` exactly when
`⟨-c⟩ ⊥ q` is isotropic (`QuadraticForm.mem_unitValueSet_iff_not_anisotropic_mk_rankOne_add`). The
invariants of `⟨-c⟩ ⊥ q` are `(n + 1, [-c] + d, s · (-c, d)_K)`, by the orthogonal-sum formulas
`TauCeti.RegularFormClass.discr_mk_rankOne_add` and
`TauCeti.RegularFormClass.localHasse_mk_rankOne_add`.

## Main results

* `QuadraticForm.mem_unitValueSet_iff_squareClass_ne_or_localHasse_eq_of_finrank_eq_three`: the
  units represented by a regular ternary form.
* `QuadraticForm.notMem_unitValueSet_iff_anisotropic_and_squareClass_eq_of_finrank_eq_three`: a
  regular ternary form fails to represent `c` exactly when it is anisotropic and `[c] = -d`.
* `QuadraticForm.mem_unitValueSet_of_four_le_finrank`: a regular form of dimension at least four
  represents every unit.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.2, Corollary to Theorem 6.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:21.
-/

public section

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The represented units of a regular ternary space** (Serre IV, Corollary to Thm 6). A unit
`c` is represented exactly when its square class is not `-d`, or it is and the local Hasse
invariant is `(-1, -d)_K`, where `d` is the plain discriminant. -/
theorem mem_unitValueSet_iff_squareClass_ne_or_localHasse_eq_of_finrank_eq_three
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (c : Kˣ) :
    c ∈ Q.unitValueSet ↔
      squareClass c ≠ squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ) ∨
        RegularFormClass.localHasse (formClass Q hQ) =
          hilbertSymbolOnSquareClasses (squareClass (-1 : Kˣ))
            (squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ)) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, RegularFormClass.discr (formClass Q hQ) = squareClass u :=
    ⟨_, (squareClass_toMul_out _).symm⟩
  -- Comparing `[c]` with `-d = [-1 * u]` yields `IsSquare (c * (-1 * u))`; normalize it to the
  -- discriminant `-c * u` of `⟨-c⟩ ⊥ Q`, so that both disjuncts test the same square.
  have hdiscr : c * (-1 * u) = -c * u := by simp
  -- `Q` represents `c` exactly when the quaternary class `⟨-c⟩ ⊥ Q` is isotropic, which the
  -- quaternary criterion reads off its discriminant `[-c u]` and Hasse invariant `s · (-c, u)_K`.
  rw [mem_unitValueSet_iff_not_anisotropic_mk_rankOne_add Q hQ,
    RegularFormClass.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four
      (by simp [hV]),
    RegularFormClass.discr_mk_rankOne_add, RegularFormClass.localHasse_mk_rankOne_add, hu]
  generalize RegularFormClass.localHasse (formClass Q hQ) = s
  simp only [← squareClass_mul, hilbertSymbolOnSquareClasses_squareClass, ne_eq,
    squareClass_eq_zero_iff, squareClass_eq_iff_isSquare_mul, hdiscr]
  by_cases hsq : IsSquare (-c * u)
  · -- Here `-c` lies in the square class of `u`, so `(-c, u)_K = (u, u)_K = (-1, u)_K`.
    have hcu : hilbertSymbol (-c) u = hilbertSymbol (-1) u := by
      rw [hilbertSymbol_congr_sq (-c) u u u hsq ⟨u, rfl⟩, hilbertSymbol_self, hilbertSymbol_comm]
    simp only [hsq, not_true_eq_false, false_or, hcu, hilbertSymbol_mul_right h2]
    rw [← mul_inv_eq_iff_eq_mul, Int.units_inv_eq_self]
  · simp only [hsq, not_false_eq_true, true_or]

/-- **The units missed by a regular ternary space.** A regular ternary form fails to represent a
unit `c` exactly when it is anisotropic and the square class of `c` is `-d`, where `d` is the
plain discriminant. So an anisotropic ternary form represents every unit outside one square
class, and an isotropic one represents every unit. -/
theorem notMem_unitValueSet_iff_anisotropic_and_squareClass_eq_of_finrank_eq_three
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (c : Kˣ) :
    c ∉ Q.unitValueSet ↔
      Q.Anisotropic ∧
        squareClass c = squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ) := by
  rw [mem_unitValueSet_iff_squareClass_ne_or_localHasse_eq_of_finrank_eq_three Q hQ hV,
    ← not_anisotropic_iff_localHasse_eq_of_finrank_eq_three Q hQ hV]
  tauto

/-- **Representation in dimension at least four** (Serre IV, Corollary to Thm 6). A regular
quadratic form on a space of dimension at least four over `K` represents every unit. -/
theorem mem_unitValueSet_of_four_le_finrank (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV : 4 ≤ Module.finrank K V) (c : Kˣ) : c ∈ Q.unitValueSet := by
  -- `⟨-c⟩ ⊥ Q` has rank at least five, so it is isotropic.
  rw [mem_unitValueSet_iff_not_anisotropic_mk_rankOne_add Q hQ]
  refine RegularFormClass.not_anisotropic_of_five_le_rank ?_
  rw [RegularFormClass.rank_add, RegularFormClass.rank_mk, rank_formClass]
  dsimp only
  omega

end QuadraticForm
