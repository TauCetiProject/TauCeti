/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Equiv
public import TauCeti.Analysis.Normed.Field.RootsOfUnity.PolynomialValue

/-!
# Specializing the last variable at a primitive root of unity minus one

For a finite family of polynomials over a discrete valuation ring, a single level of primitive
roots preserves a coefficient of bounded total degree in each polynomial after specializing the
last variable. The same remaining exponent vector works for every primitive root at that level.
The level bound is uniform in the family and in its polynomial degrees.
-/

public section

namespace TauCeti

open MvPolynomial

/-- **One common level for specializing the last variable of a polynomial family.**
Let `K` be an ultrametric normed field in which the prime `p` satisfies `‖(p : K)‖ < 1`, and
let `φ : O →+* K` map a discrete valuation ring into the closed unit ball of `K`. Fix a finite type
`ι`, positive real numbers `c` and `ε`, and a total-degree cutoff `D`. There is a bound `M`
depending only on `p`, `ε`, `D`, `c`, `φ` and the cardinality of `ι`.

Suppose each member of a family `P` of polynomials over `O` in `n + 1` variables has a
coefficient `a` with `c ≤ ‖φ a‖` on a monomial of total degree at most `D`. There are a level
`1 ≤ m ≤ M` with `1 / totient (p ^ m) ≤ ε` and, for each member `P j`, an exponent vector `u j`
in the remaining variables of total degree at most `D`. For every primitive `p ^ m`-th root
`ζ` in `K`, let `Q` be obtained from `P j` by mapping coefficients through `φ` and specializing
the last variable at `ζ - 1`. Then `Q.coeff (u j) ≠ 0` and `c * ‖(p : K)‖ ^ ε ≤ ‖Q.coeff (u j)‖`.
-/
theorem exists_level_le_norm_coeff_specialize_last_sub_one
    {K O ι : Type*} [NormedField K] [IsUltrametricDist K]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite ι]
    {p : ℕ} [Fact p.Prime] (hp : ‖(p : K)‖ < 1)
    (φ : O →+* K) (hφ : ∀ a, ‖φ a‖ ≤ 1) (n D : ℕ) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (P : ι → MvPolynomial (Fin (n + 1)) O),
      (∀ j, ∃ d : Fin (n + 1) →₀ ℕ,
        (d.sum fun _ e ↦ e) ≤ D ∧ c ≤ ‖φ ((P j).coeff d)‖) →
      ∃ m, 1 ≤ m ∧ m ≤ M ∧ ((p ^ m).totient : ℝ)⁻¹ ≤ ε ∧
        ∃ u : ι → Fin n →₀ ℕ, (∀ j, ((u j).sum fun _ e ↦ e) ≤ D) ∧
          ∀ ζ : K, IsPrimitiveRoot ζ (p ^ m) → ∀ j,
            let Q := map (Polynomial.eval₂RingHom φ (ζ - 1))
              (optionEquivRight O (Fin n) (rename finSuccEquivLast (P j)))
            Q.coeff (u j) ≠ 0 ∧ c * ‖(p : K)‖ ^ ε ≤ ‖Q.coeff (u j)‖ := by
  obtain ⟨M, hM⟩ := exists_level_le_norm_eval₂_sub_one (ι := ι) hp φ hφ D hc hε
  refine ⟨M, fun P hP ↦ ?_⟩
  choose d hd hc' using hP
  have splitDegree (j : ι) :
      ((Finsupp.init (d j)).sum fun _ e ↦ e) + (d j) (Fin.last n) ≤ D := by
    have h := hd j
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_castSucc] at h
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa only [Finsupp.init_apply] using h
  let F (j : ι) := (optionEquivRight O (Fin n) (rename finSuccEquivLast (P j))).coeff
    (Finsupp.init (d j))
  have hF (j : ι) : ∃ k ≤ D, c ≤ ‖φ ((F j).coeff k)‖ := by
    refine ⟨d j (Fin.last n), (Nat.le_add_left _ _).trans (splitDegree j), ?_⟩
    simpa only [F, optionEquivRight_rename_finSuccEquivLast_coeff_coeff, Finsupp.snoc_init_self]
      using hc' j
  obtain ⟨m, hm, hmM, hmε, hall⟩ := hM F hF
  refine ⟨m, hm, hmM, hmε, fun j ↦ Finsupp.init (d j),
    fun j ↦ (Nat.le_add_right _ _).trans (splitDegree j), fun ζ hζ j ↦ ?_⟩
  simpa only [coeff_map, Polynomial.coe_eval₂RingHom, F] using hall ζ hζ j

end TauCeti
