/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Norms of monomials

For a point `x : σ → R` of a normed commutative ring with `‖1‖ = 1` and an exponent
`t : σ →₀ ℕ`, the monomial `xᵗ = ∏ᵢ xᵢ ^ tᵢ` has norm at most `cᵗ = ∏ᵢ cᵢ ^ tᵢ` whenever
`‖xᵢ‖ ≤ cᵢ` for every `i`, that is, whenever `x` lies in the closed polydisc of polyradius `c`.

## Main results

* `Finsupp.norm_prod_pow_le`: the norm of a monomial on the closed polydisc of polyradius `c` is
  at most its weight `cᵗ`.
* `TauCeti.exists_forall_norm_prod_pow_le_mul_prod`: in finitely many variables, coordinatewise
  bounds `‖xᵢ ^ j‖ ≤ Dᵢ cᵢ ^ j` on the powers give a bound `‖xᵗ‖ ≤ D cᵗ` on all monomials, with
  no condition on `‖1‖` and no bound on `‖xᵢ‖` itself.
-/

public section

namespace Finsupp

/-- On the closed polydisc `‖xᵢ‖ ≤ cᵢ`, the monomial `xᵗ = ∏ᵢ xᵢ ^ tᵢ` has norm at most
`cᵗ = ∏ᵢ cᵢ ^ tᵢ`. -/
theorem norm_prod_pow_le {σ R : Type*} [NormedCommRing R] [NormOneClass R] {x : σ → R}
    {c : σ → ℝ} (hx : ∀ i, ‖x i‖ ≤ c i) (t : σ →₀ ℕ) :
    ‖t.prod (x · ^ ·)‖ ≤ t.prod (c · ^ ·) :=
  (Finset.norm_prod_le _ _).trans <| Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hx i) _)

end Finsupp

namespace TauCeti

/-- Coordinatewise bounds `‖x i ^ j‖ ≤ Dᵢ * c i ^ j` on the powers of finitely many elements give
a bound `‖∏ i, x i ^ t i‖ ≤ D * ∏ i, c i ^ t i` on their monomials. Such elements may have norm
larger than `c i`, as a nilpotent element may. -/
theorem exists_forall_norm_prod_pow_le_mul_prod {σ R : Type*} [Fintype σ] [NormedCommRing R]
    {x : σ → R} {c : σ → ℝ} (hc : ∀ i, 0 ≤ c i) (h : ∀ i, ∃ Dᵢ, ∀ j, ‖x i ^ j‖ ≤ Dᵢ * c i ^ j) :
    ∃ D, ∀ t : σ →₀ ℕ, ‖∏ i, x i ^ t i‖ ≤ D * t.prod (c · ^ ·) := by
  choose Dᵢ hDᵢ using h
  refine ⟨max ‖(1 : R)‖ (∏ i, Dᵢ i), fun t ↦ ?_⟩
  rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp [Finset.univ_eq_empty]
  calc ‖∏ i, x i ^ t i‖ ≤ ∏ i, ‖x i ^ t i‖ := Finset.norm_prod_le' _ Finset.univ_nonempty _
    _ ≤ ∏ i, (Dᵢ i * c i ^ t i) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hDᵢ i _
    _ = (∏ i, Dᵢ i) * ∏ i, c i ^ t i := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _)

end TauCeti

end
