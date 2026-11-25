/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Isolating

/-!
# The oriented count of a forced Lyapunov–Schmidt reduction

A gluing construction solves a nonlinear equation in two steps. For each value of a
finite-dimensional parameter `p`, ranging over an oriented manifold `M`, the equation is split into
a *complementary* part, solved by the quadratic correction of
`TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic`,

`e p + D p x + N p x = 0`,  with `x` in the range of a right inverse `Q p` of `D p`,

and a finite-dimensional *obstruction* part `Φ p x = 0`, valued in a vector space `H` of the same
dimension as `M`. Substituting the correction `x p` into the obstruction part gives the
**reduced section** `p ↦ Φ p (x p)`, and the solutions of the full system, with `x` small and in the
range of `Q p`, are exactly the pairs `(p, x p)` at the zeros of the reduced section (the
correction is unique on a ball, `TauCeti.eq_of_add_add_eq_zero`). On an isolating open set
`U ⊆ M`, these zeros are counted with orientation signs by the local degree
(`TauCeti.HomologicalOrientation.localDegree`).

Now *force* the system: change the residual `e₀ p` of the complementary equation to `e₁ p`, and the
obstruction map `Φ₀ p` to `Φ₁ p`, for instance by a small curvature perturbation of an elliptic
equation and a change of the point constraints. The forced correction moves by at most `2 C` times
the change of residual (`TauCeti.norm_sub_le_two_mul_mul_norm_sub`), where `C` bounds the right
inverses. So if the direct change of the obstruction map is at most `β` and `Φ₀ p` is
`K`-Lipschitz along the correction, the forced reduced section is within

`β + 2 C K ‖e₀ p - e₁ p‖`

of the unforced one (`TauCeti.norm_sub_le_add_two_mul_mul_mul_norm_sub`). This file draws the
consequences for the count. Let `b` be a margin of the unforced reduced section on the frontier of
`U`, `b ≤ ‖Φ₀ p (x₀ p)‖`, and let the forcing satisfy `‖e₀ p - e₁ p‖ ≤ η` there, with

`β + 2 C K η < b`.

* **Boundary separation.** The forced reduced section stays at least `b - (β + 2 C K η) > 0` away
  from zero on the frontier (`TauCeti.sub_le_norm_of_add_add_eq_zero`), so `U` is isolating for it
  as well.
* **Invariance of the count.** The forced and unforced reduced sections have the same local degree
  on `U` at `0` (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_add_add_eq_zero`), by
  Rouché's principle `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_norm_sub_lt`.
* **Existence.** If the unforced count is nonzero, the forced system has a solution `(p, y)` with
  `p ∈ U`: `y` is in the range of `Q p`, has norm at most `r`, solves the forced complementary
  equation, and is a zero of the forced obstruction map `Φ₁ p`
  (`HomologicalOrientation.exists_mem_add_add_eq_zero_and_eq_zero_of_localDegree_restrict_ne_zero`).

The admissible size of the forcing is thus fixed by the constants `C`, `K` and the boundary margin
`b` of the unforced problem alone. The corrections `x₀` and `x₁` are any solutions of norm at most
`r` in the range of `Q p` on a ball with `C L r ≤ 1 / 2`, for instance the families constructed by
`TauCeti.exists_continuousOn_forall_add_add_add_eq_zero`. Those are continuous in `p`, so the
reduced sections are continuous, as their local degrees require, when `Φ₀` and `Φ₁` are.

## Main results

* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_add_add_eq_zero`: forcing below the
  margin does not change the oriented count of the zeros of the reduced section.
* `HomologicalOrientation.exists_mem_add_add_eq_zero_and_eq_zero_of_localDegree_restrict_ne_zero`:
  a nonzero unforced count gives a solution of the forced system.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* K. Deimling, *Nonlinear Functional Analysis*, Springer, 1985, Chapter 1, Theorem 3.1
  (homotopy invariance and Rouché's principle for the degree).
-/

public section

open Module Metric Set TopologicalSpace
open scoped NNReal

namespace TauCeti

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n)
  {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  (o' : HomologicalOrientation H H n) (hE : finrank ℝ E = n) (hH : finrank ℝ H = n)
  {X : Type*} {Y G : M → Type*} [SeminormedAddCommGroup X] [∀ p, SeminormedAddCommGroup (Y p)]
  [∀ p, FunLike (G p) (Y p) X] [∀ p, AddMonoidHomClass (G p) (Y p) X]
  {Q : ∀ p, G p} {D N : ∀ p, X → Y p} {C L : ℝ≥0} {δ : ℝ}
  (hDQ : ∀ p y, D p (Q p y) = y) (hQ : ∀ p y, ‖Q p y‖ ≤ C * ‖y‖)
  (hN : ∀ p, ∀ x ∈ closedBall (0 : X) δ, ∀ y ∈ closedBall (0 : X) δ,
    ‖N p x - N p y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)

include hH hDQ hQ hN in
/-- **Forcing below the boundary margin does not change the count.** Let `U ⊆ M` have compact
closure. Over the frontier of `U`, let `x₀ p` solve the unforced complementary equation
`e₀ p + D p x + N p x = 0` and `x₁ p` the forced one `e₁ p + D p x + N p x = 0`, both in the range
of `Q p` and of norm at most `r ≤ δ` with `C L r ≤ 1 / 2`, with `‖e₀ p - e₁ p‖ ≤ η`. Let the forced
obstruction map differ from the unforced one by at most `β` at `x₁ p`, and let the unforced one be
`K`-Lipschitz between `x₀ p` and `x₁ p`. If the unforced reduced section `f p = Φ₀ p (x₀ p)` has
norm at least `b` on the frontier, with `β + 2 C K η < b`, then the forced reduced section
`g p = Φ₁ p (x₁ p)` has the same local degree on `U` at `0`. -/
theorem localDegree_restrict_eq_of_add_add_eq_zero {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) {Φ₀ Φ₁ : M → X → H} {e₀ e₁ : ∀ p, Y p}
    {x₀ x₁ : M → X} {f g : C(M, H)} {r b β K η : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2)
    (hK : 0 ≤ K) (hf : ∀ p ∈ frontier (U : Set M), f p = Φ₀ p (x₀ p))
    (hg : ∀ p ∈ frontier (U : Set M), g p = Φ₁ p (x₁ p))
    (hx₀ : ∀ p ∈ frontier (U : Set M), x₀ p ∈ range (Q p) ∧ ‖x₀ p‖ ≤ r ∧
      e₀ p + D p (x₀ p) + N p (x₀ p) = 0)
    (hx₁ : ∀ p ∈ frontier (U : Set M), x₁ p ∈ range (Q p) ∧ ‖x₁ p‖ ≤ r ∧
      e₁ p + D p (x₁ p) + N p (x₁ p) = 0)
    (hΦ : ∀ p ∈ frontier (U : Set M), ‖Φ₁ p (x₁ p) - Φ₀ p (x₁ p)‖ ≤ β)
    (hΦ₀ : ∀ p ∈ frontier (U : Set M), ‖Φ₀ p (x₁ p) - Φ₀ p (x₀ p)‖ ≤ K * ‖x₁ p - x₀ p‖)
    (he : ∀ p ∈ frontier (U : Set M), ‖e₀ p - e₁ p‖ ≤ η)
    (hb : ∀ p ∈ frontier (U : Set M), b ≤ ‖f p‖) (hβ : β + 2 * C * K * η < b) :
    (o.comap U.isOpenEmbedding').localDegree o' hE (g.restrict U) 0 =
      (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) 0 := by
  refine (o.localDegree_restrict_eq_of_norm_sub_lt o' hE hH hU fun p hp ↦ ?_).symm
  obtain ⟨hx₀Q, hx₀r, hx₀e⟩ := hx₀ p hp
  obtain ⟨hx₁Q, hx₁r, hx₁e⟩ := hx₁ p hp
  have h := norm_sub_le_add_two_mul_mul_mul_norm_sub (hDQ p) (hQ p) (hN p) hrδ hr hK hx₀r hx₁r
    hx₀Q hx₀e hx₁Q hx₁e (hΦ p hp) (hΦ₀ p hp)
  -- On the frontier the two reduced sections are closer than the margin `b ≤ ‖f p‖`.
  have hη : 2 * C * K * ‖e₀ p - e₁ p‖ ≤ 2 * C * K * η :=
    mul_le_mul_of_nonneg_left (he p hp) (mul_nonneg (mul_nonneg zero_le_two C.coe_nonneg) hK)
  have hbp := hb p hp
  rw [hf p hp] at hbp
  rw [hf p hp, hg p hp, sub_zero, sub_zero]
  linarith [norm_nonneg (Φ₁ p (x₁ p))]

include hH hDQ hQ hN in
/-- **A nonzero unforced count gives a solution of the forced system.** In the situation of
`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_add_add_eq_zero`, with the forced
correction `x₁ p` and the forced reduced section `g p = Φ₁ p (x₁ p)` given over the closure of
`U`, suppose that the unforced reduced section has nonzero local degree on `U` at `0`. Then there
is `p ∈ U` and `y` in the range of `Q p`, of norm at most `r`, solving the forced complementary
equation `e₁ p + D p y + N p y = 0` and the forced obstruction equation `Φ₁ p y = 0`. When
`C L r < 1`, such a `y` is the only solution of the forced complementary equation at `p` in the
range of `Q p` of norm at most `r` (`TauCeti.eq_of_add_add_eq_zero`). -/
theorem exists_mem_add_add_eq_zero_and_eq_zero_of_localDegree_restrict_ne_zero {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) {Φ₀ Φ₁ : M → X → H} {e₀ e₁ : ∀ p, Y p}
    {x₀ x₁ : M → X} {f g : C(M, H)} {r b β K η : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2)
    (hK : 0 ≤ K) (hf : ∀ p ∈ frontier (U : Set M), f p = Φ₀ p (x₀ p))
    (hg : ∀ p ∈ closure (U : Set M), g p = Φ₁ p (x₁ p))
    (hx₀ : ∀ p ∈ frontier (U : Set M), x₀ p ∈ range (Q p) ∧ ‖x₀ p‖ ≤ r ∧
      e₀ p + D p (x₀ p) + N p (x₀ p) = 0)
    (hx₁ : ∀ p ∈ closure (U : Set M), x₁ p ∈ range (Q p) ∧ ‖x₁ p‖ ≤ r ∧
      e₁ p + D p (x₁ p) + N p (x₁ p) = 0)
    (hΦ : ∀ p ∈ frontier (U : Set M), ‖Φ₁ p (x₁ p) - Φ₀ p (x₁ p)‖ ≤ β)
    (hΦ₀ : ∀ p ∈ frontier (U : Set M), ‖Φ₀ p (x₁ p) - Φ₀ p (x₀ p)‖ ≤ K * ‖x₁ p - x₀ p‖)
    (he : ∀ p ∈ frontier (U : Set M), ‖e₀ p - e₁ p‖ ≤ η)
    (hb : ∀ p ∈ frontier (U : Set M), b ≤ ‖f p‖) (hβ : β + 2 * C * K * η < b)
    (hdeg : (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) 0 ≠ 0) :
    ∃ p ∈ U, ∃ y ∈ range (Q p), ‖y‖ ≤ r ∧ e₁ p + D p y + N p y = 0 ∧ Φ₁ p y = 0 := by
  rw [← o.localDegree_restrict_eq_of_add_add_eq_zero o' hE hH hDQ hQ hN hU hrδ hr hK hf
    (fun p hp ↦ hg p (frontier_subset_closure hp)) hx₀
    (fun p hp ↦ hx₁ p (frontier_subset_closure hp)) hΦ hΦ₀ he hb hβ] at hdeg
  obtain ⟨p, hpU, hp⟩ := o.exists_mem_apply_eq_of_localDegree_restrict_ne_zero o' hE hH hdeg
  obtain ⟨hpQ, hpr, hpe⟩ := hx₁ p (subset_closure hpU)
  exact ⟨p, hpU, x₁ p, hpQ, hpr, hpe, (hg p (subset_closure hpU)).symm.trans hp⟩

end HomologicalOrientation

end TauCeti
