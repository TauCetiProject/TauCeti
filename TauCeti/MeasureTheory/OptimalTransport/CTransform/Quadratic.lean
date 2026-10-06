/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Rockafellar
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic

/-!
# The quadratic cost and convex analysis

On a real inner product space `E`, the quadratic transport cost `c (x, y) = ‖x - y‖ ^ 2 / 2`
differs from the pairing cost `-⟪x, y⟫` by the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`
(`TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic`, which also identifies the
`c`-cyclically monotone sets of the quadratic cost with the classically cyclically monotone
sets). Split terms are absorbed by the `c`-transform vocabulary, so the whole `c`-transform
theory of the quadratic cost is the Legendre–Fenchel theory of the inner product: a potential
`φ` is `c`-concave exactly when `u = ‖·‖ ^ 2 / 2 - φ` is a Legendre–Fenchel conjugate, its
`c`-transform is `‖y‖ ^ 2 / 2 - u⋆ y`, and its `c`-superdifferential is the graph of the
subdifferential `∂u`. Rockafellar's theorem then produces, from a `c`-cyclically monotone set, a
conjugate `u` whose subdifferential graph contains it. This is the algebraic step of Brenier's
theorem: applied to the support of a quadratic optimal plan, it yields the convex potential from
which the Brenier map is later extracted, once finite dimension, absolute continuity of the
source and almost-everywhere differentiability of `u` enter; none of these analytic and
measure-theoretic hypotheses is used here. Every bridge in this file accounts for the factor
`1 / 2` in the cost.

## Main statements

* `TauCeti.cTransform_norm_sub_sq_div_two`, `TauCeti.cTransformSymm_norm_sub_sq_div_two`,
  `TauCeti.isCConcave_norm_sub_sq_div_two_iff`, `TauCeti.isCConcaveSymm_norm_sub_sq_div_two_iff`
  and `TauCeti.cSuperdifferential_norm_sub_sq_div_two` — the two `c`-transforms, `c`-concavity
  on the source and on the target, and the `c`-superdifferential for the quadratic cost in terms
  of the Legendre–Fenchel conjugate and the subdifferential of `‖·‖ ^ 2 / 2 - φ`;
* `TauCeti.IsCyclicallyMonotone.exists_fenchelConjugate_innerₗ_subset_subdifferential`
  — **Rockafellar's theorem for the quadratic cost**: a `c`-cyclically monotone set lies in the
  subdifferential graph of a Legendre–Fenchel conjugate for the inner product.

## References

* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*, Comm.
  Pure Appl. Math. 44 (1991), 375--417.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1 and Theorem 2.12, where the quadratic cost is reduced to convex analysis.
-/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `c`-transform of a potential `φ` for the quadratic cost is `‖y‖ ^ 2 / 2 - u⋆ y`, where
`u = ‖·‖ ^ 2 / 2 - φ` and `u⋆` is its Legendre–Fenchel conjugate for the inner product. -/
@[simp]
theorem cTransform_norm_sub_sq_div_two (φ : E → EReal) (y : E) :
    cTransform (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) φ y =
      ((‖y‖ ^ 2 / 2 : ℝ) : EReal) -
        fenchelConjugate (innerₗ E) (fun x => ((‖x‖ ^ 2 / 2 : ℝ) : EReal) - φ x) y := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    cTransform_add_add (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2) (fun y => ‖y‖ ^ 2 / 2),
    cTransform_pairingCost, sub_eq_add_neg]
  simp only [EReal.neg_sub_coe]

/-- The symmetric `c`-transform of a potential `ψ` on the target for the quadratic cost is
`‖x‖ ^ 2 / 2 - v⋆ x`, where `v = ‖·‖ ^ 2 / 2 - ψ` and `v⋆` is its Legendre–Fenchel conjugate for
the inner product; the quadratic cost is symmetric, so the formula is the same as for the
infimal `c`-transform. -/
@[simp]
theorem cTransformSymm_norm_sub_sq_div_two (ψ : E → EReal) (x : E) :
    cTransformSymm (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) ψ x =
      ((‖x‖ ^ 2 / 2 : ℝ) : EReal) -
        fenchelConjugate (innerₗ E) (fun y => ((‖y‖ ^ 2 / 2 : ℝ) : EReal) - ψ y) x := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    cTransformSymm_add_add (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2) (fun y => ‖y‖ ^ 2 / 2),
    cTransformSymm_pairingCost, flip_innerₗ, sub_eq_add_neg]
  simp only [EReal.neg_sub_coe]

/-- A potential `φ` is `c`-concave for the quadratic cost exactly when `‖·‖ ^ 2 / 2 - φ` is a
Legendre–Fenchel conjugate for the inner product. -/
theorem isCConcave_norm_sub_sq_div_two_iff (φ : E → EReal) :
    IsCConcave (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) φ ↔
      ∃ g : E → EReal,
        (fun x => ((‖x‖ ^ 2 / 2 : ℝ) : EReal) - φ x) = fenchelConjugate (innerₗ E) g := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    isCConcave_add_add_iff (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2) (fun y => ‖y‖ ^ 2 / 2),
    isCConcave_pairingCost_iff, flip_innerₗ]
  simp only [EReal.neg_sub_coe]

/-- A potential `ψ` on the target is `c`-concave for the quadratic cost exactly when
`‖·‖ ^ 2 / 2 - ψ` is a Legendre–Fenchel conjugate for the inner product; the quadratic cost is
symmetric, so the criterion is the same as for potentials on the source. -/
theorem isCConcaveSymm_norm_sub_sq_div_two_iff (ψ : E → EReal) :
    IsCConcaveSymm (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) ψ ↔
      ∃ g : E → EReal,
        (fun y => ((‖y‖ ^ 2 / 2 : ℝ) : EReal) - ψ y) = fenchelConjugate (innerₗ E) g := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    isCConcaveSymm_add_add_iff (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2)
      (fun y => ‖y‖ ^ 2 / 2),
    isCConcaveSymm_pairingCost_iff]
  simp only [EReal.neg_sub_coe]

/-- The `c`-superdifferential of a potential `φ` for the quadratic cost is the graph of the
subdifferential of `‖·‖ ^ 2 / 2 - φ` for the inner product. -/
@[simp]
theorem cSuperdifferential_norm_sub_sq_div_two (φ : E → EReal) :
    cSuperdifferential (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) φ =
      {p | p.2 ∈ subdifferential (innerₗ E) (fun x => ((‖x‖ ^ 2 / 2 : ℝ) : EReal) - φ x) p.1} := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    cSuperdifferential_add_add (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2)
      (fun y => ‖y‖ ^ 2 / 2),
    cSuperdifferential_pairingCost]
  simp only [EReal.neg_sub_coe]

/-- The subdifferential graph of any extended-real function on `E` is `c`-cyclically monotone
for the quadratic cost. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential (u : E → EReal) :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2)
      {p | p.2 ∈ subdifferential (innerₗ E) u p.1} :=
  isCyclicallyMonotone_norm_sub_sq_div_two_iff.2
    (isCyclicallyMonotone_pairingCost_subdifferential (innerₗ E) u)

/-- **Rockafellar's theorem for the quadratic cost.** A `c`-cyclically monotone set for the cost
`‖x - y‖ ^ 2 / 2` lies in the subdifferential graph of a Legendre–Fenchel conjugate `u = g⋆` for
the inner product: `y ∈ ∂u(x)` for every `(x, y)` in the set. -/
theorem IsCyclicallyMonotone.exists_fenchelConjugate_innerₗ_subset_subdifferential
    {S : Set (E × E)} (hS : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S) :
    ∃ g : E → EReal,
      S ⊆ {p | p.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) g) p.1} := by
  have hS' := isCyclicallyMonotone_norm_sub_sq_div_two_iff.1 hS
  obtain ⟨g, hg⟩ := hS'.exists_fenchelConjugate_subset_subdifferential
  rw [flip_innerₗ] at hg
  exact ⟨g, hg⟩

/-- **`c`-cyclically monotone sets for the quadratic cost are exactly the subsets of
subdifferential graphs of Legendre–Fenchel conjugates for the inner product.** Every such
conjugate is convex and lower semicontinuous for the norm topology. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff_exists_fenchelConjugate (S : Set (E × E)) :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      ∃ g : E → EReal,
        S ⊆ {p | p.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) g) p.1} :=
  ⟨fun hS => hS.exists_fenchelConjugate_innerₗ_subset_subdifferential,
    fun ⟨_, h⟩ => (isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential _).mono h⟩

end TauCeti

end

end
