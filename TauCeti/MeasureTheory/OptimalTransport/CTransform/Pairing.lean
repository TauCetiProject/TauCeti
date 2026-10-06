/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing

/-!
# The `c`-transform for the cost induced by a pairing

Let `E` and `F` be real vector spaces paired by `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, written `⟪x, y⟫ = B x y`.
The transport cost `c (x, y) = -⟪x, y⟫` induced by the pairing
(`TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing`) turns the `c`-transform vocabulary of
optimal transport into the Legendre–Fenchel vocabulary of convex analysis with the signs
reversed: the infimal `c`-transform of a potential `φ` is `-(-φ)⋆`, where `⋆` is the
Legendre–Fenchel conjugate, a potential is `c`-concave exactly when `-φ` is a conjugate, and the
`c`-superdifferential of `φ` is the graph of the subdifferential of `-φ`. This file records that
dictionary. Costs that differ from the pairing cost by a split term `a x + b y`, such as the
quadratic cost `‖x - y‖ ^ 2 / 2` on an inner product space, reduce to it through the split-shift
lemmas of `TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic`.

## Main statements

* `TauCeti.cTransform_pairingCost` and `TauCeti.cTransformSymm_pairingCost` — the two
  `c`-transforms for the pairing cost are the negated Legendre–Fenchel conjugates of the negated
  potentials, for the pairing and for its transpose;
* `TauCeti.isCConcave_pairingCost_iff` and `TauCeti.isCConcaveSymm_pairingCost_iff` — a
  potential on the source, respectively on the target, is `c`-concave for the pairing cost
  exactly when its negative is a conjugate for the transposed pairing, respectively for the
  pairing;
* `TauCeti.cSuperdifferential_pairingCost` — the `c`-superdifferential for the pairing cost is
  the graph of the subdifferential of the negated potential.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1 and §2.4, where the translation between the quadratic cost and convex analysis is
  carried out.
-/

public section

noncomputable section

namespace TauCeti

variable {E F : Type*} [AddCommMonoid F] [Module ℝ F]

section

variable [AddCommMonoid E] [Module ℝ E] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- The infimal `c`-transform for the pairing cost is the negative of the Legendre–Fenchel
conjugate of the negated potential: `φᶜ y = -(-φ)⋆ y`. -/
@[simp]
theorem cTransform_pairingCost (φ : E → EReal) (y : F) :
    cTransform (pairingCost B) φ y = -fenchelConjugate B (fun x => -φ x) y := by
  have hneg : -(⨆ x, ((B x y : EReal) - -φ x)) = ⨅ x, -((B x y : EReal) - -φ x) :=
    EReal.negOrderIso.map_iSup _
  rw [cTransform_apply, fenchelConjugate_apply, hneg]
  refine iInf_congr fun x => ?_
  rw [pairingCost_apply, EReal.neg_coe_sub, EReal.coe_neg, sub_eq_add_neg, sub_eq_add_neg,
    add_comm]

/-- The symmetric `c`-transform for the pairing cost is the negative of the Legendre–Fenchel
conjugate, for the transposed pairing, of the negated potential. -/
@[simp]
theorem cTransformSymm_pairingCost (ψ : F → EReal) (x : E) :
    cTransformSymm (pairingCost B) ψ x = -fenchelConjugate B.flip (fun y => -ψ y) x := by
  rw [cTransformSymm_eq_cTransform, ← pairingCost_flip, cTransform_pairingCost]

/-- A potential is `c`-concave for the pairing cost exactly when its negative is a
Legendre–Fenchel conjugate for the transposed pairing. -/
theorem isCConcave_pairingCost_iff (φ : E → EReal) :
    IsCConcave (pairingCost B) φ ↔
      ∃ g : F → EReal, (fun x => -φ x) = fenchelConjugate B.flip g := by
  constructor
  · intro h
    refine ⟨fun y => -cTransform (pairingCost B) φ y, funext fun x => ?_⟩
    calc -φ x = -cTransformSymm (pairingCost B) (cTransform (pairingCost B) φ) x := by
          rw [h.cTransformSymm_cTransform]
      _ = fenchelConjugate B.flip (fun y => -cTransform (pairingCost B) φ y) x := by
          rw [cTransformSymm_pairingCost, neg_neg]
  · rintro ⟨g, hg⟩
    have hφ : φ = cTransformSymm (pairingCost B) fun y => -g y := funext fun x => by
      rw [cTransformSymm_pairingCost]
      simp only [neg_neg]
      rw [← congr_fun hg x, neg_neg]
    rw [hφ]
    exact isCConcave_cTransformSymm _ _

/-- A potential on the target is `c`-concave for the pairing cost exactly when its negative is a
Legendre–Fenchel conjugate for the pairing. -/
theorem isCConcaveSymm_pairingCost_iff (ψ : F → EReal) :
    IsCConcaveSymm (pairingCost B) ψ ↔
      ∃ g : E → EReal, (fun y => -ψ y) = fenchelConjugate B g := by
  rw [isCConcaveSymm_iff_isCConcave, ← pairingCost_flip, isCConcave_pairingCost_iff,
    LinearMap.flip_flip]

end

variable [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- The `c`-superdifferential of a potential for the pairing cost is the graph of the
subdifferential of the negated potential. -/
@[simp]
theorem cSuperdifferential_pairingCost (φ : E → EReal) :
    cSuperdifferential (pairingCost B) φ = {p | p.2 ∈ subdifferential B (fun x => -φ x) p.1} := by
  ext ⟨x, y⟩
  rw [mk_mem_cSuperdifferential_iff, Set.mem_ofPred_eq,
    mem_subdifferential_iff_add_fenchelConjugate_eq, cTransform_pairingCost, pairingCost_apply,
    EReal.add_eq_coe_iff_neg_add_neg_eq, neg_neg, neg_neg]

end TauCeti

end

end
