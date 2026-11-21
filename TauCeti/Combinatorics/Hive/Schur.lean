/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Combinatorics.Hive.LittlewoodRichardson
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# The hive Littlewood–Richardson rule for Schur polynomials

For polynomial dominant weights `λ, μ` of `GLₙ`, the product of Schur polynomials
`diagramSchurPoly n R λ.shape * diagramSchurPoly n R μ.shape` expands over dominant weights `γ`
with multiplicities given by the fixed-boundary integer hive counts
`hiveCount (productBoundary λ μ γ)`.

## Main results

* `TauCeti.Hive.schur_mul_eq_finsum_hiveCount`: hive Littlewood–Richardson expansion for products
  of Schur polynomials over any commutative semiring.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) **46**
  (2000), 43–60.
-/

public section

namespace TauCeti.Hive

/-- **The hive Littlewood–Richardson rule for Schur polynomials**: over any commutative semiring
`R`, the product of the Schur polynomials of two polynomial dominant weights `λ, μ` expands as a
finitely supported sum over dominant weights `γ` with multiplicity
`hiveCount (productBoundary λ μ γ)`. -/
theorem schur_mul_eq_finsum_hiveCount {n : ℕ} {R : Type*} [CommSemiring R]
    (lam μ : DominantWeight n) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    diagramSchurPoly n R lam.shape * diagramSchurPoly n R μ.shape =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • diagramSchurPoly n R γ.shape := by
  classical
  rw [diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau,
    sum_nsmul_diagramSchurPoly_eq_sum_colLen_le]
  let e : {ν : (lam.shape.card + μ.shape.card).Partition //
      (YoungDiagram.ofPartition ν).colLen 0 ≤ n} ↪ DominantWeight n :=
    ⟨fun ν => weightOfShape n (YoungDiagram.ofPartition ν.val), fun ν₁ ν₂ h => Subtype.ext <|
      YoungDiagram.ofPartition_injective <| by
        have h' := congrArg DominantWeight.shape h
        rwa [shape_weightOfShape ν₁.property, shape_weightOfShape ν₂.property] at h'⟩
  have he (ν) : e ν = weightOfShape n (YoungDiagram.ofPartition ν.val) := rfl
  have hsupp : Function.support (fun γ : DominantWeight n =>
      hiveCount (productBoundary lam μ γ) • diagramSchurPoly n R γ.shape) ⊆
      (Finset.univ.map e : Set (DominantWeight n)) := by
    intro γ hγ
    have hpos : 0 < hiveCount (productBoundary lam μ γ) := Nat.pos_of_ne_zero fun h0 => by
      simp [h0] at hγ
    obtain ⟨⟨h, hb⟩⟩ := hiveCount_pos_iff.mp hpos
    have hγp : γ.IsPolynomial := isPolynomial_of_productBoundary hb hlam hμ
    let T := lrTableauOfHive hlam hμ ⟨h, hb⟩
    refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨⟨γ.shape.toPartition T.card_eq, by simp⟩,
      Finset.mem_univ _, ?_⟩)
    rw [he, YoungDiagram.ofPartition_toPartition, weightOfShape_shape hγp]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hpoly : (e ν).IsPolynomial := isPolynomial_weightOfShape n _
  have hshape : (e ν).shape = YoungDiagram.ofPartition ν.val := shape_weightOfShape ν.property
  rw [hiveCount_productBoundary_eq_natCard_lrTableau hlam hμ hpoly, hshape]

end TauCeti.Hive
