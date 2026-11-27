/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.LittlewoodRichardson
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# The hive model of the Littlewood–Richardson rule for Schur polynomials

Combining the cardinality bridge
`TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau_shape` with Stembridge's
Schur-polynomial Littlewood–Richardson rule
(`TauCeti.diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau`) yields the **hive model
of the Littlewood–Richardson rule** in `N ≤ n` variables
(`TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`): for polynomial dominant
weights `λ, μ : DominantWeight n`, any `N ≤ n`, and any commutative semiring `R`,

`s_λ · s_μ = ∑ᶠ γ : DominantWeight n, hiveCount (productBoundary λ μ γ) • s_γ`

in `N` variables (`MvPolynomial (Fin N) R`). Non-polynomial weights `γ` and weights of total size
distinct from `|λ| + |μ|` have zero hive count, while Young diagrams of more than `n` rows vanish in
`N ≤ n` variables (`TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen`). This generalizes the `N = n`
statement `TauCeti.Hive.schur_mul_eq_finsum_hiveCount` in
`TauCeti.Combinatorics.Hive.Multiplicity` without requiring representation theory; sharpness of the
`N ≤ n` bound is recorded there as `TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`, and
input-swap symmetry of `hiveCount` is `TauCeti.Hive.hiveCount_comm` (with the purely
polynomial/combinatorial proof on Young diagrams in `YoungDiagram.natCard_lrTableau_comm`).

## Main results

* `TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`: **the hive model of the
  Littlewood–Richardson rule** for Schur polynomials in `N ≤ n` variables over any commutative
  semiring.

## References

* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: Proof of the saturation
  conjecture*, J. Amer. Math. Soc. 12 (1999), 1055–1090, Theorem 4 and Appendix 2, Proposition 4.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. 11 (2004), R61, Theorem 1.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

open YoungDiagram (ofPartition)

/-! ### The Schur-polynomial expansion over hive counts -/

/-- **The hive model of the Littlewood–Richardson rule** (Knutson–Tao–Woodward, Theorem 1;
Knutson–Tao I, Theorem 4 with Appendix 2, Proposition 4): for polynomial dominant weights
`λ, μ : DominantWeight n`, any `N ≤ n`, and any commutative semiring `R`, the product of Schur
polynomials in `N` variables expands over all dominant weights `γ : DominantWeight n` with integer
hive counts as coefficients. -/
theorem diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount {n N : ℕ} (hN : N ≤ n)
    {R : Type*} [CommSemiring R] {lam μ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    diagramSchurPoly N R lam.shape * diagramSchurPoly N R μ.shape =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape := by
  classical
  let ι := {ν : (lam.shape.card + μ.shape.card).Partition // (ofPartition ν).colLen 0 ≤ n}
  let embDiag : ι ↪ {μ : YoungDiagram // μ.colLen 0 ≤ n} :=
    (⟨ofPartition, YoungDiagram.ofPartition_injective⟩ : _ ↪ YoungDiagram).subtypeMap
      (fun _ h => h)
  let emb : ι ↪ DominantWeight n :=
    embDiag.trans ((shapeEquivPolynomialWeight n).toEmbedding.trans (Function.Embedding.subtype _))
  have hemb (ν : ι) : emb ν = weightOfShape n (ofPartition ν.val) :=
    Subtype.ext (by
      simp [emb, embDiag, shapeEquivPolynomialWeight_apply_coe, Function.Embedding.subtypeMap])
  let f (γ : DominantWeight n) : MvPolynomial (Fin N) R :=
    hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape
  have hsupp : Function.support f ⊆ (Finset.univ.map emb : Finset (DominantWeight n)) := by
    intro γ hγ_supp
    have hcnt : hiveCount (productBoundary lam μ γ) ≠ 0 :=
      Function.support_smul_subset_left (fun γ => hiveCount (productBoundary lam μ γ))
        (fun γ => diagramSchurPoly N R γ.shape) hγ_supp
    obtain ⟨h⟩ := hiveCount_pos_iff.mp (Nat.pos_of_ne_zero hcnt)
    have hγ_poly : γ.IsPolynomial := isPolynomial_of_productBoundary h.property hlam hμ
    have hcard : γ.shape.card = lam.shape.card + μ.shape.card := Int.ofNat_inj.mp <| by
      rw [DominantWeight.natCast_card_shape hγ_poly, Nat.cast_add,
        DominantWeight.natCast_card_shape hlam, DominantWeight.natCast_card_shape hμ,
        sum_eq_of_productBoundary h.property]
    refine Finset.mem_coe.mpr (Finset.mem_map.mpr
      ⟨⟨γ.shape.toPartition hcard, by
        rw [YoungDiagram.ofPartition_toPartition]
        exact DominantWeight.colLen_zero_shape_le γ⟩, Finset.mem_univ _, ?_⟩)
    rw [hemb, YoungDiagram.ofPartition_toPartition, weightOfShape_shape hγ_poly]
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_map,
    diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau,
    ← Fintype.sum_subtype_add_sum_subtype fun ν => (ofPartition ν).colLen 0 ≤ n,
    Fintype.sum_eq_zero (fun ν : {ν // ¬(ofPartition ν).colLen 0 ≤ n} => _) fun ν => by
      rw [diagramSchurPoly_eq_zero_of_lt_colLen (hN.trans_lt (not_le.mp ν.property)), smul_zero],
    add_zero]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [f, hemb ν, shape_weightOfShape ν.property]
  congr 1
  rw [hiveCount_productBoundary_eq_natCard_lrTableau_shape hlam hμ
    (isPolynomial_weightOfShape n (ofPartition ν.val)), shape_weightOfShape ν.property]

end TauCeti.Hive
