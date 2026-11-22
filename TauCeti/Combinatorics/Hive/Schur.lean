/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Combinatorics.Hive.LittlewoodRichardson
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete

/-!
# The hive model of the Littlewood–Richardson rule for Schur polynomials

Taking cardinalities across the bijections of `TauCeti.Combinatorics.Hive.LittlewoodRichardson`
identifies integer hive counts `hiveCount (productBoundary λ μ γ)` with Littlewood–Richardson
coefficients `c^γ_{λ μ} = Nat.card (LRTableau λ γ μ)` for polynomial weights
(`TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau_shape`), for Young diagrams of at
most `n` rows (`TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`, giving rank
independence in `TauCeti.Hive.hiveCount_weightOfShape_eq_of_colLen_le`), and for arbitrary signed
dominant weights via determinant shifts (`TauCeti.Hive.hiveCount_productBoundary_eq_ite_detShift`).

Combining this cardinality bridge with Stembridge's Schur-polynomial Littlewood–Richardson rule
(`TauCeti.diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau`) yields the **hive model
of the Littlewood–Richardson rule**
(`TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`): for polynomial dominant
weights `λ, μ : DominantWeight n` and any commutative semiring `R`,

`s_λ · s_μ = ∑ᶠ γ : DominantWeight n, hiveCount (productBoundary λ μ γ) • s_γ`

in `n` variables (`MvPolynomial (Fin n) R`). Non-polynomial weights `γ` and weights of total size
distinct from `|λ| + |μ|` have zero hive count, while Young diagrams of more than `n` rows vanish in
`n` variables (`TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen`). This variable-count matching is
sharp (`TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_ne_finsum_hiveCount_one_two`): in two
variables for `n = 1` and `λ = μ = (1)`, `s_{(1)}^2 = s_{(2)} + s_{(1, 1)}`, whereas the rank-`1`
hive sum sees only `s_{(2)}`.

Combining `TauCeti.Hive.hiveCount_productBoundary_eq_ite_detShift` with the symmetry
`TauCeti.natCard_lrTableau_comm` yields the non-obvious input-swap symmetry
`hiveCount (productBoundary λ μ γ) = hiveCount (productBoundary μ λ γ)` for all signed dominant
weights `λ, μ, γ : DominantWeight n` (`TauCeti.Hive.hiveCount_comm`).

## Main results

* `TauCeti.Hive.hiveCount_weightOfShape_eq_of_colLen_le`: rank stability of hive counts.
* `TauCeti.Hive.hiveCount_productBoundary_eq_ite_detShift`: universal formula for arbitrary signed
  dominant weights `λ, μ, γ : DominantWeight n`.
* `TauCeti.Hive.hiveCount_comm`: symmetry `hiveCount (productBoundary λ μ γ) =
  hiveCount (productBoundary μ λ γ)` for all signed dominant weights.
* `TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`: **the hive model of the
  Littlewood–Richardson rule** for Schur polynomials in `n` variables over any commutative semiring.
* `TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_ne_finsum_hiveCount_one_two`: sharpness of the
  `n`-variable restriction.

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

/-! ### Rank stability, universal signed formula, and input-swap symmetry -/

/-- **Rank stability of hive counts**: for Young diagrams `λ, μ, ν` fitting in both `n` and `m`
rows, their `GL_n` and `GL_m` hive counts coincide. -/
theorem hiveCount_weightOfShape_eq_of_colLen_le {n m : ℕ} {lam μ ν : YoungDiagram}
    (hlam_n : lam.colLen 0 ≤ n) (hμ_n : μ.colLen 0 ≤ n) (hν_n : ν.colLen 0 ≤ n)
    (hlam_m : lam.colLen 0 ≤ m) (hμ_m : μ.colLen 0 ≤ m) (hν_m : ν.colLen 0 ≤ m) :
    hiveCount (productBoundary (weightOfShape n lam) (weightOfShape n μ) (weightOfShape n ν)) =
      hiveCount (productBoundary (weightOfShape m lam) (weightOfShape m μ) (weightOfShape m ν)) :=
  (hiveCount_productBoundary_eq_natCard_lrTableau hlam_n hν_n hμ_n).trans
    (hiveCount_productBoundary_eq_natCard_lrTableau hlam_m hν_m hμ_m).symm

/-- **Universal signed hive-count formula**: for arbitrary signed dominant weights
`λ, μ, γ : DominantWeight n`, `hiveCount (productBoundary λ μ γ)` equals the Littlewood–Richardson
coefficient of `(γ.shift (-(λ.detShift + μ.detShift))).shape / λ.detShiftShape` with content
`μ.detShiftShape` when `λ.detShift + μ.detShift ≤ γ.detShift`, and `0` otherwise. -/
theorem hiveCount_productBoundary_eq_ite_detShift {n : ℕ} (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      if lam.detShift + μ.detShift ≤ γ.detShift then
        Nat.card (LRTableau lam.detShiftShape
          (γ.shift (-(lam.detShift + μ.detShift))).shape μ.detShiftShape)
      else 0 := by
  split_ifs with hdet
  · rw [← natCard_fixedIntegerHive]
    exact Nat.card_congr (fixedIntegerHiveSignedEquivLRTableau hdet)
  · exact hiveCount_productBoundary_eq_zero_of_detShift_lt (lt_of_not_ge hdet)

/-- **Input-swap symmetry of `hiveCount`** for all signed dominant weights `λ, μ, γ`:
`hiveCount (productBoundary λ μ γ) = hiveCount (productBoundary μ λ γ)`. Unlike cyclic rotation and
reflection (`hiveCount_rotate`, `hiveCount_reflect`), swapping `(λ, μ)` without dualizing `γ` is not
a geometric symmetry of a single hive. -/
theorem hiveCount_comm {n : ℕ} (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) = hiveCount (productBoundary μ lam γ) := by
  rw [hiveCount_productBoundary_eq_ite_detShift, hiveCount_productBoundary_eq_ite_detShift,
    add_comm μ.detShift, natCard_lrTableau_comm]

/-! ### The Schur-polynomial expansion over hive counts -/

/-- **The hive model of the Littlewood–Richardson rule** (Knutson–Tao–Woodward, Theorem 1;
Knutson–Tao I, Theorem 4 with Appendix 2, Proposition 4): for polynomial dominant weights
`λ, μ : DominantWeight n` and any commutative semiring `R`, the product of Schur polynomials in `n`
variables expands over all dominant weights `γ : DominantWeight n` with integer hive counts as
coefficients. -/
theorem diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount {n : ℕ} {R : Type*}
    [CommSemiring R] {lam μ : DominantWeight n} (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    diagramSchurPoly n R lam.shape * diagramSchurPoly n R μ.shape =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • diagramSchurPoly n R γ.shape := by
  classical
  let ι := {ν : (lam.shape.card + μ.shape.card).Partition // (ofPartition ν).colLen 0 ≤ n}
  let embDiag : ι ↪ {μ : YoungDiagram // μ.colLen 0 ≤ n} :=
    ⟨fun ν => ⟨ofPartition ν.val, ν.property⟩,
      fun _ _ h => Subtype.ext (YoungDiagram.ofPartition_injective (congrArg Subtype.val h))⟩
  let emb : ι ↪ DominantWeight n :=
    embDiag.trans ((shapeEquivPolynomialWeight n).toEmbedding.trans (Function.Embedding.subtype _))
  let f (γ : DominantWeight n) : MvPolynomial (Fin n) R :=
    hiveCount (productBoundary lam μ γ) • diagramSchurPoly n R γ.shape
  have hsupp : Function.support f ⊆ (Finset.univ.map emb : Finset (DominantWeight n)) := by
    intro γ hγ_supp
    have hcnt : hiveCount (productBoundary lam μ γ) ≠ 0 :=
      Function.support_smul_subset_left (fun γ => hiveCount (productBoundary lam μ γ))
        (fun γ => diagramSchurPoly n R γ.shape) hγ_supp
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
    exact (congrArg (weightOfShape n) (YoungDiagram.ofPartition_toPartition hcard)).trans
      (weightOfShape_shape hγ_poly)
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_map,
    diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau,
    sum_nsmul_diagramSchurPoly_eq_sum_colLen_le]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hterm : emb ν = weightOfShape n (ofPartition ν.val) := rfl
  simp only [f, hterm, shape_weightOfShape ν.property]
  congr 1
  rw [hiveCount_productBoundary_eq_natCard_lrTableau_shape hlam hμ
    (isPolynomial_weightOfShape n (ofPartition ν.val)), shape_weightOfShape ν.property]

private theorem finsum_hiveCount_one_eq_smul :
    let lam : DominantWeight 1 := ⟨![1], by decide⟩
    let γ₁ : DominantWeight 1 := ⟨![2], by decide⟩
    (∑ᶠ γ : DominantWeight 1,
      hiveCount (productBoundary lam lam γ) • diagramSchurPoly 2 ℤ γ.shape) =
      hiveCount (productBoundary lam lam γ₁) • diagramSchurPoly 2 ℤ γ₁.shape := by
  intro lam γ₁
  refine finsum_eq_single _ γ₁ fun γ hne => ?_
  have hsum : lam.val 0 + lam.val 0 ≠ γ.val 0 := fun h =>
    hne (by ext i; fin_cases i; simpa [lam, γ₁] using h.symm)
  simp [hiveCount_one_productBoundary, hsum]

/-- **Sharpness of the `n`-variable restriction in
`diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`**: in `2` variables for `n = 1` and
`λ = μ = (1)`, `s_{(1)}^2 = s_{(2)} + s_{(1, 1)}`, whereas summing over `γ : DominantWeight 1`
produces only `s_{(2)}` because `γ.shape` has at most one row. -/
theorem diagramSchurPoly_mul_diagramSchurPoly_ne_finsum_hiveCount_one_two :
    let lam : DominantWeight 1 := ⟨![1], by decide⟩
    diagramSchurPoly 2 ℤ lam.shape * diagramSchurPoly 2 ℤ lam.shape ≠
      ∑ᶠ γ : DominantWeight 1,
        hiveCount (productBoundary lam lam γ) • diagramSchurPoly 2 ℤ γ.shape := by
  intro lam heq
  let γ₁ : DominantWeight 1 := ⟨![2], by decide⟩
  have hlam : lam.IsPolynomial := by
    rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_succ]; decide
  have hγ₁ : γ₁.IsPolynomial := by
    rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_succ]; decide
  have hcard_lam : lam.shape.card = 1 :=
    Int.ofNat_inj.mp ((DominantWeight.natCast_card_shape hlam).trans (by decide))
  have hcard_γ₁ : γ₁.shape.card = 2 :=
    Int.ofNat_inj.mp ((DominantWeight.natCast_card_shape hγ₁).trans (by decide))
  have hcnt : hiveCount (productBoundary lam lam γ₁) = 1 := by
    simp [hiveCount_one_productBoundary, lam, γ₁]
  rw [finsum_hiveCount_one_eq_smul, hcnt, one_smul,
    diagramSchurPoly_eq_hsymm_of_colLen_le_one (DominantWeight.colLen_zero_shape_le lam),
    diagramSchurPoly_eq_hsymm_of_colLen_le_one (DominantWeight.colLen_zero_shape_le γ₁),
    hcard_lam, hcard_γ₁] at heq
  have heval := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℤ))) heq
  rw [map_mul, eval_hsymm_fin_two, eval_hsymm_fin_two] at heval
  simp at heval

end TauCeti.Hive
