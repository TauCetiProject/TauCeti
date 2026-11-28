/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.LittlewoodRichardson
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod

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
`N ≤ n` variables (`TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen`) without requiring rational Weyl
modules or `FDRep`; sharpness of the `N ≤ n` bound is recorded here as
`TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`, and input-swap symmetry of `hiveCount`
is `TauCeti.Hive.hiveCount_comm` (via `TauCeti.natCard_lrTableau_comm`).

## Main results

* `TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`: **the hive model of the
  Littlewood–Richardson rule** for Schur polynomials in `N ≤ n` variables over any commutative
  semiring.
* `TauCeti.Hive.finite_support_hiveCount_smul_diagramSchurPoly`,
  `TauCeti.Hive.map_finsum_hiveCount_smul_diagramSchurPoly`,
  `TauCeti.Hive.eval₂_finsum_hiveCount_smul_diagramSchurPoly`,
  `TauCeti.Hive.aeval_snoc_zero_finsum_hiveCount_smul_diagramSchurPoly`,
  `TauCeti.Hive.finsum_hiveCount_smul_diagramSchurPoly_eq_of_shape_eq`, and
  `TauCeti.Hive.finsum_hiveCount_smul_diagramSchurPoly_eq_zero`:
  finite support, coefficient-ring transport, evaluation transport, rank comparison and
  vanishing, and last-variable specialization along `Fin.snoc · 0`.
* `TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`: **sharpness** of the `N ≤ n` bound.
* `TauCeti.Hive.hiveCount_comm`: **input symmetry** `hiveCount (productBoundary l m p) =
  hiveCount (productBoundary m l p)`, without requiring rational Weyl modules or `FDRep`.

## References

* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: Proof of the saturation
  conjecture*, J. Amer. Math. Soc. 12 (1999), 1055–1090, Theorem 4 and Appendix 2, Proposition 4.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. 11 (2004), R61, Theorem 1.
-/

public section

open scoped BigOperators

open MvPolynomial

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
  have hrange : ∀ γ ∉ Set.range emb, f γ = 0 := by
    intro γ hγ
    by_contra hne
    have hcnt : hiveCount (productBoundary lam μ γ) ≠ 0 := fun h => hne (by simp [f, h])
    rw [hiveCount_productBoundary_of_isPolynomial hlam hμ γ] at hcnt
    split_ifs at hcnt with hγ_poly
    · obtain ⟨T⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hcnt)).1
      refine hγ ⟨⟨γ.shape.toPartition T.card_eq, ?_⟩, ?_⟩
      · rw [YoungDiagram.ofPartition_toPartition]
        exact DominantWeight.colLen_zero_shape_le γ
      · rw [hemb, YoungDiagram.ofPartition_toPartition, weightOfShape_shape hγ_poly]
    · exact absurd rfl hcnt
  rw [← TauCeti.finsum_comp_eq_of_injective emb.injective f hrange, finsum_eq_sum_of_fintype,
    diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau,
    sum_smul_diagramSchurPoly_eq_sum_colLen_le hN]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [f, hemb ν, shape_weightOfShape ν.property]
  congr 1
  rw [hiveCount_productBoundary_eq_natCard_lrTableau_shape hlam hμ
    (isPolynomial_weightOfShape n (ofPartition ν.val)), shape_weightOfShape ν.property]

/-- Finiteness of the support of the hive-indexed Schur sum, enabling `map_finsum` along any
ring or semiring homomorphism. -/
theorem finite_support_hiveCount_smul_diagramSchurPoly {n N : ℕ} {R : Type*}
    [CommSemiring R] (lam μ : DominantWeight n) :
    (Function.support fun γ : DominantWeight n =>
      hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape).Finite :=
  Function.HasFiniteSupport.smul_left
    (f := fun γ => hiveCount (productBoundary lam μ γ))
    (by simpa [Function.HasFiniteSupport, Function.support, Nat.pos_iff_ne_zero] using
      finite_support_hiveCount_productBoundary lam μ)
    (fun γ => diagramSchurPoly N R γ.shape)

/-- Coefficient-ring transport for the hive-indexed Schur sum along any semiring homomorphism
`f : R →+* S`. -/
theorem map_finsum_hiveCount_smul_diagramSchurPoly {n N : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (lam μ : DominantWeight n) :
    MvPolynomial.map f
        (∑ᶠ γ : DominantWeight n,
          hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • diagramSchurPoly N S γ.shape := by
  rw [map_finsum (MvPolynomial.map f)
    (finite_support_hiveCount_smul_diagramSchurPoly lam μ)]
  refine finsum_congr fun γ => ?_
  rw [_root_.map_nsmul, map_diagramSchurPoly]

/-- Evaluation transport for the hive-indexed Schur sum along any semiring homomorphism
`f : R →+* S` and point `x : Fin N → S`. -/
theorem eval₂_finsum_hiveCount_smul_diagramSchurPoly {n N : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : Fin N → S) (lam μ : DominantWeight n) :
    eval₂ f x
        (∑ᶠ γ : DominantWeight n,
          hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • eval x (diagramSchurPoly N S γ.shape) := by
  rw [← MvPolynomial.eval_map, map_finsum_hiveCount_smul_diagramSchurPoly,
    map_finsum (eval x) (finite_support_hiveCount_smul_diagramSchurPoly lam μ)]
  refine finsum_congr fun γ => ?_
  rw [_root_.map_nsmul]

/-- Setting the last variable to `0` transports the `(N + 1)`-variable hive-indexed Schur sum
of rank `n` termwise to the `N`-variable sum of the same rank, without polynomiality or row-bound
hypotheses. -/
theorem aeval_snoc_zero_finsum_hiveCount_smul_diagramSchurPoly {n N : ℕ} {R : Type*}
    [CommSemiring R] (lam μ : DominantWeight n) :
    aeval (Fin.snoc (X : Fin N → MvPolynomial (Fin N) R) 0)
        (∑ᶠ γ : DominantWeight n,
          hiveCount (productBoundary lam μ γ) • diagramSchurPoly (N + 1) R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape := by
  rw [map_finsum (aeval (Fin.snoc (X : Fin N → MvPolynomial (Fin N) R) 0))
    (finite_support_hiveCount_smul_diagramSchurPoly lam μ)]
  refine finsum_congr fun γ => ?_
  rw [_root_.map_nsmul, aeval_snoc_zero_diagramSchurPoly]

/-- Two hive-indexed Schur sums in a common alphabet `Fin N` (`N ≤ m`, `N ≤ n`) coincide when their
polynomial input weights have the same Young diagrams. -/
theorem finsum_hiveCount_smul_diagramSchurPoly_eq_of_shape_eq {m n N : ℕ} {R : Type*}
    [CommSemiring R] (hNm : N ≤ m) (hNn : N ≤ n)
    {lam₁ μ₁ : DominantWeight m} {lam₂ μ₂ : DominantWeight n}
    (hl₁ : lam₁.IsPolynomial) (hm₁ : μ₁.IsPolynomial)
    (hl₂ : lam₂.IsPolynomial) (hm₂ : μ₂.IsPolynomial)
    (hlam : lam₁.shape = lam₂.shape) (hμ : μ₁.shape = μ₂.shape) :
    (∑ᶠ γ : DominantWeight m,
      hiveCount (productBoundary lam₁ μ₁ γ) • diagramSchurPoly N R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam₂ μ₂ γ) • diagramSchurPoly N R γ.shape := by
  rw [← diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount hNm hl₁ hm₁,
    hlam, hμ, diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount hNn hl₂ hm₂]

/-- The hive-indexed Schur sum in `N` variables vanishes when either polynomial input weight of
rank `n` has more than `N` rows (which in particular forces `N < n`). -/
theorem finsum_hiveCount_smul_diagramSchurPoly_eq_zero {n N : ℕ} {R : Type*}
    [CommSemiring R] {lam μ : DominantWeight n}
    (hl : lam.IsPolynomial) (hm : μ.IsPolynomial)
    (hlt : N < lam.shape.colLen 0 ∨ N < μ.shape.colLen 0) :
    (∑ᶠ γ : DominantWeight n,
      hiveCount (productBoundary lam μ γ) • diagramSchurPoly N R γ.shape) = 0 := by
  have hN : N ≤ n := by
    rcases hlt with h | h
    · exact (h.trans_le lam.colLen_zero_shape_le).le
    · exact (h.trans_le μ.colLen_zero_shape_le).le
  rw [← diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount hN hl hm]
  rcases hlt with h | h
  · rw [diagramSchurPoly_eq_zero_of_lt_colLen h, zero_mul]
  · rw [diagramSchurPoly_eq_zero_of_lt_colLen h, mul_zero]

/-- Sharpness of the `N ≤ n` alphabet bound in
`diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`: for rank `1` weights
`λ = μ = (1)` evaluated in `2` variables, `s_{(1)}² = s_{(2)} + s_{(1, 1)}`, whereas the rank-`1`
hive sum produces only `s_{(2)}` and omits the nonzero term `s_{(1, 1)}`. -/
theorem schur_mul_two_vars_ne_finsum_hiveCount_one :
    let ω : DominantWeight 1 := ⟨![1], by decide⟩
    diagramSchurPoly 2 ℤ ω.shape * diagramSchurPoly 2 ℤ ω.shape ≠
      ∑ᶠ γ : DominantWeight 1,
        hiveCount (productBoundary ω ω γ) • diagramSchurPoly 2 ℤ γ.shape := by
  intro ω heq
  let std₂ : DominantWeight 2 := ⟨![1, 0], by decide⟩
  let sym₂ : DominantWeight 2 := ⟨![2, 0], by decide⟩
  let det₂ : DominantWeight 2 := ⟨![1, 1], by decide⟩
  have hstd₂ : std₂.IsPolynomial := by rw [DominantWeight.isPolynomial_def]; decide
  have hrhs₁ : (∑ᶠ γ : DominantWeight 1,
      hiveCount (productBoundary ω ω γ) • diagramSchurPoly 2 ℤ γ.shape) =
      diagramSchurPoly 2 ℤ sym₂.shape := by
    rw [finsum_eq_single _ (ω + ω)]
    · rw [(DominantWeight.shape_eq_shape_iff (ω + ω) sym₂).mpr fun i => by
        rcases i with _ | _ | i <;> rfl]
      simp [hiveCount_one_productBoundary]
    · intro γ hγ
      have hne : ω.val 0 + ω.val 0 ≠ γ.val 0 := fun h => hγ <| by
        ext i; rw [Fin.fin_one_eq_zero i]; simp [← h]
      simp [hiveCount_one_productBoundary, hne]
  have hsupp₂ : Function.support
      (fun δ : DominantWeight 2 =>
        hiveCount (productBoundary std₂ std₂ δ) • diagramSchurPoly 2 ℤ δ.shape) ⊆
      ({sym₂, det₂} : Finset (DominantWeight 2)) := by
    intro δ hδ
    rw [Function.mem_support] at hδ
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hnot
    dsimp only [sym₂, det₂] at hnot
    rw [hiveCount_two_std_std_eq] at hδ
    simp only [hnot, ↓reduceIte, zero_smul] at hδ
    exact hδ rfl
  have hlhs₂ : diagramSchurPoly 2 ℤ ω.shape * diagramSchurPoly 2 ℤ ω.shape =
      diagramSchurPoly 2 ℤ sym₂.shape + diagramSchurPoly 2 ℤ det₂.shape := by
    rw [(DominantWeight.shape_eq_shape_iff ω std₂).mpr fun i => by
        rcases i with _ | _ | i <;> rfl,
      diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount le_rfl hstd₂ hstd₂,
      finsum_eq_sum_of_support_subset _ hsupp₂, Finset.sum_pair (by decide : sym₂ ≠ det₂),
      hiveCount_two_std_std_eq, hiveCount_two_std_std_eq]
    simp [sym₂, det₂]
  rw [hlhs₂, hrhs₁] at heq
  exact diagramSchurPoly_ne_zero det₂.colLen_zero_shape_le (add_eq_left.mp heq)

/-! ### Input-swap symmetry of hive counts -/

/-- **Symmetry of hive counts in the two inputs**: `c^p_{l, m} = c^p_{m, l}` for all dominant
weights `l, m, p` of `GL n`. -/
theorem hiveCount_comm {n : ℕ} (l m p : DominantWeight n) :
    hiveCount (productBoundary l m p) = hiveCount (productBoundary m l p) := by
  rw [hiveCount_productBoundary, hiveCount_productBoundary, add_comm l.detShift m.detShift]
  split_ifs
  · exact natCard_lrTableau_comm _ _ _
  · rfl

end TauCeti.Hive
