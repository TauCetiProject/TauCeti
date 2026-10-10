/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Pieri

/-!
# Products of complete homogeneous symmetric polynomials in the Schur basis

A product of complete homogeneous symmetric polynomials expands in the Schur polynomials with the
Kostka numbers as coefficients: for a partition `ν`,

`h_ν = h_{ν₁} ⋯ h_{ν_k} = ∑_μ K_{μν} s_μ`,

where `K_{μν}` is the number of semistandard tableaux of shape `μ` and content `ν`.  This is
`TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly`, for Mathlib's `MvPolynomial.hsymmPart` in an
arbitrary finite alphabet.  The same holds for an arbitrary ordered sequence of degrees in place of
the parts of `ν`, with the Kostka number of a shape and a content that need not be weakly
decreasing (`TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly`).

Together with the monomial expansion `s_μ = ∑_ξ K_{μξ} m_ξ`
(`TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm`), the expansion computes the coefficients of
`h_ν` in terms of Kostka numbers alone: the coefficient of `x^ξ` in `h_ν` is `∑_μ K_{μν} K_{μξ}`
(`TauCeti.coeff_hsymmPart`, and `TauCeti.coeff_hsymmPart_partWeight` at partitions).  On the side
of the symmetric groups `h_ν` corresponds to the permutation module `M^ν` and `s_μ` to the Specht
module `S^μ` (classically, through the Frobenius characteristic map), so this is the
symmetric-function half of Young's rule `M^ν ≅ ⊕_μ K_{μν} S^μ`.

## The argument

The expansion is the Pieri rule `h_r · s_ν = ∑ s_μ` (`TauCeti.hsymm_mul_diagramSchurPoly`), the sum
running over the shapes `μ` obtained from `ν` by adding a horizontal strip of `r` cells, iterated
along a sequence of degrees `c₀, …, c_{k-1}`.  Each iteration adds one horizontal strip, so after
`k` steps the coefficient of `s_μ` counts the chains `∅ = μ⁰ ⊆ μ¹ ⊆ ⋯ ⊆ μᵏ = μ` of shapes in which
`μⁱ / μⁱ⁻¹` is a horizontal strip of `c_{i-1}` cells.  Such a chain is a semistandard tableau of
shape `μ` and content `c`: the cells of `μⁱ / μⁱ⁻¹` are those carrying the letter `i - 1`.  The
induction step reads this bijection one letter at a time, as the weight-refined branching rule for
tableaux `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`, re-indexed by partitions:
erasing the largest letter of a tableau leaves a tableau on a shape interlacing the original one,
whose size is fixed by how often the erased letter occurred.

## Main results

* `TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly`: **the expansion of
  `h_{c₀} ⋯ h_{c_{k-1}}` in the Schur polynomials**, for an arbitrary sequence of degrees, and
  `TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly`, the same in a finite alphabet.
* `TauCeti.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly`: **`h_ν = ∑_μ K_{μν} s_μ`** for a partition
  `ν`, in a finite alphabet.
* `TauCeti.coeff_hsymmPart`: the coefficient of `h_ν` at an arbitrary monomial `x^d` is
  `∑_μ K_{μν} K_{μd}`, and `TauCeti.coeff_hsymmPart_partWeight`, the same at the monomial of a
  partition `ξ`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 6.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Section 7.12.
* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {R : Type*} [CommSemiring R]

open scoped Classical in
/-- The weight-refined branching rule, re-indexed by partitions: the shapes interlacing the shape of
`μ` that contribute are the Young diagrams of the partitions of `|μ| - c k`. -/
private theorem card_weight_eq_sum_partition {k n : ℕ} (c : Fin (k + 1) → ℕ)
    (μ : (n + c (Fin.last k)).Partition) :
    Nat.card {T : BoundedSSYT (k + 1) (diagramOf μ) // ⇑(BoundedSSYT.weight T) = c} =
      ∑ ν : n.Partition with (diagramOf μ).InterlacedBy (diagramOf ν),
        Nat.card {T : BoundedSSYT k (diagramOf ν) //
          ⇑(BoundedSSYT.weight T) = fun i => c i.castSucc} := by
  classical
  rw [BoundedSSYT.card_weight_eq_sum_interlacingShapes]
  symm
  refine sum_bij_ne_zero (fun ν _ _ => diagramOf ν) (fun ν hν hne => ?_)
    (fun ν₁ _ _ ν₂ _ _ h => diagramOf_injective h) (fun ν hν hne => ?_) fun _ _ _ => rfl
  · refine mem_filter.mpr ⟨YoungDiagram.mem_interlacingShapes.mpr
      ⟨(mem_filter.mp hν).2, not_lt.mp fun hlt => hne ?_⟩, ?_⟩
    · have := BoundedSSYT.isEmpty_of_lt_colLen hlt
      exact Nat.card_of_isEmpty
    · rw [card_diagramOf, card_diagramOf]
  · obtain ⟨hν, hcard⟩ := mem_filter.mp hν
    have hn : ν.card = n := by rw [card_diagramOf] at hcard; omega
    refine ⟨toPartition ν hn, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_, ?_⟩
    · rw [diagramOf_toPartition]
      exact (YoungDiagram.mem_interlacingShapes.mp hν).1
    · rwa [diagramOf_toPartition]
    · exact diagramOf_toPartition ν hn

open scoped Classical in
/-- The expansion of a product of complete homogeneous symmetric polynomials in the Schur
polynomials, with the coefficients written as numbers of bounded tableaux of a given weight, and
the size `n` of the shapes a parameter fixed by a hypothesis. -/
private theorem prod_hsymm_eq_sum_card_smul (N : ℕ) :
    ∀ (k : ℕ) (c : Fin k → ℕ) (n : ℕ), ∑ i, c i = n →
      ∏ i, hsymm (Fin N) R (c i) = ∑ μ : n.Partition,
        (Nat.card {T : BoundedSSYT k (diagramOf μ) // ⇑(BoundedSSYT.weight T) = c} : R) •
          diagramSchurPoly N R (diagramOf μ)
  | 0, c, n, hc => by
    rw [Fin.sum_univ_zero] at hc
    subst hc
    have hbot : diagramOf (default : Nat.Partition 0) = ⊥ := diagramOf_eq_bot _
    have hcard : Nat.card {T : BoundedSSYT 0 (diagramOf (default : Nat.Partition 0)) //
        ⇑(BoundedSSYT.weight T) = c} = 1 := by
      rw [hbot, Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun T T' => Subtype.ext (Subsingleton.elim _ _)⟩,
        ⟨⟨default, Subsingleton.elim _ _⟩⟩⟩
    rw [Fin.prod_univ_zero, Fintype.sum_unique, hcard, hbot, diagramSchurPoly_bot, Nat.cast_one,
      one_smul]
  | k + 1, c, n, hc => by
    rw [Fin.sum_univ_castSucc] at hc
    subst hc
    have pieri (ν : (∑ i : Fin k, c i.castSucc).Partition) :
        hsymm (Fin N) R (c (Fin.last k)) * diagramSchurPoly N R (diagramOf ν) =
          ∑ μ : (∑ i : Fin k, c i.castSucc + c (Fin.last k)).Partition with
            (diagramOf μ).InterlacedBy (diagramOf ν), diagramSchurPoly N R (diagramOf μ) := by
      have h := hsymm_mul_diagramSchurPoly (R := R) (N := N) (diagramOf ν) (c (Fin.last k))
      rwa [card_diagramOf] at h
    rw [Fin.prod_univ_castSucc, prod_hsymm_eq_sum_card_smul N k _ _ rfl, mul_comm, mul_sum]
    simp_rw [mul_smul_comm, pieri, Finset.smul_sum, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun μ _ => ?_
    rw [card_weight_eq_sum_partition, Nat.cast_sum, sum_smul, sum_filter]

/-- **A product of complete homogeneous symmetric polynomials in the Schur basis.**  For a sequence
of degrees `d₀, …, d_{k-1}` summing to `n`, in the alphabet `Fin N`,

`h_{d₀} ⋯ h_{d_{k-1}} = ∑_μ K_{μ d} s_μ`,

the sum running over the partitions `μ` of `n`, where `K_{μ d}` is the number of semistandard
tableaux of shape `μ` using the letter `i` exactly `dᵢ` times.  The degrees need not be weakly
decreasing.  No bound relating `N` and `k` is needed: the shapes with more than `N` rows contribute
nothing, their Schur polynomials vanishing in `N` variables. -/
theorem prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly {N k n : ℕ} (d : Fin k →₀ ℕ)
    (hd : d.degree = n) :
    ∏ i, hsymm (Fin N) R (d i) = ∑ μ : n.Partition,
      (diagramKostkaNumber (diagramOf μ) (Finsupp.mapDomain Fin.val d) : R) •
        diagramSchurPoly N R (diagramOf μ) := by
  rw [prod_hsymm_eq_sum_card_smul N k d n ((Finsupp.degree_eq_sum d).symm.trans hd)]
  refine sum_congr rfl fun μ _ => ?_
  rw [← BoundedSSYT.card_weight_eq,
    Nat.card_congr (Equiv.subtypeEquivRight fun T => DFunLike.coe_fn_eq)]

/-- **A product of complete homogeneous symmetric polynomials in the Schur basis**, in a finite
alphabet `σ`: for a sequence of degrees `d₀, …, d_{k-1}` summing to `n`,
`h_{d₀} ⋯ h_{d_{k-1}} = ∑_μ K_{μ d} s_μ`, the sum running over the partitions `μ` of `n`.  This is
`TauCeti.prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly` with the alphabet renamed. -/
theorem prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly {σ : Type*} [Fintype σ]
    [DecidableEq σ] {k n : ℕ} (d : Fin k →₀ ℕ) (hd : d.degree = n) :
    ∏ i, hsymm σ R (d i) = ∑ μ : n.Partition,
      (diagramKostkaNumber (diagramOf μ) (Finsupp.mapDomain Fin.val d) : R) • schurPoly σ R μ := by
  have h := prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly (R := R)
    (N := Fintype.card σ) d hd
  apply_fun rename (Fintype.equivFin σ).symm at h
  rw [map_prod, map_sum] at h
  simp only [rename_hsymm, map_smul, ← schurPoly_eq_rename] at h
  exact h

/-- **`h_ν = ∑_μ K_{μν} s_μ`.**  In a finite alphabet, the product `h_ν = h_{ν₁} ⋯ h_{ν_k}` of the
complete homogeneous symmetric polynomials over the parts of a partition `ν` of `n` expands in the
Schur polynomials of the partitions of `n`, with the Kostka numbers `K_{μν}` as coefficients.  This
is the symmetric-function form of Young's rule for the permutation modules of the symmetric
groups. -/
theorem hsymmPart_eq_sum_kostkaNumber_smul_schurPoly (σ : Type*) [Fintype σ] [DecidableEq σ]
    {n : ℕ} (ν : n.Partition) :
    hsymmPart σ R ν = ∑ μ : n.Partition, (kostkaNumber μ ν : R) • schurPoly σ R μ := by
  -- Expand along the row lengths `l` of the shape of `ν`.
  set l := (diagramOf ν).rowLens with hl
  have hl_apply (i : Fin l.length) : rowLenWeight l.length (diagramOf ν) i = l[i.1] := by
    rw [rowLenWeight_apply, ← YoungDiagram.getD_rowLens]
    exact List.getD_eq_getElem l 0 i.2
  have hdeg : (rowLenWeight l.length (diagramOf ν)).degree = n := by
    rw [Finsupp.degree_eq_sum]
    simp only [hl_apply]
    refine (Fin.sum_univ_fun_getElem l id).trans ?_
    rw [List.map_id, hl, YoungDiagram.sum_rowLens_eq_card, card_diagramOf]
  have hprod : hsymmPart σ R ν = ∏ i, hsymm σ R (rowLenWeight l.length (diagramOf ν) i) := by
    simp only [hl_apply]
    rw [Fin.prod_univ_fun_getElem, hsymmPart, hl, rowLens_diagramOf, ← Multiset.prod_coe,
      ← Multiset.map_coe, Multiset.sort_eq]
  rw [hprod, prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly _ hdeg,
    mapDomain_rowLenWeight (by rw [hl, YoungDiagram.length_rowLens])]
  simp only [kostkaNumber_def]

/-- **The coefficients of `h_ν` are sums of products of Kostka numbers**: the coefficient of `h_ν`
at an arbitrary exponent `d` is `∑_μ K_{μν} K_{μd}`, where `K_{μd}` is the Kostka number of the
shape of `μ` and the content obtained from `d` by numbering the alphabet with `Fintype.equivFin`,
as in `TauCeti.coeff_schurPoly`. -/
theorem coeff_hsymmPart {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ} (ν : n.Partition)
    (d : σ →₀ ℕ) :
    (hsymmPart σ R ν).coeff d =
      ∑ μ : n.Partition, (kostkaNumber μ ν * diagramKostkaNumber (diagramOf μ)
        (Finsupp.mapDomain (fun x => (Fintype.equivFin σ x : ℕ)) d) : R) := by
  rw [hsymmPart_eq_sum_kostkaNumber_smul_schurPoly, coeff_sum]
  exact sum_congr rfl fun μ _ => by rw [coeff_smul, coeff_schurPoly, smul_eq_mul]

/-- **The coefficients of `h_ν` at partitions**: the coefficient of the monomial recording the parts
of `ξ` in `h_ν` is `∑_μ K_{μν} K_{μξ}`.  The row bound is what makes the monomial record all of
`ξ`, as in `TauCeti.coeff_schurPoly_partWeight`. -/
theorem coeff_hsymmPart_partWeight {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
    (ν ξ : n.Partition) (h : (diagramOf ξ).colLen 0 ≤ Fintype.card σ) :
    (hsymmPart σ R ν).coeff (partWeight σ ξ) =
      ∑ μ : n.Partition, (kostkaNumber μ ν * kostkaNumber μ ξ : R) := by
  rw [coeff_hsymmPart]
  exact sum_congr rfl fun μ _ => by
    rw [← coeff_schurPoly (R := R) μ, coeff_schurPoly_partWeight μ ξ h]

end TauCeti
