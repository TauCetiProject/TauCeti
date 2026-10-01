/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.GroupTheory.Perm.SignedDomination
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import TauCeti.Data.Fin.StrictAnti

/-!
# The Pieri rule for Schur polynomials

Multiplying a Schur polynomial by a complete homogeneous symmetric polynomial adds horizontal
strips: for every `r`,

`h_r · s_ν = ∑_μ s_μ`,

the sum running over the diagrams `μ` with `ν.card + r` cells whose row lengths **interlace** those
of `ν`, `μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`, equivalently over the `μ ⊇ ν` whose skew shape `μ / ν` has at most
one cell in each column.  Every term carries the coefficient `1`.  This is
`TauCeti.hsymm_mul_diagramSchurPoly` for Young diagrams in the alphabet `Fin N`, and
`TauCeti.hsymm_mul_schurPoly` for partitions in an arbitrary finite alphabet.

Iterating the rule from `s_∅ = 1` along the parts of a partition `ν` expands the product
`h_{ν₁} ⋯ h_{ν_k}` in Schur polynomials with the Kostka numbers as coefficients, which is the
symmetric-function half of Young's rule for the permutation modules of the symmetric groups.

## The cancellation

The computation happens on alternants.  `TauCeti.hsymm_mul_alternant` expands `h_r · a_α` as the sum
of `a_{α + γ}` over the exponent vectors `γ` of total degree `r`.  Taking `α` to be the beta-numbers
`β_j = ν_j + (N - 1 - j)` of `ν`, the shifted vectors `β + γ` are no longer decreasing, so each must
be sorted back (`TauCeti.exists_strictAnti_comp`, uniquely by `TauCeti.eq_of_strictAnti_comp`) at
the cost of the sign of the sorting permutation; a strictly decreasing result is again a vector of
beta-numbers (`YoungDiagram.exists_eq_betaNumber_of_strictAnti`), and a repeated exponent kills the
alternant.  Grouping the shifts by the shape they sort to leaves, for each shape `μ`, the signed
count of the permutations `τ` with `β_j ≤ β(μ)_{τ j}` for all `j`.  That count is `1` exactly when
the comparisons cut out the initial segments, which is interlacing, and `0` otherwise
(`TauCeti.sum_sign_filter_forall_le_of_strictAnti`).  Both the sorting and the cancellation are
genuinely needed: a shift of total degree `r` is an arbitrary exponent vector, so the shifted
beta-numbers are in general neither distinct nor decreasing.

## Main statements

* `TauCeti.forall_betaNumber_le_iff_interlacedBy`: the comparisons of beta-numbers that cut out
  initial segments are exactly interlacing.
* `TauCeti.hsymm_mul_alternant_betaNumber`: the Pieri rule for alternants of beta-numbers.
* `TauCeti.hsymm_mul_diagramSchurPoly`: the Pieri rule for the Schur polynomial of a Young diagram.
* `TauCeti.hsymm_mul_schurPoly`: the Pieri rule for the Schur polynomial of a partition in a finite
  alphabet.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5 (Pieri's formula).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Section 7.15 (Pieri's rule).
-/

public section

open MvPolynomial Finset

namespace TauCeti

/-- **Interlacing, read on beta-numbers.**  For diagrams `μ` and `ν` with at most `N` rows, the
beta-number of `ν` at `j` is at most the beta-number of `μ` at `i` exactly for `i ≤ j` precisely
when the row lengths interlace, `μ₀ ≥ ν₀ ≥ μ₁ ≥ ⋯`, that is, when `μ / ν` is a horizontal strip. -/
theorem forall_betaNumber_le_iff_interlacedBy {N : ℕ} {μ ν : YoungDiagram}
    (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) :
    (∀ i j : Fin N, ν.betaNumber N j ≤ μ.betaNumber N i ↔ i ≤ j) ↔
      μ.InterlacedBy ν := by
  simp only [YoungDiagram.betaNumber_def, YoungDiagram.interlacedBy_iff]
  constructor
  · intro h i
    have h' : ∀ a b : ℕ, a < N → b < N →
        (ν.rowLen b + (N - 1 - b) ≤ μ.rowLen a + (N - 1 - a) ↔ a ≤ b) := by
      intro a b ha hb
      simpa [Fin.le_def] using h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨?_, ?_⟩
    · by_cases hi : i + 1 < N
      · have hlt := ((h' (i + 1) i hi (by omega)).not).mpr (by omega)
        omega
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (by omega))]
        exact Nat.zero_le _
    · by_cases hi : i < N
      · have := (h' i i hi hi).mpr le_rfl
        omega
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hν.trans (by omega))]
        exact Nat.zero_le _
  · intro h i j
    rw [Fin.le_def]
    have hiN : (i : ℕ) < N := i.isLt
    have hjN : (j : ℕ) < N := j.isLt
    refine ⟨fun hle => ?_, fun hle => ?_⟩
    · by_contra hij
      have hij' : (j : ℕ) < (i : ℕ) := by omega
      have h1 : μ.rowLen i ≤ μ.rowLen ((j : ℕ) + 1) := μ.rowLen_anti _ _ (by omega)
      have h2 : μ.rowLen ((j : ℕ) + 1) ≤ ν.rowLen j := (h j).1
      omega
    · have h1 : ν.rowLen j ≤ μ.rowLen j := (h j).2
      have h2 : μ.rowLen j ≤ μ.rowLen i := μ.rowLen_anti _ _ hle
      omega

section Alternant

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- **The Pieri rule for alternants of beta-numbers.**  Let `ν` be a Young diagram with at most `N`
rows and `β` its beta-numbers relative to `N`, so that `a_β = s_ν · a_δ`.  Multiplying `a_β` by the
complete homogeneous symmetric polynomial `h_r` gives the sum, with no signs, of the alternants of
the beta-numbers of the diagrams `μ` with at most `N` rows obtained from `ν` by adding a horizontal
strip of `r` cells. -/
theorem hsymm_mul_alternant_betaNumber {N : ℕ} (ν : YoungDiagram) (hν : ν.colLen 0 ≤ N) (r : ℕ) :
    hsymm (Fin N) R r * alternant (Fin N) R (fun j => ν.betaNumber N j) =
      ∑ μ : (ν.card + r).Partition with
          ((diagramOf μ).InterlacedBy ν ∧ (diagramOf μ).colLen 0 ≤ N),
        alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N j) := by
  -- The proof runs in four steps.  The complete-homogeneous rule for alternants expands the
  -- left-hand side as a sum over the shifts `γ` of total degree `r`.  The shifts that repeat an
  -- exponent are discarded, their alternants vanishing.  The remaining ones are then put in
  -- bijection (`hbij`) with the pairs of a shape `μ` and a permutation `τ` carrying the
  -- beta-numbers of `ν` below those of `μ`: the shape and the permutation are the data of sorting
  -- `β + γ` back into decreasing order.  Summing over `τ` first leaves, for each shape, the signed
  -- count of those permutations, which is `1` exactly on the shapes that interlace `ν`.
  classical
  set β : Fin N → ℕ := fun j => ν.betaNumber N j with hβ
  have hβanti : StrictAnti β := ν.strictAnti_betaNumber N
  have hβsum : ∑ i : Fin N, β i = ν.card + ∑ j : Fin N, (N - 1 - (j : ℕ)) := ν.sum_betaNumber hν
  rw [hsymm_mul_alternant]
  -- A shift producing a repeated exponent kills the alternant.
  rw [← Finset.sum_filter_of_ne
    (p := fun γ : Fin N → ℕ => Function.Injective fun i => β i + γ i) fun γ _ hγ => by
      by_contra hninj
      exact hγ (alternant_eq_zero_of_not_injective hninj)]
  -- Sorting the surviving shifts pairs them with a shape and a dominating permutation.
  set P : Finset (ν.card + r).Partition :=
    {μ | (diagramOf μ).colLen 0 ≤ N} with hP
  set T : (ν.card + r).Partition → Finset (Equiv.Perm (Fin N)) :=
    fun μ => {τ | ∀ j, β j ≤ (diagramOf μ).betaNumber N (τ j)} with hT
  have hval : ∀ x ∈ P.sigma T, ∀ i,
      β i + ((diagramOf x.1).betaNumber N (x.2 i) - β i) =
        (diagramOf x.1).betaNumber N (x.2 i) := by
    intro x hx i
    have hdom := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
    have := hdom i
    omega
  have hfun : ∀ x ∈ P.sigma T,
      (fun i => β i + ((diagramOf x.1).betaNumber N (x.2 i) - β i)) =
        (fun j : Fin N => (diagramOf x.1).betaNumber N j) ∘ ⇑x.2 :=
    fun x hx => funext fun i => hval x hx i
  have hbij : ∑ x ∈ P.sigma T,
        alternant (Fin N) R (fun j => (diagramOf x.1).betaNumber N (x.2 j)) =
      ∑ γ ∈ {γ ∈ Finset.piAntidiag (univ : Finset (Fin N)) r |
          Function.Injective fun i => β i + γ i},
        alternant (Fin N) R (fun i => β i + γ i) := by
    refine Finset.sum_bij
      (fun x _ => fun i => (diagramOf x.1).betaNumber N (x.2 i) - β i) ?_ ?_ ?_ ?_
    · -- The shift has total degree `r` and no repeated exponent.
      intro x hx
      have hcol : (diagramOf x.1).colLen 0 ≤ N :=
        (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_piAntidiag.mpr ⟨?_, fun i _ => Finset.mem_univ i⟩, ?_⟩
      · have hsum1 : ∑ i : Fin N, (β i + ((diagramOf x.1).betaNumber N (x.2 i) - β i)) =
            ∑ j : Fin N, (diagramOf x.1).betaNumber N j := by
          rw [Finset.sum_congr rfl fun i _ => hval x hx i]
          exact Equiv.sum_comp x.2 fun j : Fin N => (diagramOf x.1).betaNumber N j
        rw [Finset.sum_add_distrib, hβsum, (diagramOf x.1).sum_betaNumber hcol,
          card_diagramOf] at hsum1
        omega
      · rw [hfun x hx]
        exact ((diagramOf x.1).strictAnti_betaNumber N).injective.comp x.2.injective
    · -- Distinct pairs give distinct shifts: the shape and the permutation are the sorting data.
      intro x hx y hy hxy
      have hxy' : (fun i => β i + ((diagramOf x.1).betaNumber N (x.2 i) - β i)) =
          (fun i => β i + ((diagramOf y.1).betaNumber N (y.2 i) - β i)) :=
        funext fun i => by rw [congrFun hxy i]
      have hsx : StrictAnti ((fun i => β i + ((diagramOf y.1).betaNumber N (y.2 i) - β i)) ∘
          ⇑(x.2).symm) := by
        rw [← hxy', hfun x hx]
        simpa [Function.comp_def] using (diagramOf x.1).strictAnti_betaNumber N
      have hsy : StrictAnti ((fun i => β i + ((diagramOf y.1).betaNumber N (y.2 i) - β i)) ∘
          ⇑(y.2).symm) := by
        rw [hfun y hy]
        simpa [Function.comp_def] using (diagramOf y.1).strictAnti_betaNumber N
      have hp : x.2 = y.2 := by
        simpa using congrArg Equiv.symm (eq_of_strictAnti_comp hsx hsy)
      have hbx : ∀ i, (diagramOf x.1).betaNumber N (x.2 i) =
          (diagramOf y.1).betaNumber N (y.2 i) := fun i => by
        have h1 := hval x hx i
        have h2 := hval y hy i
        have h3 := congrFun hxy i
        omega
      have hbeta : ∀ j : Fin N,
          (diagramOf x.1).betaNumber N j = (diagramOf y.1).betaNumber N j := fun j => by
        have h := hbx ((x.2).symm j)
        rw [← hp] at h
        simpa using h
      have hshape : diagramOf x.1 = diagramOf y.1 :=
        YoungDiagram.eq_of_betaNumber_eq (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).1).2
          fun i hi => hbeta ⟨i, hi⟩
      exact Sigma.ext (diagramOf_injective hshape) (by rw [hp])
    · -- Every shift of total degree `r` with distinct exponents sorts to such a pair.
      intro γ hγ
      obtain ⟨hγmem, hγinj⟩ := Finset.mem_filter.mp hγ
      obtain ⟨τ₀, hτ₀⟩ := exists_strictAnti_comp hγinj
      obtain ⟨μ₀, hμ₀col, hμ₀beta⟩ := YoungDiagram.exists_eq_betaNumber_of_strictAnti hτ₀
      have hsumγ : ∑ i : Fin N, γ i = r := (Finset.mem_piAntidiag.mp hγmem).1
      have hcard : μ₀.card = ν.card + r := by
        have h1 : ∑ j : Fin N, μ₀.betaNumber N j = ∑ i : Fin N, (β i + γ i) := by
          rw [Finset.sum_congr rfl fun j _ => hμ₀beta j]
          exact Equiv.sum_comp τ₀ fun i : Fin N => β i + γ i
        rw [μ₀.sum_betaNumber hμ₀col, Finset.sum_add_distrib, hβsum, hsumγ] at h1
        omega
      refine ⟨⟨toPartition μ₀ hcard, τ₀.symm⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [diagramOf_toPartition]⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
        rw [diagramOf_toPartition, hμ₀beta]
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        exact Nat.le_add_right _ _
      · refine funext fun i => ?_
        rw [diagramOf_toPartition, hμ₀beta]
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        omega
    · intro x hx
      exact congrArg (alternant (Fin N) R) (funext fun i => (hval x hx i).symm)
  rw [← hbij, Finset.sum_sigma]
  -- The permutations dominating a given shape contribute their signed count.
  have hterm : ∀ μ ∈ P,
      ∑ τ ∈ T μ, alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N (τ j)) =
        if (diagramOf μ).InterlacedBy ν then
          alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N j) else 0 := by
    intro μ hμ
    have hcol : (diagramOf μ).colLen 0 ≤ N := (Finset.mem_filter.mp hμ).2
    have hstep : ∀ τ : Equiv.Perm (Fin N),
        alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N (τ j)) =
          (Equiv.Perm.sign τ : ℤ) •
            alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N j) := by
      intro τ
      -- The two sides differ only by folding the composition that `alternant_comp_perm` matches.
      have hcomp : (fun j : Fin N => (diagramOf μ).betaNumber N (τ j)) =
          (fun j : Fin N => (diagramOf μ).betaNumber N j) ∘ ⇑τ := rfl
      rw [hcomp, alternant_comp_perm]
      simp [Units.smul_def]
    rw [hT, Finset.sum_congr rfl fun τ _ => hstep τ, ← Finset.sum_smul,
      sum_sign_filter_forall_le_of_strictAnti hβanti ((diagramOf μ).strictAnti_betaNumber N)]
    -- `hβ` unfolds the abbreviation so that the beta-number criterion applies to the condition.
    simp only [hβ, forall_betaNumber_le_iff_interlacedBy hcol hν]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, hP, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun μ _ => ?_) fun _ _ => rfl
  exact and_comm

end Alternant

variable {R : Type*} [CommSemiring R]

open scoped Classical in
/-- **The Pieri rule for Schur polynomials.**  Multiplying the Schur polynomial of a Young diagram
`ν` in the alphabet `Fin N` by the complete homogeneous symmetric polynomial `h_r` gives the sum of
the Schur polynomials of the diagrams `μ` obtained from `ν` by adding a horizontal strip of `r`
cells, each with coefficient `1`: `h_r · s_ν = ∑_μ s_μ`.  No bound on the number of rows is needed:
the Schur polynomials of the diagrams with more than `N` rows vanish on both sides.  Nor is `r`
required to be positive: at `r = 0` the only strip is empty and the sum is the single term `s_ν`. -/
theorem hsymm_mul_diagramSchurPoly {N : ℕ} (ν : YoungDiagram) (r : ℕ) :
    hsymm (Fin N) R r * diagramSchurPoly N R ν =
      ∑ μ : (ν.card + r).Partition with (diagramOf μ).InterlacedBy ν,
        diagramSchurPoly N R (diagramOf μ) := by
  -- Prove the identity over `ℤ`, where the nonzero Vandermonde alternant `a_δ` can be
  -- cancelled in `ℤ[x]`.  Both sides have natural-number coefficients, so the identity descends
  -- along the injection `ℕ → ℤ`, and the resulting identity over `ℕ` maps to any commutative
  -- semiring.
  suffices hℤ : hsymm (Fin N) ℤ r * diagramSchurPoly N ℤ ν =
      ∑ μ : (ν.card + r).Partition with (diagramOf μ).InterlacedBy ν,
        diagramSchurPoly N ℤ (diagramOf μ) by
    have hℕ : hsymm (Fin N) ℕ r * diagramSchurPoly N ℕ ν =
        ∑ μ : (ν.card + r).Partition with (diagramOf μ).InterlacedBy ν,
          diagramSchurPoly N ℕ (diagramOf μ) :=
      MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective <| by
        simpa [map_diagramSchurPoly, map_hsymm, map_sum] using hℤ
    have h := congrArg (MvPolynomial.map (Nat.castRingHom R)) hℕ
    simpa [map_diagramSchurPoly, map_hsymm, map_sum] using h
  by_cases hν : ν.colLen 0 ≤ N
  · -- Cancel the staircase alternant, whose exponents are pairwise distinct.
    have hδ : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) := fun i j h => by
      have := i.isLt
      have := j.isLt
      exact Fin.ext (by simp only at h; omega)
    refine mul_right_cancel₀ (alternant_ne_zero_of_injective hδ) ?_
    rw [mul_assoc, diagramSchurPoly_mul_alternant N ν hν,
      hsymm_mul_alternant_betaNumber ν hν r, sum_mul, ← filter_filter, sum_filter]
    refine sum_congr rfl fun μ _ => ?_
    split_ifs with hμ
    · rw [diagramSchurPoly_mul_alternant N _ hμ]
    · rw [diagramSchurPoly_eq_zero_of_lt_colLen (Nat.lt_of_not_le hμ), zero_mul]
  · -- Both sides vanish: `ν` and every diagram containing it have more than `N` rows.
    have hν' : N < ν.colLen 0 := Nat.lt_of_not_le hν
    rw [diagramSchurPoly_eq_zero_of_lt_colLen hν', mul_zero]
    refine (sum_eq_zero fun μ hμ => ?_).symm
    have hle := ((mem_filter.mp hμ).2).le
    have hN : ν.rowLen N ≠ 0 := by
      intro h0
      have : (N, 0) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr hν'
      rw [YoungDiagram.mem_iff_lt_rowLen, h0] at this
      omega
    have hμN : N < (diagramOf μ).colLen 0 := by
      by_contra h
      exact hN (Nat.eq_zero_of_le_zero ((YoungDiagram.rowLen_le_of_le hle N).trans
        (YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.not_lt.mp h)).le))
    exact diagramSchurPoly_eq_zero_of_lt_colLen hμN

open scoped Classical in
/-- **The Pieri rule for Schur polynomials of partitions.**  In a finite alphabet `σ`, for a
partition `ν` of `n`, `h_r · s_ν = ∑_μ s_μ`, the sum running over the partitions `μ` of `n + r`
whose Young diagram contains that of `ν` with a horizontal strip as complement. -/
theorem hsymm_mul_schurPoly {σ : Type*} [Fintype σ] {n : ℕ} (ν : n.Partition) (r : ℕ) :
    hsymm σ R r * schurPoly σ R ν =
      ∑ μ : (n + r).Partition with (diagramOf μ).InterlacedBy (diagramOf ν),
        schurPoly σ R μ := by
  have h := hsymm_mul_diagramSchurPoly (R := R) (N := Fintype.card σ) (diagramOf ν) r
  rw [card_diagramOf] at h
  have h' := congrArg (rename (Fintype.equivFin σ).symm) h
  rw [map_mul, rename_hsymm, ← schurPoly_eq_rename] at h'
  rw [h', map_sum]
  exact sum_congr rfl fun μ _ => (schurPoly_eq_rename μ).symm

end TauCeti
