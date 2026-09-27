/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.VerticalStrip
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# The dual Pieri rule for Schur polynomials

Multiplying a Schur polynomial by an elementary symmetric polynomial adds vertical strips: for
every `r`,

`e_r · s_ν = ∑_μ s_μ`,

the sum running over the diagrams `μ` for which `μ / ν` is a vertical strip with `r` cells, that is
over the ways of lengthening `r` distinct rows of `ν` by one cell each.  This is
`TauCeti.esymm_mul_diagramSchurPoly` for Young diagrams in the alphabet `Fin N`, and
`TauCeti.esymm_mul_schurPoly` for partitions in an arbitrary finite alphabet.  It is the `e`-half
of the Pieri rule, dual to the `h`-half that adds horizontal strips; unlike the Murnaghan-Nakayama
rule for power sums, every term carries the sign `+1`.

## The route

The whole computation happens on alternants.  `TauCeti.esymm_mul_alternant` says that multiplying
`a_α` by `e_r` raises by one each of the exponents indexed by an `r`-element set `T`, and taking
`α` to be the beta-numbers `β_j = ν_j + (N - 1 - j)` of `ν` makes those shifts visible as shapes:
because `β` is *strictly* decreasing, an indicator shift of it either repeats an exponent — and the
alternant vanishes — or is again strictly decreasing, in which case the shifted row lengths
`ν_j + 1_T(j)` are still weakly decreasing and so are the row lengths of a Young diagram `μ`.  No
sorting is needed and no sign appears, which is exactly what distinguishes the `e`-half of the Pieri
rule from the `h`-half.

## Main statements

* `TauCeti.esymm_mul_alternant_betaNumber`: the dual Pieri rule for alternants of beta-numbers.
* `TauCeti.esymm_mul_diagramSchurPoly`: the dual Pieri rule for the Schur polynomial of a Young
  diagram.
* `TauCeti.esymm_mul_schurPoly`: the dual Pieri rule for the Schur polynomial of a partition in a
  finite alphabet.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, Example 3 (the two Pieri rules).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.15.7.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7, and the [classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 4, which name the Pieri rule among the Schur-polynomial identities.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **An injective indicator shift of the beta-numbers is a shape.**  The beta-numbers of `ν`
relative to `N` strictly decrease, so raising by one those indexed by a set `T` leaves them pairwise
distinct only if the shifted row lengths `ν_j + 1_T(j)` are still weakly decreasing: two adjacent
beta-numbers differ, and the indicator can move them by at most the single step that separates them.
Only this direction is needed, the remaining sets contributing a vanishing alternant. -/
private theorem antitone_rowLen_add_ite_of_injective {N : ℕ} {ν : YoungDiagram}
    {T : Finset (Fin N)}
    (hinj : Function.Injective fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0) :
    Antitone fun j : Fin N => ν.rowLen j + if j ∈ T then 1 else 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact fun a _ _ => absurd a.isLt (Nat.not_lt_zero _)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Fin.antitone_iff_succ_le]
  intro i
  -- Two adjacent beta-numbers are distinct, and the shift by an indicator moves them by at most
  -- the one step that separates them, so the row lengths cannot increase.
  have hne : (Fin.castSucc i) ≠ i.succ := fun h => by simpa using congrArg Fin.val h
  have hfne : ν.betaNumber (n + 1) (Fin.castSucc i) + (if Fin.castSucc i ∈ T then 1 else 0) ≠
      ν.betaNumber (n + 1) i.succ + (if i.succ ∈ T then 1 else 0) := fun h => hne (hinj h)
  have hrow : ν.rowLen ((i.succ : Fin (n + 1)) : ℕ) ≤
      ν.rowLen ((Fin.castSucc i : Fin (n + 1)) : ℕ) := ν.rowLen_anti _ _ (by simp)
  have hlt : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n + 1 := (Fin.castSucc i).isLt
  rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def] at hfne
  simp only [Fin.val_succ, Fin.val_castSucc] at hfne hrow hlt ⊢
  split_ifs at hfne ⊢ <;> omega

open scoped Classical in
/-- **The dual Pieri rule for alternants.**  Let `ν` be a Young diagram with at most `N` rows and
`β` its beta-numbers relative to `N`, so that `a_β = s_ν · a_δ`.  Multiplying `a_β` by the
elementary symmetric polynomial `e_r` gives the sum of the alternants of the beta-numbers of the
diagrams `μ` with at most `N` rows for which `μ / ν` is a vertical strip with `r` cells, each
occurring once and with coefficient `+1`. -/
theorem esymm_mul_alternant_betaNumber {N : ℕ} (ν : YoungDiagram) (hν : ν.colLen 0 ≤ N) (r : ℕ) :
    esymm (Fin N) R r * alternant (Fin N) R (fun j => ν.betaNumber N j) =
      ∑ μ : (ν.card + r).Partition with
          (diagramOf μ).IsVerticalStrip ν ∧ (diagramOf μ).colLen 0 ≤ N,
        alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N j) := by
  rw [esymm_mul_alternant]
  -- Discard the sets of rows whose shifted beta-numbers repeat: those alternants vanish.
  rw [← sum_filter_of_ne (p := fun T : Finset (Fin N) =>
      Function.Injective fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0)
    fun T _ hT => by
      by_contra hcon
      exact hT (alternant_eq_zero_of_not_injective hcon)]
  -- Every remaining set of rows lengthens `ν` to a vertical strip inside `N` rows.
  have hex : ∀ T : Finset (Fin N), T.card = r →
      (Function.Injective fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0) →
      ∃ μ : (ν.card + r).Partition,
        ((diagramOf μ).IsVerticalStrip ν ∧ (diagramOf μ).colLen 0 ≤ N) ∧
          ∀ j : Fin N, (diagramOf μ).rowLen j = ν.rowLen j + if j ∈ T then 1 else 0 := by
    intro T hcard hinj
    have hanti := antitone_rowLen_add_ite_of_injective hinj
    refine ⟨toPartition (YoungDiagram.ofRowLensFin _ hanti)
      (by rw [YoungDiagram.card_ofRowLensFin_add_ite hanti hν, hcard]), ?_, ?_⟩
    · rw [diagramOf_toPartition]
      exact ⟨YoungDiagram.isVerticalStrip_ofRowLensFin hanti hν,
        YoungDiagram.colLen_zero_ofRowLensFin_le _ hanti⟩
    · intro j
      rw [diagramOf_toPartition, YoungDiagram.rowLen_ofRowLensFin]
  choose! f hfS hfrow using hex
  refine sum_bij (fun T _ => f T) (fun T hT => mem_filter.mpr ⟨mem_univ _,
      hfS T (mem_powersetCard_univ.mp (mem_filter.mp hT).1) (mem_filter.mp hT).2⟩) ?_ ?_ ?_
  · -- The set of lengthened rows is read back off the row lengths.
    intro T₁ hT₁ T₂ hT₂ hf
    have h₁ := hfrow T₁ (mem_powersetCard_univ.mp (mem_filter.mp hT₁).1) (mem_filter.mp hT₁).2
    have h₂ := hfrow T₂ (mem_powersetCard_univ.mp (mem_filter.mp hT₂).1) (mem_filter.mp hT₂).2
    refine Finset.ext fun j => ?_
    have hval : ν.rowLen (j : ℕ) + (if j ∈ T₁ then 1 else 0)
        = ν.rowLen (j : ℕ) + (if j ∈ T₂ then 1 else 0) := by rw [← h₁ j, ← h₂ j, hf]
    by_cases hj₁ : j ∈ T₁ <;> by_cases hj₂ : j ∈ T₂ <;> simp_all
  · -- Every vertical strip inside `N` rows lengthens the rows on which it is longer.
    intro μ hμ
    obtain ⟨hstrip, hμN⟩ := (mem_filter.mp hμ).2
    set T := YoungDiagram.lengthenedRows N (diagramOf μ) ν with hT
    have hrow : ∀ j : Fin N, (diagramOf μ).rowLen j = ν.rowLen j + if j ∈ T then 1 else 0 := by
      intro j
      rw [hT]
      simp only [YoungDiagram.mem_lengthenedRows]
      exact hstrip.rowLen_eq_add_ite _
    have hcard : T.card = r := by
      have h2 := hstrip.card_lengthenedRows (N := N) hμN hν
      rw [card_diagramOf, ← hT] at h2
      omega
    have hinj : Function.Injective
        fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0 := by
      intro a b hab
      have hab' : ν.betaNumber N a + (if a ∈ T then 1 else 0) =
          ν.betaNumber N b + (if b ∈ T then 1 else 0) := hab
      refine Fin.ext (YoungDiagram.injOn_betaNumber (diagramOf μ) N a.isLt b.isLt ?_)
      rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def, hrow a, hrow b]
      rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def] at hab'
      split_ifs at hab' ⊢ <;> omega
    refine ⟨T, mem_filter.mpr ⟨mem_powersetCard_univ.mpr hcard, hinj⟩, ?_⟩
    refine diagramOf_injective (YoungDiagram.eq_of_betaNumber_eq (hfS T hcard hinj).2 hμN
      fun i hi => ?_)
    rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def,
      show i = ((⟨i, hi⟩ : Fin N) : ℕ) from rfl, hfrow T hcard hinj, hrow ⟨i, hi⟩]
  · intro T hT
    refine congrArg _ (funext fun j => ?_)
    rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def,
      hfrow T (mem_powersetCard_univ.mp (mem_filter.mp hT).1) (mem_filter.mp hT).2 j,
      Nat.add_right_comm]

open scoped Classical in
/-- **The dual Pieri rule for Schur polynomials.**  Multiplying the Schur polynomial of a Young
diagram `ν` in the alphabet `Fin N` by the elementary symmetric polynomial `e_r` gives the sum of
the Schur polynomials of the diagrams `μ` for which `μ / ν` is a vertical strip with `r` cells:
`e_r · s_ν = ∑_μ s_μ`.  No bound on the number of rows is needed: the Schur polynomials of the
diagrams with more than `N` rows vanish on both sides. -/
theorem esymm_mul_diagramSchurPoly {N : ℕ} (ν : YoungDiagram) (r : ℕ) :
    esymm (Fin N) R r * diagramSchurPoly N R ν =
      ∑ μ : (ν.card + r).Partition with (diagramOf μ).IsVerticalStrip ν,
        diagramSchurPoly N R (diagramOf μ) := by
  -- Prove the identity over `ℤ`, where the nonzero Vandermonde alternant `a_δ` can be
  -- cancelled in `ℤ[x]`, then map its integer coefficients to the target commutative ring.
  suffices hℤ : esymm (Fin N) ℤ r * diagramSchurPoly N ℤ ν =
      ∑ μ : (ν.card + r).Partition with (diagramOf μ).IsVerticalStrip ν,
        diagramSchurPoly N ℤ (diagramOf μ) by
    have h := congrArg (MvPolynomial.map (Int.castRingHom R)) hℤ
    simpa [map_diagramSchurPoly, esymm, map_sum] using h
  by_cases hν : ν.colLen 0 ≤ N
  · -- Cancel the staircase alternant, whose exponents are pairwise distinct.
    have hδ : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) := fun i j h => by
      have := i.isLt
      have := j.isLt
      exact Fin.ext (by simp only at h; omega)
    refine mul_right_cancel₀ (alternant_ne_zero_of_injective hδ) ?_
    rw [mul_assoc, diagramSchurPoly_mul_alternant N ν hν,
      esymm_mul_alternant_betaNumber ν hν r, sum_mul, ← filter_filter, sum_filter]
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
    rw [diagramSchurPoly_eq_zero_of_lt_colLen hμN]

open scoped Classical in
/-- **The dual Pieri rule for Schur polynomials of partitions.**  In a finite alphabet `σ`, for a
partition `ν` of `n` and every `r`,
`e_r · s_ν = ∑_μ s_μ`,
the sum running over the partitions `μ` of `n + r` whose Young diagram contains that of `ν` with a
vertical strip as complement. -/
theorem esymm_mul_schurPoly {σ : Type*} [Fintype σ] {n : ℕ} (ν : n.Partition) (r : ℕ) :
    esymm σ R r * schurPoly σ R ν =
      ∑ μ : (n + r).Partition with (diagramOf μ).IsVerticalStrip (diagramOf ν),
        schurPoly σ R μ := by
  have h := esymm_mul_diagramSchurPoly (R := R) (N := Fintype.card σ) (diagramOf ν) r
  rw [card_diagramOf] at h
  have h' := congrArg (rename (Fintype.equivFin σ).symm) h
  rw [map_mul, rename_esymm, ← schurPoly_eq_rename] at h'
  rw [h', map_sum]
  exact sum_congr rfl fun μ _ => (schurPoly_eq_rename μ).symm

end TauCeti
