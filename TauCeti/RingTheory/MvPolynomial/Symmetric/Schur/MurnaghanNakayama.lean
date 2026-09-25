/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.RimHook
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# The Murnaghan–Nakayama rule for Schur polynomials

Multiplying a Schur polynomial by a power sum adds rim hooks: for `r > 0`,

`p_r · s_ν = ∑_μ (-1) ^ ht(μ / ν) · s_μ`,

the sum running over the diagrams `μ` for which `μ / ν` is a rim hook with `r` cells, and
`ht(μ / ν)`, one less than the number of rows the hook meets, being its height.  This is
`TauCeti.psum_mul_diagramSchurPoly` for Young diagrams in the alphabet `Fin N`, and
`TauCeti.psum_mul_schurPoly` for partitions in an arbitrary finite alphabet.  Iterating it from
`s_∅ = 1` along the parts of a partition `ρ` expands the power-sum product `p_ρ` in Schur
polynomials; that expansion is the combinatorial half of the Murnaghan–Nakayama rule for the
characters of the symmetric groups, whose other half is Frobenius's formula identifying the
coefficients with character values.

## The route

Everything happens on alternants.  By the power-sum rule `TauCeti.psum_mul_alternant`,

`p_r · a_β = ∑_j a_{β + r e_j}`,

where `β` is the family of beta-numbers of `ν` relative to `N`, so that `a_β = s_ν · a_δ` is
Jacobi's bialternant.  A term in which the raised bead lands on an occupied position has a
repeated exponent and vanishes.  Every other term is a rim hook: by
`YoungDiagram.exists_isRimHook_rimHookRows_eq_Icc` the bead moved from row `j` lands at a row `a`
such that `μ / ν` is a rim hook with `r` cells meeting the rows `a ≤ i ≤ j`, and by
`YoungDiagram.IsRimHook.update_betaNumber_eq_comp_cycleIcc` the exponents `β + r e_j` are the
beta-numbers of `μ` rearranged by the cycle `(a a+1 ⋯ j)`, of sign `(-1) ^ (j - a)`, which is
the height.  Conversely a rim hook is recovered from its bottom row
(`YoungDiagram.IsRimHook.eq_of_rimHookRows_eq_Icc`), so the surviving terms are indexed by the
rim hooks exactly once.  This is `TauCeti.psum_mul_alternant_betaNumber`.

Dividing by the Vandermonde alternant `a_δ` turns the alternant identity into the Schur one.  Over
`ℤ` the alternant `a_δ` is nonzero (`TauCeti.alternant_ne_zero_of_injective`) and `ℤ[x]` is a
domain, so it can be cancelled; the identity
over an arbitrary commutative ring is its image under `ℤ → R`, Schur polynomials and power sums
having integer coefficients.

## Main statements

* `TauCeti.psum_mul_alternant_betaNumber`: the Murnaghan–Nakayama rule for alternants of
  beta-numbers.
* `TauCeti.psum_mul_diagramSchurPoly`: the Murnaghan–Nakayama rule for the Schur polynomial of a
  Young diagram.
* `TauCeti.psum_mul_schurPoly`: the Murnaghan–Nakayama rule for the Schur polynomial of a
  partition in a finite alphabet.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, Example 11.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.17.1.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- **The Murnaghan–Nakayama rule for alternants.**  Let `ν` be a Young diagram with at most `N`
rows and `β` its beta-numbers relative to `N`, so that `a_β = s_ν · a_δ`.  For `r > 0`, multiplying
`a_β` by the power sum `p_r` gives the signed sum of the alternants of the beta-numbers of the
diagrams `μ` with at most `N` rows for which `μ / ν` is a rim hook with `r` cells, each weighted
by `(-1)` to the height of its rim hook. -/
theorem psum_mul_alternant_betaNumber {N : ℕ} (ν : YoungDiagram) (hν : ν.colLen 0 ≤ N) {r : ℕ}
    (hr : 0 < r) :
    psum (Fin N) R r * alternant (Fin N) R (fun j => ν.betaNumber N j) =
      ∑ μ : (ν.card + r).Partition with
          (diagramOf μ).IsRimHook ν ∧ (diagramOf μ).colLen 0 ≤ N,
        (-1) ^ (diagramOf μ).rimHookHeight ν *
          alternant (Fin N) R (fun j => (diagramOf μ).betaNumber N j) := by
  set β : Fin N → ℕ := fun j => ν.betaNumber N j with hβ
  rw [psum_mul_alternant]
  -- A bead raised onto an occupied position repeats an exponent, and its alternant vanishes.
  rw [← sum_filter_of_ne (p := fun j => ∀ i, β i ≠ β j + r) fun j _ hj => by
    by_contra hcol
    simp only [not_forall, not_not] at hcol
    obtain ⟨i, hi⟩ := hcol
    have hij : i ≠ j := by
      rintro rfl
      omega
    refine hj (alternant_eq_zero_of_not_injective fun hinj => hij (hinj ?_))
    rw [Function.update_of_ne hij, Function.update_self, hi]]
  -- Every other bead move adds a rim hook, whose bottom row is the row of the moved bead.
  have hex : ∀ j : Fin N, (∀ i, β i ≠ β j + r) → ∃ μ : (ν.card + r).Partition,
      ((diagramOf μ).IsRimHook ν ∧ (diagramOf μ).colLen 0 ≤ N) ∧
        ∃ a, (diagramOf μ).rimHookRows ν = Icc a (j : ℕ) := by
    intro j hj
    obtain ⟨μ, hμ, hμN, hcard, a, hab⟩ :=
      YoungDiagram.exists_isRimHook_rimHookRows_eq_Icc hν j.isLt fun i hi => hj ⟨i, hi⟩
    exact ⟨toPartition μ hcard, by rw [diagramOf_toPartition]; exact ⟨hμ, hμN⟩, a,
      by rw [diagramOf_toPartition, hab]⟩
  choose! f hfS hfrows using hex
  -- The alternant of a bead move is the signed alternant of the enlarged diagram.
  have hterm : ∀ (μ : (ν.card + r).Partition) (a : ℕ) (j : Fin N)
      (hμ : (diagramOf μ).IsRimHook ν) (hab : (diagramOf μ).rimHookRows ν = Icc a (j : ℕ)),
      Function.update β j (β j + r) = (fun i : Fin N => (diagramOf μ).betaNumber N i) ∘
        Fin.cycleIcc ⟨a, (hμ.le_of_rimHookRows_eq_Icc hab).trans_lt j.isLt⟩ j := by
    intro μ a j hμ hab
    have hu := hμ.update_betaNumber_eq_comp_cycleIcc hab j.isLt
    rwa [card_diagramOf, Nat.add_sub_cancel_left] at hu
  refine sum_bij (fun j _ => f j)
    (fun j hj => mem_filter.mpr ⟨mem_univ _, hfS j (mem_filter.mp hj).2⟩) ?_ ?_ ?_
  · -- Distinct bead moves give distinct rim hooks: the bottom row of the hook is the moved row.
    intro j₁ hj₁ j₂ hj₂ hf
    obtain ⟨a₁, hab₁⟩ := hfrows j₁ (mem_filter.mp hj₁).2
    obtain ⟨a₂, hab₂⟩ := hfrows j₂ (mem_filter.mp hj₂).2
    have h₂ := ((hfS j₂ (mem_filter.mp hj₂).2).1).le_of_rimHookRows_eq_Icc hab₂
    rw [hf, hab₂] at hab₁
    have := (Set.Icc_eq_Icc_iff (c := a₁) (d := (j₁ : ℕ)) h₂).mp (by
      rw [← coe_Icc, ← coe_Icc, hab₁])
    exact Fin.ext this.2.symm
  · -- Every rim hook arises from moving the bead of its bottom row.
    intro μ hμ
    obtain ⟨hrim, hμN⟩ := (mem_filter.mp hμ).2
    obtain ⟨a, b, -, hab⟩ := hrim.exists_rimHookRows_eq_Icc
    have hbN : b < N := (hrim.lt_colLen_of_rimHookRows_eq_Icc hab).trans_le hμN
    have hfree : ∀ i, β i ≠ β ⟨b, hbN⟩ + r := fun i => by
      simpa [hβ, card_diagramOf] using hrim.betaNumber_ne_betaNumber_add hab i.isLt hbN
    refine ⟨⟨b, hbN⟩, mem_filter.mpr ⟨mem_univ _, hfree⟩, ?_⟩
    obtain ⟨a', hab'⟩ := hfrows _ hfree
    exact diagramOf_injective ((hfS _ hfree).1.eq_of_rimHookRows_eq_Icc hrim
      (by rw [card_diagramOf, card_diagramOf]) hab' hab)
  · intro j hj
    obtain ⟨a, hab⟩ := hfrows j (mem_filter.mp hj).2
    have hrim := (hfS j (mem_filter.mp hj).2).1
    have hle : a ≤ j := hrim.le_of_rimHookRows_eq_Icc hab
    rw [hterm (f j) a j hrim hab, alternant_comp_perm,
      Fin.sign_cycleIcc_of_le (Fin.le_iff_val_le_val.mpr hle),
      YoungDiagram.rimHookHeight_eq_sub hab, Units.smul_def, zsmul_eq_mul]
    simp

open scoped Classical in
/-- **The Murnaghan–Nakayama rule for Schur polynomials.**  For `r > 0`, multiplying the Schur
polynomial of a Young diagram `ν` in the alphabet `Fin N` by the power sum `p_r` gives the signed
sum of the Schur polynomials of the diagrams `μ` for which `μ / ν` is a rim hook with `r` cells,
each weighted by `(-1)` to the height of its rim hook:
`p_r · s_ν = ∑_μ (-1) ^ ht(μ / ν) · s_μ`.  No bound on the number of rows is needed: the Schur
polynomials of the diagrams with more than `N` rows vanish on both sides. -/
theorem psum_mul_diagramSchurPoly {N : ℕ} (ν : YoungDiagram) {r : ℕ} (hr : 0 < r) :
    psum (Fin N) R r * diagramSchurPoly N R ν =
      ∑ μ : (ν.card + r).Partition with (diagramOf μ).IsRimHook ν,
        (-1) ^ (diagramOf μ).rimHookHeight ν * diagramSchurPoly N R (diagramOf μ) := by
  -- The identity has integer coefficients, so it suffices to prove it over `ℤ`.
  suffices hℤ : psum (Fin N) ℤ r * diagramSchurPoly N ℤ ν =
      ∑ μ : (ν.card + r).Partition with (diagramOf μ).IsRimHook ν,
        (-1) ^ (diagramOf μ).rimHookHeight ν * diagramSchurPoly N ℤ (diagramOf μ) by
    have h := congrArg (MvPolynomial.map (Int.castRingHom R)) hℤ
    simpa [map_diagramSchurPoly, psum, map_sum] using h
  by_cases hν : ν.colLen 0 ≤ N
  · -- Cancel the staircase alternant, whose exponents are pairwise distinct.
    have hδ : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) := fun i j h => by
      have := i.isLt
      have := j.isLt
      exact Fin.ext (by simp only at h; omega)
    refine mul_right_cancel₀ (alternant_ne_zero_of_injective hδ) ?_
    rw [mul_assoc, diagramSchurPoly_mul_alternant N ν hν,
      psum_mul_alternant_betaNumber ν hν hr, sum_mul, ← filter_filter, sum_filter]
    refine sum_congr rfl fun μ _ => ?_
    split_ifs with hμ
    · rw [mul_assoc, diagramSchurPoly_mul_alternant N _ hμ]
    · rw [diagramSchurPoly_eq_zero_of_lt_colLen (Nat.lt_of_not_le hμ), mul_zero, zero_mul]
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
    rw [diagramSchurPoly_eq_zero_of_lt_colLen hμN, mul_zero]

open scoped Classical in
/-- **The Murnaghan–Nakayama rule for Schur polynomials of partitions.**  In a finite alphabet
`σ`, for a partition `ν` of `n` and `r > 0`,
`p_r · s_ν = ∑_μ (-1) ^ ht(μ / ν) · s_μ`,
the sum running over the partitions `μ` of `n + r` whose Young diagram contains that of `ν` with a
rim hook as complement, `ht` being the height of that rim hook. -/
theorem psum_mul_schurPoly {σ : Type*} [Fintype σ] {n : ℕ} (ν : n.Partition) {r : ℕ}
    (hr : 0 < r) :
    psum σ R r * schurPoly σ R ν =
      ∑ μ : (n + r).Partition with (diagramOf μ).IsRimHook (diagramOf ν),
        (-1) ^ (diagramOf μ).rimHookHeight (diagramOf ν) * schurPoly σ R μ := by
  have h := psum_mul_diagramSchurPoly (R := R) (N := Fintype.card σ) (diagramOf ν) hr
  rw [card_diagramOf] at h
  have h' := congrArg (rename (Fintype.equivFin σ).symm) h
  rw [map_mul, rename_psum, ← schurPoly_eq_rename] at h'
  rw [h', map_sum]
  refine sum_congr rfl fun μ _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, schurPoly_eq_rename]

end TauCeti
