/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.VerticalStrip
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import TauCeti.Data.Fin.StrictAnti
import TauCeti.GroupTheory.Perm.SignedDomination

/-!
# The Pieri rules for Schur polynomials

Multiplying a Schur polynomial by a complete homogeneous symmetric polynomial adds horizontal
strips, and multiplying it by an elementary symmetric polynomial adds vertical strips: for every
`r`,

`h_r · s_ν = ∑_μ s_μ` and `e_r · s_ν = ∑_μ s_μ`,

the first sum running over the diagrams `μ` with `ν.card + r` cells whose row lengths
**interlace** those of `ν`, `μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`, equivalently over the `μ ⊇ ν` whose skew
shape `μ / ν` has at most one cell in each column, and the second running over the `μ` for which
`μ / ν` is a vertical strip with `r` cells, that is over the ways of lengthening `r` distinct rows
of `ν` by one cell each.  Every term carries the coefficient `1`; unlike the Murnaghan-Nakayama
rule for power sums, no sign appears.  These are `TauCeti.hsymm_mul_diagramSchurPoly` and
`TauCeti.esymm_mul_diagramSchurPoly` for Young diagrams in the alphabet `Fin N`, and
`TauCeti.hsymm_mul_schurPoly` and `TauCeti.esymm_mul_schurPoly` for partitions in an arbitrary
finite alphabet.

Iterating the horizontal-strip rule from `s_∅ = 1` along the parts of a partition `ν` expands the
product `h_{ν₁} ⋯ h_{ν_k}` in Schur polynomials with the Kostka numbers as coefficients, which is
the symmetric-function half of Young's rule for the permutation modules of the symmetric groups.

## The cancellation

Both computations happen on alternants, and in both the exponents are taken to be the beta-numbers
`β_j = ν_j + (N - 1 - j)` of `ν`, for which `a_β = s_ν · a_δ`.

`TauCeti.hsymm_mul_alternant` expands `h_r · a_β` as the sum of `a_{β + γ}` over the exponent
vectors `γ` of total degree `r`.  Those shifted vectors are no longer decreasing, so each must be
sorted back (`Function.Injective.strictAnti_sortDesc`, uniquely by `StrictAnti.perm_eq`) at the
cost of the sign of the sorting permutation; a strictly decreasing result is again a vector of
beta-numbers (`YoungDiagram.exists_eq_betaNumber_of_strictAnti`), and a repeated exponent kills the
alternant.  Grouping the shifts by the shape they sort to leaves, for each shape `μ`, the signed
count of the permutations `τ` with `β_j ≤ β(μ)_{τ j}` for all `j`.  That count is `1` exactly when
the comparisons cut out the initial segments, which is interlacing, and `0` otherwise
(`TauCeti.sum_sign_filter_forall_le_of_antitone`).  Both the sorting and the cancellation are
genuinely needed: a shift of total degree `r` is an arbitrary exponent vector, so the shifted
beta-numbers are in general neither distinct nor decreasing.

`TauCeti.esymm_mul_alternant` instead raises by one each of the exponents indexed by an `r`-element
set `T`, and those shifts are visible as shapes straight away: because `β` is *strictly*
decreasing, an indicator shift of it either repeats an exponent — and the alternant vanishes — or is
again strictly decreasing, in which case the shifted row lengths `ν_j + 1_T(j)` are still weakly
decreasing and so are the row lengths of a Young diagram `μ`.  No sorting is needed and no sign
appears, which is exactly what separates the `e`-half of the Pieri rule from the `h`-half.

Cancelling the staircase alternant `a_δ` needs a domain, so both alternant computations are carried
out over `ℤ`.  Both sides of the resulting Schur-polynomial identities have natural-number
coefficients, which is why they descend to `ℕ` and from there to an arbitrary commutative semiring.

## Main statements

* `TauCeti.hsymm_mul_alternant_betaNumber`: the Pieri rule for alternants of beta-numbers.
* `TauCeti.hsymm_mul_diagramSchurPoly`: the Pieri rule for the Schur polynomial of a Young diagram.
* `TauCeti.hsymm_mul_schurPoly`: the Pieri rule for the Schur polynomial of a partition in a finite
  alphabet.
* `TauCeti.esymm_mul_alternant_betaNumber`: the dual Pieri rule for alternants of beta-numbers.
* `TauCeti.esymm_mul_diagramSchurPoly`: the dual Pieri rule for the Schur polynomial of a Young
  diagram.
* `TauCeti.esymm_mul_schurPoly`: the dual Pieri rule for the Schur polynomial of a partition in a
  finite alphabet.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, (5.16) and (5.17) (Pieri's formula and its dual).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.15.7 (the two Pieri rules).
-/

public section

open MvPolynomial Finset

namespace TauCeti

open YoungDiagram (ofPartition card_ofPartition)

section Alternant

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- Sorting a shift of the beta-numbers of `ν` by a permutation dominating them gives a shift of
total degree `r` with no repeated exponent. -/
private theorem sub_betaNumber_mem_piAntidiag {N r : ℕ} {ν : YoungDiagram} (hν : ν.colLen 0 ≤ N)
    {μ : (ν.card + r).Partition} (hμ : (ofPartition μ).colLen 0 ≤ N) {τ : Equiv.Perm (Fin N)}
    (hτ : ∀ j : Fin N, ν.betaNumber N j ≤ (ofPartition μ).betaNumber N (τ j)) :
    (fun i : Fin N => (ofPartition μ).betaNumber N (τ i) - ν.betaNumber N i) ∈
      {γ ∈ piAntidiag (univ : Finset (Fin N)) r |
        Function.Injective fun i : Fin N => ν.betaNumber N i + γ i} := by
  have hval : ∀ i : Fin N, ν.betaNumber N i +
      ((ofPartition μ).betaNumber N (τ i) - ν.betaNumber N i) =
        (ofPartition μ).betaNumber N (τ i) := fun i => Nat.add_sub_of_le (hτ i)
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_piAntidiag.mpr ⟨?_, fun i _ => Finset.mem_univ i⟩, ?_⟩
  · have hsum : ∑ i : Fin N, (ν.betaNumber N i +
        ((ofPartition μ).betaNumber N (τ i) - ν.betaNumber N i)) =
          ∑ j : Fin N, (ofPartition μ).betaNumber N j := by
      rw [Finset.sum_congr rfl fun i _ => hval i]
      exact Equiv.sum_comp τ fun j : Fin N => (ofPartition μ).betaNumber N j
    rw [Finset.sum_add_distrib, ν.sum_betaNumber hν, (ofPartition μ).sum_betaNumber hμ,
      card_ofPartition] at hsum
    omega
  · rw [show (fun i : Fin N => ν.betaNumber N i + ((ofPartition μ).betaNumber N (τ i) -
        ν.betaNumber N i)) = (fun j : Fin N => (ofPartition μ).betaNumber N j) ∘ ⇑τ from
        funext hval]
    exact ((ofPartition μ).strictAnti_betaNumber N).injective.comp τ.injective

/-- Distinct pairs of a shape and a dominating permutation give distinct shifts: the shape and the
permutation are the data of sorting the shifted beta-numbers back into decreasing order. -/
private theorem sigma_eq_of_sub_betaNumber_eq {N r : ℕ} {ν : YoungDiagram}
    {μ₁ μ₂ : (ν.card + r).Partition} (h₁ : (ofPartition μ₁).colLen 0 ≤ N)
    (h₂ : (ofPartition μ₂).colLen 0 ≤ N) {τ₁ τ₂ : Equiv.Perm (Fin N)}
    (hτ₁ : ∀ j : Fin N, ν.betaNumber N j ≤ (ofPartition μ₁).betaNumber N (τ₁ j))
    (hτ₂ : ∀ j : Fin N, ν.betaNumber N j ≤ (ofPartition μ₂).betaNumber N (τ₂ j))
    (h : (fun i : Fin N => (ofPartition μ₁).betaNumber N (τ₁ i) - ν.betaNumber N i) =
      fun i : Fin N => (ofPartition μ₂).betaNumber N (τ₂ i) - ν.betaNumber N i) :
    (⟨μ₁, τ₁⟩ : Σ _ : (ν.card + r).Partition, Equiv.Perm (Fin N)) = ⟨μ₂, τ₂⟩ := by
  have hbx : ∀ i : Fin N,
      (ofPartition μ₁).betaNumber N (τ₁ i) = (ofPartition μ₂).betaNumber N (τ₂ i) :=
    fun i => by
      have h1 := congrFun h i
      have h2 := hτ₁ i
      have h3 := hτ₂ i
      omega
  have hsx : StrictAnti ((fun i : Fin N => (ofPartition μ₂).betaNumber N (τ₂ i)) ∘ ⇑τ₁.symm) := by
    rw [← funext hbx]
    simpa [Function.comp_def] using (ofPartition μ₁).strictAnti_betaNumber N
  have hsy : StrictAnti ((fun i : Fin N => (ofPartition μ₂).betaNumber N (τ₂ i)) ∘ ⇑τ₂.symm) := by
    simpa [Function.comp_def] using (ofPartition μ₂).strictAnti_betaNumber N
  have hp : τ₁ = τ₂ := by simpa using congrArg Equiv.symm (hsx.perm_eq hsy)
  have hbeta : ∀ j : Fin N,
      (ofPartition μ₁).betaNumber N j = (ofPartition μ₂).betaNumber N j := fun j : Fin N => by
    have h' := hbx (τ₁.symm j)
    rw [← hp] at h'
    simpa using h'
  exact Sigma.ext (YoungDiagram.ofPartition_injective (YoungDiagram.eq_of_betaNumber_eq h₁ h₂
    fun i hi => hbeta ⟨i, hi⟩)) (by rw [hp])

open scoped Classical in
/-- Every shift of total degree `r` with distinct exponents sorts to a shape and a dominating
permutation. -/
private theorem exists_sub_betaNumber_eq {N r : ℕ} {ν : YoungDiagram} (hν : ν.colLen 0 ≤ N)
    {γ : Fin N → ℕ}
    (hγ : γ ∈ {γ ∈ piAntidiag (univ : Finset (Fin N)) r |
      Function.Injective fun i : Fin N => ν.betaNumber N i + γ i}) :
    ∃ (μ : (ν.card + r).Partition) (τ : Equiv.Perm (Fin N)), (ofPartition μ).colLen 0 ≤ N ∧
      (∀ j : Fin N, ν.betaNumber N j ≤ (ofPartition μ).betaNumber N (τ j)) ∧
      (fun i : Fin N => (ofPartition μ).betaNumber N (τ i) - ν.betaNumber N i) = γ := by
  obtain ⟨hγmem, hγinj⟩ := Finset.mem_filter.mp hγ
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : Equiv.Perm (Fin N), StrictAnti (_ ∘ τ) :=
    ⟨_, hγinj.strictAnti_sortDesc⟩
  obtain ⟨μ₀, hμ₀col, hμ₀beta⟩ := YoungDiagram.exists_eq_betaNumber_of_strictAnti hτ₀
  have hcard : μ₀.card = ν.card + r := by
    have h1 : ∑ j : Fin N, μ₀.betaNumber N j = ∑ i : Fin N, (ν.betaNumber N i + γ i) := by
      rw [Finset.sum_congr rfl fun j _ => hμ₀beta j]
      exact Equiv.sum_comp τ₀ fun i : Fin N => ν.betaNumber N i + γ i
    rw [μ₀.sum_betaNumber hμ₀col, Finset.sum_add_distrib, ν.sum_betaNumber hν,
      (Finset.mem_piAntidiag.mp hγmem).1] at h1
    omega
  refine ⟨μ₀.toPartition hcard, τ₀.symm, by rwa [YoungDiagram.ofPartition_toPartition],
    fun j : Fin N => ?_, funext fun i : Fin N => ?_⟩
  · rw [YoungDiagram.ofPartition_toPartition, hμ₀beta]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact Nat.le_add_right _ _
  · rw [YoungDiagram.ofPartition_toPartition, hμ₀beta]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    omega

open scoped Classical in
/-- The alternants of the pairs of a shape and a dominating permutation are the alternants of the
shifts of total degree `r` with distinct exponents. -/
private theorem sum_sigma_alternant_betaNumber_eq {N : ℕ} {ν : YoungDiagram}
    (hν : ν.colLen 0 ≤ N) (r : ℕ) :
    ∑ x ∈ Finset.sigma (α := fun _ : (ν.card + r).Partition => Equiv.Perm (Fin N))
        {μ | (ofPartition μ).colLen 0 ≤ N} fun μ =>
          {τ : Equiv.Perm (Fin N) |
            ∀ j : Fin N, ν.betaNumber N j ≤ (ofPartition μ).betaNumber N (τ j)},
      alternant (Fin N) R (fun j : Fin N => (ofPartition x.1).betaNumber N (x.2 j)) =
    ∑ γ ∈ {γ ∈ piAntidiag (univ : Finset (Fin N)) r |
        Function.Injective fun i : Fin N => ν.betaNumber N i + γ i},
      alternant (Fin N) R (fun i : Fin N => ν.betaNumber N i + γ i) := by
  refine Finset.sum_bij
    (fun x _ => fun i : Fin N => (ofPartition x.1).betaNumber N (x.2 i) - ν.betaNumber N i)
    ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hμ, hτ⟩ := Finset.mem_sigma.mp hx
    exact sub_betaNumber_mem_piAntidiag hν (Finset.mem_filter.mp hμ).2
      (Finset.mem_filter.mp hτ).2
  · intro x hx y hy hxy
    obtain ⟨hμx, hτx⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hμy, hτy⟩ := Finset.mem_sigma.mp hy
    exact sigma_eq_of_sub_betaNumber_eq (Finset.mem_filter.mp hμx).2 (Finset.mem_filter.mp hμy).2
      (Finset.mem_filter.mp hτx).2 (Finset.mem_filter.mp hτy).2 hxy
  · intro γ hγ
    obtain ⟨μ, τ, hμ, hτ, h⟩ := exists_sub_betaNumber_eq hν hγ
    exact ⟨⟨μ, τ⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩⟩, h⟩
  · intro x hx
    obtain ⟨-, hτ⟩ := Finset.mem_sigma.mp hx
    exact congrArg (alternant (Fin N) R)
      (funext fun i : Fin N => (Nat.add_sub_of_le ((Finset.mem_filter.mp hτ).2 i)).symm)

open scoped Classical in
/-- The permutations dominating the beta-numbers of `ν` by those of a shape `μ` contribute their
signed count: the alternants add up to that of `μ` if `ν` interlaces `μ` and to zero otherwise. -/
private theorem sum_alternant_betaNumber_dominating {N : ℕ} {ν : YoungDiagram}
    (hν : ν.colLen 0 ≤ N) {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ N) :
    ∑ τ ∈ ({τ : Equiv.Perm (Fin N) | ∀ j : Fin N, ν.betaNumber N j ≤ μ.betaNumber N (τ j)} :
        Finset _), alternant (Fin N) R (fun j : Fin N => μ.betaNumber N (τ j)) =
      if μ.InterlacedBy ν then alternant (Fin N) R (fun j : Fin N => μ.betaNumber N j) else 0 := by
  have hstep : ∀ τ : Equiv.Perm (Fin N),
      alternant (Fin N) R (fun j : Fin N => μ.betaNumber N (τ j)) =
        (Equiv.Perm.sign τ : ℤ) • alternant (Fin N) R (fun j : Fin N => μ.betaNumber N j) := by
    intro τ
    -- The two sides differ only by folding the composition that `alternant_comp_perm` matches.
    have hcomp : (fun j : Fin N => μ.betaNumber N (τ j)) =
        (fun j : Fin N => μ.betaNumber N j) ∘ ⇑τ := rfl
    rw [hcomp, alternant_comp_perm]
    simp [Units.smul_def]
  rw [Finset.sum_congr rfl fun τ _ => hstep τ, ← Finset.sum_smul,
    sum_sign_filter_forall_le_of_antitone (ν.strictAnti_betaNumber N).antitone
      (μ.strictAnti_betaNumber N).antitone]
  simp only [forall_betaNumber_le_iff_interlacedBy hμ hν]
  split_ifs <;> simp

open scoped Classical in
/-- **The Pieri rule for alternants of beta-numbers.**  Let `ν` be a Young diagram with at most `N`
rows and `β` its beta-numbers relative to `N`, so that `a_β = s_ν · a_δ`.  Multiplying `a_β` by the
complete homogeneous symmetric polynomial `h_r` gives the sum, with no signs, of the alternants of
the beta-numbers of the diagrams `μ` with at most `N` rows obtained from `ν` by adding a horizontal
strip of `r` cells. -/
theorem hsymm_mul_alternant_betaNumber {N : ℕ} (ν : YoungDiagram) (hν : ν.colLen 0 ≤ N) (r : ℕ) :
    hsymm (Fin N) R r * alternant (Fin N) R (fun j => ν.betaNumber N j) =
      ∑ μ : (ν.card + r).Partition with
          ((ofPartition μ).InterlacedBy ν ∧ (ofPartition μ).colLen 0 ≤ N),
        alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N j) := by
  -- The proof runs in four steps.  The complete-homogeneous rule for alternants expands the
  -- left-hand side as a sum over the shifts `γ` of total degree `r`.  The shifts that repeat an
  -- exponent are discarded, their alternants vanishing.  The remaining ones are then put in
  -- bijection (`sum_sigma_alternant_betaNumber_eq`) with the pairs of a shape `μ` and a
  -- permutation `τ` carrying the beta-numbers of `ν` below those of `μ`: the shape and the
  -- permutation are the data of sorting `β + γ` back into decreasing order.  Summing over `τ`
  -- first leaves, for each shape, the signed count of those permutations, which is `1` exactly on
  -- the shapes that `ν` interlaces.
  classical
  rw [hsymm_mul_alternant]
  -- A shift producing a repeated exponent kills the alternant.
  rw [← Finset.sum_filter_of_ne
    (p := fun γ : Fin N → ℕ => Function.Injective fun i : Fin N => ν.betaNumber N i + γ i)
    fun γ _ hγ => by
      by_contra hninj
      exact hγ (alternant_eq_zero_of_not_injective hninj)]
  rw [← sum_sigma_alternant_betaNumber_eq hν r, Finset.sum_sigma,
    Finset.sum_congr rfl fun μ hμ =>
      sum_alternant_betaNumber_dominating hν (Finset.mem_filter.mp hμ).2,
    ← Finset.sum_filter, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun μ _ => ?_) fun _ _ => rfl
  exact and_comm

open scoped Classical in
/-- A set `T` of `r` rows whose lengthening of the beta-numbers of `ν` has distinct exponents
lengthens `ν` to a vertical strip inside `N` rows. -/
private theorem exists_isVerticalStrip_rowLen_eq_add_ite {N r : ℕ} {ν : YoungDiagram}
    (hν : ν.colLen 0 ≤ N) (T : Finset (Fin N)) (hcard : T.card = r)
    (hinj : Function.Injective fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0) :
    ∃ μ : (ν.card + r).Partition,
      ((ofPartition μ).IsVerticalStrip ν ∧ (ofPartition μ).colLen 0 ≤ N) ∧
        ∀ j : Fin N, (ofPartition μ).rowLen j = ν.rowLen j + if j ∈ T then 1 else 0 := by
  have hanti := YoungDiagram.antitone_rowLen_add_ite_of_injective hinj
  refine ⟨(YoungDiagram.ofRowLensFin _ hanti).toPartition
    (by rw [YoungDiagram.card_ofRowLensFin_add_ite hanti hν, hcard]), ?_, ?_⟩
  · rw [YoungDiagram.ofPartition_toPartition]
    exact ⟨YoungDiagram.isVerticalStrip_ofRowLensFin hanti hν,
      YoungDiagram.colLen_zero_ofRowLensFin_le _ hanti⟩
  · intro j
    rw [YoungDiagram.ofPartition_toPartition, YoungDiagram.rowLen_ofRowLensFin]

open scoped Classical in
/-- **The dual Pieri rule for alternants.**  Let `ν` be a Young diagram with at most `N` rows and
`β` its beta-numbers relative to `N`, so that `a_β = s_ν · a_δ`.  Multiplying `a_β` by the
elementary symmetric polynomial `e_r` gives the sum of the alternants of the beta-numbers of the
diagrams `μ` with at most `N` rows for which `μ / ν` is a vertical strip with `r` cells, each
occurring once and with coefficient `+1`. -/
theorem esymm_mul_alternant_betaNumber {N : ℕ} (ν : YoungDiagram) (hν : ν.colLen 0 ≤ N) (r : ℕ) :
    esymm (Fin N) R r * alternant (Fin N) R (fun j => ν.betaNumber N j) =
      ∑ μ : (ν.card + r).Partition with
          (ofPartition μ).IsVerticalStrip ν ∧ (ofPartition μ).colLen 0 ≤ N,
        alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N j) := by
  rw [esymm_mul_alternant]
  -- Discard the sets of rows whose shifted beta-numbers repeat: those alternants vanish.
  rw [← sum_filter_of_ne (p := fun T : Finset (Fin N) =>
      Function.Injective fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0)
    fun T _ hT => by
      by_contra hcon
      exact hT (alternant_eq_zero_of_not_injective hcon)]
  -- Every remaining set of rows lengthens `ν` to a vertical strip inside `N` rows.
  choose! f hfS hfrow using exists_isVerticalStrip_rowLen_eq_add_ite (r := r) hν
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
    set T := YoungDiagram.lengthenedRows N (ofPartition μ) ν with hT
    have hrow : ∀ j : Fin N, (ofPartition μ).rowLen j = ν.rowLen j + if j ∈ T then 1 else 0 := by
      intro j
      rw [hT]
      simp only [YoungDiagram.mem_lengthenedRows]
      exact hstrip.rowLen_eq_add_ite _
    have hcard : T.card = r := by
      have h2 := hstrip.card_eq_add_card_lengthenedRows (N := N) hμN
      rw [card_ofPartition, ← hT] at h2
      omega
    have hinj : Function.Injective
        fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0 := by
      rw [hT]
      exact hstrip.injective_betaNumber_add_ite
    refine ⟨T, mem_filter.mpr ⟨mem_powersetCard_univ.mpr hcard, hinj⟩, ?_⟩
    refine YoungDiagram.ofPartition_injective
      (YoungDiagram.eq_of_betaNumber_eq (hfS T hcard hinj).2 hμN fun i hi => ?_)
    have hrw : (ofPartition (f T)).rowLen i = (ofPartition μ).rowLen i := by
      simpa using (hfrow T hcard hinj ⟨i, hi⟩).trans (hrow ⟨i, hi⟩).symm
    rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def, hrw]
  · intro T hT
    refine congrArg _ (funext fun j => ?_)
    rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def,
      hfrow T (mem_powersetCard_univ.mp (mem_filter.mp hT).1) (mem_filter.mp hT).2 j,
      Nat.add_right_comm]

end Alternant

section SchurPolynomials

variable {R : Type*} [CommSemiring R]

open scoped Classical in
/-- **From an alternant identity on beta-numbers to a Schur-polynomial identity.**  Let `p` be a
polynomial with natural-number coefficients and `P` a property of the partitions of `n` under which
the shape contains `ν`.  If, for every `ν` with at most `N` rows, multiplying the alternant of the
beta-numbers of `ν` by `p` gives the sum of the alternants of the beta-numbers of the shapes with
at most `N` rows satisfying `P`, then multiplying the Schur polynomial of `ν` by `p` gives the sum
of their Schur polynomials, over any commutative semiring and with no bound on the rows of `ν`.

This is the passage shared by the two Pieri rules below: the staircase alternant is cancelled over
`ℤ`, the shapes too tall for the alphabet drop out of both sides, and the resulting identity is
transported through `ℕ` to the target semiring. -/
private theorem mul_diagramSchurPoly_of_mul_alternant_betaNumber {N n : ℕ}
    (p : MvPolynomial (Fin N) ℕ) (ν : YoungDiagram) (P : n.Partition → Prop)
    (hP : ∀ μ, P μ → ν ≤ ofPartition μ)
    (halt : ν.colLen 0 ≤ N →
      MvPolynomial.map (Nat.castRingHom ℤ) p * alternant (Fin N) ℤ (fun j => ν.betaNumber N j) =
        ∑ μ : n.Partition with (P μ ∧ (ofPartition μ).colLen 0 ≤ N),
          alternant (Fin N) ℤ fun j => (ofPartition μ).betaNumber N j) :
    MvPolynomial.map (Nat.castRingHom R) p * diagramSchurPoly N R ν =
      ∑ μ : n.Partition with P μ, diagramSchurPoly N R (ofPartition μ) := by
  -- Prove the identity over `ℤ`, where the nonzero Vandermonde alternant `a_δ` can be cancelled
  -- in `ℤ[x]`.  Both sides have natural-number coefficients, so the identity descends along the
  -- injection `ℕ → ℤ`, and the resulting identity over `ℕ` maps to any commutative semiring.
  have hℤ : MvPolynomial.map (Nat.castRingHom ℤ) p * diagramSchurPoly N ℤ ν =
      ∑ μ : n.Partition with P μ, diagramSchurPoly N ℤ (ofPartition μ) := by
    by_cases hν : ν.colLen 0 ≤ N
    · -- Cancel the staircase alternant, whose exponents are pairwise distinct.
      refine mul_right_cancel₀ (alternant_ne_zero_of_injective (injective_staircase N)) ?_
      rw [mul_assoc, diagramSchurPoly_mul_alternant N ν hν, halt hν, sum_mul, ← filter_filter,
        sum_filter]
      refine sum_congr rfl fun μ _ => ?_
      split_ifs with hμ
      · rw [diagramSchurPoly_mul_alternant N _ hμ]
      · rw [diagramSchurPoly_eq_zero_of_lt_colLen (Nat.lt_of_not_le hμ), zero_mul]
    · -- Both sides vanish: `ν` and every diagram containing it have more than `N` rows.
      have hν' : N < ν.colLen 0 := Nat.lt_of_not_le hν
      rw [diagramSchurPoly_eq_zero_of_lt_colLen hν', mul_zero]
      refine (sum_eq_zero fun μ hμ => ?_).symm
      exact diagramSchurPoly_eq_zero_of_lt_colLen (hν'.trans_le
        (YoungDiagram.colLen_le_of_le (hP μ (mem_filter.mp hμ).2) 0))
  have hℕ : p * diagramSchurPoly N ℕ ν =
      ∑ μ : n.Partition with P μ, diagramSchurPoly N ℕ (ofPartition μ) :=
    MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective <| by
      simpa [map_diagramSchurPoly, map_sum] using hℤ
  simpa [map_diagramSchurPoly, map_sum] using
    congrArg (MvPolynomial.map (Nat.castRingHom R)) hℕ

open scoped Classical in
/-- **The Pieri rule for Schur polynomials.**  Multiplying the Schur polynomial of a Young diagram
`ν` in the alphabet `Fin N` by the complete homogeneous symmetric polynomial `h_r` gives the sum of
the Schur polynomials of the diagrams `μ` obtained from `ν` by adding a horizontal strip of `r`
cells, each with coefficient `1`: `h_r · s_ν = ∑_μ s_μ`.  No bound on the number of rows is needed:
the Schur polynomials of the diagrams with more than `N` rows vanish on both sides.  Nor is `r`
required to be positive: at `r = 0` the only strip is empty and the sum is the single term `s_ν`. -/
theorem hsymm_mul_diagramSchurPoly {N : ℕ} (ν : YoungDiagram) (r : ℕ) :
    hsymm (Fin N) R r * diagramSchurPoly N R ν =
      ∑ μ : (ν.card + r).Partition with (ofPartition μ).InterlacedBy ν,
        diagramSchurPoly N R (ofPartition μ) := by
  have h := mul_diagramSchurPoly_of_mul_alternant_betaNumber (R := R) (hsymm (Fin N) ℕ r) ν
    (fun μ => (ofPartition μ).InterlacedBy ν) (fun _ hμ => hμ.le)
    fun hν => by rw [map_hsymm]; exact hsymm_mul_alternant_betaNumber ν hν r
  rwa [map_hsymm] at h

open scoped Classical in
/-- **The Pieri rule for Schur polynomials of partitions.**  In a finite alphabet `σ`, for a
partition `ν` of `n`, `h_r · s_ν = ∑_μ s_μ`, the sum running over the partitions `μ` of `n + r`
whose Young diagram contains that of `ν` with a horizontal strip as complement. -/
theorem hsymm_mul_schurPoly {σ : Type*} [Fintype σ] {n : ℕ} (ν : n.Partition) (r : ℕ) :
    hsymm σ R r * schurPoly σ R ν =
      ∑ μ : (n + r).Partition with (ofPartition μ).InterlacedBy (ofPartition ν),
        schurPoly σ R μ := by
  have h := hsymm_mul_diagramSchurPoly (R := R) (N := Fintype.card σ) (ofPartition ν) r
  rw [card_ofPartition] at h
  have h' := congrArg (rename (Fintype.equivFin σ).symm) h
  rw [map_mul, rename_hsymm, ← schurPoly_eq_rename] at h'
  rw [h', map_sum]
  exact sum_congr rfl fun μ _ => (schurPoly_eq_rename μ).symm

open scoped Classical in
/-- **The dual Pieri rule for Schur polynomials.**  Multiplying the Schur polynomial of a Young
diagram `ν` in the alphabet `Fin N` by the elementary symmetric polynomial `e_r` gives the sum of
the Schur polynomials of the diagrams `μ` for which `μ / ν` is a vertical strip with `r` cells:
`e_r · s_ν = ∑_μ s_μ`.  No bound on the number of rows is needed: the Schur polynomials of the
diagrams with more than `N` rows vanish on both sides. -/
theorem esymm_mul_diagramSchurPoly {N : ℕ} (ν : YoungDiagram) (r : ℕ) :
    esymm (Fin N) R r * diagramSchurPoly N R ν =
      ∑ μ : (ν.card + r).Partition with (ofPartition μ).IsVerticalStrip ν,
        diagramSchurPoly N R (ofPartition μ) := by
  have h := mul_diagramSchurPoly_of_mul_alternant_betaNumber (R := R) (esymm (Fin N) ℕ r) ν
    (fun μ => (ofPartition μ).IsVerticalStrip ν) (fun _ hμ => hμ.le)
    fun hν => by rw [map_esymm]; exact esymm_mul_alternant_betaNumber ν hν r
  rwa [map_esymm] at h

open scoped Classical in
/-- **The dual Pieri rule for Schur polynomials of partitions.**  In a finite alphabet `σ`, for a
partition `ν` of `n` and every `r`,
`e_r · s_ν = ∑_μ s_μ`,
the sum running over the partitions `μ` of `n + r` whose Young diagram contains that of `ν` with a
vertical strip as complement. -/
theorem esymm_mul_schurPoly {σ : Type*} [Fintype σ] {n : ℕ} (ν : n.Partition) (r : ℕ) :
    esymm σ R r * schurPoly σ R ν =
      ∑ μ : (n + r).Partition with (ofPartition μ).IsVerticalStrip (ofPartition ν),
        schurPoly σ R μ := by
  have h := esymm_mul_diagramSchurPoly (R := R) (N := Fintype.card σ) (ofPartition ν) r
  rw [card_ofPartition] at h
  have h' := congrArg (rename (Fintype.equivFin σ).symm) h
  rw [map_mul, rename_esymm, ← schurPoly_eq_rename] at h'
  rw [h', map_sum]
  exact sum_congr rfl fun μ _ => (schurPoly_eq_rename μ).symm

end SchurPolynomials

end TauCeti
