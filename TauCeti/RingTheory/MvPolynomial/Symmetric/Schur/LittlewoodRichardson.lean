/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.OfRowLens
public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.Yamanouchi
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The Littlewood–Richardson rule in Stembridge's form

For Young diagrams `λ` and `μ`, the product of Schur polynomials in the alphabet `Fin N` expands
with natural-number coefficients in the Schur polynomials,

`s_λ · s_μ = ∑_ν c_ν · s_ν`,

where `c_ν` is the number of semistandard tableaux `T` of shape `μ` in the alphabet `Fin N` that are
`λ`-Yamanouchi (`SemistandardYoungTableau.IsYamanouchi`) and whose content added to `λ` is `ν`.
This is `TauCeti.diagramSchurPoly_mul_diagramSchurPoly`. The sum runs over the partitions `ν` of
`|λ| + |μ|`, and no bound on the rows of `λ` or `μ` is needed. Identifying the count `c_ν` with
the number `Nat.card (TauCeti.LRTableau λ ν μ)` of Littlewood–Richardson tableaux, whose
lattice condition reads the rows rather than the columns, is a separate bijection, not made here.

## Stembridge's proof

Write `δ_j = N - 1 - j` and `a_α` for the alternant of an exponent vector `α`. Since `s_μ` is
symmetric and is the sum of the monomials `x^{c(T)}` over its tableaux, multiplying an alternant
by it shifts the exponents by the contents
(`TauCeti.diagramSchurPoly_mul_alternant_eq_sum`, from `TauCeti.sum_monomial_mul_alternant`):

`s_μ · a_{λ+δ} = ∑_T a_{λ+δ+c(T)}`.

Stembridge's involution (`SemistandardYoungTableau.stembridgeInvolution`) pairs off the tableaux
that are not `λ`-Yamanouchi: it transposes the exponent vector `λ+δ+c(T)` at two adjacent places,
so the two alternants cancel, and a tableau it fixed would give an exponent vector with a repeated
entry, whose alternant vanishes. What is left is the sum over the `λ`-Yamanouchi tableaux
(`TauCeti.diagramSchurPoly_mul_alternant_betaNumber`). For those, `λ + c(T)` is a partition `ν`,
and Jacobi's bialternant formula `a_{ν+δ} = s_ν · a_δ` turns the identity into one of Schur
polynomials after cancelling `a_δ`. Cancelling needs a domain, so the computation runs over `ℤ`;
both sides have natural-number coefficients, so the identity descends to `ℕ` and from there to any
commutative semiring.

## Main statements

* `TauCeti.diagramSchurPoly_mul_alternant_eq_sum`: `s_μ · a_α = ∑_T a_{α+c(T)}`.
* `TauCeti.diagramSchurPoly_mul_alternant_betaNumber`: the Littlewood–Richardson rule for
  alternants, `s_μ · a_{λ+δ} = ∑_T a_{λ+δ+c(T)}`, the sum over the `λ`-Yamanouchi tableaux.
* `TauCeti.diagramSchurPoly_mul_diagramSchurPoly`: **the Littlewood–Richardson rule**.

## References

* J. R. Stembridge, *A concise proof of the Littlewood–Richardson rule*, Electron. J. Combin.
  **9** (2002), Note 5.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 9.
-/

public section

open MvPolynomial Finset

namespace TauCeti

open YoungDiagram (ofPartition)

variable {N : ℕ}

/-! ### Multiplying an alternant by a Schur polynomial -/

/-- **Multiplying an alternant by a Schur polynomial** shifts its exponents by the contents of
the tableaux: `s_μ · a_α = ∑_T a_{α + c(T)}`, the sum over the semistandard tableaux of shape `μ`
in the alphabet `Fin N`. -/
theorem diagramSchurPoly_mul_alternant_eq_sum {R : Type*} [CommRing R] (μ : YoungDiagram)
    (α : Fin N → ℕ) :
    diagramSchurPoly N R μ * alternant (Fin N) R α =
      ∑ T : BoundedSSYT N μ, alternant (Fin N) R fun j => α j + BoundedSSYT.weight T j := by
  have h := sum_monomial_mul_alternant (R := R) univ (fun T : BoundedSSYT N μ => T.weight)
    (fun _ => 1) (by simpa [diagramSchurPoly_eq_sum] using isSymmetric_diagramSchurPoly N R μ) α
  simpa [diagramSchurPoly_eq_sum] using h

/-! ### Stembridge's involution on bounded tableaux -/

namespace BoundedSSYT

variable {lam μ : YoungDiagram}

/-- Off the `λ`-Yamanouchi tableaux, Stembridge's involution transposes two adjacent letters of
the alphabet, so it keeps the alphabet. -/
private theorem exists_stembridgeInvolution (T : BoundedSSYT N μ)
    (h : ¬ T.1.IsYamanouchi lam) :
    ∃ k, k + 1 < N ∧ (∀ i c, (i, c) ∈ μ → T.1.stembridgeInvolution lam i c < N) ∧
      ∀ x, ((lam.rowLen x + (T.1.stembridgeInvolution lam).content x : ℕ) : ℤ) - x =
        ((lam.rowLen (Equiv.swap k (k + 1) x) + T.1.content (Equiv.swap k (k + 1) x) : ℕ) : ℤ) -
          (Equiv.swap k (k + 1) x : ℕ) := by
  obtain ⟨k, ⟨r, c, hrc, hk⟩, hval, hcont⟩ :=
    SemistandardYoungTableau.exists_intCast_rowLen_add_content_stembridgeInvolution h
  have hkN : k + 1 < N := hk ▸ T.2 r c hrc
  refine ⟨k, hkN, fun i c hic => ?_, hcont⟩
  rcases hval i c with h' | h' | h' <;> rw [h']
  · exact T.2 i c hic
  · omega
  · exact hkN

open scoped Classical in
/-- **Stembridge's involution on bounded tableaux.** -/
private noncomputable def stembridge (lam : YoungDiagram) (T : BoundedSSYT N μ) :
    BoundedSSYT N μ :=
  if h : T.1.IsYamanouchi lam then T
  else ⟨T.1.stembridgeInvolution lam, (exists_stembridgeInvolution T h).choose_spec.2.1⟩

private theorem coe_stembridge (T : BoundedSSYT N μ) :
    (stembridge lam T).1 = T.1.stembridgeInvolution lam := by
  by_cases h : T.1.IsYamanouchi lam
  · rw [stembridge, dite_eq_left h,
      SemistandardYoungTableau.stembridgeInvolution_of_isYamanouchi h]
  · rw [stembridge, dite_eq_right h]

private theorem stembridge_stembridge (T : BoundedSSYT N μ) :
    stembridge lam (stembridge lam T) = T :=
  Subtype.ext (by
    rw [coe_stembridge, coe_stembridge,
      SemistandardYoungTableau.stembridgeInvolution_stembridgeInvolution])

/-- The exponent vector `λ + δ + c(T)` of the alternant contributed by a tableau. -/
private theorem betaNumber_add_weight_stembridge (T : BoundedSSYT N μ)
    (h : ¬ T.1.IsYamanouchi lam) :
    ∃ a b : Fin N, a ≠ b ∧
      (fun j : Fin N => lam.betaNumber N j + weight (stembridge lam T) j) =
        (fun j : Fin N => lam.betaNumber N j + weight T j) ∘ Equiv.swap a b := by
  obtain ⟨k, hkN, -, hcont⟩ := exists_stembridgeInvolution T h
  refine ⟨⟨k, by omega⟩, ⟨k + 1, hkN⟩, fun hab => by simpa using congrArg Fin.val hab, ?_⟩
  funext j
  simp only [Function.comp_apply, weight_apply, coe_stembridge, YoungDiagram.betaNumber_def]
  have hj := hcont j
  have hjN := j.isLt
  set j' := Equiv.swap (⟨k, by omega⟩ : Fin N) ⟨k + 1, hkN⟩ j
  have hjle : (j : ℕ) ≤ N - 1 := by omega
  have hj'le : (j' : ℕ) ≤ N - 1 := by
    have := j'.isLt
    omega
  zify [hjle, hj'le]
  -- The transposition of `Fin N` acts on values as the transposition of `k` and `k + 1`.
  have hval : (j' : ℕ) = Equiv.swap k (k + 1) (j : ℕ) :=
    (Fin.val_injective.swap_apply (⟨k, by omega⟩ : Fin N) ⟨k + 1, hkN⟩ j).symm
  rw [hval]
  push_cast at hj ⊢
  omega

end BoundedSSYT

/-! ### The cancellation -/

open BoundedSSYT in
open scoped Classical in
/-- **The Littlewood–Richardson rule for alternants.** For Young diagrams `λ` and `μ`, multiplying
the alternant `a_{λ+δ}` of the first `N` beta-numbers of `λ` by the Schur polynomial `s_μ` gives
the sum of the alternants `a_{λ+δ+c(T)}` over the `λ`-Yamanouchi tableaux `T` of shape `μ` in the
alphabet `Fin N`. -/
theorem diagramSchurPoly_mul_alternant_betaNumber {R : Type*} [CommRing R]
    (lam μ : YoungDiagram) :
    diagramSchurPoly N R μ * alternant (Fin N) R (fun j => lam.betaNumber N j) =
      ∑ T : BoundedSSYT N μ with T.1.IsYamanouchi lam,
        alternant (Fin N) R fun j => lam.betaNumber N j + weight T j := by
  rw [diagramSchurPoly_mul_alternant_eq_sum, ← sum_filter_add_sum_filter_not univ
    (fun T : BoundedSSYT N μ => T.1.IsYamanouchi lam), add_eq_left]
  -- The tableaux that are not `λ`-Yamanouchi cancel in pairs.
  refine sum_involution (fun T _ => stembridge lam T) (fun T hT => ?_) (fun T hT hne heq => ?_)
    (fun T hT => ?_) (fun T _ => stembridge_stembridge T)
  · obtain ⟨a, b, hab, he⟩ := betaNumber_add_weight_stembridge T (mem_filter.mp hT).2
    rw [he, alternant_comp_perm, Equiv.Perm.sign_swap hab, Units.neg_smul, one_smul,
      add_neg_cancel]
  · obtain ⟨a, b, hab, he⟩ := betaNumber_add_weight_stembridge T (mem_filter.mp hT).2
    rw [heq] at he
    refine hne (alternant_eq_zero_of_not_injective fun hinj => hab (hinj ?_))
    simpa using congrFun he a
  · refine mem_filter.mpr ⟨mem_univ _, fun h => (mem_filter.mp hT).2 ?_⟩
    rwa [coe_stembridge, SemistandardYoungTableau.isYamanouchi_stembridgeInvolution_iff] at h

/-! ### The Littlewood–Richardson rule -/

namespace BoundedSSYT

variable {lam μ : YoungDiagram}

/-- **A `λ`-Yamanouchi tableau has a shape**: the partition `ν` of `|λ| + |μ|` whose row lengths
are `λ + c(T)`. It is unique, as the row lengths determine a partition. -/
private theorem existsUnique_rowLen_eq (hlam : lam.colLen 0 ≤ N) (T : BoundedSSYT N μ)
    (hT : T.1.IsYamanouchi lam) :
    ∃! ν : (lam.card + μ.card).Partition,
      ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i := by
  have hanti : Antitone fun i : Fin N => lam.rowLen i + T.1.content i :=
    fun i i' hii' => hT.antitone (Fin.val_le_of_le hii')
  set Y := YoungDiagram.ofRowLensFin _ hanti
  have hY : ∀ i, lam.rowLen i + T.1.content i = Y.rowLen i := fun i => by
    by_cases hi : i < N
    · exact (YoungDiagram.rowLen_ofRowLensFin _ hanti ⟨i, hi⟩).symm
    · rw [YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ hanti (not_lt.mp hi),
        YoungDiagram.rowLen_eq_zero_of_colLen_le (hlam.trans (not_lt.mp hi)),
        content_eq_zero T (not_lt.mp hi)]
  have hcard : Y.card = lam.card + μ.card := by
    rw [YoungDiagram.card_ofRowLensFin, sum_add_distrib, ← sum_weight T,
      YoungDiagram.card_eq_sum_range_rowLen lam hlam, Fin.sum_univ_eq_sum_range
        (fun i => lam.rowLen i) N]
    simp
  refine ⟨Y.toPartition hcard, fun i => by rw [hY, YoungDiagram.ofPartition_toPartition], ?_⟩
  intro ν hν
  refine YoungDiagram.ofPartition_injective (YoungDiagram.rowLen_injective (funext fun i => ?_))
  rw [← hν i, YoungDiagram.ofPartition_toPartition, hY]

end BoundedSSYT

open BoundedSSYT in
open scoped Classical in
/-- The Littlewood–Richardson rule over `ℤ`, for `λ` with at most `N` rows. -/
private theorem diagramSchurPoly_mul_diagramSchurPoly_int {lam μ : YoungDiagram}
    (hlam : lam.colLen 0 ≤ N) :
    diagramSchurPoly N ℤ lam * diagramSchurPoly N ℤ μ =
      ∑ ν : (lam.card + μ.card).Partition,
        #{T : BoundedSSYT N μ | T.1.IsYamanouchi lam ∧
          ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i} •
          diagramSchurPoly N ℤ (ofPartition ν) := by
  refine mul_right_cancel₀ (alternant_ne_zero_of_injective (injective_staircase N)) ?_
  rw [mul_comm (diagramSchurPoly N ℤ lam), mul_assoc, diagramSchurPoly_mul_alternant N lam hlam,
    diagramSchurPoly_mul_alternant_betaNumber, sum_mul]
  -- Group the `λ`-Yamanouchi tableaux by their shape.
  have hfib : ∀ ν : (lam.card + μ.card).Partition,
      #{T : BoundedSSYT N μ | T.1.IsYamanouchi lam ∧
          ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i} •
          diagramSchurPoly N ℤ (ofPartition ν) * alternant (Fin N) ℤ (fun j => N - 1 - j) =
        ∑ T : BoundedSSYT N μ, if T.1.IsYamanouchi lam ∧
            ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i then
          alternant (Fin N) ℤ (fun j => lam.betaNumber N j + weight T j) else 0 := by
    intro ν
    rw [← sum_filter, smul_mul_assoc, ← sum_const]
    refine sum_congr rfl fun T hT => ?_
    obtain ⟨-, hν⟩ := (mem_filter.mp hT).2
    have hνN : (ofPartition ν).colLen 0 ≤ N := by
      by_contra hlt
      have hmem : ((N, 0) : ℕ × ℕ) ∈ ofPartition ν :=
        YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le hlt)
      have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
      rw [← hν N, YoungDiagram.rowLen_eq_zero_of_colLen_le hlam, content_eq_zero T le_rfl] at this
      omega
    rw [diagramSchurPoly_mul_alternant N _ hνN]
    congr 1
    funext j
    rw [weight_apply, YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def, ← hν j]
    omega
  rw [sum_congr rfl fun ν _ => hfib ν, sum_comm, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · obtain ⟨ν, hν, huniq⟩ := existsUnique_rowLen_eq hlam T hT
    rw [sum_eq_single ν, ite_eq_left ⟨hT, hν⟩]
    · intro ν' _ hne
      exact ite_eq_right fun h => hne (huniq ν' h.2)
    · exact fun h => absurd (mem_univ ν) h
  · exact (sum_eq_zero fun ν _ => ite_eq_right (not_and_of_not_left _ hT)).symm

open scoped Classical in
/-- **The Littlewood–Richardson rule**, in Stembridge's form. The product of the Schur
polynomials of two Young diagrams `λ` and `μ` in the alphabet `Fin N` is the sum, over the
partitions `ν` of `|λ| + |μ|`, of `s_ν` counted with multiplicity the number of semistandard
tableaux `T` of shape `μ` in the alphabet `Fin N` that are `λ`-Yamanouchi and satisfy
`λ + c(T) = ν`. -/
theorem diagramSchurPoly_mul_diagramSchurPoly {R : Type*} [CommSemiring R]
    (lam μ : YoungDiagram) :
    diagramSchurPoly N R lam * diagramSchurPoly N R μ =
      ∑ ν : (lam.card + μ.card).Partition,
        #{T : BoundedSSYT N μ | T.1.IsYamanouchi lam ∧
          ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i} •
          diagramSchurPoly N R (ofPartition ν) := by
  by_cases hlam : lam.colLen 0 ≤ N
  · -- Both sides have natural-number coefficients, so the identity over `ℤ` descends to `ℕ`,
    -- whence it maps to `R`.
    have hℕ : diagramSchurPoly N ℕ lam * diagramSchurPoly N ℕ μ =
        ∑ ν : (lam.card + μ.card).Partition,
          #{T : BoundedSSYT N μ | T.1.IsYamanouchi lam ∧
            ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i} •
            diagramSchurPoly N ℕ (ofPartition ν) :=
      MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective <| by
        simpa [map_diagramSchurPoly, map_sum, map_nsmul] using
          diagramSchurPoly_mul_diagramSchurPoly_int (μ := μ) hlam
    simpa [map_diagramSchurPoly, map_sum, map_nsmul] using
      congrArg (MvPolynomial.map (Nat.castRingHom R)) hℕ
  · -- Both sides vanish: `λ`, and every shape `ν ⊇ λ` on the right, has more than `N` rows.
    have hlt : N < lam.colLen 0 := Nat.lt_of_not_le hlam
    rw [diagramSchurPoly_eq_zero_of_lt_colLen hlt, zero_mul]
    refine (sum_eq_zero fun ν _ => ?_).symm
    rcases eq_or_ne (#{T : BoundedSSYT N μ | T.1.IsYamanouchi lam ∧
        ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i}) 0 with h0 | h0
    · rw [h0, zero_smul]
    obtain ⟨T, hT⟩ := card_ne_zero.mp h0
    obtain ⟨-, hν⟩ := (mem_filter.mp hT).2
    have hle : lam ≤ ofPartition ν :=
      YoungDiagram.le_of_forall_rowLen_le fun i => hν i ▸ Nat.le_add_right _ _
    rw [diagramSchurPoly_eq_zero_of_lt_colLen
      (hlt.trans_le (YoungDiagram.colLen_le_of_le hle 0)), smul_zero]

end TauCeti
