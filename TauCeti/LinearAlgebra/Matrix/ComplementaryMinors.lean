/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import TauCeti.LinearAlgebra.Matrix.SplitFactorization
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Complexes of finite free modules split by complementary minors

Let `A : Matrix ι₁ ι₀ R` and `B : Matrix ι₂ ι₁ R` over a commutative ring satisfy
`B * A = 0`. If `A` has an invertible `a × a` minor and `B` an invertible `b × b` minor with
`a + b = |ι₁|`, then both matrices have split rank factorizations `A = L₁ M₁`, `B = L₂ M₂` with
`L₁ L₁' + M₂' M₂ = 1`; in particular the complex is split exact at `R^{ι₁}`
(`Matrix.exists_split_of_isUnit_det_submatrix`).

Over a ring `S` with a ring homomorphism `ψ : S →+* K` to a field such that every element not
killed by `ψ` is a unit (for instance a local ring and its residue field), this applies as soon as
the ranks of `A` and `B` at `ψ` add up to `|ι₁|` (`Matrix.exists_split_of_rank_map_add_eq`).
For a split complex, the homology dimension is the rank of the middle term minus the ranks of
the two differentials (`Matrix.rank_splitIdempotent_map`). These are the linear algebra
prerequisites for local splitting and cohomology-and-base-change criteria.

## Source

Adapted from `Jacobian/LinearAlgebra/Matrix/ComplementaryMinors.lean` in the Jacobian library,
accepted release `baef7723da528551b7d2f93bd9a9a53303b04dbc`.
-/

@[expose] public section

noncomputable section

open Matrix

namespace Matrix

section Ring

variable {R : Type*} [CommRing R] {ι₀ ι₁ ι₂ α β : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
  [Fintype α] [Fintype β] [DecidableEq ι₁] [DecidableEq α]
  [DecidableEq β]

/-- **Splitting a complex of free modules by complementary invertible minors.** Let `B * A = 0`
for matrices `A : R^{ι₀} → R^{ι₁}` and `B : R^{ι₁} → R^{ι₂}` over a commutative ring. If an
`a × a` minor of `A` and a `b × b` minor of `B` are units, with `a + b = |ι₁|`, then `A` and `B`
have split rank factorisations `A = L₁ M₁` through `R^a` and `B = L₂ M₂` through `R^b`, with
`L₁ L₁' + M₂' M₂ = 1`. -/
theorem exists_split_of_isUnit_det_submatrix (A : Matrix ι₁ ι₀ R) (B : Matrix ι₂ ι₁ R)
    (hBA : B * A = 0) (e₁ : α → ι₁) (e₀ : α → ι₀) (hA : IsUnit (A.submatrix e₁ e₀).det)
    (f₂ : β → ι₂) (f₁ : β → ι₁) (hB : IsUnit (B.submatrix f₂ f₁).det)
    (hcard : Fintype.card α + Fintype.card β = Fintype.card ι₁) :
    ∃ (L₁ : Matrix ι₁ α R) (M₁ : Matrix α ι₀ R) (L₁' : Matrix α ι₁ R) (M₁' : Matrix ι₀ α R)
      (L₂ : Matrix ι₂ β R) (M₂ : Matrix β ι₁ R) (L₂' : Matrix β ι₂ R) (M₂' : Matrix ι₁ β R),
      (A = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1) ∧
        (B = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) ∧ L₁ * L₁' + M₂' * M₂ = 1 := by
  classical
  set A' : Matrix ι₁ α R := A.submatrix id e₀
  set B' : Matrix β ι₁ R := B.submatrix f₂ id
  set L : Matrix α ι₁ R := (A.submatrix e₁ e₀)⁻¹ * (1 : Matrix ι₁ ι₁ R).submatrix e₁ id
  set S : Matrix ι₁ β R := (1 : Matrix ι₁ ι₁ R).submatrix id f₁ * (B.submatrix f₂ f₁)⁻¹
  set s₀ : Matrix ι₀ α R := (1 : Matrix ι₀ ι₀ R).submatrix id e₀
  set t₂ : Matrix β ι₂ R := (1 : Matrix ι₂ ι₂ R).submatrix f₂ id
  have hAs : A * s₀ = A' := mul_one_submatrix_id e₀ A
  have htB : t₂ * B = B' := one_submatrix_id_mul f₂ B
  have hLA : L * A' = 1 := by
    have : (1 : Matrix ι₁ ι₁ R).submatrix e₁ id * A' = A.submatrix e₁ e₀ := by
      rw [one_submatrix_id_mul]
      rfl
    rw [Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hA]
  have hBS : B' * S = 1 := by
    have : B' * (1 : Matrix ι₁ ι₁ R).submatrix id f₁ = B.submatrix f₂ f₁ := by
      rw [mul_one_submatrix_id]
      rfl
    rw [← Matrix.mul_assoc, this, Matrix.mul_nonsing_inv _ hB]
  have hBA' : B' * A' = 0 := by
    rw [← hAs, ← htB, Matrix.mul_assoc, ← Matrix.mul_assoc B, hBA, Matrix.zero_mul,
      Matrix.mul_zero]
  set X := L - L * S * B' with hX
  have hXA : X * A' = 1 := by
    rw [hX, Matrix.sub_mul, hLA, Matrix.mul_assoc, hBA', Matrix.mul_zero, sub_zero]
  have hXS : X * S = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.mul_assoc (L * S), hBS, Matrix.mul_one, sub_self]
  have h1 : fromRows X B' * fromCols A' S = 1 := by
    rw [fromRows_mul_fromCols, hXA, hXS, hBA', hBS, fromBlocks_one]
  obtain ⟨e⟩ : Nonempty (ι₁ ≃ α ⊕ β) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_sum, hcard])⟩
  have h2 : fromCols A' S * fromRows X B' = 1 :=
    (fromCols_mul_fromRows_eq_one_comm e _ _ _ _).2 h1
  rw [fromCols_mul_fromRows] at h2
  have hB'A : B' * A = 0 := by rw [← htB, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hBA'' : B * A' = 0 := by rw [← hAs, ← Matrix.mul_assoc, hBA, Matrix.zero_mul]
  refine ⟨A', X * A, X, s₀, B * S, B', t₂, S, ⟨?_, hXA, ?_⟩, ⟨?_, ?_, hBS⟩, h2⟩
  · calc A = (A' * X + S * B') * A := by rw [h2, Matrix.one_mul]
      _ = A' * (X * A) := by
        rw [Matrix.add_mul, Matrix.mul_assoc S, hB'A, Matrix.mul_zero, add_zero,
          Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hAs, hXA]
  · calc B = B * (A' * X + S * B') := by rw [h2, Matrix.mul_one]
      _ = B * S * B' := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc B A', hBA'', Matrix.zero_mul, zero_add]
        exact (Matrix.mul_assoc _ _ _).symm
  · rw [← Matrix.mul_assoc, htB, hBS]

end Ring

section Field

variable {K : Type*} [Field K] {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]

/-- **Ranks in a split complex over a field.** Let `B * A = 0` over a field, and suppose that the
middle term `K^{ι₁}` is split by matrices `I`, `P` with `P I = 1`, `B I = 0`, `P A = 0` and
`I P + A σ + τ B = 1`. Then `rank A + rank B + |k| = |ι₁|`: the cohomology has dimension `|k|`. -/
theorem rank_add_rank_add_card_eq {k : Type*} [Fintype k] [DecidableEq k] [DecidableEq ι₁]
    (A : Matrix ι₁ ι₀ K) (B : Matrix ι₂ ι₁ K) (I : Matrix ι₁ k K) (P : Matrix k ι₁ K)
    (σ : Matrix ι₀ ι₁ K) (τ : Matrix ι₁ ι₂ K) (hBA : B * A = 0) (hPI : P * I = 1)
    (hBI : B * I = 0) (hPA : P * A = 0) (h : I * P + A * σ + τ * B = 1) :
    A.rank + B.rank + Fintype.card k = Fintype.card ι₁ := by
  have hk : (I * P).rank = Fintype.card k := by
    refine le_antisymm ((rank_mul_le_right _ _).trans (rank_le_card_height P)) ?_
    calc Fintype.card k = (1 : Matrix k k K).rank := (rank_one).symm
      _ = (P * (I * P) * I).rank := by
        rw [← Matrix.mul_assoc, hPI, Matrix.one_mul, hPI]
      _ ≤ (I * P).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hle := rank_add_rank_add_rank_le (I * P) A B
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPI, Matrix.one_mul])
    (by rw [Matrix.mul_assoc, hPA, Matrix.mul_zero])
    (by rw [← Matrix.mul_assoc, hBI, Matrix.zero_mul]) hBA
  have hge := card_le_rank_add_rank_add_rank _ _ _ h
  have h₁ := rank_mul_le_left A σ
  have h₂ := rank_mul_le_right τ B
  omega

omit [Fintype ι₁] in
/-- The rank of a matrix with zero rows appended is its rank. -/
lemma rank_fromRows_zero [Finite ι₁] {κ : Type*} [Finite κ] (A : Matrix ι₁ ι₀ K) :
    (fromRows A (0 : Matrix κ ι₀ K)).rank = A.rank := by
  classical
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite κ
  refine le_antisymm ?_ ?_
  · have : fromRows A (0 : Matrix κ ι₀ K) = fromRows 1 0 * A := by
      rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    rw [this]
    exact rank_mul_le_right _ _
  · have : A = fromCols (1 : Matrix ι₁ ι₁ K) (0 : Matrix ι₁ κ K) *
        fromRows A (0 : Matrix κ ι₀ K) := by
      rw [fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]
    conv_lhs => rw [this]
    exact rank_mul_le_right _ _

omit [Fintype ι₁] in
/-- The rank of a matrix with columns appended is at most its rank plus the number of new
columns. -/
lemma rank_fromCols_le {κ : Type*} [Fintype κ] (A : Matrix ι₁ ι₀ K) (D : Matrix ι₁ κ K) :
    (fromCols A D).rank ≤ A.rank + Fintype.card κ := by
  classical
  have : fromCols A D = A * fromCols (1 : Matrix ι₀ ι₀ K) 0 + D * fromCols 0 1 := by
    rw [mul_fromCols, mul_fromCols, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero,
      Matrix.mul_one]
    ext a (b | b) <;> simp
  rw [this]
  refine (rank_add_le _ _).trans (Nat.add_le_add (rank_mul_le_left _ _) ?_)
  exact (rank_mul_le_left _ _).trans (rank_le_card_width D)

end Field

section Exact

variable {S K : Type*} [CommRing S] [Field K] (ψ : S →+* K)
  {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]

/-- **Splitting at a point where the ranks are complementary.** Let `ψ : S →+* K` be a ring
homomorphism to a field such that every element not killed by `ψ` is a unit. If `B * A = 0` and
the ranks of `A` and `B` at `ψ` add up to `|ι₁|`, then `A` and `B` have split rank factorisations
of these ranks, with `L₁ L₁' + M₂' M₂ = 1`. -/
theorem exists_split_of_rank_map_add_eq [DecidableEq ι₁]
    (hψ : ∀ s, ψ s ≠ 0 → IsUnit s) (A : Matrix ι₁ ι₀ S)
    (B : Matrix ι₂ ι₁ S) (hBA : B * A = 0)
    (h : (A.map ψ).rank + (B.map ψ).rank = Fintype.card ι₁) :
    ∃ (L₁ : Matrix ι₁ (Fin (A.map ψ).rank) S) (M₁ : Matrix (Fin (A.map ψ).rank) ι₀ S)
      (L₁' : Matrix (Fin (A.map ψ).rank) ι₁ S) (M₁' : Matrix ι₀ (Fin (A.map ψ).rank) S)
      (L₂ : Matrix ι₂ (Fin (B.map ψ).rank) S) (M₂ : Matrix (Fin (B.map ψ).rank) ι₁ S)
      (L₂' : Matrix (Fin (B.map ψ).rank) ι₂ S) (M₂' : Matrix ι₁ (Fin (B.map ψ).rank) S),
      (A = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1) ∧
        (B = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) ∧ L₁ * L₁' + M₂' * M₂ = 1 := by
  obtain ⟨e₁, e₀, h₁⟩ :=
    (le_rank_iff_exists_det_submatrix_ne_zero (A := A.map ψ)).1 le_rfl
  obtain ⟨f₂, f₁, h₂⟩ :=
    (le_rank_iff_exists_det_submatrix_ne_zero (A := B.map ψ)).1 le_rfl
  simp only [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h₁ h₂
  exact exists_split_of_isUnit_det_submatrix A B hBA e₁ e₀ (hψ _ h₁) f₂ f₁ (hψ _ h₂)
    (by simpa using h)

/-- The rank at `ψ` of a matrix with a split rank factorisation through `ρ` is `|ρ|`. -/
lemma rank_map_eq_of_split {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {B : Matrix ι₂ ι₁ S}
    {L : Matrix ι₂ ρ S} {M : Matrix ρ ι₁ S} {L' : Matrix ρ ι₂ S} {M' : Matrix ι₁ ρ S}
    (hB : B = L * M ∧ L' * L = 1 ∧ M * M' = 1) : (B.map ψ).rank = Fintype.card ρ := by
  obtain ⟨k, kL, kM⟩ := split_map ψ hB
  refine le_antisymm ?_ ?_
  · rw [k]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  · have : L'.map ψ * B.map ψ * M'.map ψ = 1 := by
      rw [k, Matrix.mul_assoc, Matrix.mul_assoc, kM, Matrix.mul_one, kL]
    calc Fintype.card ρ = (1 : Matrix ρ ρ K).rank := rank_one.symm
      _ ≤ (B.map ψ).rank := by
        rw [← this]
        exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- **Ranks at a point of an exact complex.** Let `B * A = 0`, where `B = L M` has a split rank
factorisation, and suppose that the complex is exact at `S^{ι₁}`: every square matrix `K` with
`B K = 0` is of the form `A V`. Then for every ring homomorphism `ψ` to a field, the ranks of `A`
and `B` at `ψ` add up to `|ι₁|`. -/
theorem rank_map_add_rank_map_eq_of_exact (A : Matrix ι₁ ι₀ S) (B : Matrix ι₂ ι₁ S)
    (hBA : B * A = 0) {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {L : Matrix ι₂ ρ S}
    {M : Matrix ρ ι₁ S} {L' : Matrix ρ ι₂ S} {M' : Matrix ι₁ ρ S}
    (hB : B = L * M ∧ L' * L = 1 ∧ M * M' = 1)
    (hex : ∀ K : Matrix ι₁ ι₁ S, B * K = 0 → ∃ V : Matrix ι₀ ι₁ S, A * V = K) :
    (A.map ψ).rank + (B.map ψ).rank = Fintype.card ι₁ := by
  classical
  have rB := rank_map_eq_of_split ψ hB
  obtain ⟨V, hV⟩ := hex (1 - M' * M) (by
    rw [hB.1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc M M',
      hB.2.2, Matrix.one_mul, sub_self])
  have h₁ : ((1 - M' * M).map ψ).rank ≤ (A.map ψ).rank := by
    rw [← hV, Matrix.map_mul]
    exact rank_mul_le_left _ _
  have h₂ : Fintype.card ι₁ ≤ ((1 - M' * M).map ψ).rank + ((M' * M).map ψ).rank := by
    rw [← rank_one (R := K) (n := ι₁)]
    refine le_of_eq_of_le ?_ (rank_add_le _ _)
    rw [← Matrix.map_add _ (map_add ψ), sub_add_cancel, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have h₃ : ((M' * M).map ψ).rank ≤ Fintype.card ρ := by
    rw [Matrix.map_mul]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have h₄ := rank_add_rank_le_card_of_mul_eq_zero (A := B.map ψ) (B := A.map ψ)
    (by rw [← Matrix.map_mul, hBA, Matrix.map_zero _ (map_zero ψ)])
  omega

end Exact

/-- After mapping to a field, the split homology idempotent has rank equal to the
middle dimension minus the ranks of the two split differentials. -/
lemma rank_splitIdempotent_map {R K : Type*} [CommRing R] [Field K]
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]
    {ρ₁ ρ₂ : ℕ} {A₁ : Matrix b a R} {A₂ : Matrix c b R}
    {L₁ : Matrix b (Fin ρ₁) R} {M₁ : Matrix (Fin ρ₁) a R}
    {L₁' : Matrix (Fin ρ₁) b R} {M₁' : Matrix a (Fin ρ₁) R}
    {L₂ : Matrix c (Fin ρ₂) R} {M₂ : Matrix (Fin ρ₂) b R}
    {L₂' : Matrix (Fin ρ₂) c R} {M₂' : Matrix b (Fin ρ₂) R}
    (h : A₂ * A₁ = 0)
    (h₁ : A₁ = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1)
    (h₂ : A₂ = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) (φ : R →+* K) :
    ((splitIdempotent L₁ L₁' M₂ M₂').map φ).rank = Fintype.card b - ρ₁ - ρ₂ := by
  have hML := mul_eq_zero_of_split h h₁.1 h₁.2.2 h₂.1 h₂.2.1
  obtain ⟨k₁, kL₁, -⟩ := split_map φ h₁
  obtain ⟨k₂, -, kM₂⟩ := split_map φ h₂
  have kML : M₂.map φ * L₁.map φ = 0 := by
    rw [← Matrix.map_mul, hML, Matrix.map_zero _ (map_zero φ)]
  have kA : A₂.map φ * A₁.map φ = 0 := by
    rw [← Matrix.map_mul, h, Matrix.map_zero _ (map_zero φ)]
  rw [splitIdempotent_map]
  have r₁ : (A₁.map φ).rank = ρ₁ := by simpa using rank_map_eq_of_split φ h₁
  have r₂ : (A₂.map φ).rank = ρ₂ := by simpa using rank_map_eq_of_split φ h₂
  have hle := rank_add_rank_add_rank_le _ (A₁.map φ) (A₂.map φ)
    (splitIdempotent_mul_self kL₁ kM₂ kML) (splitIdempotent_mul k₁ kL₁ kML)
    (mul_splitIdempotent k₂ kM₂ kML) kA
  have hge := card_le_rank_add_rank_add_rank _ _ _
    (add_splitIdempotent_add (L₁ := L₁.map φ) (L₁' := L₁'.map φ)
      (M₂ := M₂.map φ) (M₂' := M₂'.map φ))
  have p₁ : (L₁.map φ * L₁'.map φ).rank ≤ ρ₁ :=
    (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp))
  have p₂ : ((1 - L₁.map φ * L₁'.map φ) * (M₂'.map φ * M₂.map φ)).rank ≤ ρ₂ :=
    (rank_mul_le_right _ _).trans
      ((rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp)))
  omega

end Matrix
