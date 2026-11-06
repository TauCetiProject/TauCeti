/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import TauCeti.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Split rank factorizations

An invertible maximal minor gives a split rank factorization. Split factorizations of the
differentials give an idempotent cutting out homology, compatibly with extension of scalars.

## Source

Adapted from `Jacobian/LinearAlgebra/Matrix/SplitFactorization.lean` in the Jacobian library,
accepted release `baef7723da528551b7d2f93bd9a9a53303b04dbc`.
-/

public section

noncomputable section

namespace Matrix

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

/-- A factorization with a left inverse for the left factor and a right inverse for the
right factor. -/
structure IsSplitFactorization {S : Type*} [Semiring S] {a b r : Type*}
    [Fintype a] [Fintype b] [Fintype r] [DecidableEq r]
    (A : Matrix a b S) (L : Matrix a r S) (M : Matrix r b S)
    (L' : Matrix r a S) (M' : Matrix b r S) : Prop where
  eq_mul : A = L * M
  left_inv : L' * L = 1
  right_inv : M * M' = 1

/-- **Split rank factorisation.** Let `A` be a matrix over a commutative ring with an invertible
`ρ × ρ` minor `B` (rows `e₁`, columns `e₂`) and all of whose `(ρ + 1) × (ρ + 1)` minors vanish.
Then `A = L * M` with `L' * L = 1` and `M * M' = 1`, where `L = A[:, e₂] B⁻¹` and `M = A[e₁, :]`. -/
theorem exists_mul_eq_of_isUnit_det_submatrix (A : Matrix m n R) {ρ : ℕ} (e₁ : Fin ρ → m)
    (e₂ : Fin ρ → n) (hB : IsUnit (A.submatrix e₁ e₂).det)
    (hA : ∀ (f₁ : Fin (ρ + 1) ↪ m) (f₂ : Fin (ρ + 1) ↪ n), (A.submatrix f₁ f₂).det = 0) :
    ∃ (L : Matrix m (Fin ρ) R) (M : Matrix (Fin ρ) n R) (L' : Matrix (Fin ρ) m R)
      (M' : Matrix n (Fin ρ) R), IsSplitFactorization A L M L' M' := by
  classical
  set B := A.submatrix e₁ e₂ with hBdef
  let := invertibleOfIsUnitDet B hB
  refine ⟨A.submatrix id e₂ * B⁻¹, A.submatrix e₁ id, (1 : Matrix m m R).submatrix e₁ id,
    (1 : Matrix n n R).submatrix id e₂ * B⁻¹, ?_, ?_, ?_⟩
  · ext i j
    let N : Matrix (Fin ρ ⊕ Fin 1) (Fin ρ ⊕ Fin 1) R :=
      A.submatrix (Sum.elim e₁ fun _ ↦ i) (Sum.elim e₂ fun _ ↦ j)
    have hN : N.det = 0 := by
      rw [← det_submatrix_equiv_self finSumFinEquiv.symm N]
      by_cases hrow : Function.Injective (Sum.elim e₁ (fun _ : Fin 1 ↦ i) ∘
          finSumFinEquiv.symm)
      · by_cases hcol : Function.Injective (Sum.elim e₂ (fun _ : Fin 1 ↦ j) ∘
            finSumFinEquiv.symm)
        · exact hA ⟨_, hrow⟩ ⟨_, hcol⟩
        · obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hcol
          exact det_zero_of_column_eq hne (fun k ↦ congrArg (A _ ) huv)
      · obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hrow
        exact det_zero_of_row_eq hne (by ext k; exact congrArg (fun x ↦ A x _) huv)
    have hN' : N = fromBlocks B (A.submatrix e₁ fun _ : Fin 1 ↦ j)
        (A.submatrix (fun _ : Fin 1 ↦ i) e₂) (Matrix.of fun _ _ : Fin 1 ↦ A i j) := by
      ext (a | a) (b | b) <;> simp [N, B]
    rw [hN', det_fromBlocks₁₁, Matrix.det_unique (n := Fin 1)] at hN
    have h2 := ((isUnit_det_of_invertible B).mul_right_eq_zero).1 hN
    rw [Matrix.sub_apply, sub_eq_zero, invOf_eq_nonsing_inv] at h2
    refine h2.trans ?_
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  · rw [← Matrix.mul_assoc]
    have hrows := one_submatrix_mul e₁ (Equiv.refl m) (A.submatrix id e₂)
    simp only [Equiv.coe_refl, Function.comp_id, submatrix_submatrix,
      Function.id_comp] at hrows
    rw [hrows]
    exact mul_nonsing_inv B hB
  · rw [← Matrix.mul_assoc]
    have hcols := mul_submatrix_one (Equiv.refl n) e₂ (A.submatrix e₁ id)
    simp only [Equiv.coe_refl, Function.comp_id, submatrix_submatrix,
      Function.id_comp] at hcols
    rw [hcols]
    exact mul_nonsing_inv B hB

end Matrix



namespace Matrix

/-! ### Splitting the middle term of a complex of free modules -/

section SplitComplex

variable {R : Type*} [Ring R] {a b c ρ₁ ρ₂ : Type*} [Fintype a] [Fintype b] [Fintype c]
  [Fintype ρ₁] [Fintype ρ₂] [DecidableEq b] [DecidableEq ρ₁] [DecidableEq ρ₂]
  {A₁ : Matrix b a R} {A₂ : Matrix c b R}
  {L₁ : Matrix b ρ₁ R} {M₁ : Matrix ρ₁ a R} {L₁' : Matrix ρ₁ b R} {M₁' : Matrix a ρ₁ R}
  {L₂ : Matrix c ρ₂ R} {M₂ : Matrix ρ₂ b R} {L₂' : Matrix ρ₂ c R} {M₂' : Matrix b ρ₂ R}

omit [DecidableEq b] in
/-- With split factorisations `A₁ = L₁ M₁` and `A₂ = L₂ M₂` of two composable matrices with
`A₂ A₁ = 0`, also `M₂ L₁ = 0`. -/
lemma mul_eq_zero_of_isSplitFactorization (h : A₂ * A₁ = 0)
    (h₁ : IsSplitFactorization A₁ L₁ M₁ L₁' M₁')
    (h₂ : IsSplitFactorization A₂ L₂ M₂ L₂' M₂') : M₂ * L₁ = 0 := by
  obtain ⟨hA₁, _, hM₁⟩ := h₁
  obtain ⟨hA₂, hL₂, _⟩ := h₂
  exact
  calc M₂ * L₁ = L₂' * L₂ * M₂ * L₁ * (M₁ * M₁') := by
        rw [hL₂, hM₁, Matrix.one_mul, Matrix.mul_one]
    _ = L₂' * (A₂ * A₁) * M₁' := by simp only [hA₁, hA₂, Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

variable (L₁ L₁' M₂ M₂') in
/-- The idempotent `(1 - L₁ L₁') (1 - M₂' M₂)` cutting out the cohomology of a complex of free
modules in the middle degree, given split factorisations of the two differentials. -/
def splitIdempotent : Matrix b b R := (1 - L₁ * L₁') * (1 - M₂' * M₂)

omit [DecidableEq ρ₁] [DecidableEq ρ₂] in
/-- The defining formula of the homology projector. -/
lemma splitIdempotent_def : splitIdempotent L₁ L₁' M₂ M₂' =
    (1 - L₁ * L₁') * (1 - M₂' * M₂) := (rfl)

lemma splitIdempotent_mul_self (hL₁ : L₁' * L₁ = 1) (hM₂ : M₂ * M₂' = 1) (hML : M₂ * L₁ = 0) :
    splitIdempotent L₁ L₁' M₂ M₂' * splitIdempotent L₁ L₁' M₂ M₂' =
      splitIdempotent L₁ L₁' M₂ M₂' := by
  have h₁ (Z : Matrix ρ₁ b R) : L₁' * (L₁ * Z) = Z := by
    rw [← Matrix.mul_assoc, hL₁, Matrix.one_mul]
  have h₂ (Z : Matrix ρ₂ b R) : M₂ * (M₂' * Z) = Z := by
    rw [← Matrix.mul_assoc, hM₂, Matrix.one_mul]
  have h₃ (Z : Matrix ρ₁ b R) : M₂ * (L₁ * Z) = 0 := by
    rw [← Matrix.mul_assoc, hML, Matrix.zero_mul]
  simp only [splitIdempotent_def]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    h₁, h₂, h₃, Matrix.mul_zero, sub_zero]
  abel

omit [Fintype a] [DecidableEq ρ₂] in
lemma splitIdempotent_mul (hA₁ : A₁ = L₁ * M₁) (hL₁ : L₁' * L₁ = 1) (hML : M₂ * L₁ = 0) :
    splitIdempotent L₁ L₁' M₂ M₂' * A₁ = 0 := by
  have h₁ (Z : Matrix ρ₁ a R) : L₁' * (L₁ * Z) = Z := by
    rw [← Matrix.mul_assoc, hL₁, Matrix.one_mul]
  have h₃ (Z : Matrix ρ₁ a R) : M₂ * (L₁ * Z) = 0 := by
    rw [← Matrix.mul_assoc, hML, Matrix.zero_mul]
  rw [splitIdempotent_def]
  simp only [hA₁, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, h₁, h₃, Matrix.mul_zero, sub_self]

omit [Fintype c] [DecidableEq ρ₁] in
lemma mul_splitIdempotent (hA₂ : A₂ = L₂ * M₂) (hM₂ : M₂ * M₂' = 1) (hML : M₂ * L₁ = 0) :
    A₂ * splitIdempotent L₁ L₁' M₂ M₂' = 0 := by
  have h₂ (Z : Matrix ρ₂ b R) : M₂ * (M₂' * Z) = Z := by
    rw [← Matrix.mul_assoc, hM₂, Matrix.one_mul]
  have h₃ (Z : Matrix ρ₁ b R) : M₂ * (L₁ * Z) = 0 := by
    rw [← Matrix.mul_assoc, hML, Matrix.zero_mul]
  rw [splitIdempotent_def]
  simp only [hA₂, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, h₂, h₃, Matrix.mul_zero, sub_zero, sub_self]

omit [DecidableEq ρ₁] [DecidableEq ρ₂] in
lemma add_splitIdempotent_add :
    L₁ * L₁' + splitIdempotent L₁ L₁' M₂ M₂' + (1 - L₁ * L₁') * (M₂' * M₂) = 1 := by
  rw [splitIdempotent_def]
  rw [add_assoc, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one, add_sub_cancel]

omit [Fintype a] [Fintype c] [DecidableEq ρ₁] in
/-- A split factor of the homology projector lands in the kernel of the second differential. -/
lemma mul_eq_zero_of_splitIdempotent_eq_mul {k : Type*} [Fintype k] [DecidableEq k]
    (hA₂ : A₂ = L₂ * M₂) (hM₂ : M₂ * M₂' = 1) (hML : M₂ * L₁ = 0)
    {L₃ : Matrix b k R} {M₃ : Matrix k b R}
    (hε : splitIdempotent L₁ L₁' M₂ M₂' = L₃ * M₃) (h₃ : M₃ * L₃ = 1) :
    A₂ * L₃ = 0 := by
  calc A₂ * L₃ = A₂ * (L₃ * M₃) * L₃ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h₃, Matrix.mul_one]
    _ = 0 := by rw [← hε, mul_splitIdempotent hA₂ hM₂ hML, Matrix.zero_mul]

omit [Fintype a] [Fintype c] [DecidableEq ρ₂] in
/-- A split retraction of the homology projector kills the first differential. -/
lemma mul_eq_zero_of_splitIdempotent_eq_mul' {k : Type*} [Fintype k] [DecidableEq k]
    (hA₁ : A₁ = L₁ * M₁) (hL₁ : L₁' * L₁ = 1) (hML : M₂ * L₁ = 0)
    {L₃ : Matrix b k R} {M₃ : Matrix k b R}
    (hε : splitIdempotent L₁ L₁' M₂ M₂' = L₃ * M₃) (h₃ : M₃ * L₃ = 1) :
    M₃ * A₁ = 0 := by
  calc M₃ * A₁ = M₃ * (L₃ * M₃) * A₁ := by
          rw [← Matrix.mul_assoc, h₃, Matrix.one_mul]
    _ = 0 := by
        rw [← hε, Matrix.mul_assoc, splitIdempotent_mul hA₁ hL₁ hML, Matrix.mul_zero]

/-- The homology projector and two null-homotopy terms sum to the identity. -/
lemma splitIdempotent_add_add_eq_one (hA₁ : A₁ = L₁ * M₁) (hM₁ : M₁ * M₁' = 1)
    (hA₂ : A₂ = L₂ * M₂) (hL₂ : L₂' * L₂ = 1) :
    splitIdempotent L₁ L₁' M₂ M₂' + A₁ * (M₁' * L₁') +
      ((1 - L₁ * L₁') * M₂' * L₂') * A₂ = 1 := by
  have e₁ : A₁ * (M₁' * L₁') = L₁ * L₁' := by
    rw [hA₁, Matrix.mul_assoc, ← Matrix.mul_assoc M₁, hM₁, Matrix.one_mul]
  have e₂ : (1 - L₁ * L₁') * M₂' * L₂' * A₂ = (1 - L₁ * L₁') * (M₂' * M₂) := by
    rw [hA₂, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc L₂', hL₂, Matrix.one_mul]
  rw [e₁, e₂, add_comm _ (L₁ * L₁')]
  exact add_splitIdempotent_add

omit [Fintype a] [Fintype c] [DecidableEq ρ₁] [DecidableEq ρ₂] in
@[simp]
lemma splitIdempotent_map {S : Type*} [Ring S] (f : R →+* S) :
    (splitIdempotent L₁ L₁' M₂ M₂').map f =
      splitIdempotent (L₁.map f) (L₁'.map f) (M₂.map f) (M₂'.map f) := by
  simp [splitIdempotent_def, Matrix.map_mul, Matrix.map_sub, Matrix.map_one]

end SplitComplex

/-- A split factorisation stays one after applying a ring homomorphism. -/
lemma IsSplitFactorization.map {R S : Type*} [Semiring R] [Semiring S]
    {m n ρ : Type*} [Fintype m] [Fintype n]
    [Fintype ρ] [DecidableEq ρ] {A : Matrix m n R} {L : Matrix m ρ R} {M : Matrix ρ n R}
    {L' : Matrix ρ m R} {M' : Matrix n ρ R} (f : R →+* S)
    (h : IsSplitFactorization A L M L' M') :
    IsSplitFactorization (A.map f) (L.map f) (M.map f) (L'.map f) (M'.map f) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨by rw [h₁, Matrix.map_mul], ?_, ?_⟩
  · rw [← Matrix.map_mul, h₂, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, h₃, Matrix.map_one _ (map_zero f) (map_one f)]

end Matrix
