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

@[expose] public section

noncomputable section

namespace Matrix

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

/-- Multiplying by the rows `e` of the identity matrix selects the rows `e`. -/
lemma one_submatrix_id_mul [DecidableEq m] {o : Type*} {k : Type*} (e : k → m) (X : Matrix m o R) :
    (1 : Matrix m m R).submatrix e id * X = X.submatrix e id := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- Multiplying by the columns `e` of the identity matrix selects the columns `e`. -/
lemma mul_one_submatrix_id [DecidableEq n] {o : Type*} {k : Type*} (e : k → n) (X : Matrix o n R) :
    X * (1 : Matrix n n R).submatrix id e = X.submatrix id e := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- **Split rank factorisation.** Let `A` be a matrix over a commutative ring with an invertible
`ρ × ρ` minor `B` (rows `e₁`, columns `e₂`) and all of whose `(ρ + 1) × (ρ + 1)` minors vanish.
Then `A = L * M` with `L' * L = 1` and `M * M' = 1`, where `L = A[:, e₂] B⁻¹` and `M = A[e₁, :]`. -/
theorem exists_mul_eq_of_isUnit_det_submatrix (A : Matrix m n R) {ρ : ℕ} (e₁ : Fin ρ → m)
    (e₂ : Fin ρ → n) (hB : IsUnit (A.submatrix e₁ e₂).det)
    (hA : ∀ (f₁ : Fin (ρ + 1) → m) (f₂ : Fin (ρ + 1) → n), (A.submatrix f₁ f₂).det = 0) :
    ∃ (L : Matrix m (Fin ρ) R) (M : Matrix (Fin ρ) n R) (L' : Matrix (Fin ρ) m R)
      (M' : Matrix n (Fin ρ) R), A = L * M ∧ L' * L = 1 ∧ M * M' = 1 := by
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
      exact hA _ _
    have hN' : N = fromBlocks B (A.submatrix e₁ fun _ : Fin 1 ↦ j)
        (A.submatrix (fun _ : Fin 1 ↦ i) e₂) (Matrix.of fun _ _ : Fin 1 ↦ A i j) := by
      ext (a | a) (b | b) <;> rfl
    rw [hN', det_fromBlocks₁₁, Matrix.det_unique (n := Fin 1)] at hN
    have h2 := ((isUnit_det_of_invertible B).mul_right_eq_zero).1 hN
    rw [Matrix.sub_apply, sub_eq_zero, invOf_eq_nonsing_inv] at h2
    refine h2.trans ?_
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  · rw [← Matrix.mul_assoc, one_submatrix_id_mul]
    exact mul_nonsing_inv B hB
  · rw [← Matrix.mul_assoc, mul_one_submatrix_id]
    exact mul_nonsing_inv B hB

end Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

/-- A split rank factorisation `e = L * M` of an idempotent matrix satisfies `M * L = 1`. -/
lemma mul_eq_one_of_isIdempotentElem {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    {L : Matrix m ρ R} {M : Matrix ρ m R} {L' : Matrix ρ m R} {M' : Matrix m ρ R}
    (he : L * M * (L * M) = L * M) (hL : L' * L = 1) (hM : M * M' = 1) : M * L = 1 := by
  calc M * L = L' * L * (M * L) * (M * M') := by rw [hL, hM, Matrix.one_mul, Matrix.mul_one]
    _ = L' * (L * M * (L * M)) * M' := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [he, ← Matrix.mul_assoc, hL, Matrix.one_mul, hM]

variable {K : Type*} [Field K]

/-- Over a field, if `P + e + Q = 1` then the ranks of `P`, `e` and `Q` add up to at least the
size of the matrices. -/
lemma card_le_rank_add_rank_add_rank [DecidableEq m] (P e Q : Matrix m m K)
    (h : P + e + Q = 1) : Fintype.card m ≤ P.rank + e.rank + Q.rank := by
  rw [← Matrix.rank_one (R := K) (n := m), ← h]
  exact (rank_add_le _ _).trans (Nat.add_le_add_right (rank_add_le _ _) _)

/-- Over a field, let `e` be an idempotent and `A₁`, `A₂` matrices with `e A₁ = 0`, `A₂ e = 0` and
`A₂ A₁ = 0`. Then the ranks of `e`, `A₁` and `A₂` add up to at most the size of `e`: the images of
`e` and `A₁` are independent and both lie in the kernel of `A₂`. -/
lemma rank_add_rank_add_rank_le {a c : Type*} [Fintype a] (e : Matrix m m K)
    (A₁ : Matrix m a K) (A₂ : Matrix c m K) (he : e * e = e) (h₁ : e * A₁ = 0) (h₂ : A₂ * e = 0)
    (h₃ : A₂ * A₁ = 0) : e.rank + A₁.rank + A₂.rank ≤ Fintype.card m := by
  classical
  have hdisj : LinearMap.range e.mulVecLin ⊓ LinearMap.range A₁.mulVecLin = ⊥ := by
    refine eq_bot_iff.2 fun x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ↦ ?_
    simp only [Matrix.mulVecLin_apply] at hy hz
    have h1 : e *ᵥ x = x := by rw [← hy, Matrix.mulVec_mulVec, he]
    have h2 : e *ᵥ x = 0 := by rw [← hz, Matrix.mulVec_mulVec, h₁, Matrix.zero_mulVec]
    exact (Submodule.mem_bot K).2 (h1.symm.trans h2)
  have hle : LinearMap.range e.mulVecLin ⊔ LinearMap.range A₁.mulVecLin ≤
      LinearMap.ker A₂.mulVecLin := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨y, rfl⟩ <;>
      simp [LinearMap.mem_ker, Matrix.mulVec_mulVec, h₂, h₃]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e.mulVecLin)
    (LinearMap.range A₁.mulVecLin)
  rw [hdisj, finrank_bot, add_zero] at hsum
  have hker := LinearMap.finrank_range_add_finrank_ker A₂.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hker
  have := Submodule.finrank_mono hle
  simp only [Matrix.rank]
  omega

end Matrix

namespace Matrix

/-! ### Splitting the middle term of a complex of free modules -/

section SplitComplex

variable {R : Type*} [CommRing R] {a b c ρ₁ ρ₂ : Type*} [Fintype a] [Fintype b] [Fintype c]
  [Fintype ρ₁] [Fintype ρ₂] [DecidableEq b] [DecidableEq ρ₁] [DecidableEq ρ₂]
  {A₁ : Matrix b a R} {A₂ : Matrix c b R}
  {L₁ : Matrix b ρ₁ R} {M₁ : Matrix ρ₁ a R} {L₁' : Matrix ρ₁ b R} {M₁' : Matrix a ρ₁ R}
  {L₂ : Matrix c ρ₂ R} {M₂ : Matrix ρ₂ b R} {L₂' : Matrix ρ₂ c R} {M₂' : Matrix b ρ₂ R}

omit [DecidableEq b] in
/-- With split factorisations `A₁ = L₁ M₁` and `A₂ = L₂ M₂` of two composable matrices with
`A₂ A₁ = 0`, also `M₂ L₁ = 0`. -/
lemma mul_eq_zero_of_split (h : A₂ * A₁ = 0) (hA₁ : A₁ = L₁ * M₁) (hM₁ : M₁ * M₁' = 1)
    (hA₂ : A₂ = L₂ * M₂) (hL₂ : L₂' * L₂ = 1) : M₂ * L₁ = 0 :=
  calc M₂ * L₁ = L₂' * L₂ * M₂ * L₁ * (M₁ * M₁') := by
        rw [hL₂, hM₁, Matrix.one_mul, Matrix.mul_one]
    _ = L₂' * (A₂ * A₁) * M₁' := by simp only [hA₁, hA₂, Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

variable (L₁ L₁' M₂ M₂') in
/-- The idempotent `(1 - L₁ L₁') (1 - M₂' M₂)` cutting out the cohomology of a complex of free
modules in the middle degree, given split factorisations of the two differentials. -/
def splitIdempotent : Matrix b b R := (1 - L₁ * L₁') * (1 - M₂' * M₂)

lemma splitIdempotent_mul_self (hL₁ : L₁' * L₁ = 1) (hM₂ : M₂ * M₂' = 1) (hML : M₂ * L₁ = 0) :
    splitIdempotent L₁ L₁' M₂ M₂' * splitIdempotent L₁ L₁' M₂ M₂' =
      splitIdempotent L₁ L₁' M₂ M₂' := by
  have h₁ (Z : Matrix ρ₁ b R) : L₁' * (L₁ * Z) = Z := by
    rw [← Matrix.mul_assoc, hL₁, Matrix.one_mul]
  have h₂ (Z : Matrix ρ₂ b R) : M₂ * (M₂' * Z) = Z := by
    rw [← Matrix.mul_assoc, hM₂, Matrix.one_mul]
  have h₃ (Z : Matrix ρ₁ b R) : M₂ * (L₁ * Z) = 0 := by
    rw [← Matrix.mul_assoc, hML, Matrix.zero_mul]
  unfold splitIdempotent
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
  unfold splitIdempotent
  simp only [hA₁, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, h₁, h₃, Matrix.mul_zero, sub_self]

omit [Fintype c] [DecidableEq ρ₁] in
lemma mul_splitIdempotent (hA₂ : A₂ = L₂ * M₂) (hM₂ : M₂ * M₂' = 1) (hML : M₂ * L₁ = 0) :
    A₂ * splitIdempotent L₁ L₁' M₂ M₂' = 0 := by
  have h₂ (Z : Matrix ρ₂ b R) : M₂ * (M₂' * Z) = Z := by
    rw [← Matrix.mul_assoc, hM₂, Matrix.one_mul]
  have h₃ (Z : Matrix ρ₁ b R) : M₂ * (L₁ * Z) = 0 := by
    rw [← Matrix.mul_assoc, hML, Matrix.zero_mul]
  unfold splitIdempotent
  simp only [hA₂, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, h₂, h₃, Matrix.mul_zero, sub_zero, sub_self]

omit [DecidableEq ρ₁] [DecidableEq ρ₂] in
lemma add_splitIdempotent_add :
    L₁ * L₁' + splitIdempotent L₁ L₁' M₂ M₂' + (1 - L₁ * L₁') * (M₂' * M₂) = 1 := by
  unfold splitIdempotent
  rw [add_assoc, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one, add_sub_cancel]

/-- **Splitting data for the cohomology of a complex of free modules.** Given split factorisations
`A₁ = L₁ M₁`, `A₂ = L₂ M₂` of composable matrices with `A₂ A₁ = 0`, and a split factorisation
`ε = L₃ M₃`, `M₃ L₃ = 1`, of the idempotent `ε = (1 - L₁ L₁') (1 - M₂' M₂)`, the matrices `L₃`
and `M₃` exhibit `R^k` as a retract of the middle term, landing in the kernel of `A₂`, killing the
image of `A₁`, and with `L₃ M₃ + A₁ σ + τ A₂ = 1` for `σ = M₁' L₁'`, `τ = (1 - L₁ L₁') M₂' L₂'`. -/
lemma split_homology_data {k : Type*} [Fintype k] [DecidableEq k] (h : A₂ * A₁ = 0)
    (hA₁ : A₁ = L₁ * M₁) (hL₁ : L₁' * L₁ = 1) (hM₁ : M₁ * M₁' = 1)
    (hA₂ : A₂ = L₂ * M₂) (hL₂ : L₂' * L₂ = 1) (hM₂ : M₂ * M₂' = 1)
    {L₃ : Matrix b k R} {M₃ : Matrix k b R} (hε : splitIdempotent L₁ L₁' M₂ M₂' = L₃ * M₃)
    (h₃ : M₃ * L₃ = 1) :
    A₂ * L₃ = 0 ∧ M₃ * A₁ = 0 ∧
      L₃ * M₃ + A₁ * (M₁' * L₁') + (1 - L₁ * L₁') * M₂' * L₂' * A₂ = 1 := by
  have hML := mul_eq_zero_of_split h hA₁ hM₁ hA₂ hL₂
  refine ⟨?_, ?_, ?_⟩
  · calc A₂ * L₃ = A₂ * (L₃ * M₃) * L₃ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h₃, Matrix.mul_one]
      _ = 0 := by rw [← hε, mul_splitIdempotent hA₂ hM₂ hML, Matrix.zero_mul]
  · calc M₃ * A₁ = M₃ * (L₃ * M₃) * A₁ := by rw [← Matrix.mul_assoc, h₃, Matrix.one_mul]
      _ = 0 := by
          rw [← hε, Matrix.mul_assoc, splitIdempotent_mul hA₁ hL₁ hML, Matrix.mul_zero]
  · have e₁ : A₁ * (M₁' * L₁') = L₁ * L₁' := by
      rw [hA₁, Matrix.mul_assoc, ← Matrix.mul_assoc M₁, hM₁, Matrix.one_mul]
    have e₂ : (1 - L₁ * L₁') * M₂' * L₂' * A₂ = (1 - L₁ * L₁') * (M₂' * M₂) := by
      rw [hA₂, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc L₂', hL₂, Matrix.one_mul]
    rw [← hε, e₁, e₂]
    refine Eq.trans ?_ (add_splitIdempotent_add (L₁ := L₁) (L₁' := L₁') (M₂ := M₂) (M₂' := M₂'))
    abel

omit [Fintype a] [Fintype c] [DecidableEq ρ₁] [DecidableEq ρ₂] in
lemma splitIdempotent_map {S : Type*} [CommRing S] (f : R →+* S) :
    (splitIdempotent L₁ L₁' M₂ M₂').map f =
      splitIdempotent (L₁.map f) (L₁'.map f) (M₂.map f) (M₂'.map f) := by
  simp [splitIdempotent, Matrix.map_mul, Matrix.map_sub, Matrix.map_one]

end SplitComplex

/-- A split factorisation stays one after applying a ring homomorphism. -/
lemma split_map {R S : Type*} [CommRing R] [CommRing S] {m n ρ : Type*} [Fintype m] [Fintype n]
    [Fintype ρ] [DecidableEq ρ] {A : Matrix m n R} {L : Matrix m ρ R} {M : Matrix ρ n R}
    {L' : Matrix ρ m R} {M' : Matrix n ρ R} (f : R →+* S)
    (h : A = L * M ∧ L' * L = 1 ∧ M * M' = 1) :
    A.map f = L.map f * M.map f ∧ L'.map f * L.map f = 1 ∧ M.map f * M'.map f = 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨by rw [h₁, Matrix.map_mul], ?_, ?_⟩
  · rw [← Matrix.map_mul, h₂, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, h₃, Matrix.map_one _ (map_zero f) (map_one f)]

end Matrix
