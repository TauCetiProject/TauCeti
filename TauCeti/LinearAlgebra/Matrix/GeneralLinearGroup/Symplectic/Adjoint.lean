/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Killing
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Cartan
public import TauCeti.LinearAlgebra.Matrix.SkewAdjoint
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The adjoint action of the symplectic group and its compact part

The symplectic group `Sp(2n, R) = TauCeti.GLSymplectic l R` acts on its Lie algebra
`sp l R = LieAlgebra.Symplectic.sp l R` by conjugation, `Ad(A) X = A X A⁻¹`
(`TauCeti.GLSymplectic.adjoint`). This file computes the kernel of this action and, over an
ordered field, the elements whose adjoint action is orthogonal for the Cartan metric.

A matrix commuting with every element of `sp l R` is scalar
(`Matrix.mem_range_scalar_of_commute_sp`), over every commutative ring: commuting with the long
root vectors `E_(i, n + i)` and `E_(n + i, i)` kills the off-diagonal entries and pairs `i` with
`n + i`, and commuting with `E_(i, j) - E_(n + j, n + i)` compares the diagonal entries at `i`
and `j`. So the kernel of `Ad` is the scalar symplectic matrices, `c • 1` with `c ^ 2 = 1`
(`TauCeti.GLSymplectic.mem_ker_adjoint_iff`), which over a domain is the central subgroup `{±1}`.

Over a field `K` with `2 ≠ 0`, the Killing form `κ` of `sp l K` is `(2 n + 2) trace (X Y)` and
its Cartan involution is `θ X = -Xᵀ` (`LieAlgebra.Symplectic.killingForm_cartanInvolution_apply`).
Pulled back by `Ad(A)`, the form `κ(X, θ Y)` becomes `κ(X, θ (Ad(Aᵀ A) Y))`, where
`Aᵀ A = (θ A)⁻¹ A` for the group Cartan involution `θ A = (Aᵀ)⁻¹`
(`TauCeti.GLSymplectic.killingForm_adjoint_cartanInvolution_adjoint`).

Over an ordered field the *Cartan metric* `-κ(X, θ Y)` is positive definite
(`LieAlgebra.Symplectic.killingForm_cartanInvolution_self_neg`), so `Ad(A)` is orthogonal for it
exactly when `Ad(Aᵀ A) = 1`. Then `Aᵀ A = c • 1` with `c ^ 2 = 1`, and `c ≥ 0` because the
diagonal entries of `Aᵀ A` are sums of squares, so `Aᵀ A = 1`. Hence `Ad(A)` is orthogonal for the
Cartan metric exactly when `A` is an orthogonal matrix
(`TauCeti.GLSymplectic.forall_killingForm_adjoint_cartanInvolution_adjoint_eq_iff`).

Over `ℝ`, the orthogonal symplectic matrices form the realified unitary group `U(n)`
(`TauCeti.GLSymplectic.inf_unitarySubgroup`), a maximal compact subgroup of `Sp(2n, ℝ)`
(`TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`). So the elements of `Ad(Sp(2n, ℝ))`
that are orthogonal for the Cartan metric are exactly those of `Ad(U(n))`
(`TauCeti.GLSymplectic.adjoint_mem_map_GLOrthogonal_subgroupOf_iff`). Since the kernel `{±1}` of
`Ad` lies in `U(n)`, `Ad⁻¹(Ad(U(n))) = U(n)`
(`TauCeti.GLSymplectic.comap_map_adjoint_GLOrthogonal_subgroupOf`), over every commutative ring.

## Main definitions

* `TauCeti.GLSymplectic.adjoint`: the adjoint action `Ad(A) X = A X A⁻¹` of the symplectic group
  on its Lie algebra.

## Main results

* `Matrix.mem_range_scalar_of_commute_sp`: a matrix commuting with `sp l R` is scalar.
* `TauCeti.GLSymplectic.mem_ker_adjoint_iff`: the kernel of `Ad` consists of the scalar matrices
  `c • 1` with `c ^ 2 = 1`; `TauCeti.GLSymplectic.mem_ker_adjoint_iff_eq_one_or_eq_neg_one`: over a
  domain it is `{±1}`.
* `TauCeti.GLSymplectic.comap_map_adjoint_GLOrthogonal_subgroupOf`:
  `Ad⁻¹(Ad(Sp(2n, R) ∩ O(2n))) = Sp(2n, R) ∩ O(2n)`.
* `TauCeti.GLSymplectic.adjoint_cartanInvolution_apply`: `Ad(θ A) (θ X) = θ (Ad(A) X)`.
* `TauCeti.GLSymplectic.killingForm_adjoint_cartanInvolution_adjoint`: the pulled-back form
  `κ(Ad(A) X, θ (Ad(A) Y)) = κ(X, θ (Ad(Aᵀ A) Y))`.
* `TauCeti.GLSymplectic.forall_killingForm_adjoint_cartanInvolution_adjoint_eq_iff`: `Ad(A)` is
  orthogonal for the Cartan metric exactly when `A` is orthogonal.
* `TauCeti.GLSymplectic.adjoint_mem_map_GLOrthogonal_subgroupOf_iff`: the elements of
  `Ad(Sp(2n, K))` orthogonal for the Cartan metric are the adjoint actions of the orthogonal
  symplectic matrices.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, Sections 1 and 2 (the Cartan metric and the compact subgroup
  `K` of the adjoint group).
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer, 2015, Sections 1.2 and 3.7.
-/

public section

open Matrix LieAlgebra.Symplectic

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [Fintype l] [DecidableEq l]

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The long root vector `E_(i, n + i)` lies in `sp l R`. -/
private theorem single_inl_inr_mem_sp (i : l) :
    single (Sum.inl i) (Sum.inr i) (1 : R) ∈ sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_⟩ <;> grind

/-- The long root vector `E_(n + i, i)` lies in `sp l R`. -/
private theorem single_inr_inl_mem_sp (i : l) :
    single (Sum.inr i) (Sum.inl i) (1 : R) ∈ sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_⟩ <;> grind

/-- The Levi element `E_(i, j) - E_(n + j, n + i)` lies in `sp l R`. -/
private theorem single_inl_inl_sub_single_inr_inr_mem_sp (i j : l) :
    single (Sum.inl i) (Sum.inl j) (1 : R) - single (Sum.inr j) (Sum.inr i) 1 ∈ sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_⟩ <;> grind [Matrix.sub_apply]

/-- **A matrix commuting with the symplectic Lie algebra is scalar**, over every commutative
ring. -/
theorem mem_range_scalar_of_commute_sp (M : Matrix (l ⊕ l) (l ⊕ l) R)
    (hM : ∀ X ∈ sp l R, Commute M X) : M ∈ Set.range (scalar (l ⊕ l)) := by
  cases isEmpty_or_nonempty l with
  | inl _ => exact ⟨0, by ext a; exact isEmptyElim a⟩
  | inr h =>
  obtain ⟨z⟩ := h
  -- Commuting with the long root vectors makes `M` diagonal, with equal entries at `i` and
  -- `n + i`.
  have hp (i : l) := (hM _ (single_inl_inr_mem_sp (R := R) i)).symm
  have hn (i : l) := (hM _ (single_inr_inl_mem_sp (R := R) i)).symm
  have hoff (a b : l ⊕ l) (hab : a ≠ b) : M a b = 0 := by
    cases b with
    | inl i => exact col_eq_zero_of_commute_single (hp i) hab
    | inr i => exact col_eq_zero_of_commute_single (hn i) hab
  -- Commuting with a Levi element compares the diagonal entries at `i` and `j`.
  have hd (i : l) : M (Sum.inl i) (Sum.inl i) = M (Sum.inl z) (Sum.inl z) := by
    have he := congrArg (fun N : Matrix (l ⊕ l) (l ⊕ l) R ↦ N (Sum.inl i) (Sum.inl z))
      (hM _ (single_inl_inl_sub_single_inr_inr_mem_sp (R := R) i z)).eq
    simpa [mul_sub, sub_mul, mul_apply, single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]
      using he
  refine ⟨M (Sum.inl z) (Sum.inl z), ?_⟩
  ext a b
  by_cases hab : a = b
  · subst b
    rw [scalar_apply, diagonal_apply_eq]
    cases a with
    | inl i => exact (hd i).symm
    | inr i => exact ((diag_eq_of_commute_single (hp i)).symm.trans (hd i)).symm
  · simp [scalar_apply, diagonal_apply_ne _ hab, hoff a b hab]

end Matrix

namespace TauCeti.GLSymplectic

section CommRing

variable {R : Type*} [CommRing R]

/-- Conjugation by a symplectic matrix preserves the symplectic Lie algebra. -/
theorem mul_mul_inv_mem_sp {A : GL (l ⊕ l) R} (hA : A ∈ GLSymplectic l R)
    {X : Matrix (l ⊕ l) (l ⊕ l) R} (hX : X ∈ sp l R) :
    (A : Matrix (l ⊕ l) (l ⊕ l) R) * X * ((A⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) ∈
      sp l R := by
  set a := (A : Matrix (l ⊕ l) (l ⊕ l) R)
  set b := ((A⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)
  have hab : a * b = 1 := A.mul_inv
  have hba : b * a = 1 := A.inv_mul
  have hJ : a * J l R * aᵀ = J l R := mem_iff.mp hA
  -- Move `A⁻¹` and its transpose past `J` using `A J Aᵀ = J`.
  have h₁ : b * J l R = J l R * aᵀ := by
    calc b * J l R = b * (a * J l R * aᵀ) := by rw [hJ]
      _ = (b * a) * J l R * aᵀ := by simp only [Matrix.mul_assoc]
      _ = J l R * aᵀ := by rw [hba, Matrix.one_mul]
  have h₂ : J l R * bᵀ = a * J l R := by
    calc J l R * bᵀ = a * J l R * aᵀ * bᵀ := by rw [hJ]
      _ = a * J l R * (b * a)ᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = a * J l R := by rw [hba, transpose_one, Matrix.mul_one]
  rw [mem_sp_iff_mul_J_add_J_mul_transpose_eq_zero] at hX ⊢
  calc a * X * b * J l R + J l R * (a * X * b)ᵀ
      = a * X * (b * J l R) + J l R * bᵀ * Xᵀ * aᵀ := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = a * (X * J l R + J l R * Xᵀ) * aᵀ := by
        rw [h₁, h₂]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]

/-- The conjugation `X ↦ A X A⁻¹` of `sp l R` by a symplectic matrix, as a Lie automorphism. -/
private def adjointAux (A : GLSymplectic l R) : sp l R ≃ₗ⁅R⁆ sp l R where
  toFun X := ⟨_, mul_mul_inv_mem_sp A.2 X.2⟩
  map_add' X Y := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by ext1; simp
  map_lie' {X Y} := by
    ext1
    have h : (((A : GL (l ⊕ l) R)⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) *
        ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = 1 := (A : GL (l ⊕ l) R).inv_mul
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R), h, Matrix.one_mul,
      ← Matrix.mul_assoc _ ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R), h, Matrix.one_mul]
  invFun X := ⟨_, mul_mul_inv_mem_sp (inv_mem A.2) X.2⟩
  left_inv X := by
    ext1
    simp [Matrix.mul_assoc]
  right_inv X := by
    ext1
    simp [Matrix.mul_assoc]

variable (l R) in
/-- **The adjoint action** `Ad(A) X = A X A⁻¹` of the symplectic group on its Lie algebra
`sp l R`. Each `Ad(A)` is a Lie automorphism (`TauCeti.GLSymplectic.adjoint_lie`). -/
def adjoint : GLSymplectic l R →* (sp l R ≃ₗ[R] sp l R) where
  toFun A := (adjointAux A).toLinearEquiv
  map_one' := by ext X : 2; simp [adjointAux]
  map_mul' A B := by
    ext X : 2
    simp [adjointAux, Matrix.mul_assoc]

/-- The matrix of `Ad(A) X` is `A X A⁻¹`. -/
@[simp]
theorem coe_adjoint_apply (A : GLSymplectic l R) (X : sp l R) :
    (adjoint l R A X : Matrix (l ⊕ l) (l ⊕ l) R) =
      ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X *
        ((A⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) :=
  (rfl)

/-- Each `Ad(A)` preserves the Lie bracket. -/
@[simp]
theorem adjoint_lie (A : GLSymplectic l R) (X Y : sp l R) :
    adjoint l R A ⁅X, Y⁆ = ⁅adjoint l R A X, adjoint l R A Y⁆ :=
  (adjointAux A).map_lie X Y

/-- The matrix of the group Cartan involution `θ A = (Aᵀ)⁻¹`. -/
private theorem coe_cartanInvolution_val (A : GLSymplectic l R) :
    ((GLSymplectic.cartanInvolution A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      (((A : GL (l ⊕ l) R)⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ := by
  rw [GLSymplectic.coe_cartanInvolution, Matrix.GeneralLinearGroup.coe_inverseTranspose]

/-- The matrix of the inverse of `θ A = (Aᵀ)⁻¹` is `Aᵀ`. -/
private theorem coe_cartanInvolution_inv (A : GLSymplectic l R) :
    (((GLSymplectic.cartanInvolution A : GL (l ⊕ l) R)⁻¹ : GL (l ⊕ l) R) :
      Matrix (l ⊕ l) (l ⊕ l) R) = ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ := by
  rw [GLSymplectic.coe_cartanInvolution, ← map_inv,
    Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]

/-- `Ad` intertwines the Cartan involutions of the group and of the Lie algebra:
`θ (Ad(A) X) = Ad(θ A) (θ X)`, where `θ A = (Aᵀ)⁻¹` and `θ X = -Xᵀ`. -/
theorem adjoint_cartanInvolution_apply (A : GLSymplectic l R) (X : sp l R) :
    adjoint l R (GLSymplectic.cartanInvolution A) (LieAlgebra.Symplectic.cartanInvolution l R X) =
      LieAlgebra.Symplectic.cartanInvolution l R (adjoint l R A X) := by
  ext1
  simp only [coe_adjoint_apply, LieAlgebra.Symplectic.coe_cartanInvolution,
    coe_cartanInvolution_inv, coe_cartanInvolution_val, transpose_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc]

/-- **The kernel of the adjoint action** consists of the scalar matrices `c • 1` with
`c ^ 2 = 1`. -/
theorem mem_ker_adjoint_iff (A : GLSymplectic l R) :
    A ∈ (adjoint l R).ker ↔
      ∃ c : R, ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = scalar (l ⊕ l) c ∧
        c ^ 2 = 1 := by
  constructor
  · intro hA
    obtain ⟨c, hc⟩ :=
      Matrix.mem_range_scalar_of_commute_sp ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)
      fun X hX ↦ by
        have h := congrArg (fun e : sp l R ≃ₗ[R] sp l R ↦
          ((e ⟨X, hX⟩ : sp l R) : Matrix (l ⊕ l) (l ⊕ l) R)) hA
        simp only [coe_adjoint_apply, one_apply_eq_self] at h
        calc ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X
            = ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X *
                (((A⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) *
                  ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)) := by
              rw [(A : GL (l ⊕ l) R).inv_mul, Matrix.mul_one]
          _ = X * ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) := by
              rw [← Matrix.mul_assoc, h]
    cases isEmpty_or_nonempty l with
    | inl _ => exact ⟨1, by ext a; exact isEmptyElim a, one_pow 2⟩
    | inr _ =>
      refine ⟨c, hc.symm, Matrix.sq_eq_one_of_smul_one_mul_mul_transpose_eq (isUnit_J l R) ?_⟩
      simpa only [← hc, scalar_apply, smul_one_eq_diagonal] using mem_iff.mp A.2
  · rintro ⟨c, hc, -⟩
    ext X : 2
    simp only [coe_adjoint_apply, hc, one_apply_eq_self]
    rw [(scalar_commute c (fun r ↦ Commute.all c r) (X : Matrix (l ⊕ l) (l ⊕ l) R)).eq,
      Matrix.mul_assoc, ← hc, Units.mul_inv, Matrix.mul_one]

/-- Over a domain, the kernel of the adjoint action is the central subgroup `{±1}`. -/
theorem mem_ker_adjoint_iff_eq_one_or_eq_neg_one [IsDomain R] (A : GLSymplectic l R) :
    A ∈ (adjoint l R).ker ↔
      ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = 1 ∨
        ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = -1 := by
  rw [mem_ker_adjoint_iff]
  constructor
  · rintro ⟨c, hc, hc2⟩
    rcases mul_self_eq_one_iff.mp (show c * c = 1 by rwa [← sq]) with rfl | rfl
    · exact .inl (by rw [hc, map_one])
    · exact .inr (by rw [hc, map_neg, map_one])
  · rintro (h | h)
    · exact ⟨1, by rw [h, map_one], one_pow 2⟩
    · exact ⟨-1, by rw [h, map_neg, map_one], by norm_num⟩

/-- The kernel of the adjoint action consists of orthogonal matrices. -/
theorem ker_adjoint_le_GLOrthogonal_subgroupOf :
    (adjoint l R).ker ≤ (GLOrthogonal (l ⊕ l) R).subgroupOf (GLSymplectic l R) := by
  intro A hA
  obtain ⟨c, hc, hc2⟩ := (mem_ker_adjoint_iff A).mp hA
  have hcc : c * c = 1 := by rwa [← sq]
  rw [Subgroup.mem_subgroupOf, GLOrthogonal.mem_iff, hc]
  simp only [scalar_apply, diagonal_transpose, diagonal_mul_diagonal, hcc, diagonal_one]

/-- **`Ad⁻¹(Ad(U(n))) = U(n)`**: an element of the symplectic group whose adjoint action is that
of an orthogonal symplectic matrix is itself orthogonal. Over `ℝ` the orthogonal symplectic
matrices are the realified unitary group `U(n)`. -/
theorem comap_map_adjoint_GLOrthogonal_subgroupOf :
    (((GLOrthogonal (l ⊕ l) R).subgroupOf (GLSymplectic l R)).map (adjoint l R)).comap
        (adjoint l R) =
      (GLOrthogonal (l ⊕ l) R).subgroupOf (GLSymplectic l R) := by
  rw [Subgroup.comap_map_eq, sup_eq_left]
  exact ker_adjoint_le_GLOrthogonal_subgroupOf

end CommRing

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- **The Cartan metric pulled back by the adjoint action.** For `A` in the symplectic group,
`κ(Ad(A) X, θ (Ad(A) Y)) = κ(X, θ (Ad(Aᵀ A) Y))`, where `κ` is the Killing form of `sp l K`,
`θ` is its Cartan involution and `Aᵀ A = (θ A)⁻¹ A`. -/
theorem killingForm_adjoint_cartanInvolution_adjoint (A : GLSymplectic l K) (X Y : sp l K) :
    killingForm K (sp l K) (adjoint l K A X)
        (LieAlgebra.Symplectic.cartanInvolution l K (adjoint l K A Y)) =
      killingForm K (sp l K) X (LieAlgebra.Symplectic.cartanInvolution l K
        (adjoint l K ((GLSymplectic.cartanInvolution A)⁻¹ * A) Y)) := by
  rw [killingForm_cartanInvolution_apply, killingForm_cartanInvolution_apply, coe_adjoint_apply,
    coe_adjoint_apply, coe_adjoint_apply, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv,
    coe_cartanInvolution_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul,
    coe_cartanInvolution_val]
  -- Both sides are `-(2 n + 2) trace (X A⁻¹ A⁻ᵀ Yᵀ Aᵀ A)`, after cycling `A` in the trace.
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [trace_mul_comm ((A : GL (l ⊕ l) K) : Matrix (l ⊕ l) (l ⊕ l) K)]
  simp only [Matrix.mul_assoc]

end Field

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Over an ordered field, `Ad(Aᵀ A)` is the identity exactly when `A` is orthogonal. Indeed
`Aᵀ A` is then a scalar `c` with `c ^ 2 = 1` whose diagonal entries are sums of squares. -/
theorem cartanInvolution_inv_mul_mem_ker_adjoint_iff (A : GLSymplectic l K) :
    (GLSymplectic.cartanInvolution A)⁻¹ * A ∈ (adjoint l K).ker ↔
      (A : GL (l ⊕ l) K) ∈ GLOrthogonal (l ⊕ l) K := by
  constructor
  · intro h
    obtain ⟨c, hc, hc2⟩ := (mem_ker_adjoint_iff _).mp h
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, coe_cartanInvolution_inv] at hc
    rw [GLOrthogonal.mem_iff, hc]
    cases isEmpty_or_nonempty l with
    | inl _ => ext i; exact isEmptyElim i
    | inr h =>
      obtain ⟨i⟩ := h
      have hc0 : 0 ≤ c := by
        have := congrArg (fun M : Matrix (l ⊕ l) (l ⊕ l) K ↦ M (Sum.inl i) (Sum.inl i)) hc
        simp only [scalar_apply, diagonal_apply_eq, Matrix.mul_apply, transpose_apply] at this
        rw [← this]
        exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
      rcases mul_self_eq_one_iff.mp (show c * c = 1 by rwa [← sq]) with rfl | rfl
      · rw [map_one]
      · exact absurd hc0 (by norm_num)
  · intro hA
    have hθ : GLSymplectic.cartanInvolution A = A := by
      rw [GLSymplectic.cartanInvolution_eq_self_iff, mem_orthogonalGroup_iff']
      exact GLOrthogonal.mem_iff.mp hA
    rw [hθ, inv_mul_cancel]
    exact one_mem _

/-- **The adjoint action is orthogonal for the Cartan metric exactly on orthogonal matrices.**
For `A` in the symplectic group over an ordered field, `Ad(A)` preserves the Cartan metric
`(X, Y) ↦ -κ(X, θ Y)` of `sp l K`, built from the Killing form `κ` and the Cartan involution
`θ X = -Xᵀ`, exactly when `A` is an orthogonal matrix. -/
theorem forall_killingForm_adjoint_cartanInvolution_adjoint_eq_iff (A : GLSymplectic l K) :
    (∀ X Y : sp l K, killingForm K (sp l K) (adjoint l K A X)
        (LieAlgebra.Symplectic.cartanInvolution l K (adjoint l K A Y)) =
          killingForm K (sp l K) X (LieAlgebra.Symplectic.cartanInvolution l K Y)) ↔
      (A : GL (l ⊕ l) K) ∈ GLOrthogonal (l ⊕ l) K := by
  simp only [killingForm_adjoint_cartanInvolution_adjoint]
  rw [← cartanInvolution_inv_mul_mem_ker_adjoint_iff, MonoidHom.mem_ker]
  set e := adjoint l K ((GLSymplectic.cartanInvolution A)⁻¹ * A)
  constructor
  · -- If `e` preserves the metric, `e Y - Y` is orthogonal to `sp l K`, so it vanishes.
    intro h
    refine LinearEquiv.ext fun Y ↦ ?_
    rw [one_apply_eq_self]
    by_contra hne
    refine (killingForm_cartanInvolution_self_neg (sub_ne_zero.mpr hne)).ne ?_
    rw [map_sub (LieAlgebra.Symplectic.cartanInvolution l K),
      map_sub (killingForm K (sp l K) (e Y - Y)), h, sub_self]
  · intro h X Y
    rw [h, one_apply_eq_self]

/-- **The compact part of the adjoint group.** For `A` in the symplectic group over an ordered
field, `Ad(A)` is orthogonal for the Cartan metric `-κ(X, θ Y)` exactly when it is the adjoint
action of an orthogonal symplectic matrix. Over `ℝ` these are the adjoint actions of the
realified unitary group `U(n)`. -/
theorem adjoint_mem_map_GLOrthogonal_subgroupOf_iff (A : GLSymplectic l K) :
    adjoint l K A ∈ ((GLOrthogonal (l ⊕ l) K).subgroupOf (GLSymplectic l K)).map (adjoint l K) ↔
      ∀ X Y : sp l K, killingForm K (sp l K) (adjoint l K A X)
        (LieAlgebra.Symplectic.cartanInvolution l K (adjoint l K A Y)) =
          killingForm K (sp l K) X (LieAlgebra.Symplectic.cartanInvolution l K Y) := by
  rw [forall_killingForm_adjoint_cartanInvolution_adjoint_eq_iff, ← Subgroup.mem_comap,
    comap_map_adjoint_GLOrthogonal_subgroupOf, Subgroup.mem_subgroupOf]

end OrderedField

end TauCeti.GLSymplectic
