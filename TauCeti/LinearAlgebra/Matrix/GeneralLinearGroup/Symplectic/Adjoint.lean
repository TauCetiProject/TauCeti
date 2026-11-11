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
(`TauCeti.GLSymplectic.adjointAction`). This file computes the kernel of this action and, over an
ordered field, the elements whose adjoint action is orthogonal for the Cartan metric.

A matrix commuting with every element of `sp l R` is scalar
(`Matrix.mem_range_scalar_of_commute_sp`), over every commutative ring. So the kernel of `Ad` is
the scalar symplectic matrices, `c • 1` with `c ^ 2 = 1`
(`TauCeti.GLSymplectic.mem_ker_adjointAction_iff`), which over a ring without zero divisors is
the central subgroup `{±1}`.

The Cartan involution `θ X = -Xᵀ` of `sp l R` is intertwined by `Ad` with the group Cartan
involution `θ A = (Aᵀ)⁻¹` (`TauCeti.GLSymplectic.adjointAction_cartanInvolution_apply`). Since the
Killing form `κ` is invariant under the Lie automorphism `Ad(A)`, the form `κ(X, θ Y)` pulled
back by `Ad(A)` becomes `κ(X, θ (Ad(Aᵀ A) Y))`, where `Aᵀ A = (θ A)⁻¹ A`
(`TauCeti.GLSymplectic.killingForm_adjointAction_cartanInvolution_adjointAction`).

Over an ordered field the *Cartan metric* `-κ(X, θ Y)` is positive definite
(`LieAlgebra.Symplectic.killingForm_cartanInvolution_self_neg`), so `Ad(A)` is orthogonal for it
exactly when `Ad(Aᵀ A) = 1`. Then `Aᵀ A = c • 1` with `c ^ 2 = 1`, and `c ≥ 0` because the
diagonal entries of `Aᵀ A` are sums of squares, so `Aᵀ A = 1`. Hence `Ad(A)` is orthogonal for the
Cartan metric exactly when `A` is an orthogonal matrix
(`TauCeti.GLSymplectic.forall_killingForm_adjointAction_cartanInvolution_adjointAction_eq_iff`).

Over `ℝ`, the orthogonal symplectic matrices form the realified unitary group `U(n)`
(`TauCeti.GLSymplectic.inf_unitarySubgroup`), a maximal compact subgroup of `Sp(2n, ℝ)`
(`TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`). So the elements of `Ad(Sp(2n, ℝ))`
that are orthogonal for the Cartan metric are exactly those of `Ad(U(n))`
(`TauCeti.GLSymplectic.adjointAction_mem_map_GLOrthogonal_subgroupOf_iff`). Over every
commutative ring the kernel `{c • 1 | c ^ 2 = 1}` of `Ad` consists of orthogonal matrices, so
`Ad⁻¹(Ad(Sp ∩ O)) = Sp ∩ O`
(`TauCeti.GLSymplectic.comap_map_adjointAction_GLOrthogonal_subgroupOf`); over `ℝ` this is
`Ad⁻¹(Ad(U(n))) = U(n)`.

## Main definitions

* `TauCeti.GLSymplectic.adjointAction`: the adjoint action `Ad(A) X = A X A⁻¹` of the symplectic
  group on its Lie algebra.

## Main results

* `TauCeti.GLSymplectic.mem_ker_adjointAction_iff`: the kernel of `Ad` consists of the scalar
  matrices `c • 1` with `c ^ 2 = 1`;
  `TauCeti.GLSymplectic.mem_ker_adjointAction_iff_eq_one_or_eq_neg_one`: over a ring without zero
  divisors it is `{±1}`.
* `TauCeti.GLSymplectic.comap_map_adjointAction_GLOrthogonal_subgroupOf`:
  `Ad⁻¹(Ad(Sp(2n, R) ∩ O(2n))) = Sp(2n, R) ∩ O(2n)`.
* `TauCeti.GLSymplectic.adjointAction_cartanInvolution_apply`: `Ad(θ A) (θ X) = θ (Ad(A) X)`.
* `TauCeti.GLSymplectic.killingForm_adjointAction_cartanInvolution_adjointAction`: the pulled-back
  form `κ(Ad(A) X, θ (Ad(A) Y)) = κ(X, θ (Ad(Aᵀ A) Y))`.
* `TauCeti.GLSymplectic.forall_killingForm_adjointAction_cartanInvolution_adjointAction_eq_iff`:
  `Ad(A)` is orthogonal for the Cartan metric exactly when `A` is orthogonal.
* `TauCeti.GLSymplectic.adjointAction_mem_map_GLOrthogonal_subgroupOf_iff`: the elements of
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

namespace TauCeti.GLSymplectic

section CommRing

variable {R : Type*} [CommRing R]

/-- The conjugation `X ↦ A X A⁻¹` of `sp l R` by a symplectic matrix, as a Lie automorphism:
Mathlib's `skewAdjointMatricesLieSubalgebraEquiv` for `P = A⁻¹`, using `(A⁻¹)ᵀ J A⁻¹ = J`.
Here `sp l R` is by definition `skewAdjointMatricesLieSubalgebra (J l R)`. -/
private def adjointAux (A : GLSymplectic l R) : sp l R ≃ₗ⁅R⁆ sp l R :=
  (skewAdjointMatricesLieSubalgebraEquiv (J l R)
    (((A⁻¹ : GLSymplectic l R) : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)
    (Units.invertible _)).trans
    (LieEquiv.ofEq _ _ (by rw [mem_iff'.mp (A⁻¹).2, sp]))

/-- The matrix of `adjointAux A X` is `A X A⁻¹`. -/
private theorem coe_adjointAux_apply (A : GLSymplectic l R) (X : sp l R) :
    (adjointAux A X : Matrix (l ⊕ l) (l ⊕ l) R) =
      ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X *
        ((A⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) := by
  -- By definition, `adjointAux A X` is `(A⁻¹)⁻¹ X A⁻¹` as a matrix.
  refine (skewAdjointMatricesLieSubalgebraEquiv_apply (J l R) _ (Units.invertible _) X).trans ?_
  simp [coe_units_inv]

variable (l R) in
/-- **The adjoint action** `Ad(A) X = A X A⁻¹` of the symplectic group on its Lie algebra
`sp l R`. Each `Ad(A)` is a Lie automorphism (`TauCeti.GLSymplectic.adjointAction_lie`). -/
def adjointAction : GLSymplectic l R →* (sp l R ≃ₗ[R] sp l R) where
  toFun A := (adjointAux A).toLinearEquiv
  map_one' := by ext X : 2; simp [coe_adjointAux_apply]
  map_mul' A B := by
    ext X : 2
    simp [coe_adjointAux_apply, Matrix.mul_assoc]

/-- The matrix of `Ad(A) X` is `A X A⁻¹`. -/
@[simp]
theorem coe_adjointAction_apply (A : GLSymplectic l R) (X : sp l R) :
    (adjointAction l R A X : Matrix (l ⊕ l) (l ⊕ l) R) =
      ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X *
        ((A⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) :=
  coe_adjointAux_apply A X

/-- Each `Ad(A)` preserves the Lie bracket. -/
@[simp]
theorem adjointAction_lie (A : GLSymplectic l R) (X Y : sp l R) :
    adjointAction l R A ⁅X, Y⁆ = ⁅adjointAction l R A X, adjointAction l R A Y⁆ :=
  (adjointAux A).map_lie X Y

/-- `Ad` intertwines the Cartan involutions of the group and of the Lie algebra:
`θ (Ad(A) X) = Ad(θ A) (θ X)`, where `θ A = (Aᵀ)⁻¹` and `θ X = -Xᵀ`. -/
theorem adjointAction_cartanInvolution_apply (A : GLSymplectic l R) (X : sp l R) :
    adjointAction l R (GLSymplectic.cartanInvolution A)
        (LieAlgebra.Symplectic.cartanInvolution l R X) =
      LieAlgebra.Symplectic.cartanInvolution l R (adjointAction l R A X) := by
  ext1
  simp only [coe_adjointAction_apply, LieAlgebra.Symplectic.coe_cartanInvolution,
    coe_cartanInvolution_inv]
  simp only [coe_cartanInvolution, Matrix.GeneralLinearGroup.coe_inverseTranspose, transpose_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- **The kernel of the adjoint action** consists of the scalar matrices `c • 1` with
`c ^ 2 = 1`. -/
theorem mem_ker_adjointAction_iff (A : GLSymplectic l R) :
    A ∈ (adjointAction l R).ker ↔
      ∃ c : R, ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = scalar (l ⊕ l) c ∧
        c ^ 2 = 1 := by
  constructor
  · intro hA
    obtain ⟨c, hc⟩ :=
      Matrix.mem_range_scalar_of_commute_sp ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)
      fun X hX ↦ by
        have h := congrArg (fun e : sp l R ≃ₗ[R] sp l R ↦
          ((e ⟨X, hX⟩ : sp l R) : Matrix (l ⊕ l) (l ⊕ l) R)) hA
        simp only [coe_adjointAction_apply, one_apply_eq_self] at h
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
    simp only [coe_adjointAction_apply, hc, one_apply_eq_self]
    rw [(scalar_commute c (fun r ↦ Commute.all c r) (X : Matrix (l ⊕ l) (l ⊕ l) R)).eq,
      Matrix.mul_assoc, ← hc, Units.mul_inv, Matrix.mul_one]

/-- Over a ring without zero divisors, the kernel of the adjoint action is the central subgroup
`{±1}`. -/
theorem mem_ker_adjointAction_iff_eq_one_or_eq_neg_one [NoZeroDivisors R]
    (A : GLSymplectic l R) :
    A ∈ (adjointAction l R).ker ↔
      ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = 1 ∨
        ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = -1 := by
  rw [mem_ker_adjointAction_iff]
  constructor
  · rintro ⟨c, hc, hc2⟩
    rcases mul_self_eq_one_iff.mp (show c * c = 1 by rwa [← sq]) with rfl | rfl
    · exact .inl (by rw [hc, map_one])
    · exact .inr (by rw [hc, map_neg, map_one])
  · rintro (h | h)
    · exact ⟨1, by rw [h, map_one], one_pow 2⟩
    · exact ⟨-1, by rw [h, map_neg, map_one], by norm_num⟩

/-- The kernel of the adjoint action consists of orthogonal matrices. -/
theorem ker_adjointAction_le_GLOrthogonal_subgroupOf :
    (adjointAction l R).ker ≤ (GLOrthogonal (l ⊕ l) R).subgroupOf (GLSymplectic l R) := by
  intro A hA
  obtain ⟨c, hc, hc2⟩ := (mem_ker_adjointAction_iff A).mp hA
  have hcc : c * c = 1 := by rwa [← sq]
  rw [Subgroup.mem_subgroupOf, GLOrthogonal.mem_iff, hc]
  simp only [scalar_apply, diagonal_transpose, diagonal_mul_diagonal, hcc, diagonal_one]

/-- **`Ad⁻¹(Ad(U(n))) = U(n)`**: an element of the symplectic group whose adjoint action is that
of an orthogonal symplectic matrix is itself orthogonal. Over `ℝ` the orthogonal symplectic
matrices are the realified unitary group `U(n)`. -/
theorem comap_map_adjointAction_GLOrthogonal_subgroupOf :
    (((GLOrthogonal (l ⊕ l) R).subgroupOf (GLSymplectic l R)).map (adjointAction l R)).comap
        (adjointAction l R) =
      (GLOrthogonal (l ⊕ l) R).subgroupOf (GLSymplectic l R) := by
  rw [Subgroup.comap_map_eq, sup_eq_left]
  exact ker_adjointAction_le_GLOrthogonal_subgroupOf

/-- **The Cartan metric pulled back by the adjoint action.** For `A` in the symplectic group,
`κ(Ad(A) X, θ (Ad(A) Y)) = κ(X, θ (Ad(Aᵀ A) Y))`, where `κ` is the Killing form of `sp l R`,
`θ` is its Cartan involution and `Aᵀ A = (θ A)⁻¹ A`. This follows from the invariance of `κ`
under the Lie automorphism `Ad(A)`. -/
theorem killingForm_adjointAction_cartanInvolution_adjointAction (A : GLSymplectic l R)
    (X Y : sp l R) :
    killingForm R (sp l R) (adjointAction l R A X)
        (LieAlgebra.Symplectic.cartanInvolution l R (adjointAction l R A Y)) =
      killingForm R (sp l R) X (LieAlgebra.Symplectic.cartanInvolution l R
        (adjointAction l R ((GLSymplectic.cartanInvolution A)⁻¹ * A) Y)) := by
  -- `θ (Ad(A) Y) = Ad(θ A) (θ Y) = Ad(A) (Ad(A⁻¹ θ A) (θ Y)) = Ad(A) (θ (Ad((θ A)⁻¹ A) Y))`.
  rw [← adjointAction_cartanInvolution_apply, ← adjointAction_cartanInvolution_apply, map_mul,
    map_inv, cartanInvolution_cartanInvolution]
  conv_lhs => rw [← mul_inv_cancel_left A (GLSymplectic.cartanInvolution A), map_mul,
    mul_apply_eq_comp]
  exact LieAlgebra.killingForm_of_equiv_apply (adjointAux A) X _

end CommRing

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Over an ordered field, `Ad(Aᵀ A)` is the identity exactly when `A` is orthogonal. Indeed
`Aᵀ A` is then a scalar `c` with `c ^ 2 = 1` whose diagonal entries are sums of squares. -/
theorem cartanInvolution_inv_mul_mem_ker_adjointAction_iff (A : GLSymplectic l K) :
    (GLSymplectic.cartanInvolution A)⁻¹ * A ∈ (adjointAction l K).ker ↔
      (A : GL (l ⊕ l) K) ∈ GLOrthogonal (l ⊕ l) K := by
  constructor
  · intro h
    obtain ⟨c, hc, hc2⟩ := (mem_ker_adjointAction_iff _).mp h
    rw [coe_cartanInvolution_inv_mul] at hc
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
theorem forall_killingForm_adjointAction_cartanInvolution_adjointAction_eq_iff
    (A : GLSymplectic l K) :
    (∀ X Y : sp l K, killingForm K (sp l K) (adjointAction l K A X)
        (LieAlgebra.Symplectic.cartanInvolution l K (adjointAction l K A Y)) =
          killingForm K (sp l K) X (LieAlgebra.Symplectic.cartanInvolution l K Y)) ↔
      (A : GL (l ⊕ l) K) ∈ GLOrthogonal (l ⊕ l) K := by
  simp only [killingForm_adjointAction_cartanInvolution_adjointAction]
  rw [← cartanInvolution_inv_mul_mem_ker_adjointAction_iff, MonoidHom.mem_ker]
  set e := adjointAction l K ((GLSymplectic.cartanInvolution A)⁻¹ * A)
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
theorem adjointAction_mem_map_GLOrthogonal_subgroupOf_iff (A : GLSymplectic l K) :
    adjointAction l K A ∈
        ((GLOrthogonal (l ⊕ l) K).subgroupOf (GLSymplectic l K)).map (adjointAction l K) ↔
      ∀ X Y : sp l K, killingForm K (sp l K) (adjointAction l K A X)
        (LieAlgebra.Symplectic.cartanInvolution l K (adjointAction l K A Y)) =
          killingForm K (sp l K) X (LieAlgebra.Symplectic.cartanInvolution l K Y) := by
  rw [forall_killingForm_adjointAction_cartanInvolution_adjointAction_eq_iff, ← Subgroup.mem_comap,
    comap_map_adjointAction_GLOrthogonal_subgroupOf, Subgroup.mem_subgroupOf]

end OrderedField

end TauCeti.GLSymplectic
