/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import TauCeti.LinearAlgebra.Matrix.ConjInvariants

/-!
# Invariant polynomials of the split Friedberg–Jacquet representation

For the symmetric pair `(U(W₁ ⊕ W₂), U(W₁) × U(W₂))` the symmetric representation is
`Hom(W₂, W₁)` with `(g₁, g₂) • X = g₁ X g₂⁻¹`, and the signed contraction is
`r₁(X) = -X X^τ`, where `X^τ` is the Hermitian adjoint. Over the split quadratic algebra
`E = F × F`, or after extending scalars to a field splitting `E`, a Hom map becomes a pair of
square matrices `(A, B)`, its adjoint becomes `(B, A)`, the two unitary groups become
`GL_n × GL_n` acting by

  `(g, h) • (A, B) = (g A h⁻¹, h B g⁻¹)`,

and the signed contraction becomes `(A, B) ↦ -(A * B)`.

This file determines, over an infinite field `K`, the polynomial functions invariant under the
second group, and reduces those invariant under both groups to conjugation invariants on
matrices. Polynomial functions on pairs are `MvPolynomial (n × n ⊕ n × n) K`: the variable
`X (Sum.inl (i, j))` is the entry `A i j` and `X (Sum.inr (i, j))` is the entry `B i j`; a pair is
evaluated through `Sum.elim (fun p => A p.1 p.2) (fun p => B p.1 p.2)`.

* **The quotient by the second group.** A polynomial is invariant under `h • (A, B) = (A h⁻¹, h B)`
  exactly when it is a polynomial in the entries of `-(A * B)`, and that polynomial is unique
  (`TauCeti.FriedbergJacquet.Split.range_contractionPullback`,
  `TauCeti.FriedbergJacquet.Split.contractionPullback_injective`). So pulling back along the signed
  contraction is an isomorphism from the polynomial functions on matrices onto the invariant
  ring (`TauCeti.FriedbergJacquet.Split.rightInvariantsEquiv`): the contraction is the categorical
  quotient by the second group, and it is equivariant for the first group acting on matrices by
  conjugation (`TauCeti.FriedbergJacquet.Split.eval_contractionPullback_mul_mul_inv`).
* **The quotient by both groups.** Consequently a polynomial is invariant under both groups
  exactly when it is the pullback of a conjugation-invariant polynomial function on matrices
  (`TauCeti.FriedbergJacquet.Split.mem_invariants_iff_exists_contractionPullback`), so pulling back
  along the signed contraction is an isomorphism from the conjugation invariants
  `TauCeti.Matrix.conjInvariants` onto the invariants of both groups
  (`TauCeti.FriedbergJacquet.Split.invariantsEquiv`). This reduces the quotient to the adjoint
  quotient of `gl_n`.

The proof is the classical one. If `B` is invertible, acting by `h = B⁻¹` moves `(A, B)` to
`(A * B, 1)`, so an invariant `P` satisfies `P(A, B) = P(A * B, 1)`; the polynomial
`Q(Z) = P(-Z, 1)`, the pullback of `P` along the section `Z ↦ (-Z, 1)` of the contraction
(`TauCeti.FriedbergJacquet.Split.sectionPullback`), therefore agrees with `P` on the pairs with `B`
invertible. Multiplying by the generic determinant of `B` turns this into an identity at every
point, hence into an identity of polynomials over an infinite field, and the generic determinant
is a nonzero element of a domain.

The field must be infinite: over `𝔽₂` in rank one `GL₁` is trivial, every polynomial is
invariant, and `A` is not a polynomial in `A * B`. Over `ℤ`, where `GL₁ = {±1}`, the invariant
`A ^ 2` is not a polynomial in `A * B` either.

All declarations describe the split coordinate model, so they live in the namespace
`TauCeti.FriedbergJacquet.Split`; the unqualified Friedberg–Jacquet names are left for the
nonsplit Hermitian model.

## Main definitions

* `TauCeti.FriedbergJacquet.Split.contractionPullback`: the pullback of polynomial functions along
  the signed contraction `(A, B) ↦ -(A * B)`.
* `TauCeti.FriedbergJacquet.Split.sectionPullback`: the pullback along its section `Z ↦ (-Z, 1)`.
* `TauCeti.FriedbergJacquet.Split.rightInvariants`, `TauCeti.FriedbergJacquet.Split.invariants`: the
  polynomials invariant under the second group, and under both groups.
* `TauCeti.FriedbergJacquet.Split.rightInvariantsEquiv`: the isomorphism from polynomial
  functions on matrices onto the invariants of the second group.
* `TauCeti.FriedbergJacquet.Split.invariantsEquiv`: the isomorphism from the conjugation invariants
  onto the invariants of both groups.

## Main results

* `TauCeti.FriedbergJacquet.Split.sectionPullback_comp_contractionPullback`: the section splits the
  pullback, which is therefore injective.
* `TauCeti.FriedbergJacquet.Split.range_contractionPullback`: the invariants of the second group are
  exactly the pullbacks along the signed contraction.
* `TauCeti.FriedbergJacquet.Split.contractionPullback_mem_invariants_iff`,
  `TauCeti.FriedbergJacquet.Split.map_contractionPullback_conjInvariants` and
  `TauCeti.FriedbergJacquet.Split.mem_invariants_iff_exists_contractionPullback`: the invariants of
  both groups are exactly the pullbacks of conjugation-invariant polynomial functions on
  matrices.

## References

* S. Leslie, *The endoscopic fundamental lemma for unitary Friedberg–Jacquet periods*,
  Ann. of Math. 201 (2025), 551–645, §2.1, Proposition 2.1 and Lemma 2.2 (arXiv:1911.07907v3).
-/

public section

open MvPolynomial

namespace TauCeti.FriedbergJacquet.Split

section CommRing

variable (R : Type*) [CommRing R] (n : Type*) [Fintype n] [DecidableEq n]

/-- The pullback of polynomial functions along the signed contraction `(A, B) ↦ -(A * B)` from
pairs of square matrices to square matrices: it sends the entry `Z i j` to the entry `i j` of
`-(A * B)`. -/
noncomputable def contractionPullback :
    MvPolynomial (n × n) R →ₐ[R] MvPolynomial (n × n ⊕ n × n) R :=
  aeval fun p => -∑ k, X (Sum.inl (p.1, k)) * X (Sum.inr (k, p.2))

/-- The pullback of polynomial functions along the section `Z ↦ (-Z, 1)` of the signed
contraction. -/
noncomputable def sectionPullback :
    MvPolynomial (n × n ⊕ n × n) R →ₐ[R] MvPolynomial (n × n) R :=
  aeval <| Sum.elim (fun p => -X p) fun p => if p.1 = p.2 then 1 else 0

variable {R n}

omit [DecidableEq n] in
/-- The pullback along the signed contraction sends the variable `Z i j` to the entry `i j` of
`-(A * B)`. -/
@[simp]
theorem contractionPullback_X (p : n × n) :
    contractionPullback R n (X p) = -∑ k, X (Sum.inl (p.1, k)) * X (Sum.inr (k, p.2)) :=
  aeval_X _ _

omit [Fintype n] in
/-- The pullback along the section sends the variable `A i j` to `-Z i j`. -/
@[simp]
theorem sectionPullback_X_inl (p : n × n) : sectionPullback R n (X (Sum.inl p)) = -X p :=
  aeval_X _ _

omit [Fintype n] in
/-- The pullback along the section sends the variable `B i j` to the entry `i j` of `1`. -/
@[simp]
theorem sectionPullback_X_inr (p : n × n) :
    sectionPullback R n (X (Sum.inr p)) = if p.1 = p.2 then 1 else 0 :=
  aeval_X _ _

omit [DecidableEq n] in
/-- The value of a pullback along the signed contraction at a pair `(A, B)` is the value of the
original polynomial at `-(A * B)`. -/
@[simp]
theorem eval_contractionPullback (A B : Matrix n n R) (Q : MvPolynomial (n × n) R) :
    eval (Sum.elim (fun p => A p.1 p.2) fun p => B p.1 p.2) (contractionPullback R n Q) =
      eval (fun p => (-(A * B)) p.1 p.2) Q := by
  simp only [contractionPullback, map_aeval]
  congr 1
  ext i <;> simp [Matrix.mul_apply]

omit [Fintype n] in
/-- The value of a pullback along the section at `Z` is the value of the original polynomial at
the pair `(-Z, 1)`. -/
@[simp]
theorem eval_sectionPullback (Z : Matrix n n R) (P : MvPolynomial (n × n ⊕ n × n) R) :
    eval (fun p => Z p.1 p.2) (sectionPullback R n P) =
      eval (Sum.elim (fun p => (-Z) p.1 p.2) fun p => (1 : Matrix n n R) p.1 p.2) P := by
  simp only [sectionPullback, map_aeval]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
  rintro (p | p) <;> simp [Matrix.one_apply, apply_ite (eval _)]

variable (R n) in
/-- The section `Z ↦ (-Z, 1)` splits the signed contraction, so pulling back along the
contraction and then along the section is the identity. -/
@[simp]
theorem sectionPullback_comp_contractionPullback :
    (sectionPullback R n).comp (contractionPullback R n) = AlgHom.id R _ := by
  ext p : 2
  simp [contractionPullback, sectionPullback, mul_ite, Finset.sum_ite_eq']

/-- Pulling back along the signed contraction and then along its section is the identity. -/
@[simp]
theorem sectionPullback_contractionPullback (Q : MvPolynomial (n × n) R) :
    sectionPullback R n (contractionPullback R n Q) = Q :=
  DFunLike.congr_fun (sectionPullback_comp_contractionPullback R n) Q

omit [DecidableEq n] in
/-- Pulling back along the signed contraction is injective. -/
theorem contractionPullback_injective : Function.Injective (contractionPullback R n) := by
  classical
  exact Function.LeftInverse.injective sectionPullback_contractionPullback

variable (R n)

/-- The polynomial functions on pairs `(A, B)` of square matrices that are invariant under the
action `h • (A, B) = (A * h⁻¹, h * B)` of `GL n R`. This is invariance at points, not as
polynomials: over an infinite field the two agree, but over a finite ring this subalgebra can be
larger. -/
def rightInvariants : Subalgebra R (MvPolynomial (n × n ⊕ n × n) R) where
  carrier := {P | ∀ (h : GL n R) (A B : Matrix n n R),
    eval (Sum.elim (fun p => (A * (h⁻¹ : GL n R)) p.1 p.2)
      fun p => ((h : Matrix n n R) * B) p.1 p.2) P =
        eval (Sum.elim (fun p => A p.1 p.2) fun p => B p.1 p.2) P}
  mul_mem' hP hQ h A B := by simp only [map_mul, hP h A B, hQ h A B]
  add_mem' hP hQ h A B := by simp only [map_add, hP h A B, hQ h A B]
  algebraMap_mem' c h A B := by simp

/-- The polynomial functions on pairs `(A, B)` of square matrices that are invariant under the
action `(g, h) • (A, B) = (g * A * h⁻¹, h * B * g⁻¹)` of `GL n R × GL n R`. This is invariance
at points, not as polynomials: over an infinite field the two agree, but over a finite ring this
subalgebra can be larger. -/
def invariants : Subalgebra R (MvPolynomial (n × n ⊕ n × n) R) where
  carrier := {P | ∀ (g h : GL n R) (A B : Matrix n n R),
    eval (Sum.elim (fun p => ((g : Matrix n n R) * A * (h⁻¹ : GL n R)) p.1 p.2)
      fun p => ((h : Matrix n n R) * B * (g⁻¹ : GL n R)) p.1 p.2) P =
        eval (Sum.elim (fun p => A p.1 p.2) fun p => B p.1 p.2) P}
  mul_mem' hP hQ g h A B := by simp only [map_mul, hP g h A B, hQ g h A B]
  add_mem' hP hQ g h A B := by simp only [map_add, hP g h A B, hQ g h A B]
  algebraMap_mem' c g h A B := by simp

variable {R n}

/-- Membership in `TauCeti.FriedbergJacquet.Split.rightInvariants`, unfolded. -/
theorem mem_rightInvariants_iff {P : MvPolynomial (n × n ⊕ n × n) R} :
    P ∈ rightInvariants R n ↔ ∀ (h : GL n R) (A B : Matrix n n R),
      eval (Sum.elim (fun p => (A * (h⁻¹ : GL n R)) p.1 p.2)
        fun p => ((h : Matrix n n R) * B) p.1 p.2) P =
          eval (Sum.elim (fun p => A p.1 p.2) fun p => B p.1 p.2) P :=
  Iff.rfl

/-- Membership in `TauCeti.FriedbergJacquet.Split.invariants`, unfolded. -/
theorem mem_invariants_iff {P : MvPolynomial (n × n ⊕ n × n) R} :
    P ∈ invariants R n ↔ ∀ (g h : GL n R) (A B : Matrix n n R),
      eval (Sum.elim (fun p => ((g : Matrix n n R) * A * (h⁻¹ : GL n R)) p.1 p.2)
        fun p => ((h : Matrix n n R) * B * (g⁻¹ : GL n R)) p.1 p.2) P =
          eval (Sum.elim (fun p => A p.1 p.2) fun p => B p.1 p.2) P :=
  Iff.rfl

/-- Invariance under both groups implies invariance under the second. -/
theorem invariants_le_rightInvariants : invariants R n ≤ rightInvariants R n := fun P hP h A B ↦
  by simpa using hP 1 h A B

/-- The signed contraction is equivariant: acting on a pair by `(g, h)` conjugates its signed
contraction by `g`. -/
theorem eval_contractionPullback_mul_mul_inv (g h : GL n R) (A B : Matrix n n R)
    (Q : MvPolynomial (n × n) R) :
    eval (Sum.elim (fun p => ((g : Matrix n n R) * A * (h⁻¹ : GL n R)) p.1 p.2)
      fun p => ((h : Matrix n n R) * B * (g⁻¹ : GL n R)) p.1 p.2) (contractionPullback R n Q) =
        eval (fun p => ((g : Matrix n n R) * -(A * B) * (g⁻¹ : GL n R)) p.1 p.2) Q := by
  have key : -((g : Matrix n n R) * A * (h⁻¹ : GL n R) *
      ((h : Matrix n n R) * B * (g⁻¹ : GL n R))) =
        (g : Matrix n n R) * -(A * B) * (g⁻¹ : GL n R) := by
    simp [Matrix.mul_assoc]
  rw [eval_contractionPullback, key]

/-- Every pullback along the signed contraction is invariant under the second group. -/
theorem contractionPullback_mem_rightInvariants (Q : MvPolynomial (n × n) R) :
    contractionPullback R n Q ∈ rightInvariants R n := fun h A B ↦ by
  simpa using eval_contractionPullback_mul_mul_inv 1 h A B Q

/-- A pullback along the signed contraction is invariant under both groups exactly when the
original polynomial function on matrices is invariant under conjugation. -/
theorem contractionPullback_mem_invariants_iff {Q : MvPolynomial (n × n) R} :
    contractionPullback R n Q ∈ invariants R n ↔ Q ∈ Matrix.conjInvariants R n := by
  rw [Matrix.mem_conjInvariants_iff]
  refine ⟨fun hQ g Z ↦ ?_, fun hQ g h A B ↦ ?_⟩
  · have := hQ g g (-Z) 1
    rw [eval_contractionPullback_mul_mul_inv, eval_contractionPullback] at this
    simpa only [Matrix.mul_one, neg_neg] using this
  · rw [eval_contractionPullback_mul_mul_inv, eval_contractionPullback, hQ]

end CommRing

section Field

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Over an infinite field, an invariant of the second group is the pullback, along the signed
contraction, of its pullback along the section `Z ↦ (-Z, 1)`. -/
theorem contractionPullback_sectionPullback_of_mem_rightInvariants [Infinite K]
    {P : MvPolynomial (n × n ⊕ n × n) K} (hP : P ∈ rightInvariants K n) :
    contractionPullback K n (sectionPullback K n P) = P := by
  -- Multiply by the generic determinant of `B`: the identity then holds at every point.
  refine mul_left_cancel₀ ((map_ne_zero_iff _ (rename_injective _ Sum.inr_injective)).mpr
    (Matrix.det_mvPolynomialX_ne_zero n K)) (MvPolynomial.funext fun x ↦ ?_)
  set A : Matrix n n K := Matrix.of fun i j => x (Sum.inl (i, j))
  set B : Matrix n n K := Matrix.of fun i j => x (Sum.inr (i, j))
  have hx : x = Sum.elim (fun p => A p.1 p.2) fun p => B p.1 p.2 := by
    ext (p | p) <;> simp [A, B]
  rw [map_mul, map_mul, eval_rename, Matrix.eval_det_mvPolynomialX]
  simp only [Function.comp_apply]
  by_cases hB : B.det = 0
  · rw [hB, zero_mul, zero_mul]
  congr 1
  -- On the pairs with `B` invertible, act by `h = B⁻¹` to move `(A, B)` to `(A * B, 1)`.
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)
  have := hP (Matrix.GeneralLinearGroup.mkOfDetNeZero B hB)⁻¹ A B
  simp only [inv_inv, Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hBB]
    at this
  rw [hx, eval_contractionPullback, eval_sectionPullback, neg_neg, ← this]

/-- **The quotient by the second group.** Over an infinite field, the polynomial functions on
pairs of square matrices invariant under `h • (A, B) = (A * h⁻¹, h * B)` are exactly the
pullbacks along the signed contraction `(A, B) ↦ -(A * B)`. -/
theorem range_contractionPullback [Infinite K] :
    (contractionPullback K n).range = rightInvariants K n :=
  le_antisymm (by rintro _ ⟨Q, rfl⟩; exact contractionPullback_mem_rightInvariants Q)
    fun P hP ↦ ⟨_, contractionPullback_sectionPullback_of_mem_rightInvariants hP⟩

variable (K n) in
/-- Over an infinite field, pulling back along the signed contraction is an isomorphism from the
polynomial functions on square matrices onto the polynomial functions on pairs invariant under
`h • (A, B) = (A * h⁻¹, h * B)`. -/
noncomputable def rightInvariantsEquiv [Infinite K] :
    MvPolynomial (n × n) K ≃ₐ[K] rightInvariants K n :=
  (AlgEquiv.ofInjective _ contractionPullback_injective).trans
    (Subalgebra.equivOfEq _ _ range_contractionPullback)

@[simp]
theorem coe_rightInvariantsEquiv_apply [Infinite K] (Q : MvPolynomial (n × n) K) :
    (rightInvariantsEquiv K n Q : MvPolynomial (n × n ⊕ n × n) K) = contractionPullback K n Q := by
  simp [rightInvariantsEquiv]

@[simp]
theorem rightInvariantsEquiv_symm_apply [Infinite K] (P : rightInvariants K n) :
    (rightInvariantsEquiv K n).symm P = sectionPullback K n P :=
  (rightInvariantsEquiv K n).symm_apply_eq.mpr <| Subtype.ext <|
    (contractionPullback_sectionPullback_of_mem_rightInvariants P.property).symm

/-- **The quotient by both groups.** Over an infinite field, a polynomial function on pairs of
square matrices is invariant under `(g, h) • (A, B) = (g * A * h⁻¹, h * B * g⁻¹)` exactly when it
is the pullback along the signed contraction of a polynomial function on matrices invariant under
conjugation. -/
theorem mem_invariants_iff_exists_contractionPullback [Infinite K]
    {P : MvPolynomial (n × n ⊕ n × n) K} :
    P ∈ invariants K n ↔ ∃ Q ∈ Matrix.conjInvariants K n, contractionPullback K n Q = P := by
  refine ⟨fun hP ↦ ?_, ?_⟩
  · have hPQ := contractionPullback_sectionPullback_of_mem_rightInvariants
      (invariants_le_rightInvariants hP)
    refine ⟨sectionPullback K n P, ?_, hPQ⟩
    rw [← contractionPullback_mem_invariants_iff, hPQ]
    exact hP
  · rintro ⟨Q, hQ, rfl⟩
    exact contractionPullback_mem_invariants_iff.mpr hQ

/-- Over an infinite field, the image of the conjugation invariants under the pullback along the
signed contraction is the subalgebra of invariants of both groups. -/
theorem map_contractionPullback_conjInvariants [Infinite K] :
    (Matrix.conjInvariants K n).map (contractionPullback K n) = invariants K n := by
  ext P
  simp [mem_invariants_iff_exists_contractionPullback]

variable (K n) in
/-- Over an infinite field, pulling back along the signed contraction is an isomorphism from the
conjugation-invariant polynomial functions on square matrices onto the polynomial functions on
pairs invariant under `(g, h) • (A, B) = (g * A * h⁻¹, h * B * g⁻¹)`. -/
noncomputable def invariantsEquiv [Infinite K] : Matrix.conjInvariants K n ≃ₐ[K] invariants K n :=
  ((Matrix.conjInvariants K n).equivMapOfInjective _ contractionPullback_injective).trans
    (Subalgebra.equivOfEq _ _ map_contractionPullback_conjInvariants)

@[simp]
theorem coe_invariantsEquiv_apply [Infinite K] (Q : Matrix.conjInvariants K n) :
    (invariantsEquiv K n Q : MvPolynomial (n × n ⊕ n × n) K) = contractionPullback K n Q := by
  simp [invariantsEquiv]

@[simp]
theorem coe_invariantsEquiv_symm_apply [Infinite K] (P : invariants K n) :
    ((invariantsEquiv K n).symm P : MvPolynomial (n × n) K) = sectionPullback K n P := by
  conv_rhs => rw [← (invariantsEquiv K n).apply_symm_apply P, coe_invariantsEquiv_apply,
    sectionPullback_contractionPullback]

end Field

end TauCeti.FriedbergJacquet.Split
