/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Symplectic.Cartan
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.LinearAlgebra.Matrix.Trace.Positive
import TauCeti.Algebra.Lie.BaseChange.Radical
import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.Algebra.Lie.SkewAdjoint.BaseChange
import TauCeti.Algebra.Lie.SkewAdjoint.Killing
import TauCeti.LinearAlgebra.Matrix.SkewAdjoint
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# The Killing form of the symplectic Lie algebra

The standard module `l ⊕ l → K` of the symplectic Lie algebra `LieAlgebra.Symplectic.sp l K` is
irreducible over every field, as soon as `l` is nonempty. In characteristic zero it follows that
`sp l K` has trivial radical, so by Cartan's criterion its Killing form is nondegenerate. Over an
algebraically closed field the standard module is faithful, trace-free and irreducible, and
`LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` applies; over an arbitrary field of
characteristic zero, `sp l K` becomes the symplectic Lie algebra of an algebraic closure after
extension of scalars (`TauCeti.skewAdjointMatricesLieSubalgebraBaseChangeEquiv`), and triviality
of the radical descends (`LieAlgebra.hasTrivialRadical_baseChange_iff`). This descent follows the
orthogonal case, `TauCeti.hasTrivialRadical_so` in `TauCeti/Algebra/Lie/Orthogonal/Killing.lean`.

The irreducibility argument uses the elements `v ↦ ω(a, v) a` and `v ↦ ω(a, v) b + ω(b, v) a`
of `sp l K`, where `ω(x, y) = x ⬝ᵥ (J *ᵥ y)` is the standard alternating form. Given a nonzero
`v`, choose `a` with `ω(a, v) = 1`. The first element sends `v` to `a`, and the second, for
`b = w`, sends `v` to `w` plus a multiple of `a`, so a Lie submodule containing `v` contains every
vector.

The Killing form itself is explicit. For `n = card l`, so that `sp l K ⊆ gl (2 n) K`, it is

`κ(X, Y) = (2 n + 2) trace (X * Y)`

over every field of characteristic other than two. Since `Jᵀ = -J`, this is the case `ε = -1` of
the Killing form `(m - 2 ε) trace (X * Y)` of the Lie algebra of `m × m` matrices skew-adjoint for
an invertible `J` with `Jᵀ = ε • J` (`TauCeti.killingForm_skewAdjointMatricesLieSubalgebra_apply`).

Composed with the involution `θ X = -Xᵀ` (`LieAlgebra.Symplectic.cartanInvolution`), this gives
`-κ(X, θ X) = (2 n + 2) trace (X * Xᵀ)`, the sum of the squares of the entries of `X` times
`2 n + 2`. Over an ordered field it is positive for every nonzero `X`: the symmetric form
`(X, Y) ↦ -κ(X, θ Y)` is positive definite, so `θ` is a Cartan involution of the real symplectic
Lie algebra.

## Main results

* `TauCeti.isIrreducible_sp_standard`: the standard module of `sp l K` is irreducible.
* `TauCeti.hasTrivialRadical_sp`: `sp l K` has trivial radical over every field of characteristic
  zero; in particular its Killing form is nondegenerate.
* `LinearMap.BilinForm.IsAlt.hasTrivialRadical_skewAdjointLieSubalgebra`: the same for the Lie
  algebra of skew-adjoint endomorphisms of any nondegenerate alternating form.
* `LieAlgebra.Symplectic.killingForm_apply`: `κ(X, Y) = (2 n + 2) trace (X * Y)` on `sp l K`.
* `LieAlgebra.Symplectic.killingForm_cartanInvolution_apply`:
  `κ(X, θ Y) = -((2 n + 2) trace (X * Yᵀ))`.
* `LieAlgebra.Symplectic.killingForm_cartanInvolution_self_neg`: `κ(X, θ X) < 0` for nonzero `X`
  over an ordered field.
* `LieAlgebra.Symplectic.isCartanInvolution_cartanInvolution`: `θ` is a Cartan involution
  (`LieEquiv.IsCartanInvolution`) over an ordered field.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 16 (the symplectic Lie algebras).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2, 5 and 19.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the Killing forms of the classical Lie algebras) and
  Chapter VI, Section 1 (Cartan involutions).
-/

public section

namespace TauCeti

open Matrix _root_.LieAlgebra LieModule
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] [Fintype l]

section CommRing

variable {R : Type*} [CommRing R]

/-- The rank-one symplectic matrix `v ↦ ω(a, v) a` attached to a vector, where `ω` is the
standard alternating form. -/
private def rankOneMatrix (a : l ⊕ l → R) : Matrix (l ⊕ l) (l ⊕ l) R :=
  vecMulVec a (a ᵥ* J l R)

private theorem rankOneMatrix_mem_sp (a : l ⊕ l → R) : rankOneMatrix a ∈ Symplectic.sp l R := by
  rw [Symplectic.mem_sp, rankOneMatrix]
  simp only [transpose_vecMulVec, vecMulVec_mul, mul_vecMulVec, J_mulVec, neg_vecMulVec, neg_neg]

private theorem rankOneMatrix_mulVec (a v : l ⊕ l → R) :
    rankOneMatrix a *ᵥ v = ((a ᵥ* J l R) ⬝ᵥ v) • a := by
  simp [rankOneMatrix, vecMulVec_mulVec]

/-- The symplectic matrix `v ↦ ω(a, v) b + ω(b, v) a` attached to two vectors, where `ω` is the
standard alternating form. -/
private def symmetricMatrix (a b : l ⊕ l → R) : Matrix (l ⊕ l) (l ⊕ l) R :=
  vecMulVec b (a ᵥ* J l R) + vecMulVec a (b ᵥ* J l R)

private theorem symmetricMatrix_mem_sp (a b : l ⊕ l → R) :
    symmetricMatrix a b ∈ Symplectic.sp l R := by
  rw [Symplectic.mem_sp, symmetricMatrix]
  simp only [transpose_add, transpose_vecMulVec, add_mul, mul_add, vecMulVec_mul, mul_vecMulVec,
    J_mulVec, neg_vecMulVec, neg_add, neg_neg]
  exact add_comm _ _

private theorem symmetricMatrix_mulVec (a b v : l ⊕ l → R) :
    symmetricMatrix a b *ᵥ v = ((a ᵥ* J l R) ⬝ᵥ v) • b + ((b ᵥ* J l R) ⬝ᵥ v) • a := by
  simp [symmetricMatrix, add_mulVec, vecMulVec_mulVec]

end CommRing

section Field

variable {K : Type*} [Field K] [Nonempty l]

/-- **The standard module of the symplectic Lie algebra is irreducible** over every field, for a
nonempty index type. -/
instance isIrreducible_sp_standard :
    IsIrreducible K (Symplectic.sp l K) (l ⊕ l → K) := by
  apply IsIrreducible.mk
  intro N hN
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((LieSubmodule.toSubmodule_eq_bot N).not.mpr hN)
  -- The standard alternating form is nondegenerate, so some `a` pairs with `v` to one.
  obtain ⟨a, ha⟩ : ∃ a : l ⊕ l → K, (a ᵥ* J l K) ⬝ᵥ v = 1 := by
    have hJv : J l K *ᵥ v ≠ 0 := fun h ↦ hv0 <| by
      simpa [mulVec_mulVec, J_squared, neg_mulVec] using congrArg (J l K *ᵥ ·) h
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hJv
    refine ⟨Pi.single p ((J l K *ᵥ v) p)⁻¹, ?_⟩
    rw [← dotProduct_mulVec, single_dotProduct, inv_mul_cancel₀ hp]
  have hmem (A : Matrix (l ⊕ l) (l ⊕ l) K) (hA : A ∈ Symplectic.sp l K) : A *ᵥ v ∈ N := by
    have h := N.lie_mem (x := ⟨A, hA⟩) hv
    rwa [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply] at h
  have haN : a ∈ N := by
    simpa [rankOneMatrix_mulVec, ha] using hmem _ (rankOneMatrix_mem_sp a)
  rw [eq_top_iff]
  intro w _
  have h := hmem _ (symmetricMatrix_mem_sp a w)
  rw [symmetricMatrix_mulVec, ha, one_smul] at h
  simpa using N.sub_mem h (N.smul_mem ((w ᵥ* J l K) ⬝ᵥ v) haN)

end Field

section CharZero

variable (K : Type*) [Field K] [CharZero K]

/-- **The symplectic Lie algebra has trivial radical** over every field of characteristic zero.
By Cartan's criterion its Killing form is then nondegenerate. -/
instance hasTrivialRadical_sp : HasTrivialRadical K (Symplectic.sp l K) := by
  let A := AlgebraicClosure K
  have : HasTrivialRadical A (Symplectic.sp l A) := by
    cases isEmpty_or_nonempty l
    · infer_instance
    · exact hasTrivialRadical_of_isIrreducible_of_isFaithful A (Symplectic.sp l A) (l ⊕ l → A)
        fun ⟨_, hx⟩ ↦ by simpa using Symplectic.trace_eq_zero_of_mem_sp hx
  -- After extension of scalars to `A`, `sp l K` becomes `sp l A`: both are skew-adjoint matrix
  -- Lie algebras, for `J l K` and for its image `J l A`.
  have e : A ⊗[K] Symplectic.sp l K ≃ₗ⁅A⁆ Symplectic.sp l A := by
    unfold Symplectic.sp
    rw [← map_J (l := l) (algebraMap K A)]
    exact skewAdjointMatricesLieSubalgebraBaseChangeEquiv A (J l K)
  have : HasTrivialRadical A (A ⊗[K] Symplectic.sp l K) := hasTrivialRadical_of_equiv e.symm
  exact (hasTrivialRadical_baseChange_iff K (Symplectic.sp l K) A).mp this

variable {K} in
/-- **The skew-adjoint endomorphisms of a nondegenerate alternating form have trivial radical**
over every field of characteristic zero: a basis in which the form has matrix `J` identifies their
Lie algebra with `sp (Fin m) K`. By Cartan's criterion its Killing form is then nondegenerate. -/
theorem _root_.LinearMap.BilinForm.IsAlt.hasTrivialRadical_skewAdjointLieSubalgebra {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) : HasTrivialRadical K (skewAdjointLieSubalgebra B) := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  -- `Symplectic.sp (Fin m) K` is by definition the skew-adjoint matrix Lie algebra of `J`.
  have : HasTrivialRadical K (skewAdjointMatricesLieSubalgebra (J (Fin m) K)) :=
    hasTrivialRadical_sp K
  exact hasTrivialRadical_of_equiv (skewAdjointLieEquivOfBasis b B hb)

end CharZero

end TauCeti

namespace LieAlgebra.Symplectic

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] [Fintype l]

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- **The Killing form of the symplectic Lie algebra**: for `n = card l`, so that
`sp l K ⊆ gl (2 n) K`, it is `κ(X, Y) = (2 n + 2) trace (X * Y)`, over every field of
characteristic other than two. -/
theorem killingForm_apply (X Y : sp l K) :
    killingForm K (sp l K) X Y =
      (2 * Fintype.card l + 2) * ((X : Matrix (l ⊕ l) (l ⊕ l) K) * Y).trace := by
  have := TauCeti.killingForm_skewAdjointMatricesLieSubalgebra_apply (J := J l K) (ε := -1)
    (by rw [J_transpose, neg_one_smul]) (isUnit_of_mul_self_eq_neg_one (J_squared l K)) X Y
  refine this.trans ?_
  rw [Fintype.card_sum]
  push_cast
  ring

/-- The Killing form of `sp l K` twisted by the involution `θ Y = -Yᵀ`:
`κ(X, θ Y) = -((2 n + 2) trace (X * Yᵀ))`. -/
theorem killingForm_cartanInvolution_apply (X Y : sp l K) :
    killingForm K (sp l K) X (cartanInvolution l K Y) =
      -((2 * Fintype.card l + 2) *
        ((X : Matrix (l ⊕ l) (l ⊕ l) K) * (Y : Matrix (l ⊕ l) (l ⊕ l) K)ᵀ).trace) := by
  rw [killingForm_apply, coe_cartanInvolution, mul_neg, trace_neg, mul_neg]

end Field

/-- Over an ordered field, `κ(X, θ X) < 0` for every nonzero `X ∈ sp l K`, where `θ X = -Xᵀ`,
since `-κ(X, θ X)` is `2 n + 2` times the sum of the squares of the entries of `X`. -/
theorem killingForm_cartanInvolution_self_neg {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {X : sp l K} (hX : X ≠ 0) :
    killingForm K (sp l K) X (cartanInvolution l K X) < 0 := by
  rw [killingForm_cartanInvolution_apply, neg_lt_zero]
  have htrace : 0 < ((X : Matrix (l ⊕ l) (l ⊕ l) K) * (X : Matrix (l ⊕ l) (l ⊕ l) K)ᵀ).trace :=
    Matrix.trace_mul_transpose_pos (fun h ↦ hX (Subtype.ext h))
  positivity

/-- **`θ X = -Xᵀ` is a Cartan involution of `sp l K`** over an ordered field. -/
theorem isCartanInvolution_cartanInvolution {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : (cartanInvolution l K).IsCartanInvolution :=
  LieEquiv.isCartanInvolution_iff.mpr
    ⟨cartanInvolution_cartanInvolution, fun _ ↦ killingForm_cartanInvolution_self_neg⟩

end LieAlgebra.Symplectic
