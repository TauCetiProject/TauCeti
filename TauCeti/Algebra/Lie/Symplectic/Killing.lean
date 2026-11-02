/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import TauCeti.Algebra.Lie.Symplectic.Cartan
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Lie.GeneralLinear.Killing
import TauCeti.Algebra.Lie.OfAssociative
import TauCeti.LinearAlgebra.Matrix.Trace.LinearMap
import TauCeti.Algebra.Lie.BaseChange.Radical
import TauCeti.Algebra.Lie.SkewAdjoint.BaseChange

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

over every field of characteristic other than two. The matrices `Z` with `J Zᵀ J = Z` are exactly
those of `sp l K`, and `Z ↦ Z + J Zᵀ J` maps `gl (2 n) K` onto `sp l K`, acting on it as
multiplication by two. The operator `ad X ∘ ad Y` of `gl (2 n) K` preserves `sp l K`, so twice
its trace on `sp l K` is its trace on `gl (2 n) K`, which is `4 n trace (X * Y)` by the Killing
form of `gl (2 n) K` (`Matrix.killingForm_apply`), plus the trace of its composite with
`Z ↦ J Zᵀ J`, which is `4 trace (X * Y)`.

Composed with the involution `θ X = -Xᵀ` (`LieAlgebra.Symplectic.cartanInvolution`), this gives
`-κ(X, θ X) = (2 n + 2) trace (X * Xᵀ)`, the sum of the squares of the entries of `X` times
`2 n + 2`. Over an ordered field it is positive for every nonzero `X`: the symmetric form
`(X, Y) ↦ -κ(X, θ Y)` is positive definite, so `θ` is a Cartan involution of the real symplectic
Lie algebra.

## Main results

* `TauCeti.isIrreducible_sp_standard`: the standard module of `sp l K` is irreducible.
* `TauCeti.hasTrivialRadical_sp`: `sp l K` has trivial radical over every field of characteristic
  zero; in particular its Killing form is nondegenerate.
* `LieAlgebra.Symplectic.killingForm_apply`: `κ(X, Y) = (2 n + 2) trace (X * Y)` on `sp l K`.
* `LieAlgebra.Symplectic.killingForm_cartanInvolution_apply`:
  `κ(X, θ Y) = -((2 n + 2) trace (X * Yᵀ))`.
* `LieAlgebra.Symplectic.killingForm_cartanInvolution_self_neg`: `κ(X, θ X) < 0` for nonzero `X`
  over an ordered field.

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

end CharZero

end TauCeti

namespace LieAlgebra.Symplectic

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] [Fintype l]

section CommRing

variable {R : Type*} [CommRing R]

/-- The linear involution `Z ↦ J Zᵀ J` of the matrices, whose fixed points form `sp l R`. -/
private noncomputable def jConj : Matrix (l ⊕ l) (l ⊕ l) R →ₗ[R] Matrix (l ⊕ l) (l ⊕ l) R :=
  LinearMap.mulLeft R (J l R) ∘ₗ LinearMap.mulRight R (J l R) ∘ₗ
    (transposeLinearEquiv (l ⊕ l) (l ⊕ l) R R).toLinearMap

private theorem jConj_apply (Z : Matrix (l ⊕ l) (l ⊕ l) R) : jConj Z = J l R * Zᵀ * J l R := by
  simp [jConj, mul_assoc]

private theorem jConj_jConj (Z : Matrix (l ⊕ l) (l ⊕ l) R) : jConj (jConj Z) = Z := by
  simp only [jConj_apply, transpose_mul, J_transpose, transpose_transpose, neg_mul, mul_neg,
    neg_neg, ← mul_assoc]
  simpa only [mul_assoc] using J_mul_mul_J_mul_J Z

/-- The map `Z ↦ Z + J Zᵀ J` into `sp l R`, which is multiplication by two on `sp l R`. -/
private noncomputable def symmetrize : Matrix (l ⊕ l) (l ⊕ l) R →ₗ[R] sp l R where
  toFun Z := ⟨Z + jConj Z, by
    rw [mem_sp_iff_J_mul_transpose_mul_J_eq, ← jConj_apply, map_add, jConj_jConj, add_comm]⟩
  map_add' Z W := by ext1; simp only [map_add, AddMemClass.coe_add]; abel
  map_smul' c Z := by ext1; simp

private theorem coe_symmetrize_apply (Z : Matrix (l ⊕ l) (l ⊕ l) R) :
    (symmetrize Z : Matrix (l ⊕ l) (l ⊕ l) R) = Z + jConj Z :=
  rfl

/-- The trace of `Z ↦ J (A Z B)ᵀ J` on the matrices. -/
private theorem trace_jConj_comp (A B : Matrix (l ⊕ l) (l ⊕ l) R) :
    LinearMap.trace R _ (jConj ∘ₗ LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B) =
      -(J l R * Bᵀ * J l R * A).trace := by
  have h : jConj ∘ₗ LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B =
      LinearMap.mulLeft R (J l R * Bᵀ) ∘ₗ LinearMap.mulRight R (Aᵀ * J l R) ∘ₗ
        (transposeLinearEquiv (l ⊕ l) (l ⊕ l) R R).toLinearMap := by
    ext1 Z
    simp [jConj_apply, transpose_mul, mul_assoc]
  rw [h, trace_mulLeft_comp_mulRight_comp_transpose]
  simp [transpose_mul, J_transpose, mul_assoc]

/-- For `A, B ∈ sp l R`, the operator `Z ↦ J (⁅A, ⁅B, Z⁆⁆)ᵀ J` of the matrices has trace
`4 trace (A * B)`. -/
private theorem trace_jConj_comp_ad_comp_ad {A B : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ sp l R)
    (hB : B ∈ sp l R) :
    LinearMap.trace R _ (jConj ∘ₗ ad R _ A ∘ₗ ad R _ B) = 4 * (A * B).trace := by
  have hA' := (mem_sp_iff_J_mul_transpose_mul_J_eq A).mp hA
  have hB' := (mem_sp_iff_J_mul_transpose_mul_J_eq B).mp hB
  have hBA : J l R * (B * A)ᵀ * J l R = -(A * B) := by
    calc J l R * (B * A)ᵀ * J l R = J l R * Aᵀ * -(J l R * J l R) * Bᵀ * J l R := by
          rw [transpose_mul, J_squared]; noncomm_ring
      _ = -((J l R * Aᵀ * J l R) * (J l R * Bᵀ * J l R)) := by noncomm_ring
      _ = -(A * B) := by rw [hA', hB']
  have hl : jConj ∘ₗ LinearMap.mulLeft R (A * B) =
      jConj ∘ₗ LinearMap.mulLeft R (A * B) ∘ₗ LinearMap.mulRight R 1 := by
    ext1 Z; simp
  have hr : jConj ∘ₗ LinearMap.mulRight R (B * A) =
      jConj ∘ₗ LinearMap.mulLeft R 1 ∘ₗ LinearMap.mulRight R (B * A) := by
    ext1 Z; simp
  rw [ad_comp_ad]
  simp only [LinearMap.comp_add, LinearMap.comp_sub, map_add, map_sub]
  rw [hl, hr]
  simp only [trace_jConj_comp, transpose_one, mul_one, hA', hB', hBA, J_squared, neg_mul, one_mul,
    trace_neg, neg_neg, trace_mul_comm B A]
  ring

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Twice the Killing form of `sp l K` is twice `(2 n + 2) trace (X * Y)`, over every field. -/
private theorem two_mul_killingForm_apply (X Y : sp l K) :
    2 * killingForm K (sp l K) X Y =
      2 * ((2 * Fintype.card l + 2) * ((X : Matrix (l ⊕ l) (l ⊕ l) K) * Y).trace) := by
  set L := ad K (Matrix (l ⊕ l) (l ⊕ l) K) X ∘ₗ ad K (Matrix (l ⊕ l) (l ⊕ l) K) Y with hL
  -- `symmetrize` turns the action of `L` on the matrices into twice its action on `sp l K`.
  have h1 : symmetrize ∘ₗ L ∘ₗ (sp l K).incl.toLinearMap =
      (2 : K) • (ad K (sp l K) X ∘ₗ ad K (sp l K) Y) := by
    ext1 W
    have hW : jConj (L W) = L W := by
      rw [jConj_apply, ← mem_sp_iff_J_mul_transpose_mul_J_eq]
      exact (sp l K).lie_mem X.2 ((sp l K).lie_mem Y.2 W.2)
    apply Subtype.ext
    simp only [LinearMap.comp_apply, coe_symmetrize_apply, LinearMap.smul_apply,
      LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, hW]
    simp [hL, two_smul]
  have h2 : (sp l K).incl.toLinearMap ∘ₗ symmetrize = LinearMap.id + jConj := by
    ext1 Z; simp [coe_symmetrize_apply]
  -- Cycling the trace moves the computation to the matrices.
  have htrace : LinearMap.trace K _ (symmetrize ∘ₗ L ∘ₗ (sp l K).incl.toLinearMap) =
      LinearMap.trace K _ L + LinearMap.trace K _ (jConj ∘ₗ L) := by
    rw [← LinearMap.comp_assoc, ← LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, h2,
      LinearMap.add_comp, map_add, LinearMap.id_comp]
  rw [h1, map_smul, smul_eq_mul, ← killingForm_apply_apply] at htrace
  rw [htrace, hL, ← killingForm_apply_apply, Matrix.killingForm_apply,
    trace_eq_zero_of_mem_sp X.2, Fintype.card_sum, trace_jConj_comp_ad_comp_ad X.2 Y.2]
  push_cast
  ring

variable [NeZero (2 : K)]

/-- **The Killing form of the symplectic Lie algebra**: for `n = card l`, so that
`sp l K ⊆ gl (2 n) K`, it is `κ(X, Y) = (2 n + 2) trace (X * Y)`, over every field of
characteristic other than two. -/
theorem killingForm_apply (X Y : sp l K) :
    killingForm K (sp l K) X Y =
      (2 * Fintype.card l + 2) * ((X : Matrix (l ⊕ l) (l ⊕ l) K) * Y).trace :=
  mul_left_cancel₀ two_ne_zero (two_mul_killingForm_apply X Y)

/-- The Killing form of `sp l K` twisted by the involution `θ Y = -Yᵀ`:
`κ(X, θ Y) = -((2 n + 2) trace (X * Yᵀ))`. -/
theorem killingForm_cartanInvolution_apply (X Y : sp l K) :
    killingForm K (sp l K) X (cartanInvolution l K Y) =
      -((2 * Fintype.card l + 2) *
        ((X : Matrix (l ⊕ l) (l ⊕ l) K) * (Y : Matrix (l ⊕ l) (l ⊕ l) K)ᵀ).trace) := by
  rw [killingForm_apply, coe_cartanInvolution, mul_neg, trace_neg, mul_neg]

end Field

/-- **`θ X = -Xᵀ` is a Cartan involution of `sp l K`** over an ordered field: `κ(X, θ X) < 0`
for every nonzero `X`, since `-κ(X, θ X)` is `2 n + 2` times the sum of the squares of the
entries of `X`. -/
theorem killingForm_cartanInvolution_self_neg {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {X : sp l K} (hX : X ≠ 0) :
    killingForm K (sp l K) X (cartanInvolution l K X) < 0 := by
  rw [killingForm_cartanInvolution_apply, neg_lt_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (X : Matrix (l ⊕ l) (l ⊕ l) K) i j ≠ 0 := by
    by_contra! h
    exact hX (Subtype.ext (Matrix.ext h))
  have htrace : 0 < ((X : Matrix (l ⊕ l) (l ⊕ l) K) * (X : Matrix (l ⊕ l) (l ⊕ l) K)ᵀ).trace := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
        ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩
  positivity

end LieAlgebra.Symplectic
