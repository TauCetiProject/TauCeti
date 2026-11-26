/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Algebra.Ring.Int.Units
public import TauCeti.LinearAlgebra.SesquilinearForm.Separating
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Signed hermitian spaces and the adjoint of an endomorphism

Let `K` be a commutative ring with a ring endomorphism `σ` (the involution: the identity for
orthogonal and symplectic forms, the Galois conjugation of a quadratic extension for hermitian and
skew-hermitian forms) and let `ε = ±1`. A **signed hermitian space** is a `K`-module `V` with a
nondegenerate `ε`-hermitian form: a pairing `h : V × V → K`, `σ`-semilinear in the first
variable and linear in the second, with `h w v = ε σ (h v w)`.

Over a field, on a finite-dimensional signed hermitian space every endomorphism `a` has a unique
adjoint `a*`, characterized by `h (a v) w = h v (a* w)`. The adjoint is `σ`-semilinear in `a`,
reverses composition and is an involution. This is the adjoint that defines the unitary group
`{g | g* g = 1}` and its Lie algebra `{X | X* = -X}`; the adjoint of a map between two
hermitian spaces can be read off from it on their orthogonal sum.

## Main definitions

* `TauCeti.SignedHermitianSpace K V σ ε`: a nondegenerate `ε`-hermitian form on `V`;
* `TauCeti.signedHermitianAdjoint H`: the adjoint, as a `σ`-semilinear map on `Module.End K V`;
* `TauCeti.SignedHermitianSpace.standard`: the standard hermitian form `∑ σ (v i) * w i` on
  `n → K`, whose adjoint is the conjugate transpose
  (`TauCeti.signedHermitianAdjoint_standard_toLin'`);
* `TauCeti.SignedHermitianSpace.diagonal σ ε a`: the diagonal space `⟨a₁, …, aₙ⟩`, the form
  `∑ σ (v i) * a i * w i` on `n → K`.

## Main statements

* `TauCeti.signedHermitianAdjoint_unique`: an endomorphism `b` with `h (a v) w = h v (b w)` is
  the adjoint of `a`;
* `TauCeti.signedHermitianAdjoint_id`, `TauCeti.signedHermitianAdjoint_comp`: the adjoint of the
  identity is the identity, and `(a ∘ b)* = b* ∘ a*`;
* `TauCeti.signedHermitianAdjoint_involutive`: `a** = a`.

## References

* R. Kurinczuk, D. Skodlerack and S. Stevens, *Endo-parameters for p-adic classical groups*,
  Invent. Math. 223 (2021), 597–723, §3.3.
-/

public section

open Module

namespace TauCeti

section CommRing

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {σ : K →+* K} {ε : ℤˣ}

variable (K V σ ε) in
/-- A **signed hermitian space** `(V, h)` over a commutative ring `K` with involution `σ`, of sign
`ε = ±1`: a form `h` on `V`, `σ`-semilinear in the first variable and linear in the second, which is
`ε`-hermitian, `h w v = ε σ (h v w)`, and nondegenerate. For `σ = id` and `ε = 1` (resp. `-1`)
these are the nondegenerate symmetric (resp. skew-symmetric) bilinear forms; for the conjugation
of a quadratic extension they are the hermitian (resp. skew-hermitian) forms.

Only left separation is stored: by `ε`-hermitian symmetry it gives right separation
(`SignedHermitianSpace.nondegenerate`). -/
@[ext]
structure SignedHermitianSpace where
  /-- The form, `σ`-semilinear in the first variable and linear in the second. -/
  form : V →ₛₗ[σ] V →ₗ[K] K
  /-- The form is `ε`-hermitian. -/
  form_swap : ∀ v w, form w v = ε • σ (form v w)
  /-- The only vector orthogonal to every vector is zero. -/
  separatingLeft : form.SeparatingLeft

namespace SignedHermitianSpace

variable (H : SignedHermitianSpace K V σ ε)

/-- A signed hermitian form is reflexive: `h v w = 0` if and only if `h w v = 0`. -/
theorem isRefl : H.form.IsRefl := fun v w hvw ↦ by
  rw [H.form_swap, hvw, map_zero, smul_zero]

/-- The value `h x x` of an `ε`-hermitian form satisfies `σ (h x x) = ε h x x`: it is fixed by the
involution for a hermitian form and negated by it for a skew-hermitian one. -/
theorem apply_form_self (x : V) : σ (H.form x x) = ε • H.form x x := by
  conv_rhs => rw [H.form_swap x x]
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- A signed hermitian form separates on the right as well. -/
theorem separatingRight : H.form.SeparatingRight := fun w hw ↦
  H.separatingLeft w fun v ↦ H.isRefl _ _ (hw v)

/-- A signed hermitian form is nondegenerate. -/
theorem nondegenerate : H.form.Nondegenerate :=
  ⟨H.separatingLeft, H.separatingRight⟩

/-- A signed hermitian form of sign `1` is hermitian symmetric in the sense of Mathlib's
`LinearMap.IsSymm`. -/
theorem isSymm (H : SignedHermitianSpace K V σ 1) : H.form.IsSymm :=
  ⟨fun v w ↦ by rw [H.form_swap v w, one_smul]⟩

/-! ### Diagonal spaces -/

section Diagonal

variable [RingHomInvPair σ σ]

variable (σ ε) in
/-- The **diagonal space** `⟨a₁, …, aₙ⟩`: the module `n → K` with the form
`h x y = ∑ σ (x i) * a i * y i` of the diagonal matrix `diag (a₁, …, aₙ)`, for non-zero-divisors
`a i` with `σ (a i) = ε • a i`. Over a field, `standard σ n` is the case `ε = 1`, `a i = 1`. -/
def diagonal {n : Type*} [Fintype n] [DecidableEq n] (a : n → K) (ha : ∀ i, σ (a i) = ε • a i)
    (ha₀ : ∀ i, a i ∈ nonZeroDivisors K) : SignedHermitianSpace K (n → K) σ ε where
  form := Matrix.toLinearMapₛₗ₂' K σ (RingHom.id K) (Matrix.diagonal a)
  form_swap x y := by
    simp only [Matrix.toLinearMapₛₗ₂'_diagonal_apply, map_sum, map_mul, ha,
      RingHomInvPair.comp_apply_eq₂, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Int.units_smul_eq_cast_mul, Int.units_smul_eq_cast_mul]
    linear_combination (-(σ (y i) * a i * x i)) * Int.cast_units_sq (R := K) ε
  separatingLeft x hx := funext fun j ↦ by
    have hj : σ (x j) * a j = 0 := by
      simpa [Matrix.toLinearMapₛₗ₂'_diagonal_apply, Pi.single_apply] using hx (Pi.single j 1)
    have := (mul_right_mem_nonZeroDivisors_eq_zero_iff (ha₀ j)).1 hj
    exact (map_eq_zero_iff _ (RingHomInvPair.toRingEquiv σ σ).injective).1 this

/-- The form of `⟨a₁, …, aₙ⟩` is `∑ σ (x i) * a i * y i`. -/
@[simp]
theorem diagonal_form_apply {n : Type*} [Fintype n] [DecidableEq n] (a : n → K)
    (ha : ∀ i, σ (a i) = ε • a i) (ha₀ : ∀ i, a i ∈ nonZeroDivisors K) (x y : n → K) :
    (diagonal σ ε a ha ha₀).form x y = ∑ i, σ (x i) * a i * y i :=
  Matrix.toLinearMapₛₗ₂'_diagonal_apply σ a x y

end Diagonal

end SignedHermitianSpace

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K} {ε : ℤˣ}

/-! ### The adjoint of an endomorphism -/

section Adjoint

variable (H : SignedHermitianSpace K V σ ε)

private theorem eq_of_forall_form_apply_eq {b b' : Module.End K V}
    (h : ∀ v w, H.form v (b w) = H.form v (b' w)) : b = b' :=
  LinearMap.ext fun w ↦ sub_eq_zero.1 <| H.separatingRight _ fun v ↦ by
    rw [map_sub, h, sub_self]

variable [FiniteDimensional K V]

/-- Every endomorphism of a finite-dimensional signed hermitian space has an adjoint. -/
private theorem exists_form_apply_eq (a : Module.End K V) :
    ∃ b : Module.End K V, ∀ v w, H.form (a v) w = H.form v (b w) :=
  LinearMap.exists_linearMap_forall_apply_eq_apply H.separatingRight
    (H.form.comp a : V →ₛₗ[σ] V →ₗ[K] K)

/-- A chosen adjoint of `a`, before its semilinearity in `a` is established. -/
private noncomputable def adjointAux (a : Module.End K V) : Module.End K V :=
  (exists_form_apply_eq H a).choose

private theorem form_adjointAux (a : Module.End K V) (v w : V) :
    H.form v (adjointAux H a w) = H.form (a v) w :=
  ((exists_form_apply_eq H a).choose_spec v w).symm

/-- The **adjoint** `a*` of an endomorphism `a` of a finite-dimensional signed hermitian space
`(V, h)`: the unique endomorphism with `h (a v) w = h v (a* w)`
(`signedHermitianAdjoint_form_right`, `signedHermitianAdjoint_unique`). It is `σ`-semilinear in
`a`: `(c • a)* = σ c • a*`. -/
noncomputable def signedHermitianAdjoint : Module.End K V →ₛₗ[σ] Module.End K V where
  toFun := adjointAux H
  map_add' a b := eq_of_forall_form_apply_eq H fun v w ↦ by
    simp [form_adjointAux, map_add]
  map_smul' c a := eq_of_forall_form_apply_eq H fun v w ↦ by
    simp [form_adjointAux]

/-- The defining property of the adjoint: `h v (a* w) = h (a v) w`. -/
@[simp]
theorem signedHermitianAdjoint_form_right (a : Module.End K V) (v w : V) :
    H.form v (signedHermitianAdjoint H a w) = H.form (a v) w :=
  form_adjointAux H a v w

/-- The adjoint moves to the other side: `h (a* v) w = h v (a w)`. -/
@[simp]
theorem signedHermitianAdjoint_form_left (a : Module.End K V) (v w : V) :
    H.form (signedHermitianAdjoint H a v) w = H.form v (a w) := by
  rw [H.form_swap, signedHermitianAdjoint_form_right, ← H.form_swap]

/-- **Uniqueness of the adjoint.** An endomorphism `b` with `h (a v) w = h v (b w)` for all `v`,
`w` is the adjoint of `a`. -/
theorem signedHermitianAdjoint_unique {a b : Module.End K V}
    (h : ∀ v w, H.form (a v) w = H.form v (b w)) : signedHermitianAdjoint H a = b :=
  eq_of_forall_form_apply_eq H fun v w ↦ by rw [signedHermitianAdjoint_form_right, h]

/-- An endomorphism `b` is the adjoint of `a` exactly when `h (a v) w = h v (b w)` for all `v`,
`w`. -/
theorem signedHermitianAdjoint_eq_iff {a b : Module.End K V} :
    signedHermitianAdjoint H a = b ↔ ∀ v w, H.form (a v) w = H.form v (b w) :=
  ⟨fun h v w ↦ by rw [← h, signedHermitianAdjoint_form_right],
    signedHermitianAdjoint_unique H⟩

/-- The adjoint `a*` is the left adjoint of `a` for the flipped form, in the sense of Mathlib's
`LinearMap.IsAdjointPair` (`h.flip (a* v) w = h.flip v (a w)`). -/
theorem isAdjointPair_signedHermitianAdjoint (a : Module.End K V) :
    LinearMap.IsAdjointPair H.form.flip H.form.flip (signedHermitianAdjoint H a) a :=
  fun v w ↦ signedHermitianAdjoint_form_right H a w v

/-- The adjoint of the identity is the identity. -/
@[simp]
theorem signedHermitianAdjoint_id : signedHermitianAdjoint H LinearMap.id = LinearMap.id :=
  signedHermitianAdjoint_unique H fun _ _ ↦ rfl

/-- The adjoint reverses composition: `(a ∘ b)* = b* ∘ a*`. -/
@[simp]
theorem signedHermitianAdjoint_comp (a b : Module.End K V) :
    signedHermitianAdjoint H (a ∘ₗ b) =
      signedHermitianAdjoint H b ∘ₗ signedHermitianAdjoint H a :=
  signedHermitianAdjoint_unique H fun v w ↦ by simp

/-- The adjoint of the identity is the identity, stated with the unit of `Module.End K V`. -/
@[simp]
theorem signedHermitianAdjoint_one : signedHermitianAdjoint H 1 = 1 :=
  signedHermitianAdjoint_id H

/-- The adjoint reverses multiplication in `Module.End K V`: `(a * b)* = b* * a*`. -/
@[simp]
theorem signedHermitianAdjoint_mul (a b : Module.End K V) :
    signedHermitianAdjoint H (a * b) = signedHermitianAdjoint H b * signedHermitianAdjoint H a :=
  signedHermitianAdjoint_comp H a b

/-- The adjoint of the adjoint is the original endomorphism. -/
@[simp]
theorem signedHermitianAdjoint_signedHermitianAdjoint (a : Module.End K V) :
    signedHermitianAdjoint H (signedHermitianAdjoint H a) = a :=
  signedHermitianAdjoint_unique H fun v w ↦ signedHermitianAdjoint_form_left H a v w

/-- Taking adjoints is an involution. -/
theorem signedHermitianAdjoint_involutive : Function.Involutive (signedHermitianAdjoint H) :=
  signedHermitianAdjoint_signedHermitianAdjoint H

end Adjoint

/-! ### The standard hermitian space -/

namespace SignedHermitianSpace

variable (σ) [RingHomInvPair σ σ] (n : Type*) [Fintype n] [DecidableEq n]

/-- The **standard hermitian space** of rank `n` over a field with involution `σ`: the form
`h v w = ∑ i, σ (v i) * w i` on `n → K`, with Gram matrix the identity. For `σ = id` it is the
dot product. -/
noncomputable def standard : SignedHermitianSpace K (n → K) σ 1 where
  form := Matrix.toLinearMapₛₗ₂' K σ (RingHom.id K) 1
  form_swap v w := by
    simp [Matrix.toLinearMapₛₗ₂'_apply, Matrix.one_apply, map_sum, mul_comm]
  separatingLeft v hv := funext fun i ↦ by
    simpa [Matrix.toLinearMapₛₗ₂'_apply, Matrix.one_apply, Pi.single_apply] using
      hv (Pi.single i 1)

variable {σ n}

/-- The standard hermitian form is `h v w = ∑ i, σ (v i) * w i`. -/
@[simp]
theorem standard_form_apply (v w : n → K) :
    (standard σ n).form v w = ∑ i, σ (v i) * w i := by
  simp [standard, Matrix.toLinearMapₛₗ₂'_apply, Matrix.one_apply, mul_comm]

end SignedHermitianSpace

/-- In the standard hermitian space the adjoint of a matrix is its conjugate transpose: the
transpose of the matrix with `σ` applied to each entry. For a star ring and `σ = starRingEnd K`
this is `Matrix.conjTranspose`. -/
theorem signedHermitianAdjoint_standard_toLin' [RingHomInvPair σ σ] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) :
    signedHermitianAdjoint (SignedHermitianSpace.standard σ n) (Matrix.toLin' A) =
      Matrix.toLin' (A.map σ).transpose := by
  refine signedHermitianAdjoint_unique _ fun v w ↦ ?_
  simp only [SignedHermitianSpace.standard_form_apply, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

end Field

end TauCeti
