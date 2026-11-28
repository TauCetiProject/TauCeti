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
# Signed hermitian spaces and adjoints

Let `K` be a commutative ring with a ring endomorphism `σ` (the involution: the identity for
orthogonal and symplectic forms, the Galois conjugation of a quadratic extension for hermitian and
skew-hermitian forms) and let `ε = ±1`. A **signed hermitian space** is a `K`-module `V` with a
nondegenerate `ε`-hermitian form: a pairing `h : V × V → K`, `σ`-semilinear in the first
variable and linear in the second, with `h w v = ε σ (h v w)`.

Over a field, let `(V₁, h₁)` and `(V₂, h₂)` be signed hermitian spaces of the same sign, with `V₁`
finite-dimensional. Every linear map `X : V₁ → V₂` has a unique adjoint `X^τ : V₂ → V₁`,
characterized by `h₂ (X v) w = h₁ v (X^τ w)`. The adjoint is `σ`-semilinear in `X` and reverses
composition; when `V₂` is finite-dimensional too it is an involution. The two spaces must carry
their own forms: for the lines `⟨1⟩` and `⟨a⟩`, with forms `σ x * y` and `σ x * a * y`, the adjoint
of the identity map from `⟨a⟩` to `⟨1⟩` is multiplication by `a⁻¹`, not the identity.

On a single finite-dimensional signed hermitian space this gives the adjoint `a*` of an
endomorphism `a`, characterized by `h (a v) w = h v (a* w)`. This is the adjoint that defines the
unitary group `{g | g* g = 1}` and its Lie algebra `{X | X* = -X}`.

## Main definitions

* `TauCeti.SignedHermitianSpace K V σ ε`: a nondegenerate `ε`-hermitian form on `V`;
* `TauCeti.signedHermitianHomAdjoint H₁ H₂`: the adjoint, as a `σ`-semilinear map
  `(V₁ →ₗ[K] V₂) →ₛₗ[σ] (V₂ →ₗ[K] V₁)`;
* `TauCeti.signedHermitianAdjoint H`: the adjoint `signedHermitianHomAdjoint H H`, as a
  `σ`-semilinear map on `Module.End K V`;
* `TauCeti.SignedHermitianSpace.standard`: the standard hermitian form `∑ σ (v i) * w i` on
  `n → K`, whose adjoint is the conjugate transpose
  (`TauCeti.signedHermitianHomAdjoint_standard_toLin'`,
  `TauCeti.signedHermitianAdjoint_standard_toLin'`);
* `TauCeti.SignedHermitianSpace.diagonal σ ε a`: the diagonal space `⟨a₁, …, aₙ⟩`, the form
  `∑ σ (v i) * a i * w i` on `n → K`.

## Main statements

* `TauCeti.signedHermitianHomAdjoint_unique`, `TauCeti.signedHermitianAdjoint_unique`: a map `Y`
  with `h₂ (X v) w = h₁ v (Y w)` is the adjoint of `X`;
* `TauCeti.signedHermitianHomAdjoint_comp`, `TauCeti.signedHermitianAdjoint_comp`: the adjoint
  reverses composition;
* `TauCeti.signedHermitianHomAdjoint_signedHermitianHomAdjoint`,
  `TauCeti.signedHermitianAdjoint_involutive`: `X^τ^τ = X`;
* `TauCeti.signedHermitianAdjoint_id`: the adjoint of the identity is the identity;
* `TauCeti.SignedHermitianSpace.map_map_eq_of_nontrivial`: on a nonzero signed hermitian space
  over a domain, `σ σ = id`.

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

/-- On a nonzero signed hermitian space over a domain, the involution squares to the identity:
`σ σ` fixes every value of the form, in particular `a h v w` for a nonzero value `h v w`. -/
theorem map_map_eq_of_nontrivial [IsDomain K] (H : SignedHermitianSpace K V σ ε) [Nontrivial V]
    (a : K) : σ (σ a) = a := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ : ∃ w, H.form v w ≠ 0 := by
    by_contra! h
    exact hv (H.separatingLeft v h)
  have h2 (x y : V) : σ (σ (H.form x y)) = H.form x y := by
    conv_rhs => rw [H.form_swap y x, H.form_swap x y]
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have := h2 v (a • w)
  simp only [map_smul, smul_eq_mul, map_mul, h2] at this
  exact mul_right_cancel₀ hw this

end SignedHermitianSpace

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K} {ε : ℤˣ}

/-! ### The adjoint of a linear map between two signed hermitian spaces -/

section HomAdjoint

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]
  (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε)

private theorem eq_of_forall_form_apply_eq {Y Y' : V₂ →ₗ[K] V₁}
    (h : ∀ v w, H₁.form v (Y w) = H₁.form v (Y' w)) : Y = Y' :=
  LinearMap.ext fun w ↦ sub_eq_zero.1 <| H₁.separatingRight _ fun v ↦ by
    rw [map_sub, h, sub_self]

variable [FiniteDimensional K V₁]

/-- Every linear map out of a finite-dimensional signed hermitian space has an adjoint. -/
private theorem exists_form_apply_eq (X : V₁ →ₗ[K] V₂) :
    ∃ Y : V₂ →ₗ[K] V₁, ∀ v w, H₂.form (X v) w = H₁.form v (Y w) :=
  LinearMap.exists_linearMap_forall_apply_eq_apply H₁.separatingRight
    (H₂.form.comp X : V₁ →ₛₗ[σ] V₂ →ₗ[K] K)

/-- A chosen adjoint of `X`, before its semilinearity in `X` is established. -/
private noncomputable def homAdjointAux (X : V₁ →ₗ[K] V₂) : V₂ →ₗ[K] V₁ :=
  (exists_form_apply_eq H₁ H₂ X).choose

private theorem form_homAdjointAux (X : V₁ →ₗ[K] V₂) (v : V₁) (w : V₂) :
    H₁.form v (homAdjointAux H₁ H₂ X w) = H₂.form (X v) w :=
  ((exists_form_apply_eq H₁ H₂ X).choose_spec v w).symm

/-- The **adjoint** `X^τ : V₂ → V₁` of a linear map `X : V₁ → V₂` between signed hermitian spaces
of the same sign, `V₁` finite-dimensional: the unique linear map with `h₂ (X v) w = h₁ v (X^τ w)`
(`signedHermitianHomAdjoint_form_right`, `signedHermitianHomAdjoint_unique`). It is
`σ`-semilinear in `X`: `(c • X)^τ = σ c • X^τ`. -/
noncomputable def signedHermitianHomAdjoint : (V₁ →ₗ[K] V₂) →ₛₗ[σ] (V₂ →ₗ[K] V₁) where
  toFun := homAdjointAux H₁ H₂
  map_add' X Y := eq_of_forall_form_apply_eq H₁ fun v w ↦ by
    simp [form_homAdjointAux, map_add]
  map_smul' c X := eq_of_forall_form_apply_eq H₁ fun v w ↦ by
    simp [form_homAdjointAux]

/-- The defining property of the adjoint: `h₁ v (X^τ w) = h₂ (X v) w`. -/
@[simp]
theorem signedHermitianHomAdjoint_form_right (X : V₁ →ₗ[K] V₂) (v : V₁) (w : V₂) :
    H₁.form v (signedHermitianHomAdjoint H₁ H₂ X w) = H₂.form (X v) w :=
  form_homAdjointAux H₁ H₂ X v w

/-- The adjoint moves to the other side: `h₁ (X^τ w) v = h₂ w (X v)`. -/
@[simp]
theorem signedHermitianHomAdjoint_form_left (X : V₁ →ₗ[K] V₂) (w : V₂) (v : V₁) :
    H₁.form (signedHermitianHomAdjoint H₁ H₂ X w) v = H₂.form w (X v) := by
  rw [H₁.form_swap, signedHermitianHomAdjoint_form_right, ← H₂.form_swap]

/-- **Uniqueness of the adjoint.** A linear map `Y : V₂ → V₁` with `h₂ (X v) w = h₁ v (Y w)` for
all `v`, `w` is the adjoint of `X`. -/
theorem signedHermitianHomAdjoint_unique {X : V₁ →ₗ[K] V₂} {Y : V₂ →ₗ[K] V₁}
    (h : ∀ v w, H₂.form (X v) w = H₁.form v (Y w)) : signedHermitianHomAdjoint H₁ H₂ X = Y :=
  eq_of_forall_form_apply_eq H₁ fun v w ↦ by rw [signedHermitianHomAdjoint_form_right, h]

/-- A linear map `Y` is the adjoint of `X` exactly when `h₂ (X v) w = h₁ v (Y w)` for all `v`,
`w`. -/
theorem signedHermitianHomAdjoint_eq_iff {X : V₁ →ₗ[K] V₂} {Y : V₂ →ₗ[K] V₁} :
    signedHermitianHomAdjoint H₁ H₂ X = Y ↔ ∀ v w, H₂.form (X v) w = H₁.form v (Y w) :=
  ⟨fun h v w ↦ by rw [← h, signedHermitianHomAdjoint_form_right],
    signedHermitianHomAdjoint_unique H₁ H₂⟩

/-- The adjoint of the adjoint is the original map: `X^τ^τ = X`. -/
@[simp]
theorem signedHermitianHomAdjoint_signedHermitianHomAdjoint [FiniteDimensional K V₂]
    (X : V₁ →ₗ[K] V₂) :
    signedHermitianHomAdjoint H₂ H₁ (signedHermitianHomAdjoint H₁ H₂ X) = X :=
  signedHermitianHomAdjoint_unique H₂ H₁ fun w v ↦ signedHermitianHomAdjoint_form_left H₁ H₂ X w v

/-- The adjoint reverses composition: `(Y ∘ X)^τ = X^τ ∘ Y^τ`. -/
theorem signedHermitianHomAdjoint_comp [FiniteDimensional K V₂] (H₃ : SignedHermitianSpace K V₃ σ ε)
    (X : V₁ →ₗ[K] V₂) (Y : V₂ →ₗ[K] V₃) :
    signedHermitianHomAdjoint H₁ H₃ (Y ∘ₗ X) =
      signedHermitianHomAdjoint H₁ H₂ X ∘ₗ signedHermitianHomAdjoint H₂ H₃ Y :=
  signedHermitianHomAdjoint_unique H₁ H₃ fun v w ↦ by simp

/-- The adjoint commutes with scalars from a ring `F` of scalars of `K` that `σ` fixes:
`(c • X)^τ = c • X^τ` when `σ c = c`, for instance for `c` in the base field of a quadratic
extension. -/
theorem signedHermitianHomAdjoint_smul_of_map_algebraMap {F : Type*} [CommSemiring F]
    [Algebra F K] [Module F V₁] [Module F V₂] [IsScalarTower F K V₁] [IsScalarTower F K V₂]
    {c : F} (hc : σ (algebraMap F K c) = algebraMap F K c) (X : V₁ →ₗ[K] V₂) :
    signedHermitianHomAdjoint H₁ H₂ (c • X) = c • signedHermitianHomAdjoint H₁ H₂ X := by
  rw [← algebraMap_smul K c X, LinearMap.map_smulₛₗ, hc, algebraMap_smul]

end HomAdjoint

/-! ### The adjoint of an endomorphism -/

section Adjoint

variable (H : SignedHermitianSpace K V σ ε) [FiniteDimensional K V]

/-- The **adjoint** `a*` of an endomorphism `a` of a finite-dimensional signed hermitian space
`(V, h)`: the unique endomorphism with `h (a v) w = h v (a* w)`
(`signedHermitianAdjoint_form_right`, `signedHermitianAdjoint_unique`). It is `σ`-semilinear in
`a`: `(c • a)* = σ c • a*`. It is the adjoint `signedHermitianHomAdjoint H H` of `a` as a linear
map from `(V, h)` to itself (`signedHermitianHomAdjoint_self`). -/
noncomputable def signedHermitianAdjoint : Module.End K V →ₛₗ[σ] Module.End K V :=
  signedHermitianHomAdjoint H H

/-- On a single space the adjoint of a linear map is the adjoint of an endomorphism. -/
@[simp]
theorem signedHermitianHomAdjoint_self (a : Module.End K V) :
    signedHermitianHomAdjoint H H a = signedHermitianAdjoint H a :=
  (rfl)

/-- The defining property of the adjoint: `h v (a* w) = h (a v) w`. -/
@[simp]
theorem signedHermitianAdjoint_form_right (a : Module.End K V) (v w : V) :
    H.form v (signedHermitianAdjoint H a w) = H.form (a v) w :=
  signedHermitianHomAdjoint_form_right H H a v w

/-- The adjoint moves to the other side: `h (a* v) w = h v (a w)`. -/
@[simp]
theorem signedHermitianAdjoint_form_left (a : Module.End K V) (v w : V) :
    H.form (signedHermitianAdjoint H a v) w = H.form v (a w) :=
  signedHermitianHomAdjoint_form_left H H a v w

/-- **Uniqueness of the adjoint.** An endomorphism `b` with `h (a v) w = h v (b w)` for all `v`,
`w` is the adjoint of `a`. -/
theorem signedHermitianAdjoint_unique {a b : Module.End K V}
    (h : ∀ v w, H.form (a v) w = H.form v (b w)) : signedHermitianAdjoint H a = b :=
  signedHermitianHomAdjoint_unique H H h

/-- An endomorphism `b` is the adjoint of `a` exactly when `h (a v) w = h v (b w)` for all `v`,
`w`. -/
theorem signedHermitianAdjoint_eq_iff {a b : Module.End K V} :
    signedHermitianAdjoint H a = b ↔ ∀ v w, H.form (a v) w = H.form v (b w) :=
  signedHermitianHomAdjoint_eq_iff H H

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
  signedHermitianHomAdjoint_comp H H H b a

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
  signedHermitianHomAdjoint_signedHermitianHomAdjoint H H a

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

/-- Between standard hermitian spaces the adjoint of a matrix is its conjugate transpose: the
transpose of the matrix with `σ` applied to each entry. For a star ring and `σ = starRingEnd K`
this is `Matrix.conjTranspose`. -/
theorem signedHermitianHomAdjoint_standard_toLin' [RingHomInvPair σ σ] {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (A : Matrix m n K) :
    signedHermitianHomAdjoint (SignedHermitianSpace.standard σ n)
        (SignedHermitianSpace.standard σ m) (Matrix.toLin' A) =
      Matrix.toLin' (A.map σ).transpose := by
  refine signedHermitianHomAdjoint_unique _ _ fun v w ↦ ?_
  simp only [SignedHermitianSpace.standard_form_apply, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- In the standard hermitian space the adjoint of a matrix is its conjugate transpose: the
transpose of the matrix with `σ` applied to each entry. For a star ring and `σ = starRingEnd K`
this is `Matrix.conjTranspose`. -/
theorem signedHermitianAdjoint_standard_toLin' [RingHomInvPair σ σ] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) :
    signedHermitianAdjoint (SignedHermitianSpace.standard σ n) (Matrix.toLin' A) =
      Matrix.toLin' (A.map σ).transpose :=
  signedHermitianHomAdjoint_standard_toLin' A

end Field

end TauCeti
