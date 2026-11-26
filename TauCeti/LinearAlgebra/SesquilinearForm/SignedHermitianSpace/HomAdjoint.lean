/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry

/-!
# The adjoint of a linear map between two signed hermitian spaces

Let `(V₁, h₁)` and `(V₂, h₂)` be signed hermitian spaces of the same sign over a field `K` with
involution `σ`, with `V₁` finite-dimensional. Every linear map `X : V₁ → V₂` has a unique adjoint
`X^τ : V₂ → V₁`, characterized by `h₂ (X v) w = h₁ v (X^τ w)`. This is the adjoint between the two
spaces of a symmetric pair such as `(U(V₁ ⊥ V₂), U(V₁) × U(V₂))`, whose infinitesimal symmetric
space is `Hom(V₂, V₁)`.

The adjoint is `σ`-semilinear in `X` and reverses composition; when `V₂` is finite-dimensional too
it is an involution. It agrees with the adjoint `TauCeti.signedHermitianAdjoint` of an endomorphism
when `(V₁, h₁) = (V₂, h₂)`. The adjoint of an isometric equivalence is
its inverse; in particular an automorphism of `(V, h)` lies in the unitary group `U(V)` exactly
when its adjoint is its inverse.

The two spaces must carry their own forms: for the lines `⟨1⟩` and `⟨a⟩`, with forms
`σ x * y` and `σ x * a * y`, the adjoint of the identity map from `⟨a⟩` to `⟨1⟩` is multiplication
by `a⁻¹`, not the identity.

## Main definitions

* `TauCeti.signedHermitianHomAdjoint H₁ H₂`: the adjoint, as a `σ`-semilinear map
  `(V₁ →ₗ[K] V₂) →ₛₗ[σ] (V₂ →ₗ[K] V₁)`.

## Main statements

* `TauCeti.signedHermitianHomAdjoint_form_right`, `TauCeti.signedHermitianHomAdjoint_unique`: the
  defining property `h₁ v (X^τ w) = h₂ (X v) w`, and uniqueness.
* `TauCeti.signedHermitianHomAdjoint_comp`: `(Y ∘ X)^τ = X^τ ∘ Y^τ`.
* `TauCeti.signedHermitianHomAdjoint_signedHermitianHomAdjoint`: `X^τ^τ = X`.
* `TauCeti.signedHermitianHomAdjoint_self`: on a single space it is
  `TauCeti.signedHermitianAdjoint`.
* `TauCeti.signedHermitianHomAdjoint_isometryEquiv`: the adjoint of an isometric equivalence is its
  inverse.
* `TauCeti.signedHermitianHomAdjoint_standard_toLin'`: between standard hermitian spaces the adjoint
  of a matrix is its conjugate transpose.
* `TauCeti.SignedHermitianSpace.mem_isometryGroup_iff_signedHermitianAdjoint_eq_symm`: `g ∈ U(V)`
  exactly when `g* = g⁻¹`.
-/

public section

open Module

namespace TauCeti

variable {K V V₁ V₂ V₃ : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁]
  [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃] {σ : K →+* K}
  {ε : ℤˣ}

section Adjoint

variable (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε)

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

/-- On a single space the adjoint of a linear map is the adjoint of an endomorphism. -/
@[simp]
theorem signedHermitianHomAdjoint_self (H : SignedHermitianSpace K V σ ε) [FiniteDimensional K V]
    (a : Module.End K V) : signedHermitianHomAdjoint H H a = signedHermitianAdjoint H a :=
  (signedHermitianAdjoint_unique H fun v w ↦
    (signedHermitianHomAdjoint_form_right H H a v w).symm).symm

/-- The adjoint of an isometric equivalence is its inverse. -/
@[simp]
theorem signedHermitianHomAdjoint_isometryEquiv (f : SignedHermitianSpace.IsometryEquiv H₁ H₂) :
    signedHermitianHomAdjoint H₁ H₂ f.toLinearEquiv = f.symm.toLinearEquiv :=
  signedHermitianHomAdjoint_unique H₁ H₂ fun v w ↦ by
    conv_lhs => rw [← f.apply_symm_apply w]
    exact f.map_app v (f.symm w)

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

end Adjoint

/-- In the standard hermitian space the adjoint of a matrix is its conjugate transpose: the
transpose of the matrix with `σ` applied to each entry. For a star ring and `σ = starRingEnd K`
this is `Matrix.conjTranspose`. -/
theorem signedHermitianAdjoint_standard_toLin' [RingHomInvPair σ σ] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) :
    signedHermitianAdjoint (SignedHermitianSpace.standard σ n) (Matrix.toLin' A) =
      Matrix.toLin' (A.map σ).transpose := by
  rw [← signedHermitianHomAdjoint_self, signedHermitianHomAdjoint_standard_toLin']

namespace SignedHermitianSpace

/-- An automorphism `g` of a finite-dimensional signed hermitian space lies in its unitary group
`U(V)`, the isometry group of the form, exactly when its adjoint is its inverse: `g* = g⁻¹`. -/
theorem mem_isometryGroup_iff_signedHermitianAdjoint_eq_symm (H : SignedHermitianSpace K V σ ε)
    [FiniteDimensional K V] {g : V ≃ₗ[K] V} :
    g ∈ H.form.isometryGroup ↔
      signedHermitianAdjoint H (g : Module.End K V) = (g.symm : Module.End K V) := by
  refine ⟨fun hg ↦ (signedHermitianAdjoint_eq_iff H).2 fun v w ↦ ?_,
    fun hg ↦ LinearMap.mem_isometryGroup_iff.2 fun x y ↦ ?_⟩
  · conv_lhs => rw [← g.apply_symm_apply w]
    exact LinearMap.mem_isometryGroup_iff.1 hg v (g.symm w)
  · have h := signedHermitianAdjoint_form_right H (g : Module.End K V) x (g y)
    rw [hg] at h
    simpa using h.symm

end SignedHermitianSpace

end TauCeti
