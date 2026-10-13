/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The functional calculus of a symmetric operator in finite dimension

Let `T` be a symmetric endomorphism of a finite-dimensional inner product space `E` over `ℝ` or
`ℂ` (any `RCLike` field `𝕜`). For a real function `f : ℝ → ℝ`, the operator `f(T)` is the
spectral sum `∑ᵢ f(λᵢ) eᵢ ⊗ eᵢ` over an orthonormal eigenbasis `(eᵢ)` of `T` with eigenvalues
`(λᵢ)`. This file defines it as `LinearMap.IsSymmetric.cfc` and proves the identities that make
it a functional calculus: `f(T)` acts as multiplication by `f(λ)` on every eigenvector of `T` with
eigenvalue `λ`, and it is the unique endomorphism doing so. Everything else follows from this
characterization: `f(T)` is symmetric, depends only on the values of `f` at the eigenvalues of
`T`, is additive and multiplicative in `f`, recovers `T` from the identity function, is compatible
with composition of functions, and is preserved by every linear map intertwining two symmetric
operators. In particular `f(T)` commutes with every endomorphism commuting with `T`.

No continuity of `f` is required, and the construction works uniformly over `RCLike` scalars, so
it applies to real inner product spaces, where Mathlib's continuous functional calculus for
self-adjoint operators is not available. A function that is nonnegative on the spectrum gives a
positive operator; applied to `Real.sqrt` on a positive operator, this yields the positive square
root `LinearMap.IsPositive.sqrt`.

The name follows `Matrix.IsHermitian.cfc`, Mathlib's eigenbasis construction of the functional
calculus of a Hermitian matrix.

## Main declarations

* `LinearMap.IsSymmetric.cfc`: the functional calculus `f(T)` of a symmetric operator `T`.
* `LinearMap.IsSymmetric.cfc_apply_of_apply_eq_smul`: `f(T)x = f(λ)x` whenever `Tx = λx`.
* `LinearMap.IsSymmetric.eq_cfc_iff`: `f(T)` is the unique endomorphism acting by `f(λ)` on
  the eigenvectors of `T` with eigenvalue `λ`.
* `LinearMap.IsSymmetric.cfc_eq_sum`: the spectral sum formula over any ordered eigenbasis.
* `LinearMap.IsSymmetric.isSymmetric_cfc`, `LinearMap.IsSymmetric.cfc_congr`,
  `LinearMap.IsSymmetric.cfc_id`, `LinearMap.IsSymmetric.cfc_mul`,
  `LinearMap.IsSymmetric.cfc_comp`: the algebraic laws of the calculus.
* `LinearMap.IsSymmetric.isPositive_cfc`: `f(T)` is positive when `f` is nonnegative at the
  eigenvalues of `T`.
* `LinearMap.IsSymmetric.comp_cfc_eq_cfc_comp` and `LinearMap.IsSymmetric.commute_cfc`:
  intertwiners of symmetric operators intertwine their functional calculi; in particular the
  commutant of `T` commutes with `f(T)`.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  §§2.5 and 7.2 (the spectral theorem and functions of Hermitian matrices).
-/

public section

open Module.End InnerProductSpace
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {T : E →ₗ[𝕜] E} {n : ℕ}

/-- The functional calculus `f(T)` of a symmetric operator `T` on a finite-dimensional inner
product space: the spectral sum `∑ᵢ f(λᵢ) eᵢ ⊗ eᵢ` of the rank-one projections
`eᵢ ⊗ eᵢ = rankOne 𝕜 eᵢ eᵢ` over Mathlib's ordered orthonormal eigenbasis `(eᵢ)` of `T`, whose
eigenvalues are `(λᵢ)`.

The result does not depend on the choice of eigenbasis: see `cfc_eq_sum` and `eq_cfc_iff`. -/
noncomputable def cfc (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i, (f (hT.eigenvalues rfl i) : 𝕜) •
    (rankOne 𝕜 (hT.eigenvectorBasis rfl i) (hT.eigenvectorBasis rfl i) : E →ₗ[𝕜] E)

/-- For an eigenvector `x` of `T` with eigenvalue `μ`, the spectral coefficient
`f(λᵢ)⟪eᵢ, x⟫` equals `f(μ)⟪eᵢ, x⟫`: either `λᵢ = μ`, or `eᵢ` is orthogonal to `x`. -/
private theorem coe_mul_inner_eigenvectorBasis_eq (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) {x : E} {μ : ℝ} (hx : T x = (μ : 𝕜) • x)
    (i : Fin n) :
    (f (hT.eigenvalues hn i) : 𝕜) * ⟪hT.eigenvectorBasis hn i, x⟫_𝕜 =
      (f μ : 𝕜) * ⟪hT.eigenvectorBasis hn i, x⟫_𝕜 := by
  by_cases hμ : hT.eigenvalues hn i = μ
  · rw [hμ]
  have h0 := hT.orthogonalFamily_eigenspaces (by exact_mod_cast hμ)
    ⟨_, mem_eigenspace_iff.mpr (hT.apply_eigenvectorBasis hn i)⟩ ⟨x, mem_eigenspace_iff.mpr hx⟩
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply] at h0
  rw [h0, mul_zero, mul_zero]

/-- The spectral sum over any ordered eigenbasis acts by `f(μ)` on an eigenvector with
eigenvalue `μ`. -/
private theorem sum_rankOne_apply_of_apply_eq_smul (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) {x : E} {μ : ℝ} (hx : T x = (μ : 𝕜) • x) :
    (∑ i, (f (hT.eigenvalues hn i) : 𝕜) •
      (rankOne 𝕜 (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) : E →ₗ[𝕜] E)) x =
      (f μ : 𝕜) • x := by
  conv_rhs => rw [← (hT.eigenvectorBasis hn).sum_repr' x, Finset.smul_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, smul_smul, coe_mul_inner_eigenvectorBasis_eq hT hn f hx]

/-- **Eigenvector action.** If `Tx = μx`, then `f(T)x = f(μ)x`. -/
theorem cfc_apply_of_apply_eq_smul (hT : T.IsSymmetric) (f : ℝ → ℝ) {x : E} {μ : ℝ}
    (hx : T x = (μ : 𝕜) • x) : hT.cfc f x = (f μ : 𝕜) • x :=
  sum_rankOne_apply_of_apply_eq_smul hT rfl f hx

/-- The functional calculus acts diagonally on every ordered eigenbasis of `T`. -/
@[simp]
theorem cfc_apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (f : ℝ → ℝ) (i : Fin n) :
    hT.cfc f (hT.eigenvectorBasis hn i) =
      (f (hT.eigenvalues hn i) : 𝕜) • hT.eigenvectorBasis hn i :=
  hT.cfc_apply_of_apply_eq_smul f (hT.apply_eigenvectorBasis hn i)

/-- **Uniqueness.** An endomorphism equals `f(T)` exactly when it acts as multiplication by `f(μ)`
on every eigenvector of `T` with eigenvalue `μ`. -/
theorem eq_cfc_iff (hT : T.IsSymmetric) (f : ℝ → ℝ) {S : E →ₗ[𝕜] E} :
    S = hT.cfc f ↔ ∀ (μ : ℝ) (x : E), T x = (μ : 𝕜) • x → S x = (f μ : 𝕜) • x := by
  refine ⟨fun h μ x hx ↦ h ▸ hT.cfc_apply_of_apply_eq_smul f hx, fun h ↦ ?_⟩
  refine (hT.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, cfc_apply_eigenvectorBasis,
    h _ _ (hT.apply_eigenvectorBasis rfl i)]

/-- The functional calculus is the spectral sum over any ordered eigenbasis of `T`. -/
theorem cfc_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) :
    hT.cfc f = ∑ i, (f (hT.eigenvalues hn i) : 𝕜) •
      (rankOne 𝕜 (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) : E →ₗ[𝕜] E) :=
  ((hT.eq_cfc_iff f).mpr fun _ _ hx ↦ sum_rankOne_apply_of_apply_eq_smul hT hn f hx).symm

/-- The spectral expansion of `f(T)x` in any ordered eigenbasis of `T`. -/
theorem cfc_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) (x : E) :
    hT.cfc f x = ∑ i, ((f (hT.eigenvalues hn i) : 𝕜) * ⟪hT.eigenvectorBasis hn i, x⟫_𝕜) •
      hT.eigenvectorBasis hn i := by
  simp [hT.cfc_eq_sum hn, smul_smul]

/-- The functional calculus of a symmetric operator is symmetric. -/
theorem isSymmetric_cfc (hT : T.IsSymmetric) (f : ℝ → ℝ) : (hT.cfc f).IsSymmetric :=
  isSymmetric_sum _ fun _ _ ↦ (isSymmetric_rankOne_self _).smul (RCLike.conj_ofReal _)

/-- The functional calculus only depends on the values of `f` at the eigenvalues of `T`. -/
theorem cfc_congr (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (hfg : ∀ μ : ℝ, HasEigenvalue T (μ : 𝕜) → f μ = g μ) : hT.cfc f = hT.cfc g := by
  refine (hT.eq_cfc_iff g).mpr fun μ x hx ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rw [hT.cfc_apply_of_apply_eq_smul f hx,
    hfg μ (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hx0⟩)]

/-- The identity function recovers the operator. -/
@[simp]
theorem cfc_id (hT : T.IsSymmetric) : hT.cfc _root_.id = T :=
  ((hT.eq_cfc_iff _root_.id).mpr fun _ _ hx ↦ hx).symm

/-- The identity function, written as a lambda, recovers the operator. -/
@[simp]
theorem cfc_id' (hT : T.IsSymmetric) : hT.cfc (fun μ ↦ μ) = T :=
  hT.cfc_id

/-- A constant function gives the corresponding multiple of the identity. -/
@[simp]
theorem cfc_const (hT : T.IsSymmetric) (c : ℝ) : hT.cfc (fun _ ↦ c) = (c : 𝕜) • 1 :=
  ((hT.eq_cfc_iff _).mpr fun _ _ _ ↦ rfl).symm

/-- The zero function gives the zero operator. -/
@[simp]
theorem cfc_zero (hT : T.IsSymmetric) : hT.cfc 0 = 0 :=
  ((hT.eq_cfc_iff 0).mpr fun _ _ _ ↦ by simp).symm

/-- The constant function `1` gives the identity operator. -/
@[simp]
theorem cfc_one (hT : T.IsSymmetric) : hT.cfc 1 = 1 :=
  ((hT.eq_cfc_iff 1).mpr fun _ _ _ ↦ by simp).symm

/-- The functional calculus is additive in the function. -/
theorem cfc_add (hT : T.IsSymmetric) (f g : ℝ → ℝ) : hT.cfc (f + g) = hT.cfc f + hT.cfc g :=
  ((hT.eq_cfc_iff _).mpr fun _ _ hx ↦ by
    rw [LinearMap.add_apply, hT.cfc_apply_of_apply_eq_smul f hx,
      hT.cfc_apply_of_apply_eq_smul g hx, Pi.add_apply, RCLike.ofReal_add, add_smul]).symm

/-- **Product law.** The functional calculus is multiplicative in the function:
`(fg)(T) = f(T)g(T)`. -/
theorem cfc_mul (hT : T.IsSymmetric) (f g : ℝ → ℝ) : hT.cfc (f * g) = hT.cfc f * hT.cfc g :=
  ((hT.eq_cfc_iff _).mpr fun _ _ hx ↦ by
    rw [Module.End.mul_apply, hT.cfc_apply_of_apply_eq_smul g hx, map_smul,
      hT.cfc_apply_of_apply_eq_smul f hx, smul_smul, Pi.mul_apply, RCLike.ofReal_mul,
      mul_comm]).symm

/-- Composition of functions corresponds to iterating the functional calculus:
`(g ∘ f)(T) = g(f(T))`. -/
theorem cfc_comp (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    hT.cfc (g ∘ f) = (hT.isSymmetric_cfc f).cfc g :=
  ((hT.eq_cfc_iff _).mpr fun _ _ hx ↦
    (hT.isSymmetric_cfc f).cfc_apply_of_apply_eq_smul g
      (hT.cfc_apply_of_apply_eq_smul f hx)).symm

/-- A linear map intertwining two symmetric operators intertwines their functional calculi:
if `S T = T' S`, then `S f(T) = f(T') S`. -/
theorem comp_cfc_eq_cfc_comp (hT : T.IsSymmetric) {T' : F →ₗ[𝕜] F} (hT' : T'.IsSymmetric)
    {S : E →ₗ[𝕜] F} (hS : S ∘ₗ T = T' ∘ₗ S) (f : ℝ → ℝ) :
    S ∘ₗ hT.cfc f = hT'.cfc f ∘ₗ S := by
  refine (hT.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  have hSe : T' (S (hT.eigenvectorBasis rfl i)) =
      (hT.eigenvalues rfl i : 𝕜) • S (hT.eigenvectorBasis rfl i) := by
    rw [← LinearMap.comp_apply, ← hS, LinearMap.comp_apply, apply_eigenvectorBasis, map_smul]
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearMap.comp_apply,
    cfc_apply_eigenvectorBasis, map_smul, hT'.cfc_apply_of_apply_eq_smul f hSe]

/-- **Commutant preservation.** Every endomorphism commuting with `T` commutes with `f(T)`. -/
theorem commute_cfc (hT : T.IsSymmetric) {S : E →ₗ[𝕜] E} (hS : Commute S T) (f : ℝ → ℝ) :
    Commute S (hT.cfc f) :=
  hT.comp_cfc_eq_cfc_comp hT hS.eq f

/-- **Positivity.** If `f` is nonnegative at every eigenvalue of `T`, then `f(T)` is positive. -/
theorem isPositive_cfc (hT : T.IsSymmetric) {f : ℝ → ℝ}
    (hf : ∀ μ : ℝ, HasEigenvalue T (μ : 𝕜) → 0 ≤ f μ) : (hT.cfc f).IsPositive := by
  -- `f(T) = R * R` for the symmetric operator `R = (√f)(T)`.
  have hR : hT.cfc f = hT.cfc (fun μ ↦ √(f μ)) * hT.cfc (fun μ ↦ √(f μ)) := by
    rw [← cfc_mul]
    exact hT.cfc_congr fun μ hμ ↦ (Real.mul_self_sqrt (hf μ hμ)).symm
  refine ⟨hT.isSymmetric_cfc f, fun x ↦ ?_⟩
  rw [hR, Module.End.mul_apply, hT.isSymmetric_cfc _ _ x]
  exact inner_self_nonneg

end LinearMap.IsSymmetric
