/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite self-adjoint functional calculus

For a symmetric endomorphism of a finite-dimensional real or complex inner-product space,
`finiteFunctionalCalculus` applies an arbitrary real-valued function to the eigenvalues.
It is the spectral sum of the rank-one projections onto an orthonormal eigenbasis.
Its action on every eigenspace characterizes it independently of the chosen eigenbasis.

The product law and preservation of the commutant allow scalar identities to be transferred
to operators. In particular this calculus can be applied to the scalar square-root function
when constructing positive square roots and operator moduli.

The construction uses Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` and
`InnerProductSpace.rankOne`. For the finite spectral calculus, see Horn and Johnson,
*Matrix Analysis*, 2nd ed.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace
open InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {T : E →ₗ[𝕜] E}

/-- Apply a real-valued function to a symmetric endomorphism by its finite spectral sum.
No continuity assumption on the function is needed. -/
def finiteFunctionalCalculus (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i : Fin (Module.finrank 𝕜 E),
    (f (hT.eigenvalues rfl i) : 𝕜) •
      (rankOne 𝕜 (hT.eigenvectorBasis rfl i) (hT.eigenvectorBasis rfl i)).toLinearMap

/-- The defining spectral sum of rank-one projections. -/
theorem finiteFunctionalCalculus_def (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    finiteFunctionalCalculus hT f = ∑ i : Fin (Module.finrank 𝕜 E),
      (f (hT.eigenvalues rfl i) : 𝕜) •
        (rankOne 𝕜 (hT.eigenvectorBasis rfl i) (hT.eigenvectorBasis rfl i)).toLinearMap := (rfl)

/-- The spectral sum evaluated at a vector, in eigenbasis coordinates. -/
theorem finiteFunctionalCalculus_apply (hT : T.IsSymmetric) (f : ℝ → ℝ) (x : E) :
    finiteFunctionalCalculus hT f x =
      ∑ i, ((f (hT.eigenvalues rfl i) : 𝕜) *
        (hT.eigenvectorBasis rfl).repr x i) • hT.eigenvectorBasis rfl i := by
  simp [finiteFunctionalCalculus, OrthonormalBasis.repr_apply_apply, smul_smul]

/-- Each chosen eigenbasis vector is multiplied by the function of its eigenvalue. -/
@[simp]
theorem finiteFunctionalCalculus_apply_eigenvectorBasis (hT : T.IsSymmetric)
    (f : ℝ → ℝ) (i : Fin (Module.finrank 𝕜 E)) :
    finiteFunctionalCalculus hT f (hT.eigenvectorBasis rfl i) =
      (f (hT.eigenvalues rfl i) : 𝕜) • hT.eigenvectorBasis rfl i := by
  classical
  simp [finiteFunctionalCalculus_apply, OrthonormalBasis.repr_self]

/-- The calculus is diagonal in the eigenbasis of the original operator. -/
theorem repr_finiteFunctionalCalculus_apply (hT : T.IsSymmetric)
    (f : ℝ → ℝ) (x : E) (i : Fin (Module.finrank 𝕜 E)) :
    (hT.eigenvectorBasis rfl).repr (finiteFunctionalCalculus hT f x) i =
      (f (hT.eigenvalues rfl i) : 𝕜) * (hT.eigenvectorBasis rfl).repr x i := by
  classical
  simp [finiteFunctionalCalculus_apply, OrthonormalBasis.repr_apply_apply,
    Pi.single_apply]

/-- Real-valued spectral symbols give symmetric operators. -/
theorem isSymmetric_finiteFunctionalCalculus (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    (finiteFunctionalCalculus hT f).IsSymmetric := by
  apply LinearMap.isSymmetric_sum
  intro i _
  exact LinearMap.IsSymmetric.smul (by simp) (isSymmetric_rankOne_self _)

/-- Symbols agreeing on the eigenvalues give the same operator. -/
theorem finiteFunctionalCalculus_congr (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (h : ∀ i : Fin (Module.finrank 𝕜 E), f (hT.eigenvalues rfl i) =
      g (hT.eigenvalues rfl i)) :
    finiteFunctionalCalculus hT f = finiteFunctionalCalculus hT g := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp [h i]

/-- Applying the identity symbol recovers the original operator. -/
@[simp]
theorem finiteFunctionalCalculus_id (hT : T.IsSymmetric) :
    finiteFunctionalCalculus hT id = T := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp

/-- A constant symbol gives a scalar multiple of the identity operator. -/
@[simp]
theorem finiteFunctionalCalculus_const (hT : T.IsSymmetric) (c : ℝ) :
    finiteFunctionalCalculus hT (fun _ => c) = (c : 𝕜) • LinearMap.id := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp

/-- The calculus preserves addition of symbols. -/
theorem finiteFunctionalCalculus_add (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    finiteFunctionalCalculus hT (f + g) =
      finiteFunctionalCalculus hT f + finiteFunctionalCalculus hT g := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp [add_smul]

/-- The calculus preserves multiplication of a symbol by a real scalar. -/
theorem finiteFunctionalCalculus_smul (hT : T.IsSymmetric) (c : ℝ) (f : ℝ → ℝ) :
    finiteFunctionalCalculus hT (c • f) = (c : 𝕜) • finiteFunctionalCalculus hT f := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp [smul_smul, RCLike.algebraMap_eq_ofReal]

/-- The calculus preserves multiplication of symbols, with multiplication of endomorphisms
meaning composition. -/
theorem finiteFunctionalCalculus_mul (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    finiteFunctionalCalculus hT (f * g) =
      finiteFunctionalCalculus hT f * finiteFunctionalCalculus hT g := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp [Module.End.mul_apply, smul_smul, RCLike.algebraMap_eq_ofReal, mul_comm]

/-- Applying a symbol to an arbitrary eigenvector multiplies it by the value of the symbol.
The vector is allowed to be zero. -/
theorem finiteFunctionalCalculus_apply_of_apply_eq_smul (hT : T.IsSymmetric)
    (f : ℝ → ℝ) {μ : ℝ} {x : E} (hx : T x = (μ : 𝕜) • x) :
    finiteFunctionalCalculus hT f x = (f μ : 𝕜) • x := by
  apply (hT.eigenvectorBasis rfl).repr.injective
  ext i
  rw [repr_finiteFunctionalCalculus_apply]
  have hi := hT.eigenvectorBasis_apply_self_apply rfl x i
  rw [hx, map_smul] at hi
  by_cases hz : (hT.eigenvectorBasis rfl).repr x i = 0
  · simp [hz]
  · have hμ : hT.eigenvalues rfl i = μ := by
      apply RCLike.ofReal_injective (K := 𝕜)
      exact mul_right_cancel₀ hz hi.symm
    simp [hμ, RCLike.real_smul_eq_coe_mul]

/-- The eigenspace action characterizes the calculus. Symmetry of the candidate operator
is not an additional assumption: it follows from this characterization. -/
theorem eq_finiteFunctionalCalculus_iff (hT : T.IsSymmetric) (f : ℝ → ℝ)
    (S : E →ₗ[𝕜] E) :
    S = finiteFunctionalCalculus hT f ↔
      ∀ (μ : ℝ) (x : E), T x = (μ : 𝕜) • x → S x = (f μ : 𝕜) • x := by
  constructor
  · rintro rfl μ x hx
    exact finiteFunctionalCalculus_apply_of_apply_eq_smul hT f hx
  · intro h
    apply (hT.eigenvectorBasis rfl).toBasis.ext
    intro i
    simpa using h _ _ (hT.apply_eigenvectorBasis rfl i)

/-- Every endomorphism commuting with the original operator commutes with its finite
functional calculus. No symmetry assumption on the commuting endomorphism is needed. -/
theorem commute_finiteFunctionalCalculus (hT : T.IsSymmetric) (f : ℝ → ℝ)
    {S : E →ₗ[𝕜] E} (hS : Commute S T) :
    Commute S (finiteFunctionalCalculus hT f) := by
  rw [commute_iff_eq]
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  have hi : T (S (hT.eigenvectorBasis rfl i)) =
      (hT.eigenvalues rfl i : 𝕜) • S (hT.eigenvectorBasis rfl i) := by
    have he := congrArg (fun A : E →ₗ[𝕜] E => A (hT.eigenvectorBasis rfl i)) hS.eq
    simpa [Module.End.mul_apply] using he.symm
  simp [Module.End.mul_apply,
    finiteFunctionalCalculus_apply_of_apply_eq_smul hT f hi]

end TauCeti
