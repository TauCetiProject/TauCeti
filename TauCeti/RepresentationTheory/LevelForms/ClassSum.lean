/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.LinearAlgebra.Matrix.PosDef.Kronecker
public import TauCeti.RepresentationTheory.LevelForms.Basic

/-!
# Rational Gram matrices for unweighted class sums

Evaluate a level form at the chosen double coset representatives and record each value in
coefficient coordinates. If the coefficient pairing has a positive definite rational Gram
matrix, its sum over the classes has one copy of that matrix in each diagonal block.
This gives rational coordinates for the class-sum product at a free level, where every
stabilizer has order one and no stabilizer weights enter the product.

The construction follows `New.LevelPlaces.LevelForm.valueCoord`, `valueMetric` and
`inner_eq_valueCoord` in `grh/src/Lib/Adelic/AutomorphicForms/PAdicGauge.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace Kronecker

namespace Representation

variable {G : Type*} [Group G] {J : Subgroup G} {ι : Type*}

section Coordinates

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The coordinates of a level form are the coefficient coordinates of its values at the
chosen points, indexed by the class and the coefficient index. -/
def levelFormsValueCoord (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G)
    (c : DoubleCoset.Quotient (Γ : Set G) J → G) (e : M →ₗ[R] (ι → R)) :
    ρ.levelForms Γ →ₗ[R] (DoubleCoset.Quotient (Γ : Set G) J × ι → R) :=
  LinearMap.pi fun i ↦
    (LinearMap.proj i.2).comp (e.comp ((LinearMap.proj (c i.1)).comp (ρ.levelForms Γ).subtype))

/-- The coordinate in position `(q, j)` is the `j`th coefficient of the value at `c q`. -/
@[simp] theorem levelFormsValueCoord_apply (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G)
    (c : DoubleCoset.Quotient (Γ : Set G) J → G) (e : M →ₗ[R] (ι → R))
    (f : ρ.levelForms Γ) (q : DoubleCoset.Quotient (Γ : Set G) J) (j : ι) :
    ρ.levelFormsValueCoord Γ c e f (q, j) = e ((f : G → M) (c q)) j := (rfl)

end Coordinates

/-- The unweighted class sum has the rational Gram matrix obtained by repeating the
coefficient Gram matrix once per class. In particular, at free levels this gives the Gram
matrix for the class-sum product. The rational matrix is positive definite after casting to
`ℂ`, with no assumption on the choice of representatives for the displayed identity. -/
theorem levelForms_classSum_rationalGram {M : Type*} [SeminormedAddCommGroup M]
    [InnerProductSpace ℂ M] (ρ : Representation ℂ Jᵐᵒᵖ M) (Γ : Subgroup G)
    [Fintype (DoubleCoset.Quotient (Γ : Set G) J)]
    [DecidableEq (DoubleCoset.Quotient (Γ : Set G) J)] [Fintype ι]
    (c : DoubleCoset.Quotient (Γ : Set G) J → G) (e : M →ₗ[ℂ] (ι → ℂ))
    (Q : Matrix ι ι ℚ) (hQ : (Q.map (algebraMap ℚ ℂ)).PosDef)
    (hinner : ∀ x y : M, ⟪x, y⟫_ℂ = star (e x) ⬝ᵥ (Q.map (algebraMap ℚ ℂ) *ᵥ e y)) :
    let C := DoubleCoset.Quotient (Γ : Set G) J
    let A := (((1 : Matrix C C ℚ) ⊗ₖ Q).map (algebraMap ℚ ℂ))
    let coord := ρ.levelFormsValueCoord Γ c e
    A.PosDef ∧ ∀ f g : ρ.levelForms Γ,
      ∑ q, ⟪(f : G → M) (c q), (g : G → M) (c q)⟫_ℂ = star (coord f) ⬝ᵥ (A *ᵥ coord g) := by
  dsimp only
  let C := DoubleCoset.Quotient (Γ : Set G) J
  have hmap : ((1 : Matrix C C ℚ) ⊗ₖ Q).map (algebraMap ℚ ℂ) =
      (1 : Matrix C C ℂ) ⊗ₖ Q.map (algebraMap ℚ ℂ) := by
    ext ⟨q, i⟩ ⟨r, j⟩
    by_cases h : q = r <;> simp [h]
  rw [hmap]
  refine ⟨hQ.one_kronecker, fun f g ↦ ?_⟩
  rw [Matrix.star_dotProduct_one_kronecker_mulVec]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simpa only [levelFormsValueCoord_apply] using hinner ((f : G → M) (c q)) ((g : G → M) (c q))

end Representation
