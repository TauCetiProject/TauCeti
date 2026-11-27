/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.GroupTheory.DoubleCoset.ClassSum
public import TauCeti.RepresentationTheory.LevelForms
import TauCeti.LinearAlgebra.Matrix.Kronecker.Basic
import TauCeti.LinearAlgebra.Matrix.PosDef.Kronecker

/-!
# Rational coordinates for the class-sum pairing of level forms

At a level with trivial stabilizers, the class-sum pairing is the sum of the inner products of
values at double coset representatives. If the coefficient space has a rational Gram matrix,
the block diagonal matrix with one copy per class computes this pairing in value coordinates.
We use `1 ⊗ₖ B` for the repeated rational Gram matrix. Its complex realization is positive
definite by `Matrix.PosDef.one_kronecker` and `Matrix.posDef_gram_of_linearIndependent`.
The pairing on conjugated coordinates is computed blockwise using the same rational matrix.

The value-coordinate and Gram formulas are those of `New.LevelPlaces.LevelForm.valueCoord`,
`valueMetric`, and `inner_eq_valueCoord` in lsernau/grh-lean (`72fead1`,
`grh/src/Lib/Adelic/AutomorphicForms/PAdicGauge.lean`).
-/

public section

open MulOpposite TauCeti
open scoped Matrix InnerProductSpace Kronecker

namespace Representation

variable {G ι : Type*} [Group G] {J : Subgroup G}

section Coordinates

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G)
  (c : DoubleCoset.Quotient (Γ : Set G) J → G) (b : Module.Basis ι R M)

/-- The value coordinates of a level form: evaluate at each class representative and take the
coefficients in the basis `b`. The index is a pair of a class and a basis index. -/
def levelFormsValueCoord :
    ρ.levelForms Γ →ₗ[R] ((DoubleCoset.Quotient (Γ : Set G) J × ι) → R) where
  toFun f i := b.repr ((f : G → M) (c i.1)) i.2
  map_add' f g := by ext i; simp
  map_smul' r f := by ext i; simp

/-- A value coordinate is the specified coefficient of the value at the class representative. -/
@[simp] theorem levelFormsValueCoord_apply (f : ρ.levelForms Γ)
    (i : DoubleCoset.Quotient (Γ : Set G) J × ι) :
    ρ.levelFormsValueCoord Γ c b f i = b.repr ((f : G → M) (c i.1)) i.2 := (rfl)

end Coordinates

/-- Value coordinates at a full set of representatives determine the level form. -/
theorem levelFormsValueCoord_injective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G)
    (c : DoubleCoset.Quotient (Γ : Set G) J → G) (b : Module.Basis ι R M)
    (hc : ∀ q, DoubleCoset.mk Γ J (c q) = q) :
    Function.Injective (ρ.levelFormsValueCoord Γ c b) := by
  intro f g h
  apply levelForms_ext c hc
  intro q
  apply b.repr.injective
  ext i
  simpa only [levelFormsValueCoord_apply] using congrFun h ⟨q, i⟩

section Pairing

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  (ρ : Representation ℂ Jᵐᵒᵖ M) (Γ : Subgroup G) [Fintype (DoubleCoset.Quotient (Γ : Set G) J)]
  [DecidableEq (DoubleCoset.Quotient (Γ : Set G) J)] [Fintype ι]

/-- At a level with trivial stabilizers, the class sum of coefficient inner products is the
pairing of the two value-coordinate vectors against the repeated rational Gram matrix. -/
theorem doubleCosetClassSum_inner_eq_valueCoord (c : DoubleCoset.Quotient (Γ : Set G) J → G)
    (hc : ∀ q, DoubleCoset.mk Γ J (c q) = q)
    (hfree : ∀ q, Nat.card (mackeySubgroup (c q) J Γ) = 1)
    (hρ : ∀ u x y, ⟪ρ (op u) x, ρ (op u) y⟫_ℂ = ⟪x, y⟫_ℂ)
    (b : Module.Basis ι ℂ M) {B : Matrix ι ι ℚ}
    (hB : B.map (Rat.cast : ℚ → ℂ) = Matrix.gram ℂ b) (f g : ρ.levelForms Γ) :
    doubleCosetClassSum Γ J (fun a ↦ ⟪(f : G → M) a, (g : G → M) a⟫_ℂ) =
      star (ρ.levelFormsValueCoord Γ c b f) ⬝ᵥ
        ((((1 : Matrix (DoubleCoset.Quotient (Γ : Set G) J) _ ℚ) ⊗ₖ B).map
          (Rat.castHom ℂ)) *ᵥ ρ.levelFormsValueCoord Γ c b g) := by
  have hleft (γ : G) (hγ : γ ∈ Γ) (a : G) :
      ⟪(f : G → M) (γ * a), (g : G → M) (γ * a)⟫_ℂ = ⟪(f : G → M) a, (g : G → M) a⟫_ℂ := by
    rw [levelForms_apply_mul_left f hγ, levelForms_apply_mul_left g hγ]
  have hright (u : G) (hu : u ∈ J) (a : G) :
      ⟪(f : G → M) (a * u), (g : G → M) (a * u)⟫_ℂ = ⟪(f : G → M) a, (g : G → M) a⟫_ℂ := by
    rw [levelForms_apply_mul_right f ⟨u, hu⟩, levelForms_apply_mul_right g ⟨u, hu⟩, hρ]
  rw [doubleCosetClassSum_eq_finsum hleft hright c hc, finsum_eq_sum_of_fintype,
    Matrix.map_kronecker, Matrix.map_one _ (map_zero _) (map_one _), Rat.coe_castHom, hB,
    Matrix.dotProduct_one_kronecker_mulVec]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [hfree, Nat.cast_one, inv_one, one_smul, Pi.star_apply, levelFormsValueCoord_apply]
  have h := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℂ) b
    (fun i ↦ b.repr ((f : G → M) (c q)) i) (fun i ↦ b.repr ((g : G → M) (c q)) i)
  rw [b.sum_repr, b.sum_repr] at h
  exact h.symm

end Pairing

end Representation
