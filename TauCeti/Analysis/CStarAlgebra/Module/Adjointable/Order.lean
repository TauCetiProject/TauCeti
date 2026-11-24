/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Modulus of adjointable operators

For a rectangular adjointable operator `T : TauCeti.AdjointableMap A E F` on a complete Hilbert
C⋆-module `E`, the operator `T* ∘ T` is positive in the C⋆-algebra `L_A(E)`
(`TauCeti.AdjointableMap.adjoint_comp_self_nonneg`), so it has a positive square root. This file
develops the basic API of the resulting operator modulus `|T| = √(T* ∘ T)`.

## Main declarations

* `TauCeti.AdjointableMap.abs`: the modulus `|T| = CFC.sqrt (T.adjoint.comp T)` in `L_A(E)` for
  `T : L_A(E, F)`, satisfying `⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A` (`inner_abs_abs`),
  `‖|T| x‖ = ‖T x‖` (`norm_abs_apply`), and `‖|T|‖ = ‖T‖` (`norm_abs`).

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
* Bruce Blackadar, *Operator Algebras*, Section II.7.2.
-/

public section

namespace TauCeti

namespace AdjointableMap

section Abs

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- The modulus `|T| = √(T* ∘ T) ∈ L_A(E)` of an adjointable operator `T : E → F`, defined via
the continuous functional calculus on `L_A(E)`. -/
noncomputable def abs [CompleteSpace E] (T : AdjointableMap A E F) : AdjointableMap A E E :=
  CFC.sqrt (T.adjoint.comp T)

@[simp]
theorem abs_nonneg [CompleteSpace E] (T : AdjointableMap A E F) : 0 ≤ T.abs :=
  CFC.sqrt_nonneg _

theorem isSelfAdjoint_abs [CompleteSpace E] (T : AdjointableMap A E F) : IsSelfAdjoint T.abs :=
  (abs_nonneg T).isSelfAdjoint

@[simp]
theorem abs_mul_abs [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs * T.abs = T.adjoint.comp T :=
  CFC.sqrt_mul_sqrt_self _ (adjoint_comp_self_nonneg T)

@[simp]
theorem abs_zero [CompleteSpace E] : (0 : AdjointableMap A E F).abs = 0 := by
  rw [abs, adjoint_zero, zero_comp, CFC.sqrt_zero]

@[simp]
theorem abs_id [CompleteSpace E] : (AdjointableMap.id A E).abs = AdjointableMap.id A E := by
  rw [abs, adjoint_id, id_comp, ← one_def, CFC.sqrt_one]

@[simp]
theorem abs_one [CompleteSpace E] : (1 : AdjointableMap A E E).abs = 1 :=
  abs_id

/-- The modulus of a positive operator in `L_A(E)` is the operator itself. -/
theorem abs_of_nonneg [CompleteSpace E] {T : AdjointableMap A E E} (hT : 0 ≤ T) :
    T.abs = T := by
  rw [abs, ← mul_def, ← star_eq_adjoint, hT.isSelfAdjoint.star_eq, CFC.sqrt_mul_self T hT]

/-- An adjointable endomorphism equals its modulus if and only if it is positive. -/
@[simp]
theorem abs_eq_self_iff [CompleteSpace E] {T : AdjointableMap A E E} :
    T.abs = T ↔ 0 ≤ T :=
  ⟨fun h => h ▸ abs_nonneg T, abs_of_nonneg⟩

@[simp]
theorem abs_abs [CompleteSpace E] (T : AdjointableMap A E F) : T.abs.abs = T.abs :=
  abs_of_nonneg (abs_nonneg T)

/-- `|T|` preserves all `A`-valued inner products relative to `T`:
`⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A`. -/
theorem inner_abs_abs [CompleteSpace E] (T : AdjointableMap A E F) (x y : E) :
    inner A (T.abs x) (T.abs y) = inner A (T x) (T y) := by
  rw [← T.abs.adjoint_inner_right, isSelfAdjoint_iff_adjoint_eq.mp (isSelfAdjoint_abs T),
    ← mul_apply_eq_comp, abs_mul_abs, comp_apply, T.adjoint_inner_right]

@[simp]
theorem norm_abs_apply [CompleteSpace E] (T : AdjointableMap A E F) (x : E) :
    ‖T.abs x‖ = ‖T x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x := T x), inner_abs_abs]

@[simp]
theorem norm_abs [CompleteSpace E] (T : AdjointableMap A E F) : ‖T.abs‖ = ‖T‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self,
    (isSelfAdjoint_abs T).star_eq, abs_mul_abs, norm_adjoint_comp_self]

@[simp]
theorem abs_eq_zero [CompleteSpace E] {T : AdjointableMap A E F} : T.abs = 0 ↔ T = 0 := by
  rw [← norm_eq_zero, norm_abs, norm_eq_zero]

/-- The modulus `|T|` has the same kernel as `T`. -/
theorem ker_abs [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs.toContinuousLinearMap.ker = T.toContinuousLinearMap.ker := by
  ext x
  simp [← norm_eq_zero]

end Abs

end AdjointableMap

end TauCeti
