/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Positivity, spectral order, and modulus of adjointable operators

In the C⋆-algebra `L_A(E) = TauCeti.AdjointableMap A E E` of a complete Hilbert C⋆-module `E`,
positivity in the spectral order is characterized purely by `A`-valued inner products without
assuming self-adjointness beforehand (`TauCeti.AdjointableMap.nonneg_iff`, Lance Theorem 4.1):
`0 ≤ T ↔ ∀ x : E, 0 ≤ ⟪x, T x⟫_A`.

From this characterization we deduce the Loewner order criterion `le_iff`, Paschke's operator
inequality `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` (`inner_map_self_le`), and the basic API of the
operator modulus `|T| = √(T* ∘ T)` (`abs`) for rectangular adjointable operators `T : L_A(E, F)`.

## Main declarations

* `TauCeti.AdjointableMap.nonneg_iff`: `0 ≤ T ↔ ∀ x, 0 ≤ ⟪x, T x⟫_A` in `L_A(E)`.
* `TauCeti.AdjointableMap.le_iff`: `S ≤ T ↔ ∀ x, ⟪x, S x⟫_A ≤ ⟪x, T x⟫_A` in `L_A(E)`.
* `TauCeti.AdjointableMap.inner_map_self_le`: Paschke's inequality
  `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A`.
* `TauCeti.AdjointableMap.abs`: the modulus `|T| = CFC.sqrt (T.adjoint.comp T)` in `L_A(E)` for
  `T : L_A(E, F)`, satisfying `⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A` and `‖|T| x‖ = ‖T x‖`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4
  (Theorem 4.1).
* William L. Paschke, *Inner product modules over B⋆-algebras*, Trans. Amer. Math. Soc. 182
  (1973), 443–468.
* Bruce Blackadar, *Operator Algebras*, Section II.7.2.
-/

public section

open MulOpposite

namespace TauCeti

namespace AdjointableMap

section Order

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Lance's positivity theorem (Theorem 4.1): in the C⋆-algebra `L_A(E)` of a complete Hilbert
C⋆-module `E`, an operator `T` is positive (`0 ≤ T` in the spectral order) if and only if
`0 ≤ ⟪x, T x⟫_A` in `A` for every `x ∈ E`. Self-adjointness of `T` is not assumed separately. -/
theorem nonneg_iff [CompleteSpace E] {T : AdjointableMap A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x => ?_, fun h => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply, ← inner_star_left, star_star]
    exact CStarModule.inner_self_nonneg
  · have hsa : IsSelfAdjoint T :=
      isSelfAdjoint_iff_forall_isSelfAdjoint.mpr fun x => .of_nonneg (h x)
    refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
    set N := T⁻
    have hN : 0 ≤ N := CFC.negPart_nonneg T
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
    have hTN : T * N = -(star R * R * N) := by
      conv_lhs => rw [← CFC.posPart_sub_negPart T hsa]
      rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
    have hRN : R * N = 0 := by
      ext x
      have hx := h (N x)
      have heq : inner A (N x) (T (N x)) = -inner A ((R * N) x) ((R * N) x) := by
        rw [← mul_apply, hTN, neg_apply, CStarModule.inner_neg_right, mul_assoc, mul_apply,
          ← inner_star_left, star_star, ← mul_apply]
      rw [heq, Left.nonneg_neg_iff] at hx
      exact CStarModule.inner_self.mp (le_antisymm hx CStarModule.inner_self_nonneg)
    rw [← star_mul_self_eq_zero, hN.isSelfAdjoint.star_eq]
    calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
      _ = 0 := by rw [hRN, mul_zero]

/-- The spectral order on `L_A(E)` is characterized by `S ≤ T ↔ ∀ x, ⟪x, S x⟫_A ≤ ⟪x, T x⟫_A`. -/
theorem le_iff [CompleteSpace E] {S T : AdjointableMap A E E} :
    S ≤ T ↔ ∀ x : E, inner A x (S x) ≤ inner A x (T x) := by
  rw [← sub_nonneg, nonneg_iff]
  simp_rw [sub_apply, CStarModule.inner_sub_right, sub_nonneg]

/-- For any rectangular adjointable operator `T : E → F` with `E` complete, `T* ∘ T` is positive
in `L_A(E)`. -/
@[simp]
theorem adjoint_comp_self_nonneg [CompleteSpace E] (T : AdjointableMap A E F) :
    0 ≤ T.adjoint.comp T :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, ← T.inner_map_left]
    exact CStarModule.inner_self_nonneg

/-- For any rectangular adjointable operator `T : E → F` with `F` complete, `T ∘ T*` is positive
in `L_A(F)`. -/
@[simp]
theorem self_comp_adjoint_nonneg [CompleteSpace F] (T : AdjointableMap A E F) :
    0 ≤ T.comp T.adjoint := by
  simpa only [adjoint_adjoint] using adjoint_comp_self_nonneg T.adjoint

/-- Conjugating a positive operator in `L_A(F)` by `T : L_A(E, F)` gives a positive operator in
`L_A(E)`. -/
theorem adjoint_comp_nonneg_comp [CompleteSpace E] [CompleteSpace F]
    {S : AdjointableMap A F F} (hS : 0 ≤ S) (T : AdjointableMap A E F) :
    0 ≤ (T.adjoint.comp S).comp T :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, comp_apply, ← T.inner_map_left]
    exact nonneg_iff.mp hS (T x)

/-- Paschke's operator inequality for adjointable maps: `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` in
`A`. -/
theorem inner_map_self_le [CompleteSpace E] (T : AdjointableMap A E F) (x : E) :
    inner A (T x) (T x) ≤ ‖T‖ ^ 2 • inner A x x := by
  have hbound : T.adjoint.comp T ≤ algebraMap ℝ (AdjointableMap A E E) ‖T.adjoint.comp T‖ :=
    (adjoint_comp_self_nonneg T).isSelfAdjoint.le_algebraMap_norm_self
  have hx := le_iff.mp hbound x
  rwa [comp_apply, ← T.inner_map_left, norm_adjoint_comp_self, Algebra.algebraMap_eq_smul_one,
    ← Complex.coe_smul, smul_apply, one_apply, CStarModule.inner_smul_right_complex,
    Complex.coe_smul] at hx

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
  rw [T.abs.inner_map_left, isSelfAdjoint_iff'.mp (isSelfAdjoint_abs T), ← mul_apply,
    abs_mul_abs, comp_apply, ← T.inner_map_left]

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

end Order

section RightOrder

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- Positivity in `L_A(E)` for a right Hilbert `A`-module, in `A`-valued inner-product form. -/
theorem unop_nonneg_iff {T : AdjointableMap Aᵐᵒᵖ E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ unop (inner Aᵐᵒᵖ x (T x)) := by
  simp_rw [nonneg_iff, unop_nonneg]

/-- The spectral order in `L_A(E)` for a right Hilbert `A`-module, in `A`-valued inner-product
form. -/
theorem unop_le_iff {S T : AdjointableMap Aᵐᵒᵖ E E} :
    S ≤ T ↔ ∀ x : E, unop (inner Aᵐᵒᵖ x (S x)) ≤ unop (inner Aᵐᵒᵖ x (T x)) := by
  simp_rw [le_iff, unop_le_unop]

/-- Paschke's operator inequality for right Hilbert `A`-modules:
`⟨T x, T x⟩_A ≤ ‖T‖ ^ 2 • ⟨x, x⟩_A`. -/
theorem unop_inner_map_self_le (T : AdjointableMap Aᵐᵒᵖ E F) (x : E) :
    unop (inner Aᵐᵒᵖ (T x) (T x)) ≤ ‖T‖ ^ 2 • unop (inner Aᵐᵒᵖ x x) :=
  unop_le_unop.mpr (T.inner_map_self_le x)

end RightOrder

end AdjointableMap

end TauCeti
