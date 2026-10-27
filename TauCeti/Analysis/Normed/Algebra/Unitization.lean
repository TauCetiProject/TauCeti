/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Subalgebra.Adjoin
public import Mathlib.Algebra.Algebra.Subalgebra.Unitization
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Algebra.Equiv

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unitizations of closed nonunital subalgebras

For a closed nonunital subalgebra `B` of a Banach algebra `A` which does not contain `1`,
the map `(r, b) ↦ r • 1 + b` identifies its external ℓ¹ unitization with the closed unital
subalgebra `Algebra.adjoin 𝕜 (B : Set A) = B + 𝕜 1` inside `A`. The identification and its
inverse are bounded; the inherited norm need not equal the ℓ¹ norm.

No normalization of the norm of the identity is assumed. The forward map is bounded by
`max ‖(1 : A)‖ 1`, so the results apply to any complete nontrivially normed scalar field.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The algebraic identification is Mathlib's `NonUnitalSubalgebra.unitizationAlgEquiv`;
  the ℓ¹ norm is Mathlib's `WithLp.unitization_norm_def`.
-/

public section

namespace NonUnitalSubalgebra

section NormedField

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  (B : NonUnitalSubalgebra 𝕜 A)

/-- The natural unitization map is bounded for the ℓ¹ norm, without normalizing `‖1‖`. -/
theorem norm_unitization_le (x : WithLp 1 (Unitization 𝕜 B)) :
    ‖unitization B (WithLp.ofLp x)‖ ≤ max ‖(1 : A)‖ 1 * ‖x‖ := by
  rw [unitization_apply, Algebra.algebraMap_eq_smul_one, WithLp.unitization_norm_def, mul_add]
  calc
    ‖(WithLp.ofLp x).fst • (1 : A) + (WithLp.ofLp x).snd‖ ≤
        ‖(WithLp.ofLp x).fst‖ * ‖(1 : A)‖ + ‖(WithLp.ofLp x).snd‖ := by
      -- The norm on the subtype `B` is induced from `A`.
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul]; rfl)
    _ ≤ max ‖(1 : A)‖ 1 * ‖(WithLp.ofLp x).fst‖ +
        max ‖(1 : A)‖ 1 * ‖(WithLp.ofLp x).snd‖ := by
      apply add_le_add
      · rw [mul_comm ‖(WithLp.ofLp x).fst‖]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)

/-- Continuity of the natural map from the external ℓ¹ unitization into the ambient algebra. -/
@[continuity]
theorem continuous_unitization :
    Continuous (fun x : WithLp 1 (Unitization 𝕜 B) ↦ unitization B (WithLp.ofLp x)) := by
  exact AddMonoidHomClass.continuous_of_bound
    ((unitization B).comp (WithLp.unitizationAlgEquiv 𝕜).toAlgHom)
    (max ‖(1 : A)‖ 1) B.norm_unitization_le

end NormedField

section TopologicalAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Ring A] [TopologicalSpace A] [IsTopologicalAddGroup A] [Algebra 𝕜 A]
  [ContinuousSMul 𝕜 A] (B : NonUnitalSubalgebra 𝕜 A)

/-- Adjoining the identity to a closed nonunital subalgebra gives a closed subalgebra.
Its underlying vector subspace is `B.toSubmodule ⊔ 𝕜 ∙ (1 : A)`. -/
theorem isClosed_adjoin (hB : IsClosed (B : Set A)) :
    IsClosed (Algebra.adjoin 𝕜 (B : Set A) : Set A) := by
  rw [← Subalgebra.coe_toSubmodule, B.adjoin_eq_span_one_sup, sup_comm]
  exact B.toSubmodule.isClosed_sup_finiteDimensional (Submodule.span 𝕜 {1}) hB

end TopologicalAlgebra

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] (B : NonUnitalSubalgebra 𝕜 A)

/-- A closed nonunital subalgebra omitting the ambient identity has its external ℓ¹
unitization boundedly isomorphic to its unital closure with the inherited norm. -/
noncomputable def unitizationContinuousAlgEquiv (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) :
    WithLp 1 (Unitization 𝕜 B) ≃A[𝕜] Algebra.adjoin 𝕜 (B : Set A) := by
  letI : CompleteSpace B := hB.completeSpace_coe
  letI : CompleteSpace (Algebra.adjoin 𝕜 (B : Set A)) := (B.isClosed_adjoin hB).completeSpace_coe
  let e := (WithLp.unitizationAlgEquiv 𝕜).trans (unitizationAlgEquiv B h1)
  have he_coe : (fun x ↦ (e x : A)) =
      fun x ↦ unitization B (WithLp.ofLp x) := rfl
  have he : Continuous e := continuous_induced_rng.mpr (by
    simp only [Function.comp_def, he_coe]
    exact B.continuous_unitization)
  exact { e with
    continuous_toFun := he
    continuous_invFun := by
      -- Explicit carriers fix the algebra-to-linear coercion for elaboration.
      exact LinearEquiv.continuous_symm (𝕜 := 𝕜) (𝕜' := 𝕜)
        (E := WithLp 1 (Unitization 𝕜 B)) (F := Algebra.adjoin 𝕜 (B : Set A))
        e.toLinearEquiv (by simpa only [AlgEquiv.coe_toLinearEquiv] using he) }

/-- The continuous unitization identification has the standard algebraic identification as its
underlying algebra equivalence, so its inverse is the same algebraic inverse. -/
theorem unitizationContinuousAlgEquiv_toAlgEquiv (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) :
    (B.unitizationContinuousAlgEquiv hB h1).toAlgEquiv =
      (WithLp.unitizationAlgEquiv 𝕜).trans (unitizationAlgEquiv B h1) := (rfl)

/-- The bounded identification sends the two unitization coordinates to their sum in `A`. -/
@[simp]
theorem unitizationContinuousAlgEquiv_apply_coe (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) (x : WithLp 1 (Unitization 𝕜 B)) :
    (B.unitizationContinuousAlgEquiv hB h1 x : A) =
      algebraMap 𝕜 A (WithLp.ofLp x).fst + (WithLp.ofLp x).snd := by
  rfl

end NontriviallyNormedField

end NonUnitalSubalgebra
