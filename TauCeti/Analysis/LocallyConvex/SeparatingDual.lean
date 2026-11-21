/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Spaces with separating dual

On any topological vector space `E` over a topological field `𝕜` with separating dual
(`SeparatingDual 𝕜 E`), Mathlib's `Algebra.IsCentral.instContinuousLinearMap` establishes that
`E →L[𝕜] E` is a central `𝕜`-algebra. Equivalently, an operator `T : E →L[𝕜] E` commutes with every
continuous linear operator on `E` if and only if it is a scalar multiple of the identity
(`ContinuousLinearMap.commute_forall_iff`). In particular this applies to every normed space over
`ℝ` or `ℂ`.

Furthermore, forgetting continuity on the codomain of canonical evaluation
`ContinuousLinearMap.applyₗ` recovers the flipped coercion `(ContinuousLinearMap.coeLM 𝕜).flip`
used in Mathlib's `separatingDual_iff_injective` (`ContinuousLinearMap.coeLM_comp_applyₗ`), and
any evaluation-like map recovering continuous linear functionals is injective
(`TauCeti.injective_of_forall_apply_eq`).
-/

public section

namespace ContinuousLinearMap

section Commutant

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [TopologicalSpace 𝕜] [TopologicalSpace E]
  [IsTopologicalRing 𝕜] [Module 𝕜 E] [SeparatingDual 𝕜 E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]

/-- An operator on a topological vector space with separating dual commutes with every continuous
linear operator if and only if it is a scalar multiple of the identity. -/
theorem commute_forall_iff {T : E →L[𝕜] E} :
    (∀ a : E →L[𝕜] E, Commute T a) ↔ ∃ c : 𝕜, T = c • 1 := by
  have hmem : (∀ a : E →L[𝕜] E, Commute T a) ↔ T ∈ Subalgebra.center 𝕜 (E →L[𝕜] E) := by
    rw [Subalgebra.mem_center_iff]
    exact forall_congr' fun _ => by simp [Commute, SemiconjBy, eq_comm]
  rw [hmem, Algebra.IsCentral.mem_center_iff (K := 𝕜)]
  exact exists_congr fun _ => by simp [Algebra.algebraMap_eq_smul_one]

end Commutant

/-- Forgetting continuity on the codomain of canonical evaluation `applyₗ` recovers the flipped
coercion `(coeLM 𝕜).flip` used in `separatingDual_iff_injective`. -/
theorem coeLM_comp_applyₗ {𝕜 E G : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] [AddCommGroup G] [Module 𝕜 G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G] :
    (coeLM (R := 𝕜) 𝕜 (M := E →L[𝕜] G) (N₃ := G)).comp (applyₗ G (RingHom.id 𝕜)) =
      (coeLM (R := 𝕜) 𝕜 (M := E) (N₃ := G)).flip :=
  rfl

end ContinuousLinearMap

namespace TauCeti

/-- Any map `ev : E → H` into a family of `𝕜`-valued functions on `G` that recovers every
`φ : StrongDual 𝕜 E` along some map `p : StrongDual 𝕜 E → G` is injective when continuous
functionals separate points of `E`. -/
theorem injective_of_forall_apply_eq {𝕜 E G H : Type*} [Ring 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [SeparatingDual 𝕜 E] [FunLike H G 𝕜]
    {ev : E → H} {p : StrongDual 𝕜 E → G}
    (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x) :
    Function.Injective ev := fun x y hxy ↦
  (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ by
    rw [← hev x φ, ← hev y φ, hxy]

end TauCeti
