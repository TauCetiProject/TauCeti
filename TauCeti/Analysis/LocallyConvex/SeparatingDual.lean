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

Furthermore, separating dual is characterized by injectivity of canonical evaluation into the strong
bidual (`TauCeti.injective_applyₗ_id_iff`), and any evaluation-like map recovering continuous linear
functionals is injective (`TauCeti.injective_of_forall_apply_eq`).
-/

public section

namespace ContinuousLinearMap

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

/-- Canonical evaluation into the strong bidual is injective if and only if continuous linear
functionals separate points of `E`. -/
theorem injective_applyₗ_id_iff (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] :
    Function.Injective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) ↔ SeparatingDual 𝕜 E := by
  refine ⟨fun hinj ↦ ⟨fun x hx ↦ ?_⟩, fun _ ↦
    injective_of_forall_apply_eq (p := id) fun _ _ ↦ rfl⟩
  contrapose! hx
  exact hinj (ContinuousLinearMap.ext fun f ↦ by simp [hx f])

end TauCeti
