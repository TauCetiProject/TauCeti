/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Right translation of bounded continuous functions

Right translation acts on bounded continuous functions by `R(g) f(x) = f(xg)`.
It preserves the supremum norm and the subspace of functions invariant under left
translation by a subgroup. Restricting the translating group along a homomorphism
allows one to translate only at the finite places of an adelic group.
-/

public section

namespace BoundedContinuousFunction

variable (𝕜 V : Type*) [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

section Monoid

variable (G : Type*) [Monoid G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Right translation on bounded continuous functions. -/
noncomputable def rightRegular : Representation 𝕜 G (G →ᵇ V) where
  toFun g := (compContinuousCLM V 𝕜 (ContinuousMap.mulRight g)).toLinearMap
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_assoc]

variable {𝕜 V G}

/-- The right regular action evaluates at the right translate of its argument. -/
@[simp]
theorem rightRegular_apply (g : G) (f : G →ᵇ V) (x : G) :
    rightRegular 𝕜 V G g f x = f (x * g) :=
  (rfl)

end Monoid

section Group

variable {𝕜 V} {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Right translation preserves the supremum norm. -/
@[simp]
theorem norm_rightRegular (g : G) (f : G →ᵇ V) :
    ‖rightRegular 𝕜 V G g f‖ = ‖f‖ := by
  obtain ⟨e, he⟩ : ∃ e : (⊤ : Submodule 𝕜 (G →ᵇ V)) ≃ₗᵢ[𝕜] (⊤ : Submodule 𝕜 (G →ᵇ V)),
      ∀ f, (e f : G →ᵇ V) = rightRegular 𝕜 V G g f :=
    ⟨compContinuousₗᵢ _ (ContinuousMap.mulRight g) (ContinuousMap.mulRight g⁻¹) (by simp)
      (by simp) (fun _ _ ↦ trivial) (fun _ _ ↦ trivial), fun _ ↦ compContinuousₗᵢ_apply ..⟩
  exact (congrArg norm (he ⟨f, trivial⟩)).symm.trans (e.norm_map ⟨f, trivial⟩)

variable (𝕜 V) {H : Type*} [Monoid H] (Γ : Subgroup G) (i : H →* G)

/-- Bounded continuous functions invariant under left translation by `Γ`, with right
translation restricted along `i`. -/
noncomputable def leftInvariantSubrepresentation :
    Subrepresentation ((rightRegular 𝕜 V G).comp i) where
  toSubmodule := ⨅ γ : Γ,
    (compContinuousCLM V 𝕜 (ContinuousMap.mulLeft (γ : G))).toLinearMap.fixedSubmodule
  apply_mem_toSubmodule h f hf := by
    simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff,
      BoundedContinuousFunction.ext_iff, ContinuousLinearMap.coe_coe, compContinuousCLM_apply,
      compContinuous_apply, ContinuousMap.coe_mulLeft, MonoidHom.comp_apply,
      rightRegular_apply] at hf ⊢
    exact fun γ x ↦ by simpa only [mul_assoc] using hf γ (x * i h)

/-- Membership is left invariance, independently of the translating homomorphism. -/
@[simp]
theorem mem_leftInvariantSubrepresentation_iff (f : G →ᵇ V) :
    f ∈ leftInvariantSubrepresentation 𝕜 V Γ i ↔ ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x := by
  rw [← Subrepresentation.mem_toSubmodule]
  simp only [leftInvariantSubrepresentation, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff,
    BoundedContinuousFunction.ext_iff, Subtype.forall, ContinuousLinearMap.coe_coe,
    compContinuousCLM_apply, compContinuous_apply, ContinuousMap.coe_mulLeft]

end Group

end BoundedContinuousFunction
