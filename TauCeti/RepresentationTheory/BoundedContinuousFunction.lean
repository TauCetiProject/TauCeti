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
Surjective right translations preserve the supremum norm. Right translation preserves the
subspace of functions invariant under left translation by a set of elements.
Restricting the translating monoid along a homomorphism
allows one to translate only at the finite places of an adelic group.
-/

public section

namespace BoundedContinuousFunction

variable (𝕜 V : Type*) [Semiring 𝕜] [PseudoMetricSpace 𝕜]
  [SeminormedAddCommGroup V] [Module 𝕜 V] [IsBoundedSMul 𝕜 V]

section Monoid

variable (G : Type*) [Monoid G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Right translation on bounded continuous functions. -/
noncomputable def rightRegular : Representation 𝕜 G (G →ᵇ V) where
  toFun g := compContinuousₗ V 𝕜 (ContinuousMap.mulRight g)
  map_one' := by ext f x; simp [compContinuousₗ_apply]
  map_mul' g h := by ext f x; simp [compContinuousₗ_apply, mul_assoc]

variable {𝕜 V G}

/-- The right regular action evaluates at the right translate of its argument. -/
@[simp]
theorem rightRegular_apply (g : G) (f : G →ᵇ V) (x : G) :
    rightRegular 𝕜 V G g f x = f (x * g) := by
  simp only [rightRegular, MonoidHom.coe_mk, OneHom.coe_mk, compContinuousₗ_apply,
    compContinuous_apply, ContinuousMap.coe_mulRight]

/-- A surjective right translation preserves the supremum norm. -/
theorem norm_rightRegular_of_surjective (g : G) (hg : Function.Surjective (· * g))
    (f : G →ᵇ V) : ‖rightRegular 𝕜 V G g f‖ = ‖f‖ := by
  simpa only [rightRegular, MonoidHom.coe_mk, OneHom.coe_mk, compContinuousₗ_apply] using
    f.norm_compContinuous_eq_of_surjective (ContinuousMap.mulRight g) hg

private theorem mem_iInf_fixedSubmodule_mulLeft_iff (S : Set G) (f : G →ᵇ V) :
    f ∈ ⨅ γ : S,
      (compContinuousₗ V 𝕜 (ContinuousMap.mulLeft (γ : G))).fixedSubmodule ↔
      ∀ γ ∈ S, ∀ x, f (γ * x) = f x := by
  simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff,
    BoundedContinuousFunction.ext_iff, Subtype.forall, compContinuousₗ_apply,
    compContinuous_apply, ContinuousMap.coe_mulLeft]

variable (𝕜 V) {H : Type*} [Monoid H] (S : Set G) (i : H →* G)

/-- Bounded continuous functions invariant under left translation by elements of `S`,
with right translation restricted along `i`. -/
noncomputable def leftInvariantSubrepresentation :
    Subrepresentation ((rightRegular 𝕜 V G).comp i) where
  toSubmodule := ⨅ γ : S,
    (compContinuousₗ V 𝕜 (ContinuousMap.mulLeft (γ : G))).fixedSubmodule
  apply_mem_toSubmodule h f hf := by
    rw [mem_iInf_fixedSubmodule_mulLeft_iff] at hf ⊢
    simp only [MonoidHom.comp_apply, rightRegular_apply]
    exact fun γ hγ x ↦ by simpa only [mul_assoc] using hf γ hγ (x * i h)

/-- Membership is left invariance, independently of the translating homomorphism. -/
@[simp]
theorem mem_leftInvariantSubrepresentation_iff (f : G →ᵇ V) :
    f ∈ leftInvariantSubrepresentation 𝕜 V S i ↔ ∀ γ ∈ S, ∀ x, f (γ * x) = f x := by
  rw [← Subrepresentation.mem_toSubmodule]
  simp only [leftInvariantSubrepresentation, mem_iInf_fixedSubmodule_mulLeft_iff]

end Monoid

section Group

variable {𝕜 V} {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Right translation preserves the supremum norm. -/
@[simp]
theorem norm_rightRegular (g : G) (f : G →ᵇ V) :
    ‖rightRegular 𝕜 V G g f‖ = ‖f‖ :=
  norm_rightRegular_of_surjective g (mul_right_surjective g) f

end Group

end BoundedContinuousFunction
