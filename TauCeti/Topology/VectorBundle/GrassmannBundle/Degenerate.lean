/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.Basic
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The Grassmann bundles of `0`-planes and of full planes

Let `E → B` be a real vector bundle of finite rank `N` with continuous fibre norm. The Grassmann
bundles `G_0(E)` and `G_N(E)` have a single point in each fibre, the projection `0` and the
identity `1` of `E_b`, so the projection to the base is a homeomorphism in both cases
(`TauCeti.grassmannBundle.projHomeomorphZero`, `TauCeti.grassmannBundle.projHomeomorphFinrank`):
it is a continuous bijection, and closed because it is proper. For the tangent bundle of a
Riemannian manifold `M` of dimension `N` this identifies `G_0(M)` and `G_N(M)` with `M`, by
`x ↦ (x, 0)` and `x ↦ (x, 1)`.

## Main declarations

* `TauCeti.grassmannBundle.projHomeomorphOfForallEqSingleton`: the projection is a homeomorphism
  when every fibre Grassmannian is a single point.
* `TauCeti.grassmannBundle.projHomeomorphZero`: `G_0(E) ≃ₜ B`.
* `TauCeti.grassmannBundle.projHomeomorphFinrank`: `G_N(E) ≃ₜ B` for `N` the rank of `E`.
-/

public section

noncomputable section

open Bundle Set Module

namespace TauCeti.grassmannBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContinuousFiberNorm F E] {k : ℕ}

variable (F E)

omit [FiniteDimensional ℝ F] [ContinuousFiberNorm F E] in
/-- If every fibre Grassmannian `G(E_b, k)` is a single point, the projection `G_k(E) → B` is
bijective. -/
theorem proj_bijective_of_forall_eq_singleton {Q : ∀ b, E b →L[ℝ] E b}
    (hQ : ∀ b, Euclidean.grassmannian ℝ (E b) k = {Q b}) :
    Function.Bijective (proj : grassmannBundle F E k → B) := by
  refine ⟨?_, fun b ↦ ⟨fiberIncl F E k b ⟨Q b, by rw [hQ b]; rfl⟩, proj_fiberIncl b _⟩⟩
  rintro ⟨⟨b, P⟩, hP⟩ ⟨⟨b', P'⟩, hP'⟩ h
  rw [proj_apply, proj_apply] at h
  obtain rfl : b = b' := h
  have h₁ := mem_grassmannBundle.1 hP
  have h₂ := mem_grassmannBundle.1 hP'
  rw [hQ, mem_singleton_iff] at h₁ h₂
  apply Subtype.ext
  dsimp only at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- **The projection is a homeomorphism** when every fibre Grassmannian `G(E_b, k)` is a single
point: it is a continuous bijection, and closed because it is proper. -/
def projHomeomorphOfForallEqSingleton {Q : ∀ b, E b →L[ℝ] E b}
    (hQ : ∀ b, Euclidean.grassmannian ℝ (E b) k = {Q b}) : grassmannBundle F E k ≃ₜ B :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective _ (proj_bijective_of_forall_eq_singleton F E hQ)) continuous_proj
    (isProperMap_proj F E k).isClosedMap

@[simp]
theorem coe_projHomeomorphOfForallEqSingleton {Q : ∀ b, E b →L[ℝ] E b}
    (hQ : ∀ b, Euclidean.grassmannian ℝ (E b) k = {Q b}) :
    ⇑(projHomeomorphOfForallEqSingleton F E hQ) = proj := by
  simp [projHomeomorphOfForallEqSingleton]

/-- The inverse of the projection sends `b` to the only point `(b, Q b)` over `b`. -/
@[simp]
theorem coe_projHomeomorphOfForallEqSingleton_symm_apply {Q : ∀ b, E b →L[ℝ] E b}
    (hQ : ∀ b, Euclidean.grassmannian ℝ (E b) k = {Q b}) (b : B) :
    ((projHomeomorphOfForallEqSingleton F E hQ).symm b :
        TotalSpace (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b) = ⟨b, Q b⟩ := by
  have h : (projHomeomorphOfForallEqSingleton F E hQ).symm b =
      fiberIncl F E k b ⟨Q b, by rw [hQ b]; rfl⟩ :=
    (projHomeomorphOfForallEqSingleton F E hQ).symm_apply_eq.2
      (by rw [coe_projHomeomorphOfForallEqSingleton, proj_fiberIncl])
  rw [h, coe_fiberIncl_apply]

omit [ContinuousFiberNorm F E] in
/-- The fibre Grassmannian of full planes is the identity. -/
@[simp]
theorem grassmannian_finrank_fiber (b : B) :
    Euclidean.grassmannian ℝ (E b) (finrank ℝ F) = {1} := by
  have := VectorBundle.finiteDimensional ℝ F E b
  rw [← VectorBundle.finrank_eq ℝ F E b]
  exact Euclidean.grassmannian_finrank

/-- **The bundle of `0`-planes is the base**: `G_0(E) ≃ₜ B`, with inverse `b ↦ (b, 0)`. -/
def projHomeomorphZero : grassmannBundle F E 0 ≃ₜ B :=
  projHomeomorphOfForallEqSingleton F E (Q := fun _ ↦ 0) fun b ↦
    Euclidean.grassmannian_zero (E := E b)

/-- **The bundle of full planes is the base**: `G_N(E) ≃ₜ B` for `N` the rank of `E`, with
inverse `b ↦ (b, 1)`. -/
def projHomeomorphFinrank : grassmannBundle F E (finrank ℝ F) ≃ₜ B :=
  projHomeomorphOfForallEqSingleton F E (Q := fun _ ↦ 1) (grassmannian_finrank_fiber F E)

@[simp]
theorem coe_projHomeomorphZero : ⇑(projHomeomorphZero F E) = proj :=
  coe_projHomeomorphOfForallEqSingleton F E _

@[simp]
theorem coe_projHomeomorphFinrank : ⇑(projHomeomorphFinrank F E) = proj :=
  coe_projHomeomorphOfForallEqSingleton F E _

/-- The inverse of `G_0(E) ≃ₜ B` sends `b` to the zero projection of `E_b`. -/
@[simp]
theorem coe_projHomeomorphZero_symm_apply (b : B) :
    ((projHomeomorphZero F E).symm b : TotalSpace (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b) = ⟨b, 0⟩ :=
  coe_projHomeomorphOfForallEqSingleton_symm_apply F E _ b

/-- The inverse of `G_N(E) ≃ₜ B` sends `b` to the identity of `E_b`. -/
@[simp]
theorem coe_projHomeomorphFinrank_symm_apply (b : B) :
    ((projHomeomorphFinrank F E).symm b : TotalSpace (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b) =
      ⟨b, 1⟩ :=
  coe_projHomeomorphOfForallEqSingleton_symm_apply F E _ b

end TauCeti.grassmannBundle
