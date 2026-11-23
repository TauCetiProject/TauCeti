/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Quaternion
public import Mathlib.Tactic.FunProp
public import TauCeti.Topology.VectorBundle.Projectivization.Basic

/-!
# Fibres and degenerate cases of Hermitian projective bundles

The fibre identification is continuous in both directions and preserves the original line and
preferred-frame formulas. Real and complex line bundles project homeomorphically to their bases,
including a disconnected base. A nonzero projective line in a trivial rank-two bundle over the
noncompact real line is recovered by the fibre identification. Rank zero and an empty base retain
their empty native total spaces. The semilinear continuity interface does not require a norm,
completeness or finite-dimensionality.
-/

public noncomputable section

open Bundle TauCeti Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti.ProjectiveBundleClients

section Semilinear

variable {K L V W : Type*} [DivisionRing K] [DivisionRing L]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [AddCommGroup W] [Module L W] [TopologicalSpace W]
  {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

example (f : V ≃ₛₗ[σ] W) (hf : Continuous f) :
    Continuous (LinearEquiv.mapProjectivization f) := by
  fun_prop

example {X : Type*} [TopologicalSpace X] (f : V ≃ₛₗ[σ] W) (hf : Continuous f)
    (g : X → ℙ K V) (hg : Continuous g) :
    Continuous fun x ↦ LinearEquiv.mapProjectivization f (g x) := by
  fun_prop

example (f : V ≃ₛₗ[σ] W) (hf : Continuous f.symm) :
    Continuous (LinearEquiv.mapProjectivization f).symm := by
  rw [LinearEquiv.mapProjectivization_symm]
  fun_prop

end Semilinear

example : Continuous (LinearEquiv.mapProjectivization
    (LinearEquiv.refl (Quaternion ℝ) (Quaternion ℝ × Quaternion ℝ))) :=
  LinearEquiv.continuous_mapProjectivization _
    ((continuous_id : Continuous (id : Quaternion ℝ × Quaternion ℝ → _)).congr
      fun x ↦ (LinearEquiv.refl_apply x).symm)

section Associated

variable {G B F : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace B]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]

example (s : ∀ b, P b) (hs : Continuous fun b ↦ TotalSpace.mk' G b (s b))
    (b : B) (v : F) :
    (AssociatedBundle.prodHomeomorphOfSection s hs).symm
      (⟨b, AssociatedBundle.mk G (s b) v⟩ : TotalSpace F (AssociatedBundle G P F)) = (b, v) := by
  simp

end Associated

section NativeFibres

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type*)
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E] [FiniteDimensional 𝕜 F]
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V] [FiniteDimensional 𝕜 V] [Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)]

example (b : B) :
    Continuous (ProjectiveBundle.fiberHomeomorph (𝕜 := 𝕜) (F := F) (E := E) (V := V) b) :=
  (ProjectiveBundle.fiberHomeomorph b).continuous

example (b : B) :
    Continuous (ProjectiveBundle.fiberHomeomorph (𝕜 := 𝕜) (F := F) (E := E) (V := V) b).symm :=
  (ProjectiveBundle.fiberHomeomorph b).symm.continuous

example (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :
    FiniteDimensional 𝕜 (ProjectiveBundle.tautologicalLine y) :=
  inferInstance

example (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :
    (y, (⟨y.proj, 0⟩ : TotalSpace F E)) ∈ ProjectiveBundle.tautologicalLineSet 𝕜 F E V :=
  ProjectiveBundle.mk_mem_tautologicalLineSet_iff.2 (Submodule.zero_mem _)

example : IsProperMap (TotalSpace.proj :
    TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) → B) :=
  ProjectiveBundle.isProperMap_proj

example [T2Space B] : IsClosed (ProjectiveBundle.tautologicalLineSet 𝕜 F E V) :=
  ProjectiveBundle.isClosed_tautologicalLineSet

example {b : B} (φ : OrthonormalFrameBundle.Fiber 𝕜 F E V b) (ℓ : ℙ 𝕜 V) :
    (ProjectiveBundle.fiberHomeomorph b).symm
      (LinearEquiv.mapProjectivization φ.frame.toLinearEquiv ℓ) =
        AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ ℓ := by
  simp

end NativeFibres

local instance (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Fact (Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) =
      Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n))) := ⟨rfl⟩

private def complexLine : ℙ ℂ (EuclideanSpace ℂ (Fin 2)) :=
  Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin 2) 1) (by
    intro h
    have he := congrArg (fun v : EuclideanSpace ℂ (Fin 2) ↦ v 0) h
    simp at he)

example (b : ℝ) :
    ProjectiveBundle.fiberHomeomorph b
        (AssociatedBundle.mk (unitary (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
          (OrthonormalFrameBundle.trivialFrame ℝ b) complexLine) = complexLine := by
  have h := ProjectiveBundle.snd_trivialHomeomorph
    (⟨b, AssociatedBundle.mk (unitary (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      (OrthonormalFrameBundle.trivialFrame ℝ b) complexLine⟩ :
        TotalSpace (ℙ ℂ (EuclideanSpace ℂ (Fin 2)))
          (ProjectiveBundle ℂ (EuclideanSpace ℂ (Fin 2))
            (Trivial ℝ (EuclideanSpace ℂ (Fin 2))) (EuclideanSpace ℂ (Fin 2))))
  rw [ProjectiveBundle.trivialHomeomorph_mk] at h
  exact h.symm

example {B : Type*} [TopologicalSpace B]
    (y : TotalSpace (ℙ ℂ (EuclideanSpace ℂ (Fin 0)))
      (ProjectiveBundle ℂ (EuclideanSpace ℂ (Fin 0))
        (Trivial B (EuclideanSpace ℂ (Fin 0))) (EuclideanSpace ℂ (Fin 0)))) : False := by
  have ℓ := ProjectiveBundle.fiberHomeomorph y.proj y.snd
  exact ℓ.rep_ne_zero (Subsingleton.elim _ _)

section Empty

/-- The empty base has its unique topology. -/
local instance emptyTopology : TopologicalSpace Empty := ⊥

example (y : TotalSpace (ℙ ℂ (EuclideanSpace ℂ (Fin 2)))
    (ProjectiveBundle ℂ (EuclideanSpace ℂ (Fin 2))
      (Trivial Empty (EuclideanSpace ℂ (Fin 2))) (EuclideanSpace ℂ (Fin 2)))) : False :=
  Empty.elim y.proj

end Empty

section Disconnected

/-- The two-point base carries the discrete topology. -/
local instance boolTopology : TopologicalSpace Bool := ⊥

example (𝕜 : Type*) [RCLike 𝕜]
    (y : TotalSpace (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin 1)))
      (ProjectiveBundle 𝕜 (EuclideanSpace 𝕜 (Fin 1))
        (Trivial Bool (EuclideanSpace 𝕜 (Fin 1))) (EuclideanSpace 𝕜 (Fin 1)))) :
    (ProjectiveBundle.projHomeomorphOfFinrankEqOne (by simp) y) = y.proj := by
  simp

example (𝕜 : Type*) [RCLike 𝕜]
    (y : TotalSpace (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin 1)))
      (ProjectiveBundle 𝕜 (EuclideanSpace 𝕜 (Fin 1))
        (Trivial Bool (EuclideanSpace 𝕜 (Fin 1))) (EuclideanSpace 𝕜 (Fin 1)))) :
    ProjectiveBundle.tautologicalLine y = ⊤ :=
  ProjectiveBundle.tautologicalLine_eq_top_of_finrank_eq_one (by simp) y

end Disconnected

example {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V]
    [NormedSpace 𝕜 V] : IsBoundedSMul (V →L[𝕜] V) V :=
  inferInstance

end TauCeti.ProjectiveBundleClients
