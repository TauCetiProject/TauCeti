/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Basic

/-!
# Pullbacks of smooth fibrewise maps

A smooth fibrewise map induces a smooth map of pullbacks along a smooth map of bases, by the
smooth universal property of the pullback total space.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ManifoldTotalSpace

variable {n : ℕ∞ω} {𝕜 B B' F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB']
  {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners 𝕜 EB' HB'}
  [TopologicalSpace B'] [ChartedSpace HB' B']
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
  [TopologicalSpace F] [ChartedSpace HF F]
  {P Q : B → Type*}
  [TopologicalSpace (TotalSpace F P)] [∀ b, TopologicalSpace (P b)] [FiberBundle F P]
  [∀ b, Nonempty (P b)]
  [TopologicalSpace (TotalSpace F Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle F Q]
  [∀ b, Nonempty (Q b)]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- Pullback along a smooth base map preserves smoothness of fibrewise maps. -/
theorem contMDiff_fiberwiseMap_pullback (f : K) (hf : ContMDiff IB' IB n f)
    {φ : ∀ b, P b → Q b}
    (hφ : ContMDiff (IB.prod IF) (IB.prod IF) n (fiberwiseMap (F := F) φ)) :
    ContMDiff (IB'.prod IF) (IB'.prod IF) n
      (fiberwiseMap (F := F) (E := (f : B' → B) *ᵖ P) (E' := (f : B' → B) *ᵖ Q)
        fun b ↦ φ (f b)) := by
  let q : ManifoldTotalSpace F ((f : B' → B) *ᵖ P) → TotalSpace F ((f : B' → B) *ᵖ Q) :=
    fun x ↦ ⟨((homeomorph F ((f : B' → B) *ᵖ P)).symm x).proj,
      φ _ ((homeomorph F ((f : B' → B) *ᵖ P)).symm x).snd⟩
  have h : ContMDiff (IB'.prod IF) (IB'.prod IF) n
      (fun x ↦ homeomorph F ((f : B' → B) *ᵖ Q) (q x)) := by
    refine (contMDiff_pullback_iff f hf).2 ⟨?_, ?_⟩
    · exact contMDiff_proj n F ((f : B' → B) *ᵖ P) IB' IF
    · convert hφ.comp (contMDiff_pullbackLift (E := P) n IF f hf) using 1
      funext x
      exact (fiberwiseMap_homeomorph φ (Pullback.lift f
        ((homeomorph F ((f : B' → B) *ᵖ P)).symm x))).symm
  exact h.congr fun x ↦ (congrFun (fiberwiseMap_eq
    (E := (f : B' → B) *ᵖ P) (E' := (f : B' → B) *ᵖ Q) _) x)

end TauCeti.ManifoldTotalSpace
