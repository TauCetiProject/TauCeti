/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.Basic

/-!
# Homotopy invariance of the split Grothendieck group of finite-rank bundle cores

This module lifts homotopy invariance of `TauCeti.FiniteRankBundleCore` pullbacks to the split
Grothendieck group `TauCeti.SplitK0 (TauCeti.FiniteRankBundleCore 𝕜 ·)`.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.splitK0_of_pullback_cylinderSlice_eq`: slice pullbacks over `X × I`
  at arbitrary times represent equal classes in `SplitK0 (FiniteRankBundleCore 𝕜 X)`.
* `ContinuousMap.Homotopic.splitK0_map_pullbackFunctor_eq`: homotopic maps induce equal pullback
  homomorphisms on `SplitK0 (FiniteRankBundleCore 𝕜 ·)`.
* `TauCeti.FiniteRankBundleCore.splitK0PullbackEquiv`: the additive group isomorphism induced by a
  homotopy equivalence `X ≃ₕ Y` between paracompact R₁ spaces.
-/

public section

open CategoryTheory
open scoped ContinuousMap unitInterval

namespace TauCeti.FiniteRankBundleCore

universe u v w z

variable {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- Over a paracompact R₁ base `X`, the slice pullbacks of a finite-rank core over `X × I` at any
two times represent the same class in `SplitK0 (FiniteRankBundleCore 𝕜 X)`. -/
theorem splitK0_of_pullback_cylinderSlice_eq {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (A : FiniteRankBundleCore 𝕜 (X × I)) (s t : I) :
    (SplitK0.of (A.pullback (cylinderSlice X s)) : SplitK0 (FiniteRankBundleCore 𝕜 X)) =
      SplitK0.of (A.pullback (cylinderSlice X t)) := by
  obtain ⟨e⟩ := nonempty_iso_pullback_cylinderSlice A s t
  exact SplitK0.of_congr e

/-- Homotopic maps out of a paracompact R₁ space induce equal pullback homomorphisms on
`SplitK0 (FiniteRankBundleCore 𝕜 ·)`. -/
theorem _root_.ContinuousMap.Homotopic.splitK0_map_pullbackFunctor_eq {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) (𝕜 : Type v) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [CompleteSpace 𝕜] :
    SplitK0.map (pullbackFunctor (𝕜 := 𝕜) f₀) = SplitK0.map (pullbackFunctor (𝕜 := 𝕜) f₁) :=
  SplitK0.map_congr fun A ↦ h.nonempty_iso_pullback A

section HomotopyEquiv

variable [R1Space Y] [ParacompactSpace Y]

/-- A homotopy equivalence `e : X ≃ₕ Y` between paracompact R₁ spaces induces an additive
isomorphism `SplitK0 (FiniteRankBundleCore 𝕜 Y) ≃+ SplitK0 (FiniteRankBundleCore 𝕜 X)` by
pullback. -/
noncomputable def splitK0PullbackEquiv (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) :
    SplitK0 (FiniteRankBundleCore 𝕜 Y) ≃+ SplitK0 (FiniteRankBundleCore 𝕜 X) :=
  (SplitK0.map (pullbackFunctor (𝕜 := 𝕜) e.toFun)).toAddEquiv
    (SplitK0.map (pullbackFunctor (𝕜 := 𝕜) e.symm.toFun))
    (SplitK0.hom_ext fun A ↦ by
      have hsymm : e.symm.toFun = e.invFun := ContinuousMap.ext (congrFun e.coe_invFun.symm)
      obtain ⟨iso⟩ := e.right_inv.nonempty_iso_pullback A
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, pullback_comp, hsymm,
        SplitK0.of_congr iso, pullback_id, AddMonoidHom.id_apply])
    (SplitK0.hom_ext fun A ↦ by
      have hsymm : e.symm.toFun = e.invFun := ContinuousMap.ext (congrFun e.coe_invFun.symm)
      obtain ⟨iso⟩ := e.left_inv.nonempty_iso_pullback A
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, pullback_comp, hsymm,
        SplitK0.of_congr iso, pullback_id, AddMonoidHom.id_apply])

@[simp]
theorem splitK0PullbackEquiv_of (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) (A : FiniteRankBundleCore 𝕜 Y) :
    splitK0PullbackEquiv 𝕜 e (SplitK0.of A) = SplitK0.of (A.pullback e.toFun) :=
  SplitK0.map_of (pullbackFunctor (𝕜 := 𝕜) e.toFun) A

@[simp]
theorem splitK0PullbackEquiv_toAddMonoidHom (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) :
    ((splitK0PullbackEquiv 𝕜 e :
        SplitK0 (FiniteRankBundleCore 𝕜 Y) ≃+ SplitK0 (FiniteRankBundleCore 𝕜 X)) :
      SplitK0 (FiniteRankBundleCore 𝕜 Y) →+ SplitK0 (FiniteRankBundleCore 𝕜 X)) =
      SplitK0.map (pullbackFunctor (𝕜 := 𝕜) e.toFun) :=
  AddMonoidHom.ext fun _ ↦ rfl

@[simp]
theorem splitK0PullbackEquiv_symm (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) :
    (splitK0PullbackEquiv 𝕜 e).symm = splitK0PullbackEquiv 𝕜 e.symm :=
  AddEquiv.ext fun _ ↦ rfl

@[simp]
theorem splitK0PullbackEquiv_refl (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (X : Type u) [TopologicalSpace X]
    [R1Space X] [ParacompactSpace X] :
    splitK0PullbackEquiv 𝕜 (ContinuousMap.HomotopyEquiv.refl X) =
      AddEquiv.refl (SplitK0 (FiniteRankBundleCore 𝕜 X)) :=
  AddEquiv.toAddMonoidHom_injective <| SplitK0.hom_ext fun A ↦ by
    have hrefl : (ContinuousMap.HomotopyEquiv.refl X).toFun = .id X := by
      ext a
      simp
    simp [hrefl]

@[simp]
theorem splitK0PullbackEquiv_trans {Z : Type z} [TopologicalSpace Z] [R1Space Z]
    [ParacompactSpace Z] (𝕜 : Type v) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [CompleteSpace 𝕜] (e₁ : X ≃ₕ Y) (e₂ : Y ≃ₕ Z) :
    splitK0PullbackEquiv 𝕜 (e₁.trans e₂) =
      (splitK0PullbackEquiv 𝕜 e₂).trans (splitK0PullbackEquiv 𝕜 e₁) :=
  AddEquiv.toAddMonoidHom_injective <| SplitK0.hom_ext fun A ↦ by
    have htrans : (e₁.trans e₂).toFun = e₂.toFun.comp e₁.toFun := by
      ext a
      simp
    simp [htrans]

end HomotopyEquiv

end TauCeti.FiniteRankBundleCore
