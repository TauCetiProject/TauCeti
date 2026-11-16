/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Logic.Small.Basic

/-!
# Smallness of variable-rank bundle atlases

When `𝕜` is `Small.{u}` in the base universe `u`, both the morphisms and the objects of
`TauCeti.FiniteRankAtlas 𝕜 X` are `Small.{u}`: morphisms inject into families of fibre maps, and
atlases inject into their locally constant rank together with the chart domains and
`Shrink.{u} 𝕜`-valued transitions on each clopen stratum, giving `EssentiallySmall.{u}`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

instance [Small.{u} 𝕜] : LocallySmall.{u} (FiniteRankAtlas 𝕜 X) where
  hom_small A D := small_of_injective
    (f := fun (φ : A ⟶ D) (x : X) (v : Fin (A.rank x) → 𝕜) => φ.fiberMap x v)
    fun _ _ h => hom_ext fun x => LinearMap.ext (congrFun (congrFun h x))

instance [Small.{u} 𝕜] : Small.{u} (FiniteRankAtlas 𝕜 X) := by
  let code (A : FiniteRankAtlas 𝕜 X) : Σ r : LocallyConstant X ℕ, ∀ n : ℕ,
      ({x : X // r x = n} → Set {x : X // r x = n}) ×
      ({x : X // r x = n} → {x : X // r x = n} → {x : X // r x = n} →
        (Fin n → Shrink.{u} 𝕜) → (Fin n → Shrink.{u} 𝕜)) :=
    ⟨A.rank, fun n => ((A.charts n).baseSet, fun b c x v i => equivShrink.{u} 𝕜
      ((A.charts n).coordChange b c x (fun j => (equivShrink.{u} 𝕜).symm (v j)) i))⟩
  refine small_of_injective (f := code) fun ⟨r₁, _, h₁⟩ ⟨r₂, _, h₂⟩ h => ?_
  obtain rfl : r₁ = r₂ := congrArg Sigma.fst h
  have hc := eq_of_heq (Sigma.mk.inj h).2
  congr; funext n
  have hcn := congrFun hc n; dsimp only [code] at hcn
  refine VectorBundleCore.ext (congrFun (congrArg Prod.fst hcn))
    (fun x => (h₁ n x).trans (h₂ n x).symm) fun b c x => ContinuousLinearMap.ext fun v =>
      funext fun j => (equivShrink.{u} 𝕜).injective ?_
  simpa only [Equiv.symm_apply_apply] using congrFun (congrFun (congrFun (congrFun (congrFun
    (congrArg Prod.snd hcn) b) c) x) (fun k => equivShrink.{u} 𝕜 (v k))) j

instance [Small.{u} 𝕜] : EssentiallySmall.{u} (FiniteRankAtlas 𝕜 X) :=
  essentiallySmall_of_small_of_locallySmall (FiniteRankAtlas 𝕜 X)

end TauCeti.FiniteRankAtlas
