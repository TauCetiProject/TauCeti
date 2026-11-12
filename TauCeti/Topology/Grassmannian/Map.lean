/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Basic

/-!
# Maps of finite Grassmannians

An injective linear map between coordinate spaces sends a plane to its image. These maps
preserve rank, are functorial, and are continuous for the frame-quotient topologies whenever
the original linear map is continuous. They provide the maps between finite ambient stages
without choosing bases of the planes. On frames the construction simply applies the linear
map to every vector.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] {r N M L : ℕ}

namespace finiteFullRankFrame

/-- Apply an injective linear map to each vector of a frame. -/
def map (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (v : finiteFullRankFrame 𝕜 r N) : finiteFullRankFrame 𝕜 r M :=
  ⟨f ∘ v.1, v.2.map' f (LinearMap.ker_eq_bot.2 hf)⟩

@[simp]
theorem coe_map (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (v : finiteFullRankFrame 𝕜 r N) : (map f hf v).1 = f ∘ v.1 := (rfl)

/-- Applying a continuous linear map to all frame vectors is continuous. -/
@[fun_prop]
theorem continuous_map [TopologicalSpace 𝕜]
    (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (hfc : Continuous f) : Continuous (map (r := r) f hf) :=
  (continuous_pi fun i ↦ hfc.comp ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _

end finiteFullRankFrame

namespace finiteGrassmannian

/-- The image of a plane under an injective linear map, retaining its dimension. -/
noncomputable def map (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (V : finiteGrassmannian 𝕜 r N) : finiteGrassmannian 𝕜 r M :=
  ⟨V.1.map f, (Submodule.equivMapOfInjective f hf V.1).finrank_eq.symm.trans V.2⟩

@[simp]
theorem coe_map (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (V : finiteGrassmannian 𝕜 r N) : (map f hf V).1 = V.1.map f := (rfl)

/-- Taking spans commutes with applying an injective linear map to frame vectors. -/
@[simp]
theorem frameSpan_map (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (v : finiteFullRankFrame 𝕜 r N) :
    frameSpan (finiteFullRankFrame.map f hf v) = map f hf (frameSpan v) := by
  apply Subtype.ext
  simp only [coe_frameSpan, finiteFullRankFrame.coe_map, coe_map, range_comp,
    Submodule.span_image]

@[simp]
theorem map_id (V : finiteGrassmannian 𝕜 r N) :
    map LinearMap.id Function.injective_id V = V :=
  Subtype.ext (Submodule.map_id _)

@[simp]
theorem map_comp (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (g : (Fin M → 𝕜) →ₗ[𝕜] (Fin L → 𝕜)) (hg : Function.Injective g)
    (V : finiteGrassmannian 𝕜 r N) :
    map (g.comp f) (hg.comp hf) V = map g hg (map f hf V) :=
  Subtype.ext (Submodule.map_comp f g V.1)

/-- An injective linear map induces an injective map of Grassmannians. -/
theorem map_injective (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f) :
    Function.Injective (map (r := r) f hf) := fun _ _ h ↦
  Subtype.ext (Submodule.map_injective_of_injective hf (congrArg Subtype.val h))

/-- A continuous injective linear map induces a continuous map of finite Grassmannians
for their frame-quotient topologies. -/
@[fun_prop]
theorem continuous_map [TopologicalSpace 𝕜]
    (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (hfc : Continuous f) : Continuous (map (r := r) f hf) := by
  apply isQuotientMap_frameSpan.continuous_iff.2
  exact (continuous_frameSpan.comp (finiteFullRankFrame.continuous_map f hf hfc)).congr
    fun v ↦ frameSpan_map f hf v

end finiteGrassmannian

end TauCeti
