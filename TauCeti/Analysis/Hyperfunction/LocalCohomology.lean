/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Hyperfunction.OneDimensional
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Topology.Sheaves.SupportedCohomology.Module

/-!
# One-dimensional hyperfunctions as local cohomology of holomorphic functions

Sato defines the hyperfunctions on an open set `U ⊆ ℝ` as the local cohomology
`H¹_U(W, 𝒪)` of the sheaf `𝒪` of holomorphic functions, for any open `W ⊆ ℂ` in which `U` is
closed. This file compares that definition with the explicit quotient
`O(ℂ ∖ ℝ) / O(W(U))` of `TauCeti.Analysis.Hyperfunction.OneDimensional`, where
`W(U) = ℂ ∖ (ℝ ∖ U)`.

First, the holomorphic functions on an open `V ⊆ ℂ`, encoded as functions on `ℂ` vanishing off
`V` (`TauCeti.Hyperfunction.holomorphicSections`), are identified with the sections over `V` of
the holomorphic structure sheaf `TauCeti.holomorphicStructureSheafModules 𝓘(ℂ) ℂ`, compatibly
with restriction (`TauCeti.Hyperfunction.holomorphicSectionsEquiv`).

Second, take `W = W(U)` and the closed set `ℝ ⊆ ℂ` (`TauCeti.Hyperfunction.realAxis`), so that
`W(U) ∩ ℝ = U` and `W(U) ∖ ℝ = ℂ ∖ ℝ`. The long exact sequence of supports
`𝒪(W(U)) ⟶ 𝒪(ℂ ∖ ℝ) ⟶ H¹_ℝ(W(U), 𝒪) ⟶ H¹(W(U), 𝒪)` shows that its connecting map induces an
injective complex-linear map
`O(ℂ ∖ ℝ) / O(W(U)) ⟶ H¹_ℝ(W(U), 𝒪)`
(`TauCeti.Hyperfunction.oneDimBoundaryToSupportedModuleH`), whose image is the kernel of
`H¹_ℝ(W(U), 𝒪) ⟶ H¹(W(U), 𝒪)`. It commutes with restriction to smaller real open sets. Hence it
is an isomorphism whenever `H¹(W(U), 𝒪) = 0`, the vanishing of the first cohomology of `𝒪` on
open subsets of `ℂ` (the additive Cousin problem), which is not proved here.

## Main declarations

* `TauCeti.Hyperfunction.holomorphicSectionsEquiv`: holomorphic functions on `V` in the ambient
  encoding are the sections of the holomorphic structure sheaf over `V`;
* `TauCeti.Hyperfunction.realAxis`: the real axis as a closed subset of `ℂ`;
* `TauCeti.Hyperfunction.oneDimBoundaryToSupportedModuleH`: the map
  `O(ℂ ∖ ℝ) / O(W(U)) ⟶ H¹_ℝ(W(U), 𝒪)`, injective
  (`TauCeti.Hyperfunction.oneDimBoundaryToSupportedModuleH_injective`), with image the kernel of
  `H¹_ℝ(W(U), 𝒪) ⟶ H¹(W(U), 𝒪)`
  (`TauCeti.Hyperfunction.mem_range_oneDimBoundaryToSupportedModuleH_iff`), and natural in `U`
  (`TauCeti.Hyperfunction.supportedModuleHPresheaf_map_oneDimBoundaryToSupportedModuleH`).

## References

* M. Sato, *Theory of hyperfunctions I*, J. Fac. Sci. Univ. Tokyo Sect. I 8 (1959), 139–193.
* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* A. Kaneko, *Introduction to hyperfunctions*, Kluwer, 1988, Chapter 1.
-/

public section

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.Hyperfunction

/-! ### Holomorphic sections as sections of the structure sheaf -/

/-- A holomorphic function on an open `V ⊆ ℂ` is complex analytic on the open submanifold `V`. -/
theorem contMDiff_holomorphicSections {V : Opens ℂ} (f : holomorphicSections V) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : V ↦ (f : ℂ → ℂ) x) :=
  (contMDiffOn_iff_contDiffOn.2 (((mem_holomorphicSections_iff.1 f.2).1.analyticOnNhd
    V.isOpen).contDiffOn V.isOpen.uniqueDiffOn)).comp_contMDiff contMDiff_subtype_val
    fun x ↦ x.2

/-- A section of the holomorphic structure sheaf over `V`, extended by zero off `V`, is a
holomorphic function on `V` in the ambient encoding. -/
theorem extend_mem_holomorphicSections {V : Opens ℂ}
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.obj (op V)) :
    Subtype.val.extend s 0 ∈ holomorphicSections V := by
  refine mem_holomorphicSections_iff.2 ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have h := (holomorphicStructureSheafModules.contMDiff s ⟨z, hz⟩).extend_subtypeVal 0
    exact ((contMDiffAt_iff_contDiffAt.1 h).differentiableAt (by simp)).differentiableWithinAt
  · exact Function.extend_apply' _ _ _ fun ⟨x, hx⟩ ↦ hz (hx ▸ x.2)

/-- The holomorphic functions on an open `V ⊆ ℂ`, encoded as functions on `ℂ` vanishing off `V`,
are the sections over `V` of the holomorphic structure sheaf of `ℂ`. -/
def holomorphicSectionsEquiv (V : Opens ℂ) :
    holomorphicSections V ≃ₗ[ℂ] (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.obj (op V) where
  toFun f := holomorphicStructureSheafModules.ofContMDiff _ (contMDiff_holomorphicSections f)
  invFun s := ⟨Subtype.val.extend s 0, extend_mem_holomorphicSections s⟩
  map_add' f g := holomorphicStructureSheafModules.ext fun x ↦ by simp
  map_smul' c f := holomorphicStructureSheafModules.ext fun x ↦ by simp
  left_inv f := Subtype.ext <| funext fun z ↦ by
    by_cases hz : z ∈ V
    · exact (Subtype.val_injective.extend_apply _ _ ⟨z, hz⟩).trans
        (holomorphicStructureSheafModules.ofContMDiff_apply _ _ _)
    · exact (Function.extend_apply' _ _ _ fun ⟨x, hx⟩ ↦ hz (hx ▸ x.2)).trans
        ((mem_holomorphicSections_iff.1 f.2).2 z hz).symm
  right_inv s := holomorphicStructureSheafModules.ext fun x ↦
    (holomorphicStructureSheafModules.ofContMDiff_apply _ _ x).trans
      (Subtype.val_injective.extend_apply _ _ x)

@[simp]
theorem holomorphicSectionsEquiv_apply {V : Opens ℂ} (f : holomorphicSections V) (x : V) :
    holomorphicSectionsEquiv V f x = (f : ℂ → ℂ) x :=
  holomorphicStructureSheafModules.ofContMDiff_apply _ _ x

@[simp]
theorem coe_holomorphicSectionsEquiv_symm_apply {V : Opens ℂ}
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.obj (op V)) (x : V) :
    ((holomorphicSectionsEquiv V).symm s : ℂ → ℂ) x = s x :=
  Subtype.val_injective.extend_apply _ _ x

/-- The identification of holomorphic functions with sections of the structure sheaf commutes
with restriction to a smaller open set. -/
theorem holomorphicSectionsEquiv_holomorphicRestrict {U V : Opens ℂ} (h : U ≤ V)
    (f : holomorphicSections V) :
    holomorphicSectionsEquiv U (holomorphicRestrict h f) =
      (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.map (homOfLE h).op
        (holomorphicSectionsEquiv V f) :=
  holomorphicStructureSheafModules.ext fun x ↦ (holomorphicSectionsEquiv_apply _ x).trans <|
    (congrFun (coe_holomorphicRestrict h f) x).trans <| (indicator_of_mem x.2 _).trans <|
      (holomorphicSectionsEquiv_apply f (Opens.inclusion h x)).symm.trans
        (holomorphicStructureSheafModules.map_apply 𝓘(ℂ) ℂ _ _ x).symm

/-! ### The real axis -/

/-- The real axis `{z | z.im = 0}`, as a closed subset of `ℂ`. -/
def realAxis : Closeds ℂ :=
  ⟨{z | z.im = 0}, isClosed_eq Complex.continuous_im continuous_const⟩

@[simp]
theorem mem_realAxis_iff {z : ℂ} : z ∈ realAxis ↔ z.im = 0 :=
  Iff.rfl

/-- The complement of the real axis is `ℂ ∖ ℝ`. -/
theorem compl_realAxis : realAxis.compl = nonRealOpen := by
  ext z
  simp [Closeds.compl]

/-- Removing the real axis from `W(U) = ℂ ∖ (ℝ ∖ U)` leaves `ℂ ∖ ℝ`. -/
theorem complexNeighborhood_inf_compl_realAxis (U : Opens ℝ) :
    complexNeighborhood U ⊓ realAxis.compl = nonRealOpen := by
  rw [compl_realAxis]
  exact inf_eq_right.2 (nonRealOpen_le_complexNeighborhood U)

/-! ### The comparison with local cohomology -/

/-- The holomorphic functions on `ℂ ∖ ℝ`, as sections of the holomorphic structure sheaf over
`W(U) ∖ ℝ = ℂ ∖ ℝ`. -/
private def nonRealSectionsEquiv (U : Opens ℝ) :
    holomorphicSections nonRealOpen ≃ₗ[ℂ] (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.obj
      (op (complexNeighborhood U ⊓ realAxis.compl)) :=
  (LinearEquiv.ofEq _ _ (by rw [complexNeighborhood_inf_compl_realAxis])).trans
    (holomorphicSectionsEquiv _)

@[simp]
private theorem nonRealSectionsEquiv_apply (U : Opens ℝ) (f : holomorphicSections nonRealOpen)
    (x : ↥(complexNeighborhood U ⊓ realAxis.compl)) :
    nonRealSectionsEquiv U f x = (f : ℂ → ℂ) x :=
  holomorphicSectionsEquiv_apply _ x

/-- The connecting map `O(ℂ ∖ ℝ) ⟶ H¹_ℝ(W(U), 𝒪)` of the long exact sequence of supports. -/
private def nonRealToSupportedModuleH (U : Opens ℝ) :
    holomorphicSections nonRealOpen →ₗ[ℂ]
      (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleH realAxis
        (complexNeighborhood U) 1 :=
  (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleHSectionsδ realAxis
    (complexNeighborhood U) ∘ₗ (nonRealSectionsEquiv U).toLinearMap

/-- The kernel of the connecting map consists of the functions extending holomorphically
across `U`. -/
private theorem ker_nonRealToSupportedModuleH (U : Opens ℝ) :
    LinearMap.ker (nonRealToSupportedModuleH U) = throughReal U := by
  ext f
  rw [LinearMap.mem_ker, nonRealToSupportedModuleH, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ((holomorphicStructureSheafModules 𝓘(ℂ) ℂ).exact_map_supportedModuleHSectionsδ _ _ _),
    mem_throughReal_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨_, ((holomorphicSectionsEquiv _).symm g).2, fun z hz ↦ ?_⟩
    have hzW : z ∈ complexNeighborhood U ⊓ realAxis.compl := by
      rwa [complexNeighborhood_inf_compl_realAxis]
    -- both sides are the value at `z` of the section over `W(U) ∖ ℝ`
    exact (coe_holomorphicSectionsEquiv_symm_apply g ⟨z, hzW.1⟩).trans <|
      (holomorphicStructureSheafModules.map_apply 𝓘(ℂ) ℂ _ g ⟨z, hzW⟩).symm.trans <|
        congr($hg ⟨z, hzW⟩).trans (nonRealSectionsEquiv_apply U f ⟨z, hzW⟩)
  · rintro ⟨g, hg, hgf⟩
    refine ⟨holomorphicSectionsEquiv _ ⟨g, hg⟩, holomorphicStructureSheafModules.ext fun x ↦ ?_⟩
    have hx : (x : ℂ) ∈ nonRealOpen := by
      rw [← complexNeighborhood_inf_compl_realAxis U]
      exact x.2
    exact (holomorphicStructureSheafModules.map_apply 𝓘(ℂ) ℂ _ _ x).trans <|
      (holomorphicSectionsEquiv_apply _ _).trans <|
        (hgf hx).trans (nonRealSectionsEquiv_apply U f x).symm

/-- The one-dimensional hyperfunctions `O(ℂ ∖ ℝ) / O(W(U))` on an open `U ⊆ ℝ` map to the local
cohomology `H¹_ℝ(W(U), 𝒪)` of the holomorphic structure sheaf, by the connecting map of the long
exact sequence of supports `𝒪(W(U)) ⟶ 𝒪(ℂ ∖ ℝ) ⟶ H¹_ℝ(W(U), 𝒪) ⟶ H¹(W(U), 𝒪)`. -/
def oneDimBoundaryToSupportedModuleH (U : Opens ℝ) :
    OneDimBoundaryQuotient U →ₗ[ℂ]
      (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleH realAxis
        (complexNeighborhood U) 1 :=
  (throughReal U).liftQ (nonRealToSupportedModuleH U) (ker_nonRealToSupportedModuleH U).ge

/-- The class of a holomorphic function `f` on `ℂ ∖ ℝ` is the connecting image of any section of
the structure sheaf over `W(U) ∖ ℝ = ℂ ∖ ℝ` with the same values as `f`. -/
theorem oneDimBoundaryToSupportedModuleH_mk (U : Opens ℝ) (f : holomorphicSections nonRealOpen)
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.obj
      (op (complexNeighborhood U ⊓ realAxis.compl)))
    (hs : ∀ x, s x = (f : ℂ → ℂ) x) :
    oneDimBoundaryToSupportedModuleH U (Submodule.Quotient.mk f) =
      (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleHSectionsδ realAxis
        (complexNeighborhood U) s :=
  congrArg _ (holomorphicStructureSheafModules.ext fun x ↦
    (nonRealSectionsEquiv_apply U f x).trans (hs x).symm)

/-- The map from one-dimensional hyperfunctions to local cohomology is injective. -/
theorem oneDimBoundaryToSupportedModuleH_injective (U : Opens ℝ) :
    Function.Injective (oneDimBoundaryToSupportedModuleH U) :=
  LinearMap.ker_eq_bot.1 <|
    (throughReal U).ker_liftQ_eq_bot' _ (ker_nonRealToSupportedModuleH U).symm

/-- The image of the one-dimensional hyperfunctions in `H¹_ℝ(W(U), 𝒪)` is the kernel of the map
`H¹_ℝ(W(U), 𝒪) ⟶ H¹(W(U), 𝒪)` forgetting the support, where `H¹(W(U), 𝒪)` is cohomology with
supports in the whole plane. -/
theorem mem_range_oneDimBoundaryToSupportedModuleH_iff (U : Opens ℝ)
    (x : (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleH realAxis
      (complexNeighborhood U) 1) :
    x ∈ LinearMap.range (oneDimBoundaryToSupportedModuleH U) ↔
      ((holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleHPresheafMap
        (le_top : realAxis ≤ ⊤) 1).app (op (complexNeighborhood U)) x = 0 := by
  rw [oneDimBoundaryToSupportedModuleH, Submodule.range_liftQ, nonRealToSupportedModuleH,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.mem_range]
  exact ((holomorphicStructureSheafModules 𝓘(ℂ) ℂ)
    |>.exact_supportedModuleHSectionsδ_supportedModuleHPresheafMap_app _ _ x).symm

/-- The map from one-dimensional hyperfunctions to local cohomology commutes with restriction to
a smaller real open set `U ≤ V`. -/
theorem supportedModuleHPresheaf_map_oneDimBoundaryToSupportedModuleH {U V : Opens ℝ}
    (h : U ≤ V) (q : OneDimBoundaryQuotient V) :
    ((holomorphicStructureSheafModules 𝓘(ℂ) ℂ).supportedModuleHPresheaf realAxis 1).map
        (homOfLE (complexNeighborhood_mono h)).op (oneDimBoundaryToSupportedModuleH V q) =
      oneDimBoundaryToSupportedModuleH U (oneDimBoundaryRestrict h q) := by
  induction q using Submodule.Quotient.induction_on with
  | H f =>
    -- the values of sections are compared explicitly, since the coercion of sections over
    -- `Opens ℂ` to functions is not unfolded by `simp`
    rw [oneDimBoundaryRestrict_mk, oneDimBoundaryToSupportedModuleH_mk V f _
        (nonRealSectionsEquiv_apply V f),
      CategoryTheory.Sheaf.supportedModuleHPresheaf_map_supportedModuleHSectionsδ,
      oneDimBoundaryToSupportedModuleH_mk U f _ fun x ↦
        (holomorphicStructureSheafModules.map_apply 𝓘(ℂ) ℂ _ _ x).trans
          (nonRealSectionsEquiv_apply V f _)]

end TauCeti.Hyperfunction
