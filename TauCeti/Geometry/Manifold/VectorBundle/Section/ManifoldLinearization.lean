/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# Linearization of a bundle section on a manifold

At a zero of a differentiable bundle section on a manifold, differentiating its fiber
coordinates gives a continuous linear map from the tangent space of the source to the fiber.
Transporting that derivative back from a preferred trivialization defines the intrinsic
linearization `TauCeti.manifoldSectionLinearization`.

The linearization can be calculated in any bundle trivialization. Consequently surjectivity,
Fredholmness, and the Fredholm index can all be checked in arbitrary fiber coordinates. When the
source is a normed space with its canonical manifold structure, this definition agrees with
`TauCeti.sectionLinearization`.

This is the chart-independent differential needed to formulate regular Fredholm sections over
Banach manifolds. It follows the convention of McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3.
-/

public section

open Bundle Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 EM HM M B F EB HB : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ a, TopologicalSpace (E a)] [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
  {b : M → B} {s : ∀ y, E (b y)} {x : M}

variable {e e' : Trivialization F (π F E)}
  [MemTrivializationAtlas e] [MemTrivializationAtlas e']

/-- The intrinsic linearization of a bundle section on a manifold at a point. Differentiate
the section's fiber coordinates in the preferred trivialization and transport the result back to
the fiber. At a zero this is independent of that choice of trivialization. -/
noncomputable def manifoldSectionLinearization (b : M → B) (s : ∀ y, E (b y)) (x : M) :
    TangentSpace IM x →L[𝕜] E (b x) :=
  ((trivializationAt F E (b x)).symmL 𝕜 (b x)).comp
    (mvfderiv IM (fun y ↦ (trivializationAt F E (b x) ⟨b y, s y⟩).2) x)

/-- The defining expression for the manifold-source section linearization. -/
theorem manifoldSectionLinearization_def :
    manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s x =
      ((trivializationAt F E (b x)).symmL 𝕜 (b x)).comp
        (mvfderiv IM (fun y ↦ (trivializationAt F E (b x) ⟨b y, s y⟩).2) x) :=
  (rfl)

/-- The zero section along a map continuous at the point has zero manifold-source
linearization. -/
@[simp]
theorem manifoldSectionLinearization_zero (hb : ContinuousAt b x) :
    manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b
      (fun y ↦ (0 : E (b y))) x = 0 := by
  let e₀ := trivializationAt F E (b x)
  have hcoord : (fun y ↦ (e₀ ⟨b y, (0 : E (b y))⟩).2) =ᶠ[𝓝 x]
      fun _ ↦ (0 : F) := by
    filter_upwards [hb.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (b x)))] with y hy
    exact congrArg Prod.snd (e₀.zeroSection 𝕜 hy)
  rw [manifoldSectionLinearization_def, hcoord.mvfderiv_eq, mvfderiv_const]
  simp

/-- At a zero, the manifold-source linearization can be computed in any bundle trivialization
whose fiber-coordinate expression is differentiable there. -/
theorem manifoldSectionLinearization_eq_symmL_comp
    (hb : MDifferentiableAt IM IB b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x)
    (hzero : s x = 0) :
    manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s x =
      (e.symmL 𝕜 (b x)).comp (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  let e₀ := trivializationAt F E (b x)
  let c : M → F →L[𝕜] F := fun y ↦ e.coordChangeL 𝕜 e₀ (b y)
  let u : M → F := fun y ↦ (e ⟨b y, s y⟩).2
  have he₀ : b x ∈ e₀.baseSet := mem_baseSet_trivializationAt F E (b x)
  have hu0 : u x = 0 := by
    dsimp only [u]
    rw [hzero]
    exact congrArg Prod.snd (e.zeroSection 𝕜 he)
  have hc : MDifferentiableAt IM 𝓘(𝕜, F →L[𝕜] F) c x := hb.coordChangeL he he₀
  have hcu : mvfderiv IM (fun y ↦ c y (u y)) x =
      (c x).comp (mvfderiv IM u x) :=
    mvfderiv_clm_apply_of_eq_zero hc hs hu0
  have hcoord : (fun y ↦ c y (u y)) =ᶠ[𝓝 x]
      fun y ↦ (e₀ ⟨b y, s y⟩).2 := by
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      ((e.open_baseSet.inter e₀.open_baseSet).mem_nhds ⟨he, he₀⟩)] with y hy
    dsimp only [c, u]
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply e e₀ hy, e.symm_apply_apply_mk hy.1]
  rw [manifoldSectionLinearization_def, ← hcoord.mvfderiv_eq, hcu]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, c, u, e₀]
  rw [Trivialization.coordChangeL_apply e (trivializationAt F E (b x))
      ⟨he, mem_baseSet_trivializationAt F E (b x)⟩,
    Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F E (b x)),
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F E (b x)),
    Trivialization.symmL_apply _ he]

/-- Reading the intrinsic manifold-source linearization in fiber coordinates recovers the
manifold derivative of the section's coordinate expression. -/
theorem continuousLinearMapAt_comp_manifoldSectionLinearization
    (hb : MDifferentiableAt IM IB b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x)
    (hzero : s x = 0) :
    (e.continuousLinearMapAt 𝕜 (b x)).comp
        (manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s x) =
      mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x := by
  rw [manifoldSectionLinearization_eq_symmL_comp hb he hs hzero]
  ext v
  simp only [ContinuousLinearMap.comp_apply, e.continuousLinearMapAt_symmL he]

/-- A zero is regular for the intrinsic manifold-source linearization exactly when its derivative
in arbitrary fiber coordinates is surjective. -/
theorem surjective_manifoldSectionLinearization_iff
    (hb : MDifferentiableAt IM IB b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x)
    (hzero : s x = 0) :
    Function.Surjective
        (manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s x) ↔
      Function.Surjective (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [manifoldSectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he]
  exact Function.Surjective.of_comp_iff'
    (e.continuousLinearEquivAt 𝕜 (b x) he).symm.bijective _

/-- At a zero, the intrinsic manifold-source linearization and any differentiable fiber-coordinate
expression have the same Fredholm index. -/
theorem index_manifoldSectionLinearization
    (hb : MDifferentiableAt IM IB b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x)
    (hzero : s x = 0) :
    LinearMap.index
        (manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s x).toLinearMap =
      LinearMap.index (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x).toLinearMap := by
  rw [manifoldSectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.index_equiv_comp]

/-- Fredholmness of the intrinsic manifold-source linearization at a zero can be checked in any
differentiable fiber-coordinate expression. -/
theorem isFredholm_manifoldSectionLinearization_iff [CompleteSpace 𝕜]
    (hb : MDifferentiableAt IM IB b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x)
    (hzero : s x = 0) :
    ContinuousLinearMap.IsFredholm
        (manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s x) ↔
      ContinuousLinearMap.IsFredholm
        (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [manifoldSectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he]
  let A := e.continuousLinearEquivAt 𝕜 (b x) he
  let : NormedAddCommGroup (E (b x)) :=
    { (NormedAddCommGroup.induced (E (b x)) F A.toLinearEquiv A.injective).replaceTopology
        A.toHomeomorph.isInducing.eq_induced with
      toAddCommGroup := inferInstance
      norm := fun v ↦ ‖A v‖
      dist_eq := (NormedAddCommGroup.induced (E (b x)) F A.toLinearEquiv A.injective).dist_eq }
  let : NormedSpace 𝕜 (E (b x)) :=
    { norm_smul_le c v := by simpa only [← map_smul A c v] using! norm_smul_le c (A v) }
  exact ContinuousLinearMap.isFredholm_equiv_comp

/-- In a trivial bundle, the intrinsic manifold-source linearization is the vector-valued
manifold derivative of the fiber component. -/
@[simp]
theorem manifoldSectionLinearization_trivial (b : M → B) (f : M → F) (x : M) :
    manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM)
      (E := Bundle.Trivial B F) b f x = mvfderiv IM f x := by
  rw [manifoldSectionLinearization_def]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply,
    Bundle.Trivial.symmL_trivialization, ContinuousLinearMap.id_comp]

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  [TopologicalSpace HN] {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace N] [ChartedSpace HN N]

/-- Pulling a section back along a differentiable map precomposes its intrinsic linearization
with the differential of that map. This is the chain rule used to pass between a manifold source
and a source chart. -/
theorem manifoldSectionLinearization_comp {g : N → M} {y : N}
    (hg : MDifferentiableAt IN IM g y)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F)
      (fun z ↦ (trivializationAt F E (b (g y)) ⟨b z, s z⟩).2) (g y)) :
    manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IN)
        (b ∘ g) (fun z ↦ s (g z)) y =
      (manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := IM) b s (g y)).comp
        (mfderiv IN IM g y) := by
  rw [manifoldSectionLinearization_def, manifoldSectionLinearization_def]
  -- The dependent pullback does not syntactically expose the coordinate expression as a
  -- composition, so make that composition explicit before applying the manifold chain rule.
  change ((trivializationAt F E (b (g y))).symmL 𝕜 (b (g y))).comp
      (mvfderiv IN ((fun z ↦
        (trivializationAt F E (b (g y)) ⟨b z, s z⟩).2) ∘ g) y) = _
  rw [mvfderiv_comp y hs hg, ContinuousLinearMap.comp_assoc]

/-- On a normed-space source with its canonical manifold structure, the manifold-source
linearization agrees with the Banach-space `sectionLinearization`. -/
@[simp]
theorem manifoldSectionLinearization_self (b : EM → B) (s : ∀ y, E (b y)) (x : EM) :
    manifoldSectionLinearization (𝕜 := 𝕜) (F := F) (IM := 𝓘(𝕜, EM)) b s x =
      sectionLinearization (𝕜 := 𝕜) (F := F) b s x := by
  rw [manifoldSectionLinearization_def, sectionLinearization_def, mvfderiv_eq_fderiv]
  rfl

end TauCeti
