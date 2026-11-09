/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.VectorBundle.ComplexSmulI
public import TauCeti.Topology.Algebra.Module.Complexification

/-!
# Complexification of topological real vector bundles

For any real vector bundle `E : B → Type*` with model fibre `F` whose complexified fibres
`ℂ ⊗[ℝ] E x` carry `TauCeti.IsComplexificationTopology (E x)` (supplied in scope
`TauCeti.Complexification` by `TauCeti.complexificationTopology`), we build the complexified vector
bundle `fun x ↦ ℂ ⊗[ℝ] E x` with Taylor-normed model fibre `TauCeti.Complexification F` (adapting
`Mathlib.Topology.VectorBundle.Hom` by Heather Macbeth and Floris van Doorn), prove
`TauCeti.continuousWithinAt_complexification_totalSpace_iff`, establish `inCoordinates` formulas and
Hom-bundle continuity for `realPartCLM`, `imaginaryPartCLM`, `oneTmulCLM`, `ITmulCLM`,
`tmulConjCLE`, `tmulConjCLM`, and `complexificationEquivProd`, and construct
`TauCeti.tmulConjHomeomorph` and `TauCeti.complexificationTotalSpaceHomeomorphProd`.

General scalar restriction (`VectorBundle.restrictScalars`, `VectorBundle.ofLinear`) and
multiplication by `Complex.I` on complex vector bundles (`VectorBundle.ofMapISmul`,
`TauCeti.smulIHomeomorph`, `TauCeti.continuous_smulIEquiv_bundle`) live in
`TauCeti.Topology.VectorBundle.RestrictScalars` and `TauCeti.Topology.VectorBundle.ComplexSmulI`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2 and §2.6.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Set Topology
open scoped TensorProduct

/-! ### Pretrivializations of the complexified vector bundle `fun x ↦ ℂ ⊗[ℝ] E x` -/

namespace Bundle.Pretrivialization

open TauCeti

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)]

/-- A real-linear trivialization `e` of `E` induces a pretrivialization of the complexified bundle
`fun x ↦ ℂ ⊗[ℝ] E x` with model fibre `TauCeti.Complexification F`. -/
def complexification (e : Trivialization F (π F E)) [e.IsLinear ℝ] :
    Pretrivialization (Complexification F) (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) where
  toFun p := ⟨p.1, ⟨e.linearMapAt ℝ p.1 (realPart (E p.1) p.2),
    e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2)⟩⟩
  invFun p := ⟨p.1, 1 ⊗ₜ[ℝ] e.symm p.1 p.2.re + Complex.I ⊗ₜ[ℝ] e.symm p.1 p.2.im⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := fun ⟨_, _⟩ hx ↦ by
    simp only [e.symm_linearMapAt hx, one_tmul_realPart_add_I_tmul_imaginaryPart]
  right_inv' := fun ⟨_, _⟩ ⟨hx, _⟩ ↦ by
    simp only [Prod.mk_right_inj]; ext <;> simp [e.coe_linearMapAt_of_mem hx, e.apply_mk_symm hx]
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {e : Trivialization F (π F E)} [e.IsLinear ℝ]

instance complexification_isLinear (e : Trivialization F (π F E)) [e.IsLinear ℝ] :
    (complexification e).IsLinear ℂ where
  linear x _ :=
    { map_add u v := by ext <;> simp [complexification, Pretrivialization.toFun']
      map_smul c u := by
        ext <;> simp [complexification, Pretrivialization.toFun', realPart_smul,
          imaginaryPart_smul, add_comm] }

theorem complexification_apply (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    complexification e p = (p.1, ⟨e.linearMapAt ℝ p.1 (realPart (E p.1) p.2),
      e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2)⟩) := (rfl)

@[simp] theorem baseSet_complexification : (complexification e).baseSet = e.baseSet := (rfl)

theorem complexification_symm_apply {b : B} (hb : b ∈ e.baseSet) (z : Complexification F) :
    (complexification e).symm b z = 1 ⊗ₜ[ℝ] e.symm b z.re + Complex.I ⊗ₜ[ℝ] e.symm b z.im := by
  rw [Pretrivialization.symm_apply _ hb]; rfl

end Bundle.Pretrivialization

/-! ### The complexified vector bundle -/

namespace TauCeti

open Pretrivialization

section VectorBundle

variable {B : Type*} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- The `VectorPrebundle` structure over `ℂ` on `fun x ↦ ℂ ⊗[ℝ] E x` with Taylor-normed model fibre
`TauCeti.Complexification F`. -/
def complexificationVectorPrebundle :
    VectorPrebundle ℂ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = Pretrivialization.complexification e}
  pretrivialization_linear' := by rintro _ ⟨e, he, rfl⟩; infer_instance
  pretrivializationAt x := Pretrivialization.complexification (trivializationAt F E x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F E x
  pretrivialization_mem_atlas x := ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    refine ⟨fun b ↦ (e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify,
      ((ContinuousLinearMap.complexifyₗᵢ F F).continuous.comp_continuousOn
        (continuousOn_coordChange ℝ e e')).congr fun _ _ ↦ by ext z <;> simp,
      fun b hb z ↦ ?_⟩
    ext <;> simp [complexification_apply, complexification_symm_apply hb.1,
      e'.coe_linearMapAt_of_mem hb.2, Trivialization.coordChangeL_apply e e' hb]
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, complexification_apply, isInducing_const_prod]
    let hb := mem_baseSet_trivializationAt F E b
    let L : E b ≃L[ℝ] F := (trivializationAt F E b).continuousLinearEquivAt ℝ b hb
    let Φ : ℂ ⊗[ℝ] E b ≃L[ℝ] Complexification F :=
      (complexificationEquivProd (E b)).trans
        ((L.prodCongr L).trans (Complexification.equivProd F).symm)
    suffices (fun u ↦ (⟨(trivializationAt F E b).linearMapAt ℝ b (realPart (E b) u),
        (trivializationAt F E b).linearMapAt ℝ b (imaginaryPart (E b) u)⟩ : Complexification F)) =
        ⇑Φ from this ▸ Φ.toHomeomorph.isInducing
    funext u; refine Complexification.ext ?_ ?_ <;>
      simp [Φ, L, (trivializationAt F E b).coe_linearMapAt_of_mem hb]

variable {F E} in
theorem mem_pretrivializationAtlas_complexificationVectorPrebundle
    {e' : Pretrivialization (Complexification F) (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x)} :
    e' ∈ (complexificationVectorPrebundle F E).pretrivializationAtlas ↔
      ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
        e' = Pretrivialization.complexification e := (Iff.rfl)

/-- Topology on the total space of the complexification `fun x ↦ ℂ ⊗[ℝ] E x`. -/
instance instTopologicalSpaceTotalSpaceComplexification :
    TopologicalSpace (TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :=
  (complexificationVectorPrebundle F E).totalSpaceTopology

/-- Fibre bundle structure on the complexification `fun x ↦ ℂ ⊗[ℝ] E x`. -/
instance instFiberBundleComplexification :
    FiberBundle (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x :=
  (complexificationVectorPrebundle F E).toFiberBundle

/-- Complex vector bundle structure on the complexification `fun x ↦ ℂ ⊗[ℝ] E x`. -/
instance instVectorBundleComplexComplexification :
    VectorBundle ℂ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x :=
  (complexificationVectorPrebundle F E).toVectorBundle

/-- Compatible real vector bundle structure on `fun x ↦ ℂ ⊗[ℝ] E x` sharing the same atlas. -/
instance instVectorBundleRealComplexification :
    VectorBundle ℝ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x :=
  VectorBundle.restrictScalars ℝ ℂ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x

end VectorBundle

end TauCeti

/-! ### Induced trivializations and coordinate formulas for `fun x ↦ ℂ ⊗[ℝ] E x` -/

namespace Bundle.Trivialization

open TauCeti

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]
  (e : Trivialization F (π F E)) [he : MemTrivializationAtlas e]

/-- The trivialization of `fun x ↦ ℂ ⊗[ℝ] E x` induced by an atlas trivialization `e` of `E`,
with base set `e.baseSet`. -/
def complexification :
    Trivialization (Complexification F) (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas
    (complexificationVectorPrebundle F E) ⟨e, he, rfl⟩

instance memTrivializationAtlas_complexification : MemTrivializationAtlas e.complexification :=
  ⟨⟨_, ⟨e, he, rfl⟩, rfl⟩⟩

@[simp] theorem baseSet_complexification : e.complexification.baseSet = e.baseSet := (rfl)

theorem complexification_apply (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    e.complexification p = (p.1, ⟨e.linearMapAt ℝ p.1 (realPart (E p.1) p.2),
      e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2)⟩) := (rfl)

@[simp] theorem complexification_apply_re
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    (e.complexification p).2.re = e.linearMapAt ℝ p.1 (realPart (E p.1) p.2) := (rfl)

@[simp] theorem complexification_apply_im
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    (e.complexification p).2.im = e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2) := (rfl)

theorem complexification_symm_apply {b : B} (hb : b ∈ e.baseSet) (z : Complexification F) :
    e.complexification.symm b z = 1 ⊗ₜ[ℝ] e.symm b z.re + Complex.I ⊗ₜ[ℝ] e.symm b z.im :=
  Pretrivialization.complexification_symm_apply hb z

@[simp] theorem coordChangeL_complexification (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.complexification.coordChangeL ℂ e'.complexification b :
      Complexification F →L[ℂ] Complexification F) =
      (e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify := by
  ext z <;> simp [Trivialization.coordChangeL_apply e.complexification e'.complexification hb,
    complexification_symm_apply e hb.1, e'.coe_linearMapAt_of_mem hb.2,
    Trivialization.coordChangeL_apply e e' hb]

@[simp] theorem coordChangeL_real_complexification (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.complexification.coordChangeL ℝ e'.complexification b :
      Complexification F →L[ℝ] Complexification F) =
      ((e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify).restrictScalars ℝ := by
  rw [← Trivialization.restrictScalars_coordChangeL ℝ ℂ e.complexification e'.complexification hb,
    coordChangeL_complexification e e' hb]

end Bundle.Trivialization

namespace TauCeti

section TrivializationAtAndMorphisms

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- A trivialization of `fun x ↦ ℂ ⊗[ℝ] E x` belongs to the trivialization atlas if and only if
it is `e.complexification` for some atlas trivialization `e` of `E`. -/
theorem mem_trivializationAtlas_complexification_iff
    {e' : Trivialization (Complexification F) (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x)} :
    MemTrivializationAtlas e' ↔
      ∃ (e : Trivialization F (π F E)) (he : MemTrivializationAtlas e),
        e' = e.complexification (he := he) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨_, ⟨e, he, rfl⟩, rfl⟩⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact Trivialization.memTrivializationAtlas_complexification e (he := he)

/-- The preferred trivialization of `fun x ↦ ℂ ⊗[ℝ] E x` at `x₀` is
`(trivializationAt F E x₀).complexification`. -/
theorem trivializationAt_complexification (x₀ : B) :
    trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀ =
      (trivializationAt F E x₀).complexification := (rfl)
@[simp] theorem baseSet_trivializationAt_complexification (x₀ : B) :
    (trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀).baseSet =
      (trivializationAt F E x₀).baseSet := (rfl)
@[simp, mfld_simps] theorem source_trivializationAt_complexification (x₀ : B) :
    (trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀).source =
      π (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ⁻¹' (trivializationAt F E x₀).baseSet := (rfl)
@[simp, mfld_simps] theorem target_trivializationAt_complexification (x₀ : B) :
    (trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀).target =
      (trivializationAt F E x₀).baseSet ×ˢ univ := (rfl)

/-- Fibrewise inverse `symmL` of the preferred trivialization of `fun y ↦ ℂ ⊗[ℝ] E y` at `a`. -/
theorem trivializationAt_complexification_symmL (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 (Complexification F)] [∀ y, Module 𝕜 (ℂ ⊗[ℝ] E y)]
    [VectorBundle 𝕜 (Complexification F) fun y ↦ ℂ ⊗[ℝ] E y] {a x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) (z : Complexification F) :
    (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).symmL 𝕜 x z =
      1 ⊗ₜ[ℝ] (trivializationAt F E a).symm x z.re +
        Complex.I ⊗ₜ[ℝ] (trivializationAt F E a).symm x z.im := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  rw [(trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).symmL_apply hx',
    trivializationAt_complexification, (trivializationAt F E a).complexification_symm_apply hx]

/-- Fibrewise `continuousLinearMapAt` of the preferred trivialization of `fun y ↦ ℂ ⊗[ℝ] E y` at
`a`. -/
theorem trivializationAt_complexification_continuousLinearMapAt (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 (Complexification F)]
    [∀ y, Module 𝕜 (ℂ ⊗[ℝ] E y)] [VectorBundle 𝕜 (Complexification F) fun y ↦ ℂ ⊗[ℝ] E y]
    {a x : B} (hx : x ∈ (trivializationAt F E a).baseSet) (u : ℂ ⊗[ℝ] E x) :
    (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).continuousLinearMapAt 𝕜 x u =
      ⟨(trivializationAt F E a ⟨x, realPart (E x) u⟩).2,
       (trivializationAt F E a ⟨x, imaginaryPart (E x) u⟩).2⟩ := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx', trivializationAt_complexification]
  ext <;> simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx]

/-! #### Continuity characterization and total-space homeomorphisms -/

/-- A map into the total space of `fun x ↦ ℂ ⊗[ℝ] E x` is continuous within `s` at `x₀` if and
only if its fibrewise real and imaginary parts into `TotalSpace F E` are continuous within `s` at
`x₀`. -/
theorem continuousWithinAt_complexification_totalSpace_iff {X : Type*} [TopologicalSpace X]
    {f : X → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {s : Set X} {x₀ : X} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s x₀ ∧
      ContinuousWithinAt
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s x₀ := by
  simp only [FiberBundle.continuousWithinAt_totalSpace,
    (Complexification.equivProd F).toHomeomorph.isInducing.continuousWithinAt_iff,
    continuousWithinAt_prod_iff, Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    Complexification.equivProd_apply, trivializationAt_complexification,
    Trivialization.complexification_apply_re, Trivialization.complexification_apply_im,
    ← and_and_left]
  refine and_congr_right fun hb ↦ ?_
  let e₀ := trivializationAt F E (f x₀).proj
  have hx₀ : (f x₀).proj ∈ e₀.baseSet := mem_baseSet_trivializationAt F E (f x₀).proj
  have he : ∀ᶠ y in 𝓝[s] x₀, (f y).proj ∈ e₀.baseSet :=
    hb.preimage_mem_nhdsWithin (e₀.open_baseSet.mem_nhds hx₀)
  have hcongr (w : ∀ y, E (f y).proj) :
      ContinuousWithinAt (fun y ↦ e₀.linearMapAt ℝ (f y).proj (w y)) s x₀ ↔
      ContinuousWithinAt (fun y ↦ (e₀ ⟨(f y).proj, w y⟩).2) s x₀ :=
    ⟨fun h ↦ h.congr_of_eventuallyEq
      (he.mono fun y hy ↦ (congrFun (e₀.coe_linearMapAt_of_mem hy) (w y)).symm)
      (congrFun (e₀.coe_linearMapAt_of_mem hx₀) (w x₀)).symm,
     fun h ↦ h.congr_of_eventuallyEq
      (he.mono fun y hy ↦ congrFun (e₀.coe_linearMapAt_of_mem hy) (w y))
      (congrFun (e₀.coe_linearMapAt_of_mem hx₀) (w x₀))⟩
  exact and_congr (hcongr _) (hcongr _)

/-- Global version of `continuousWithinAt_complexification_totalSpace_iff`. -/
theorem continuous_complexification_totalSpace_iff {X : Type*} [TopologicalSpace X]
    {f : X → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} :
    Continuous f ↔
      Continuous (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) ∧
      Continuous
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) := by
  simp_rw [continuous_iff_continuousAt, ← continuousWithinAt_univ,
    continuousWithinAt_complexification_totalSpace_iff, forall_and]

/-- A section `s : ∀ x, ℂ ⊗[ℝ] E x` is continuous if and only if its real and imaginary parts are
continuous sections of `E`. -/
theorem continuous_complexification_section_iff {s : ∀ x, ℂ ⊗[ℝ] E x} :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F) x (s x)) ↔
      Continuous (fun x ↦ TotalSpace.mk' F x (realPart (E x) (s x))) ∧
      Continuous (fun x ↦ TotalSpace.mk' F x (imaginaryPart (E x) (s x))) :=
  continuous_complexification_totalSpace_iff

variable (F E) in
/-- Fibrewise conjugation `z ⊗ₜ v ↦ conj z ⊗ₜ v` as an involutive homeomorphism of the total space
of `fun x ↦ ℂ ⊗[ℝ] E x`, with no finite-rank assumption. -/
def tmulConjHomeomorph :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₜ
      TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) :=
  have hcont : Continuous (fun p : TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ↦
      (⟨p.proj, tmulConj (E p.proj) p.2⟩ :
        TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x)) := by
    obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F) (E := E)).mp
      continuous_id
    refine (continuous_complexification_totalSpace_iff (F := F) (E := E)).mpr
      ⟨by simpa using hre, ?_⟩
    simpa [neg_one_smul] using (continuous_const (y := (-1 : ℝ))).smul_totalSpace him
  { toFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
    invFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
    left_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
    right_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
    continuous_toFun := hcont, continuous_invFun := hcont }

variable (F E) in
/-- The real/imaginary-part homeomorphism between the total space of `fun x ↦ ℂ ⊗[ℝ] E x` and the
total space of the direct-sum bundle `E ×ᵇ E`, valid without any finite-rank assumption on `F`. -/
def complexificationTotalSpaceHomeomorphProd :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₜ TotalSpace (F × F) (E ×ᵇ E) where
  toFun p := ⟨p.proj, complexificationEquivProd (E p.proj) p.2⟩
  invFun p := ⟨p.proj, (complexificationEquivProd (E p.proj)).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    rw [(FiberBundle.Prod.isInducing_diag (F₁ := F) (E₁ := E) (F₂ := F) (E₂ := E)).continuous_iff,
      Function.comp_def, continuous_prodMk]
    obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F) (E := E)).mp
      continuous_id
    exact ⟨hre.congr fun _ ↦ by simp, him.congr fun _ ↦ by simp⟩
  continuous_invFun := by
    have h := (FiberBundle.Prod.isInducing_diag (F₁ := F) (E₁ := E) (F₂ := F) (E₂ := E)).continuous
    exact (continuous_complexification_totalSpace_iff (F := F) (E := E)).mpr
      ⟨(continuous_fst.comp h).congr fun _ ↦ by simp,
        (continuous_snd.comp h).congr fun _ ↦ by simp⟩

@[simp] theorem tmulConjHomeomorph_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    tmulConjHomeomorph F E p = ⟨p.proj, tmulConj (E p.proj) p.2⟩ := (rfl)
@[simp] theorem tmulConjHomeomorph_symm :
    (tmulConjHomeomorph F E).symm = tmulConjHomeomorph F E := (rfl)
@[simp] theorem complexificationTotalSpaceHomeomorphProd_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    complexificationTotalSpaceHomeomorphProd F E p =
      ⟨p.proj, (realPart (E p.proj) p.2, imaginaryPart (E p.proj) p.2)⟩ :=
  congrArg (TotalSpace.mk p.proj) (complexificationEquivProd_apply p.2)
@[simp] theorem complexificationTotalSpaceHomeomorphProd_symm_apply
    (p : TotalSpace (F × F) (E ×ᵇ E)) :
    (complexificationTotalSpaceHomeomorphProd F E).symm p =
      ⟨p.proj, 1 ⊗ₜ[ℝ] p.2.1 + Complex.I ⊗ₜ[ℝ] p.2.2⟩ :=
  congrArg (TotalSpace.mk p.proj) (complexificationEquivProd_symm_apply p.2)
theorem proj_complexificationTotalSpaceHomeomorphProd
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    (complexificationTotalSpaceHomeomorphProd F E p).proj = p.proj := (rfl)

/-! #### Preferred-frame coordinate expressions and continuous Hom-bundle sections -/

/-- Read in preferred frames, `realPartCLM (E x)` is `Complexification.reCLM F`. -/
@[simp] theorem inCoordinates_realPartCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) F E a x a x
      (realPartCLM (E x)) = Complexification.reCLM F := by
  ext z; simp [ContinuousLinearMap.inCoordinates, trivializationAt_complexification_symmL ℝ hx,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx,
    (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `imaginaryPartCLM (E x)` is `Complexification.imCLM F`. -/
@[simp] theorem inCoordinates_imaginaryPartCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) F E a x a x
      (imaginaryPartCLM (E x)) = Complexification.imCLM F := by
  ext z; simp [ContinuousLinearMap.inCoordinates, trivializationAt_complexification_symmL ℝ hx,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx,
    (trivializationAt F E a).apply_mk_symm hx]

/-- In preferred frames, `oneTmulCLM (E x)` is `(Complexification.ofRealLI F).toCLM`. -/
@[simp] theorem inCoordinates_oneTmulCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates F E (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (oneTmulCLM (E x)) = (Complexification.ofRealLI F).toContinuousLinearMap := by
  ext v <;> simp [ContinuousLinearMap.inCoordinates, (trivializationAt F E a).symmL_apply hx,
    trivializationAt_complexification_continuousLinearMapAt ℝ hx,
    ((trivializationAt F E a).linear ℝ hx).map_zero, (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `ITmulCLM (E x)` is `v ↦ Complex.I • Complexification.ofReal v`. -/
@[simp] theorem inCoordinates_ITmulCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates F E (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (ITmulCLM (E x)) =
      (Complex.smulIEquiv (Complexification F)).toContinuousLinearMap.comp
        (Complexification.ofRealLI F).toContinuousLinearMap := by
  ext v <;> simp [ContinuousLinearMap.inCoordinates, (trivializationAt F E a).symmL_apply hx,
    trivializationAt_complexification_continuousLinearMapAt ℝ hx,
    ((trivializationAt F E a).linear ℝ hx).map_zero, (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `tmulConjCLE (E x)` is `Complexification.conjCLE F`. -/
@[simp] theorem inCoordinates_tmulConjCLE [∀ x, ContinuousNeg (E x)] (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (tmulConjCLE (E x) : ℂ ⊗[ℝ] E x →SL[starRingEnd ℂ] ℂ ⊗[ℝ] E x) =
      (Complexification.conjCLE F :
        Complexification F →SL[starRingEnd ℂ] Complexification F) := by
  ext z <;> simp [ContinuousLinearMap.inCoordinates, trivializationAt_complexification_symmL ℂ hx,
    trivializationAt_complexification_continuousLinearMapAt ℂ hx,
    ((trivializationAt F E a).linear ℝ hx).map_neg, (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `tmulConjCLM (E x)` (viewed over `ℝ`) is constant. -/
@[simp] theorem inCoordinates_tmulConjCLM [∀ x, IsTopologicalAddGroup (E x)] (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (tmulConjCLM (E x)) =
      (Complexification.ofRealLI F).toContinuousLinearMap.comp (Complexification.reCLM F) -
        ((Complex.smulIEquiv (Complexification F)).toContinuousLinearMap.comp
          (Complexification.ofRealLI F).toContinuousLinearMap).comp
            (Complexification.imCLM F) := by
  ext z <;> simp [ContinuousLinearMap.inCoordinates, trivializationAt_complexification_symmL ℝ hx,
    trivializationAt_complexification_continuousLinearMapAt ℝ hx,
    ((trivializationAt F E a).linear ℝ hx).map_neg, (trivializationAt F E a).apply_mk_symm hx]

/-- In preferred frames, `complexificationEquivProd (E x)` is `Complexification.equivProd F`. -/
@[simp] theorem inCoordinates_complexificationEquivProd (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) (F × F) (E ×ᵇ E) a x a x
      (complexificationEquivProd (E x) : ℂ ⊗[ℝ] E x →L[ℝ] E x × E x) =
      (Complexification.equivProd F : Complexification F →L[ℝ] F × F) := by
  have hxp : x ∈ (trivializationAt (F × F) (E ×ᵇ E) a).baseSet := ⟨hx, hx⟩
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    trivializationAt_complexification_symmL ℝ hx, ContinuousLinearEquiv.coe_coe,
    Complexification.equivProd_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hxp,
    FiberBundle.trivializationAt_prod F E F E a,
    complexificationEquivProd_apply, Trivialization.prod_apply' ℝ hx hx]
  ext <;> simp [(trivializationAt F E a).apply_mk_symm hx]

/-- In preferred frames, `(complexificationEquivProd (E x)).symm` is
`(Complexification.equivProd F).symm`. -/
@[simp] theorem inCoordinates_complexificationEquivProd_symm (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (F × F) (E ×ᵇ E) (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      ((complexificationEquivProd (E x)).symm : E x × E x →L[ℝ] ℂ ⊗[ℝ] E x) =
      ((Complexification.equivProd F).symm : F × F →L[ℝ] Complexification F) := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  have hxp : x ∈ (trivializationAt (F × F) (E ×ᵇ E) a).baseSet := ⟨hx, hx⟩
  refine ContinuousLinearMap.ext fun ⟨v, w⟩ ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    (trivializationAt (F × F) (E ×ᵇ E) a).symmL_apply hxp, ContinuousLinearEquiv.coe_coe]
  rw [FiberBundle.trivializationAt_prod F E F E a,
    (trivializationAt F E a).prod_symm_apply' (trivializationAt F E a) ⟨hx, hx⟩ (v, w),
    complexificationEquivProd_symm_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx',
    trivializationAt_complexification, Complexification.equivProd_symm_apply]
  ext <;> simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx,
    (trivializationAt F E a).apply_mk_symm hx]

variable [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]

/-- Fibrewise real part is a continuous section of `fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y`. -/
theorem continuous_realPartCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (realPartCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_realPartCLM a hx

/-- Fibrewise imaginary part is a continuous section of `fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y`. -/
theorem continuous_imaginaryPartCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (imaginaryPartCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_imaginaryPartCLM a hx

/-- Real inclusion `v ↦ 1 ⊗ₜ v` is a continuous section of `fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y`. -/
theorem continuous_oneTmulCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
      (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (oneTmulCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_oneTmulCLM a hx

/-- Imaginary inclusion `v ↦ I ⊗ₜ v` is a continuous section of `fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y`. -/
theorem continuous_ITmulCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
      (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (ITmulCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_ITmulCLM a hx

/-- Fibrewise conjugation is a continuous section of the conjugate-linear endomorphism bundle. -/
theorem continuous_tmulConjCLE_bundle :
    Continuous (fun x ↦ TotalSpace.mk'
      (Complexification F →SL[starRingEnd ℂ] Complexification F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →SL[starRingEnd ℂ] ℂ ⊗[ℝ] E y) x
      (tmulConjCLE (E x) : ℂ ⊗[ℝ] E x →SL[starRingEnd ℂ] ℂ ⊗[ℝ] E x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_tmulConjCLE a hx

/-- Fibrewise conjugation is a continuous section of the real endomorphism bundle. -/
theorem continuous_tmulConjCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] Complexification F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] ℂ ⊗[ℝ] E y) x (tmulConjCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_tmulConjCLM a hx

/-- `(realPart, imaginaryPart)` is a continuous section of `fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y`. -/
theorem continuous_complexificationEquivProd_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F × F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y) x
      (complexificationEquivProd (E x) : ℂ ⊗[ℝ] E x →L[ℝ] (E ×ᵇ E) x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    fun a _ hx _ ↦ inCoordinates_complexificationEquivProd a hx

/-- `(v, w) ↦ 1 ⊗ₜ v + I ⊗ₜ w` is a continuous section of `fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y`. -/
theorem continuous_complexificationEquivProd_symm_bundle :
    Continuous (fun x ↦ TotalSpace.mk' ((F × F) →L[ℝ] Complexification F)
      (E := fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y) x
      ((complexificationEquivProd (E x)).symm : (E ×ᵇ E) x →L[ℝ] ℂ ⊗[ℝ] E x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    fun a _ _ hx ↦ inCoordinates_complexificationEquivProd_symm a hx

end TrivializationAtAndMorphisms

end TauCeti

end
