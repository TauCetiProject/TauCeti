/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# The smooth complex bundle of `(0,1)`-forms

For an arbitrary smooth almost complex structure, the existing `(0,1)`-projection on real bundle
homomorphisms has a smooth complex range bundle. Its fibres are exactly the native
`SmoothAlmostComplexStructure.IsZeroOneForm` predicate. No metric or integrability is required.

The range has complex rank half the real base dimension times the complex rank of the coefficient
bundle. The construction includes zero dimensions and the empty base.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix C.1.
-/

public noncomputable section

open Bundle Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)]

/-- The existing `(0,1)`-projection, bundled as a complex-linear map on the real Hom fibre. -/
def zeroOnePartLinearMap (x : M) :
    (TangentSpace I x →L[ℝ] V x) →ₗ[ℂ] TangentSpace I x →L[ℝ] V x where
  toFun := j.zeroOnePart
  map_add' := j.zeroOnePart_add
  map_smul' := fun c η ↦ j.zeroOnePart_complex_smul c η

@[simp]
theorem zeroOnePartLinearMap_apply (x : M) (η : TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePartLinearMap x η = j.zeroOnePart η := by
  simp only [zeroOnePartLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- The complex range submodule of the native `(0,1)`-projection. -/
def zeroOneFormSubmodule (x : M) : Submodule ℂ (TangentSpace I x →L[ℝ] V x) :=
  LinearMap.range (j.zeroOnePartLinearMap x)

@[simp]
theorem mem_zeroOneFormSubmodule_iff (x : M) (η : TangentSpace I x →L[ℝ] V x) :
    η ∈ j.zeroOneFormSubmodule x ↔ j.IsZeroOneForm η := by
  rw [zeroOneFormSubmodule, LinearMap.mem_range]
  constructor
  · rintro ⟨η, rfl⟩
    exact j.isZeroOneForm_zeroOnePart η
  · intro hη
    exact ⟨η, hη.zeroOnePart_eq⟩

/-- The `(0,1)`-projection is a `C^n` map on the actual total space of the real Hom bundle.
The atlas need only be continuous; all varying coefficients come from the smooth structure `j`. -/
theorem contMDiff_totalSpace_zeroOnePart {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] F)) (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun p : TotalSpace (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) ↦
        TotalSpace.mk' (E →L[ℝ] F)
          (E := fun x ↦ TangentSpace I x →L[ℝ] V x) p.proj (j.zeroOnePart p.snd)) := by
  have hid : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] F)) (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun p : TotalSpace (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) ↦
        TotalSpace.mk' (E →L[ℝ] F)
          (E := fun x ↦ TangentSpace I x →L[ℝ] V x) p.proj p.snd) := contMDiff_id
  have hb : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] F)) I n
      (π (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x)) := Bundle.contMDiff_proj _
  have hJ := (j.toEndomorphism.contMDiff.of_le hn).comp hb
  have hc := hid.clm_bundle_comp hJ
  have hI := (contMDiff_const (c := Complex.I)).smul_totalSpace hc
  refine ((contMDiff_const (c := (2⁻¹ : ℝ))).smul_totalSpace
    (hid.add_sectionAlong hI)).congr fun p ↦ ?_
  apply congrArg (TotalSpace.mk p.proj)
  ext v
  exact j.zeroOnePart_apply p.snd v

section Rank

variable [FiniteDimensional ℝ E]

/-- In coordinates intertwining multiplication by `i` with `-j`, `(0,1)`-forms are complex
linear maps. Finite real tangent dimension makes the inverse of an arbitrary algebraic
coordinate map continuous; no tangent norm is changed. -/
def zeroOneFormLinearEquiv {G : Type*} [AddCommGroup G] [Module ℝ G] [Module ℂ G]
    [IsScalarTower ℝ ℂ G] (x : M) (φ : G ≃ₗ[ℝ] TangentSpace I x)
    (hφ : ∀ z, φ (Complex.I • z) = -(j x (φ z))) :
    j.zeroOneFormSubmodule (V := V) x ≃ₗ[ℂ] (G →ₗ[ℂ] V x) := by
  have hinv (v : TangentSpace I x) : φ.symm (j x v) = -(Complex.I • φ.symm v) := by
    apply φ.injective
    rw [φ.apply_symm_apply, map_neg, hφ, φ.apply_symm_apply]
    exact (_root_.neg_neg _).symm
  let f : j.zeroOneFormSubmodule (V := V) x →ₗ[ℂ] (G →ₗ[ℂ] V x) :=
    { toFun := fun η ↦ (η.val.toLinearMap.comp φ.toLinearMap).complexOfMapISmul fun z ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
        rw [hφ, map_neg,
          (isZeroOneForm_iff.mp ((j.mem_zeroOneFormSubmodule_iff x η.val).mp η.property)) (φ z),
          _root_.neg_neg]
      map_add' := fun η η' ↦ by ext z; simp
      map_smul' := fun c η ↦ by ext z; simp }
  let g (L : G →ₗ[ℂ] V x) : j.zeroOneFormSubmodule (V := V) x :=
    ⟨LinearMap.toContinuousLinearMap ((L.restrictScalars ℝ).comp φ.symm.toLinearMap),
      (j.mem_zeroOneFormSubmodule_iff x _).mpr (isZeroOneForm_iff.mpr fun v ↦ by
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
          LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
        rw [hinv, map_neg, map_smul])⟩
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro η
    apply Subtype.ext
    ext v
    simp [f, g]
  · intro L
    ext z
    simp [f, g]

/-- The coordinate comparison evaluates a form on the chosen tangent coordinates. -/
@[simp] theorem zeroOneFormLinearEquiv_apply {G : Type*} [AddCommGroup G] [Module ℝ G]
    [Module ℂ G] [IsScalarTower ℝ ℂ G] (x : M) (φ : G ≃ₗ[ℝ] TangentSpace I x)
    (hφ : ∀ z, φ (Complex.I • z) = -(j x (φ z)))
    (η : j.zeroOneFormSubmodule (V := V) x) (z : G) :
    j.zeroOneFormLinearEquiv x φ hφ η z = η.val (φ z) := by
  simp [zeroOneFormLinearEquiv]

/-- The inverse coordinate comparison evaluates a complex-linear map in inverse coordinates. -/
@[simp] theorem zeroOneFormLinearEquiv_symm_apply {G : Type*} [AddCommGroup G] [Module ℝ G]
    [Module ℂ G] [IsScalarTower ℝ ℂ G] (x : M) (φ : G ≃ₗ[ℝ] TangentSpace I x)
    (hφ : ∀ z, φ (Complex.I • z) = -(j x (φ z))) (L : G →ₗ[ℂ] V x)
    (v : TangentSpace I x) :
    ((j.zeroOneFormLinearEquiv x φ hφ).symm L).val v = L (φ.symm v) := by
  simp [zeroOneFormLinearEquiv]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] in
/-- The complex rank of the actual `(0,1)`-range is half the real base dimension times the
complex coefficient rank. This includes zero-dimensional models and zero-rank coefficients. -/
theorem finrank_zeroOneFormSubmodule [FiniteDimensional ℂ F] (x : M) :
    finrank ℂ (j.zeroOneFormSubmodule (V := V) x) = finrank ℝ E / 2 * finrank ℂ F := by
  let K := (-j).almostComplexStructureAt x
  have hG : finrank ℝ (TangentSpace I x) =
      2 * finrank ℂ (Fin (finrank ℝ E / 2) → ℂ) := by
    simpa only [Module.finrank_fin_fun, VectorBundle.finrank_eq ℝ E (TangentSpace I) x] using
      (Nat.two_mul_div_two_of_even K.even_finrank_real).symm
  obtain ⟨φ, hφ⟩ := K.exists_linearEquiv_I_smul hG
  have hφ' (z) : φ (Complex.I • z) = -(j x (φ z)) :=
    (hφ z).trans (((-j).almostComplexStructureAt_apply x (φ z)).trans (j.neg_apply x (φ z)))
  have : FiniteDimensional ℂ (V x) := VectorBundle.finiteDimensional ℂ F V x
  rw [(j.zeroOneFormLinearEquiv x φ hφ').finrank_eq, Module.finrank_linearMap,
    Module.finrank_fin_fun, VectorBundle.finrank_eq ℂ F V x]

end Rank

/-- The native `(0,1)`-projection with codomain restricted to its actual complex range. -/
def zeroOnePartToRange (x : M) :
    (TangentSpace I x →L[ℝ] V x) →ₗ[ℂ] j.zeroOneFormSubmodule (V := V) x :=
  (j.zeroOnePartLinearMap x).rangeRestrict

@[simp]
theorem coe_zeroOnePartToRange (x : M) (η : TangentSpace I x →L[ℝ] V x) :
    (j.zeroOnePartToRange x η : TangentSpace I x →L[ℝ] V x) = j.zeroOnePart η := by
  exact LinearMap.congr_fun (LinearMap.subtype_comp_rangeRestrict (j.zeroOnePartLinearMap x)) η

/-- The range projection fixes every `(0,1)`-form. -/
@[simp]
theorem zeroOnePartToRange_coe (x : M) (η : j.zeroOneFormSubmodule (V := V) x) :
    j.zeroOnePartToRange x (η : TangentSpace I x →L[ℝ] V x) = η := by
  apply Subtype.ext
  rw [coe_zeroOnePartToRange]
  exact ((j.mem_zeroOneFormSubmodule_iff x _).mp η.property).zeroOnePart_eq

/-- The canonical inclusion of the actual `(0,1)`-range into the real Hom total space.
The model tag `P` of the range total space does not affect the map. -/
def zeroOneFormInclusion (P : Type*) :
    TotalSpace P (fun x ↦ j.zeroOneFormSubmodule (V := V) x) →
      TotalSpace (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) :=
  fun p ↦ ⟨p.proj, p.snd⟩

/-- The actual `(0,1)`-projection on total spaces, with codomain its range. -/
def zeroOneFormProjection (P : Type*) :
    TotalSpace (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) →
      TotalSpace P (fun x ↦ j.zeroOneFormSubmodule (V := V) x) :=
  fun p ↦ ⟨p.proj, j.zeroOnePartToRange p.proj p.snd⟩

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V] in
@[simp]
theorem zeroOneFormInclusion_apply (P : Type*)
    (p : TotalSpace P (fun x ↦ j.zeroOneFormSubmodule (V := V) x)) :
    j.zeroOneFormInclusion (F := F) (V := V) P p = ⟨p.proj, p.snd⟩ := by
  simp only [zeroOneFormInclusion]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V] in
@[simp]
theorem zeroOneFormProjection_apply (P : Type*)
    (p : TotalSpace (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x)) :
    j.zeroOneFormProjection P p = ⟨p.proj, j.zeroOnePartToRange p.proj p.snd⟩ := by
  simp only [zeroOneFormProjection]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V] in
/-- Inclusion after projection recovers the original native total-space `(0,1)`-projection. -/
theorem zeroOneFormInclusion_projection (P : Type*)
    (p : TotalSpace (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x)) :
    j.zeroOneFormInclusion P (j.zeroOneFormProjection P p) =
      TotalSpace.mk' (E →L[ℝ] F) (E := fun x ↦ TangentSpace I x →L[ℝ] V x)
        p.proj (j.zeroOnePart p.snd) := by
  simp only [zeroOneFormProjection_apply, zeroOneFormInclusion_apply, coe_zeroOnePartToRange]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V] in
/-- Projection after inclusion is the identity on the actual range bundle. -/
theorem zeroOneFormProjection_inclusion (P : Type*)
    (p : TotalSpace P (fun x ↦ j.zeroOneFormSubmodule (V := V) x)) :
    j.zeroOneFormProjection P (j.zeroOneFormInclusion (F := F) (V := V) P p) = p := by
  rcases p with ⟨x, η⟩
  simp only [zeroOneFormInclusion_apply, zeroOneFormProjection_apply, zeroOnePartToRange_coe]

section Bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℂ F]

/-- The actual complex `(0,1)`-ranges have local `C^n` frames of the derived rank. -/
theorem hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule {n : ℕ∞ω} (hn : n ≤ ∞)
    [ContMDiffVectorBundle n F V I] :
    HasLocalContMDiffSubbundleFrames I n (E →L[ℝ] F)
      (Fin (finrank ℝ E / 2 * finrank ℂ F)) (j.zeroOneFormSubmodule (V := V)) := by
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    (inferInstance : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I).of_le hn
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  have : FiniteDimensional ℂ (E →L[ℝ] F) :=
    .of_restrictScalars_finite ℝ ℂ (E →L[ℝ] F)
  refine hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range
    (F₁ := E →L[ℝ] F) (j.zeroOnePartLinearMap (V := V)) ?_ ?_
    (j.finrank_zeroOneFormSubmodule (F := F))
  · simpa only [zeroOnePartLinearMap_apply] using
      j.contMDiff_totalSpace_zeroOnePart (F := F) (V := V) hn
  · intro x
    simp only [zeroOneFormSubmodule]

/-- The native range fibre bundle with the `C^n` frame atlas. Install this with `letI`, after
installing `TauCeti.subbundleTopology (E →L[ℝ] F)` on its total space. -/
@[instance_reducible]
def zeroOneFiberBundle (n : ℕ∞ω) (hn : n ≤ ∞) [ContMDiffVectorBundle n F V I] :
    letI := subbundleTopology (E →L[ℝ] F)
      (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
    FiberBundle (Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := V) x) :=
  (j.hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule (F := F) (V := V) hn).fiberBundle

/-- The native range bundle is complex linear, with the same inherited total-space topology. -/
theorem zeroOneVectorBundle (n : ℕ∞ω) (hn : n ≤ ∞) [ContMDiffVectorBundle n F V I] :
    letI := subbundleTopology (E →L[ℝ] F)
      (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
    letI := j.zeroOneFiberBundle (F := F) (V := V) n hn
    VectorBundle ℂ (Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := V) x) :=
  (j.hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule (F := F) (V := V) hn).vectorBundle

/-- The literal `(0,1)`-range bundle is `C^n`. For a smooth coefficient bundle, install the
infinity construction once and use native monotonicity for every finite regularity. -/
theorem zeroOneContMDiffVectorBundle (n : ℕ∞ω) (hn : n ≤ ∞)
    [ContMDiffVectorBundle n F V I] :
    letI := subbundleTopology (E →L[ℝ] F)
      (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
    letI := j.zeroOneFiberBundle (F := F) (V := V) n hn
    letI := j.zeroOneVectorBundle (F := F) (V := V) n hn
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := V) x)
    ContMDiffVectorBundle n (Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := V) x) I := by
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    (inferInstance : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I).of_le hn
  exact (j.hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule (F := F) (V := V) hn
    ).contMDiffVectorBundle

/-- The canonical inclusion of the actual `(0,1)`-range bundle into raw real one-forms is `C^n`. -/
theorem contMDiff_zeroOneFormInclusion (n : ℕ∞ω) (hn : n ≤ ∞)
    [ContMDiffVectorBundle n F V I] :
    letI := subbundleTopology (E →L[ℝ] F)
      (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
    letI := j.zeroOneFiberBundle (F := F) (V := V) n hn
    ContMDiff (I.prod 𝓘(ℝ, Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ))
      (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (j.zeroOneFormInclusion (F := F) (V := V) (Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)) := by
  let := subbundleTopology (E →L[ℝ] F)
    (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
  let := j.zeroOneFiberBundle (F := F) (V := V) n hn
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    (inferInstance : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I).of_le hn
  exact (j.hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule (F := F) (V := V) hn
    ).contMDiff_totalSpace_inclusion.congr fun p ↦ j.zeroOneFormInclusion_apply _ p

/-- The native `(0,1)`-projection, with codomain the actual range bundle, is `C^n`. -/
theorem contMDiff_zeroOneFormProjection (n : ℕ∞ω) (hn : n ≤ ∞)
    [ContMDiffVectorBundle n F V I] :
    letI := subbundleTopology (E →L[ℝ] F)
      (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
    letI := j.zeroOneFiberBundle (F := F) (V := V) n hn
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (I.prod 𝓘(ℝ, Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)) n
      (j.zeroOneFormProjection (F := F) (V := V) (Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ)) := by
  let := subbundleTopology (E →L[ℝ] F)
    (F' := Fin (finrank ℝ E / 2 * finrank ℂ F) → ℂ) (j.zeroOneFormSubmodule (V := V))
  let := j.zeroOneFiberBundle (F := F) (V := V) n hn
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    (inferInstance : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I).of_le hn
  refine ((j.hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule (F := F) (V := V) hn
    ).contMDiff_totalSpace_mk le_rfl (j.contMDiff_totalSpace_zeroOnePart (F := F) (V := V) hn)
    (fun p ↦ (j.mem_zeroOneFormSubmodule_iff _ _).mpr (j.isZeroOneForm_zeroOnePart p.snd))
    ).congr fun p ↦ ?_
  rw [zeroOneFormProjection_apply]
  apply congrArg (TotalSpace.mk p.proj)
  apply Subtype.ext
  exact j.coe_zeroOnePartToRange p.proj p.snd

end Bundle

end TauCeti.SmoothAlmostComplexStructure
