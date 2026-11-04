/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.Algebra.Module.Complexification

/-!
# Complex vector bundles over real bases and complexification of real vector bundles

A complex vector bundle over an arbitrary topological space `B` (for instance, a real manifold
carrying no complex structure on `B`) is a fibre bundle with complex normed model fibre `G` whose
trivializations are `ℂ`-linear and whose transition maps are continuous into `G →L[ℂ] G`. Because
scalar restriction `(G →L[ℂ] G) → (G →L[ℝ] G)` is an isometry
(`ContinuousLinearMap.norm_restrictScalars`),
continuity of the transition maps into `G →L[ℂ] G` is *equivalent* to continuity into `G →L[ℝ] G`.
Consequently, any real vector bundle `[VectorBundle ℝ G W]` whose atlas trivializations are
`ℂ`-linear — or equivalently intertwine multiplication by `Complex.I` — automatically carries a
compatible `VectorBundle ℂ G W` structure (`VectorBundle.ofLinear`, `VectorBundle.ofMapISmul`), and
its fibrewise complex structure `Complex.smulIEquiv (W x)` has constant coordinate expression
`Complex.smulIEquiv G`, hence defines a continuous section of the real endomorphism bundle and a
homeomorphism of total spaces (`TauCeti.smulIHomeomorph`).

For any real vector bundle `E : B → Type*` with model fibre `F` whose complexified fibres
`ℂ ⊗[ℝ] E x` carry `TauCeti.IsComplexificationTopology (E x)` (supplied in the
`TauCeti.Complexification` scope by `TauCeti.complexificationTopology`), we construct the
complexified vector bundle `fun x ↦ ℂ ⊗[ℝ] E x` with Taylor-normed model fibre
`TauCeti.Complexification F`:

* global `TopologicalSpace`, `FiberBundle`, `VectorBundle ℂ`, and `VectorBundle ℝ` instances on
  `TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x)`;
* constant coordinate formulas and Hom-bundle continuity for the decomposition projections
  `realPartCLM`, `imaginaryPartCLM`, inclusions `oneTmulCLM`, `ITmulCLM`, complex conjugation
  `tmulConjCLE`, and the product comparison `complexificationEquivProd`;
* the canonical total-space homeomorphism
  `TauCeti.complexificationTotalSpaceHomeomorphProd` identifying
  `TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x)` with `TotalSpace (F × F) (E ×ᵇ E)` without
  requiring finite rank or completeness.

The construction of `TauCeti.complexificationVectorPrebundle` follows Mathlib's `VectorPrebundle`
pattern in `Mathlib.Topology.VectorBundle.Hom` by Heather Macbeth and Floris van Doorn.

## Main definitions and results

* `Bundle.Trivialization.isLinear_restrictScalars`,
  `Bundle.Trivialization.isLinear_complex_of_map_I_smul`,
  `VectorBundle.restrictScalars`, `VectorBundle.ofLinear`, and `VectorBundle.ofMapISmul`:
  restricting or upgrading scalar fields on `VectorBundle` along `𝕜' ⊆ 𝕜` (in particular
  `ℝ ⊆ ℂ`).
* `TauCeti.inCoordinates_smulIEquiv`, `TauCeti.continuous_smulIEquiv_bundle`, and
  `TauCeti.smulIHomeomorph`: constant-coordinate formula and continuity of multiplication by `i` on
  any complex vector bundle viewed over `ℝ`.
* `Bundle.Pretrivialization.complexification`, `TauCeti.complexificationVectorPrebundle`, and
  `Bundle.Trivialization.complexification`: induced trivializations and vector-bundle instances on
  `fun x ↦ ℂ ⊗[ℝ] E x`.
* `TauCeti.inCoordinates_realPartCLM`, `TauCeti.inCoordinates_imaginaryPartCLM`,
  `TauCeti.inCoordinates_oneTmulCLM`, `TauCeti.inCoordinates_ITmulCLM`,
  `TauCeti.inCoordinates_tmulConjCLM`, and `TauCeti.inCoordinates_complexificationEquivProd`:
  constant coordinate expressions for the structural morphisms of `ℂ ⊗[ℝ] E x`.
* `TauCeti.complexificationTotalSpaceHomeomorphProd`: canonical homeomorphism between the total
  space of `fun x ↦ ℂ ⊗[ℝ] E x` and `TotalSpace (F × F) (E ×ᵇ E)`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2 and §2.6.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.
-/

public section

noncomputable section

open Bundle FiberBundle Set Topology
open scoped TensorProduct

/-! ### Upgrading real vector bundles to complex ones -/

namespace Bundle.Trivialization

section RestrictScalars

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}

/-- A `𝕜`-linear trivialization is also `𝕜'`-linear for any compatible scalar action `𝕜'`. -/
theorem isLinear_restrictScalars (𝕜' 𝕜 : Type*) [Semiring 𝕜'] [Semiring 𝕜] [SMul 𝕜' 𝕜]
    [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
    [AddCommMonoid F] [Module 𝕜' F] [Module 𝕜 F] [IsScalarTower 𝕜' 𝕜 F]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, IsScalarTower 𝕜' 𝕜 (E x)]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    e.IsLinear 𝕜' where
  linear b hb :=
    { map_add v w := (e.linear 𝕜 hb).map_add v w
      map_smul r v := by
        rw [← smul_one_smul 𝕜 r v, (e.linear 𝕜 hb).map_smul, smul_one_smul] }

/-- A real-linear trivialization of a bundle of complex vector spaces that commutes with
`Complex.I • ·` on every fibre over its base set is `ℂ`-linear. -/
theorem isLinear_complex_of_map_I_smul
    [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
    [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, IsScalarTower ℝ ℂ (E x)]
    (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hI : ∀ b ∈ e.baseSet, ∀ v : E b, (e ⟨b, Complex.I • v⟩).2 = Complex.I • (e ⟨b, v⟩).2) :
    e.IsLinear ℂ where
  linear b hb :=
    { map_add v w := (e.linear ℝ hb).map_add v w
      map_smul c v := by
        rw [← Complex.re_smul_add_im_smul c v, (e.linear ℝ hb).map_add,
          (e.linear ℝ hb).map_smul, (e.linear ℝ hb).map_smul, hI b hb,
          Complex.re_smul_add_im_smul] }

/-- Restricting scalars of a `𝕜`-linear coordinate change recovers the `𝕜'`-linear coordinate
change. -/
theorem restrictScalars_coordChangeL (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜' 𝕜 F]
    [TopologicalSpace (TotalSpace F E)]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
    (e e' : Trivialization F (π F E))
    [e.IsLinear 𝕜'] [e'.IsLinear 𝕜'] [e.IsLinear 𝕜] [e'.IsLinear 𝕜]
    {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.coordChangeL 𝕜 e' b : F →L[𝕜] F).restrictScalars 𝕜' = e.coordChangeL 𝕜' e' b := by
  ext v
  simp [Trivialization.coordChangeL_apply' e e' hb]

end RestrictScalars

end Bundle.Trivialization

namespace VectorBundle

variable {B : Type*} [TopologicalSpace B]

/-- Restrict a `VectorBundle 𝕜 G W` to a `VectorBundle 𝕜' G W` along a normed field extension
`𝕜' ⊆ 𝕜`, keeping the exact same total-space topology and trivialization atlas. -/
theorem restrictScalars (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜' 𝕜 G]
    (W : B → Type*) [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜' (W x)] [∀ x, Module 𝕜 (W x)]
    [∀ x, IsScalarTower 𝕜' 𝕜 (W x)]
    [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle 𝕜 G W] :
    VectorBundle 𝕜' G W where
  trivialization_linear' e _ := Trivialization.isLinear_restrictScalars 𝕜' 𝕜 e
  continuousOn_coordChange' e e' _ _ := by
    let : e.IsLinear 𝕜' := Trivialization.isLinear_restrictScalars 𝕜' 𝕜 e
    let : e'.IsLinear 𝕜' := Trivialization.isLinear_restrictScalars 𝕜' 𝕜 e'
    refine ((ContinuousLinearMap.restrictScalarsIsometry 𝕜 G G 𝕜' ℤ).isometry.continuous
      |>.comp_continuousOn (continuousOn_coordChange 𝕜 e e')).congr fun b hb ↦ ?_
    exact (Trivialization.restrictScalars_coordChangeL 𝕜' 𝕜 e e' hb).symm

/-- Upgrade a `VectorBundle 𝕜' G W` to `VectorBundle 𝕜 G W` along a normed field extension
`𝕜' ⊆ 𝕜` once every trivialization in the atlas is `𝕜`-linear. No extra structure on the base `B`
is required: continuity of coordinate changes in `G →L[𝕜] G` follows from the linear isometry
`ContinuousLinearMap.restrictScalarsIsometry`. -/
theorem ofLinear (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜' 𝕜 G]
    (W : B → Type*) [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜' (W x)] [∀ x, Module 𝕜 (W x)]
    [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle 𝕜' G W]
    (hlin : ∀ e : Trivialization G (π G W), MemTrivializationAtlas e → e.IsLinear 𝕜) :
    VectorBundle 𝕜 G W where
  trivialization_linear' e he := hlin e he
  continuousOn_coordChange' e e' he he' := by
    let : e.IsLinear 𝕜 := hlin e he
    let : e'.IsLinear 𝕜 := hlin e' he'
    rw [(ContinuousLinearMap.restrictScalarsIsometry 𝕜 G G 𝕜' ℤ
      ).isometry.isUniformEmbedding.isInducing.continuousOn_iff]
    refine (continuousOn_coordChange 𝕜' e e').congr fun b hb ↦ ?_
    exact Trivialization.restrictScalars_coordChangeL 𝕜' 𝕜 e e' hb

/-- A real vector bundle `[VectorBundle ℝ G W]` whose atlas trivializations commute with
multiplication by `Complex.I` carries a compatible `VectorBundle ℂ G W` structure, with no complex
structure assumed on the base `B`. -/
theorem ofMapISmul (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
    [IsScalarTower ℝ ℂ G]
    (W : B → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, IsScalarTower ℝ ℂ (W x)]
    [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle ℝ G W]
    (hI : ∀ e : Trivialization G (π G W), MemTrivializationAtlas e →
      ∀ b ∈ e.baseSet, ∀ v : W b, (e ⟨b, Complex.I • v⟩).2 = Complex.I • (e ⟨b, v⟩).2) :
    VectorBundle ℂ G W :=
  ofLinear ℝ ℂ G W fun e he ↦ Trivialization.isLinear_complex_of_map_I_smul e (hI e he)

end VectorBundle

namespace TauCeti

/-! ### Fibrewise multiplication by `i` on a complex vector bundle viewed over `ℝ` -/

section SmulIBundle

variable {B G : Type*} [TopologicalSpace B]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  {W : B → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, IsScalarTower ℝ ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, ContinuousConstSMul ℂ (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W]
  [VectorBundle ℂ G W] [VectorBundle ℝ G W]

/-- Read in any preferred trivialization, fibrewise multiplication by `Complex.I`
(`Complex.smulIEquiv (W x)`) is the constant model operator `Complex.smulIEquiv G`. -/
@[simp]
theorem inCoordinates_smulIEquiv (a : B) {x : B}
    (hx : x ∈ (trivializationAt G W a).baseSet) :
    ContinuousLinearMap.inCoordinates G W G W a x a x
      (Complex.smulIEquiv (W x) : W x →L[ℝ] W x) =
      (Complex.smulIEquiv G : G →L[ℝ] G) := by
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.smulIEquiv_apply]
  rw [(trivializationAt G W a).symmL_apply hx,
    ← (trivializationAt G W a).symmL_apply (R := ℂ) hx,
    ← map_smul ((trivializationAt G W a).symmL ℂ x) Complex.I v,
    (trivializationAt G W a).symmL_apply hx,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx,
    (trivializationAt G W a).apply_mk_symm hx]

/-- Read in any preferred trivialization, fibrewise multiplication by `-Complex.I`
(`(Complex.smulIEquiv (W x)).symm`) is `(Complex.smulIEquiv G).symm`. -/
@[simp]
theorem inCoordinates_smulIEquiv_symm (a : B) {x : B}
    (hx : x ∈ (trivializationAt G W a).baseSet) :
    ContinuousLinearMap.inCoordinates G W G W a x a x
      ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x) =
      ((Complex.smulIEquiv G).symm : G →L[ℝ] G) := by
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.smulIEquiv_symm_apply]
  rw [(trivializationAt G W a).symmL_apply hx,
    ← (trivializationAt G W a).symmL_apply (R := ℂ) hx,
    ← map_smul ((trivializationAt G W a).symmL ℂ x) (-Complex.I) v,
    (trivializationAt G W a).symmL_apply hx,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx,
    (trivializationAt G W a).apply_mk_symm hx]

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]

/-- Fibrewise multiplication by `Complex.I` is a continuous section of the real endomorphism bundle
`fun x ↦ W x →L[ℝ] W x`. -/
theorem continuous_smulIEquiv_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x (Complex.smulIEquiv (W x) : W x →L[ℝ] W x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv a hx

/-- Fibrewise multiplication by `-Complex.I` is a continuous section of the real endomorphism
bundle `fun x ↦ W x →L[ℝ] W x`. -/
theorem continuous_smulIEquiv_symm_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    fun a _ hx _ ↦ inCoordinates_smulIEquiv_symm a hx

variable (G W) in
/-- Multiplication by `Complex.I` on the fibres of a complex vector bundle as a homeomorphism of
its total space, with no finite-rank assumption. -/
def smulIHomeomorph : TotalSpace G W ≃ₜ TotalSpace G W where
  toFun p := ⟨p.proj, Complex.I • p.2⟩
  invFun p := ⟨p.proj, -Complex.I • p.2⟩
  left_inv := fun ⟨x, v⟩ ↦ congrArg (TotalSpace.mk x) (Complex.neg_I_smul_I_smul v)
  right_inv := fun ⟨x, v⟩ ↦ congrArg (TotalSpace.mk x) (Complex.I_smul_neg_I_smul v)
  continuous_toFun := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, Complex.smulIEquiv_apply] using
      (continuous_smulIEquiv_bundle.comp (FiberBundle.continuous_proj G W)).clm_bundle_apply
        continuous_id
  continuous_invFun := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
      Complex.smulIEquiv_symm_apply] using
      (continuous_smulIEquiv_symm_bundle.comp (FiberBundle.continuous_proj G W)).clm_bundle_apply
        continuous_id

@[simp]
theorem smulIHomeomorph_apply (p : TotalSpace G W) :
    smulIHomeomorph G W p = ⟨p.proj, Complex.I • p.2⟩ := (rfl)

@[simp]
theorem smulIHomeomorph_symm_apply (p : TotalSpace G W) :
    (smulIHomeomorph G W).symm p = ⟨p.proj, -Complex.I • p.2⟩ := (rfl)

end SmulIBundle

end TauCeti

/-! ### Pretrivializations of the complexified vector bundle `fun x ↦ ℂ ⊗[ℝ] E x` -/

namespace Bundle.Pretrivialization

open TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)]

/-- Coordinate change between the induced pretrivializations of `fun x ↦ ℂ ⊗[ℝ] E x`, given by
complexifying the real coordinate change of `E`. -/
def complexificationCoordChange (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    (b : B) : Complexification F →L[ℂ] Complexification F :=
  (e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify

theorem complexificationCoordChange_def (e e' : Trivialization F (π F E))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] :
    complexificationCoordChange e e' =
      fun b ↦ (e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify := (rfl)

theorem continuousOn_complexificationCoordChange
    [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
    (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (complexificationCoordChange e e') (e.baseSet ∩ e'.baseSet) :=
  ((ContinuousLinearMap.complexifyₗᵢ F F).continuous.comp_continuousOn
    (continuousOn_coordChange ℝ e e')).congr fun _ _ ↦ by
      ext z <;> simp [complexificationCoordChange]

/-- A real-linear trivialization `e` of `E` induces a pretrivialization of the complexified bundle
`fun x ↦ ℂ ⊗[ℝ] E x` with model fibre `TauCeti.Complexification F`, reading the real and imaginary
parts of a complexified vector in `e`. -/
def complexification (e : Trivialization F (π F E)) [e.IsLinear ℝ] :
    Pretrivialization (Complexification F)
      (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) where
  toFun p := ⟨p.1, ⟨e.linearMapAt ℝ p.1 (realPart (E p.1) p.2),
    e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2)⟩⟩
  invFun p := ⟨p.1, 1 ⊗ₜ[ℝ] e.symm p.1 p.2.re + Complex.I ⊗ₜ[ℝ] e.symm p.1 p.2.im⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by
    rintro ⟨x, u⟩ hx
    simp only [TotalSpace.mk_inj]
    rw [e.symm_linearMapAt hx, e.symm_linearMapAt hx]
    exact one_tmul_realPart_add_I_tmul_imaginaryPart (E x) u
  right_inv' := by
    rintro ⟨x, z⟩ ⟨hx, -⟩
    simp only [Prod.mk_right_inj]
    ext <;> simp [e.coe_linearMapAt_of_mem hx, e.apply_mk_symm hx]
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

theorem complexification_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    complexification e p =
      (p.1, ⟨e.linearMapAt ℝ p.1 (realPart (E p.1) p.2),
        e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2)⟩) := (rfl)

@[simp]
theorem baseSet_complexification : (complexification e).baseSet = e.baseSet := (rfl)

theorem complexification_symm_apply {b : B} (hb : b ∈ e.baseSet) (z : Complexification F) :
    (complexification e).symm b z =
      1 ⊗ₜ[ℝ] e.symm b z.re + Complex.I ⊗ₜ[ℝ] e.symm b z.im := by
  rw [Pretrivialization.symm_apply _ hb]
  rfl

theorem complexificationCoordChange_apply {e' : Trivialization F (π F E)} [e'.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet)
    (z : Complexification F) :
    complexificationCoordChange e e' b z =
      (complexification e' ⟨b, (complexification e).symm b z⟩).2 := by
  ext <;>
    simp [complexificationCoordChange, complexification_apply,
      complexification_symm_apply hb.1, e'.coe_linearMapAt_of_mem hb.2,
      Trivialization.coordChangeL_apply e e' hb]

end Bundle.Pretrivialization

/-! ### The complexified vector bundle -/

namespace TauCeti

open Pretrivialization

section VectorBundle

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- The `VectorPrebundle` structure over `ℂ` on the complexified fibres `fun x ↦ ℂ ⊗[ℝ] E x` with
Taylor-normed model fibre `TauCeti.Complexification F`. -/
def complexificationVectorPrebundle :
    VectorPrebundle ℂ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = Pretrivialization.complexification e}
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.complexification (trivializationAt F E x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F E x
  pretrivialization_mem_atlas x := ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    exact ⟨complexificationCoordChange e e',
      continuousOn_complexificationCoordChange e e',
      fun _ hb ↦ complexificationCoordChange_apply hb⟩
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, complexification_apply, isInducing_const_prod]
    let hb := mem_baseSet_trivializationAt F E b
    let L : E b ≃L[ℝ] F := (trivializationAt F E b).continuousLinearEquivAt ℝ b hb
    let Φ : ℂ ⊗[ℝ] E b ≃L[ℝ] Complexification F :=
      (complexificationEquivProd (E b)).trans
        ((L.prodCongr L).trans (Complexification.equivProd F).symm)
    have hΦ :
        (fun u : ℂ ⊗[ℝ] E b ↦
          ({ re := (trivializationAt F E b).linearMapAt ℝ b (realPart (E b) u),
             im := (trivializationAt F E b).linearMapAt ℝ b (imaginaryPart (E b) u) } :
            Complexification F)) = ⇑Φ := by
      ext u <;> simp [Φ, L, (trivializationAt F E b).coe_linearMapAt_of_mem hb]
    rw [hΦ]
    exact Φ.toHomeomorph.isInducing

variable {F E} in
theorem mem_pretrivializationAtlas_complexificationVectorPrebundle
    {e' : Pretrivialization (Complexification F)
      (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x)} :
    e' ∈ (complexificationVectorPrebundle F E).pretrivializationAtlas ↔
      ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
        e' = Pretrivialization.complexification e :=
  (Iff.rfl)

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

/-- Compatible real vector bundle structure on the complexification `fun x ↦ ℂ ⊗[ℝ] E x`, sharing
the exact same total-space topology and trivialization atlas. -/
instance instVectorBundleRealComplexification :
    VectorBundle ℝ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x :=
  VectorBundle.restrictScalars ℝ ℂ (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x

end VectorBundle

end TauCeti

/-! ### Induced trivializations and coordinate formulas for `fun x ↦ ℂ ⊗[ℝ] E x` -/

namespace Bundle.Trivialization

open TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]
  (e : Trivialization F (π F E)) [he : MemTrivializationAtlas e]

/-- The trivialization of `fun x ↦ ℂ ⊗[ℝ] E x` induced by an atlas trivialization `e` of `E`,
with base set `e.baseSet`. -/
def complexification :
    Trivialization (Complexification F)
      (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas
    (complexificationVectorPrebundle F E) ⟨e, he, rfl⟩

instance memTrivializationAtlas_complexification :
    MemTrivializationAtlas e.complexification :=
  ⟨⟨_, ⟨e, he, rfl⟩, rfl⟩⟩

@[simp]
theorem baseSet_complexification : e.complexification.baseSet = e.baseSet := (rfl)

theorem complexification_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    e.complexification p =
      (p.1, ⟨e.linearMapAt ℝ p.1 (realPart (E p.1) p.2),
        e.linearMapAt ℝ p.1 (imaginaryPart (E p.1) p.2)⟩) := (rfl)

@[simp]
theorem complexification_apply_re (x : B) (u : ℂ ⊗[ℝ] E x) :
    (e.complexification ⟨x, u⟩).2.re = e.linearMapAt ℝ x (realPart (E x) u) := (rfl)

@[simp]
theorem complexification_apply_im (x : B) (u : ℂ ⊗[ℝ] E x) :
    (e.complexification ⟨x, u⟩).2.im = e.linearMapAt ℝ x (imaginaryPart (E x) u) := (rfl)

theorem complexification_symm_apply {b : B} (hb : b ∈ e.baseSet) (z : Complexification F) :
    e.complexification.symm b z =
      1 ⊗ₜ[ℝ] e.symm b z.re + Complex.I ⊗ₜ[ℝ] e.symm b z.im :=
  Pretrivialization.complexification_symm_apply hb z

@[simp]
theorem coordChangeL_complexification (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.complexification.coordChangeL ℂ e'.complexification b :
      Complexification F →L[ℂ] Complexification F) =
      (e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify := by
  ext z <;>
    simp [Trivialization.coordChangeL_apply e.complexification e'.complexification hb,
      complexification_symm_apply e hb.1, e'.coe_linearMapAt_of_mem hb.2,
      Trivialization.coordChangeL_apply e e' hb]

@[simp]
theorem coordChangeL_real_complexification (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.complexification.coordChangeL ℝ e'.complexification b :
      Complexification F →L[ℝ] Complexification F) =
      ((e.coordChangeL ℝ e' b : F →L[ℝ] F).complexify).restrictScalars ℝ := by
  rw [← Trivialization.restrictScalars_coordChangeL ℝ ℂ e.complexification e'.complexification hb,
    coordChangeL_complexification e e' hb]

end Bundle.Trivialization

namespace TauCeti

section TrivializationAtAndMorphisms

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- A trivialization of `fun x ↦ ℂ ⊗[ℝ] E x` belongs to the trivialization atlas if and only if
it is `e.complexification` for some atlas trivialization `e` of `E`. -/
theorem mem_trivializationAtlas_complexification_iff
    {e' : Trivialization (Complexification F)
      (π (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x)} :
    MemTrivializationAtlas e' ↔
      ∃ (e : Trivialization F (π F E)) (he : MemTrivializationAtlas e),
        e' = e.complexification (he := he) := by
  constructor
  · rintro ⟨⟨_, ⟨e, he, rfl⟩, rfl⟩⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact Trivialization.memTrivializationAtlas_complexification e (he := he)

theorem trivializationAt_complexification (x₀ : B) :
    trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀ =
      (trivializationAt F E x₀).complexification := (rfl)

@[simp]
theorem baseSet_trivializationAt_complexification (x₀ : B) :
    (trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀).baseSet =
      (trivializationAt F E x₀).baseSet := (rfl)

@[simp, mfld_simps]
theorem source_trivializationAt_complexification (x₀ : B) :
    (trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀).source =
      π (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ⁻¹' (trivializationAt F E x₀).baseSet := (rfl)

@[simp, mfld_simps]
theorem target_trivializationAt_complexification (x₀ : B) :
    (trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) x₀).target =
      (trivializationAt F E x₀).baseSet ×ˢ univ := (rfl)

theorem trivializationAt_complexification_symmL {a x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) (z : Complexification F) :
    (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).symmL ℝ x z =
      1 ⊗ₜ[ℝ] (trivializationAt F E a).symm x z.re +
        Complex.I ⊗ₜ[ℝ] (trivializationAt F E a).symm x z.im := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  rw [(trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).symmL_apply hx',
    trivializationAt_complexification, (trivializationAt F E a).complexification_symm_apply hx]

theorem trivializationAt_complexification_symmL_complex {a x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) (z : Complexification F) :
    (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).symmL ℂ x z =
      1 ⊗ₜ[ℝ] (trivializationAt F E a).symm x z.re +
        Complex.I ⊗ₜ[ℝ] (trivializationAt F E a).symm x z.im := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  rw [(trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).symmL_apply hx',
    trivializationAt_complexification, (trivializationAt F E a).complexification_symm_apply hx]

/-- Read in preferred frames, `realPartCLM (E x)` is the constant projection
`Complexification.reCLM F`. -/
@[simp]
theorem inCoordinates_realPartCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) F E a x a x
      (realPartCLM (E x)) = Complexification.reCLM F := by
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    trivializationAt_complexification_symmL hx, realPartCLM_apply, map_add, realPart_tmul,
    Complex.one_re, one_smul, Complex.I_re, zero_smul, add_zero, Complexification.reCLM_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx,
    (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `imaginaryPartCLM (E x)` is the constant projection
`Complexification.imCLM F`. -/
@[simp]
theorem inCoordinates_imaginaryPartCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) F E a x a x
      (imaginaryPartCLM (E x)) = Complexification.imCLM F := by
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    trivializationAt_complexification_symmL hx, imaginaryPartCLM_apply, map_add,
    imaginaryPart_tmul, Complex.one_im, zero_smul, Complex.I_im, one_smul, zero_add,
    Complexification.imCLM_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx,
    (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `oneTmulCLM (E x)` is the constant real embedding
`(Complexification.ofRealLI F).toContinuousLinearMap`. -/
@[simp]
theorem inCoordinates_oneTmulCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      F E (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (oneTmulCLM (E x)) = (Complexification.ofRealLI F).toContinuousLinearMap := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    (trivializationAt F E a).symmL_apply hx, oneTmulCLM_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx',
    trivializationAt_complexification]
  ext <;>
    simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx,
      ((trivializationAt F E a).linear ℝ hx).map_zero,
      (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `ITmulCLM (E x)` is the constant imaginary embedding
`v ↦ Complex.I • Complexification.ofReal v`. -/
@[simp]
theorem inCoordinates_ITmulCLM (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      F E (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (ITmulCLM (E x)) =
      (Complex.smulIEquiv (Complexification F)).toContinuousLinearMap.comp
        (Complexification.ofRealLI F).toContinuousLinearMap := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    (trivializationAt F E a).symmL_apply hx, ITmulCLM_apply,
    ContinuousLinearEquiv.coe_coe, Complex.smulIEquiv_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx',
    trivializationAt_complexification]
  ext <;>
    simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx,
      ((trivializationAt F E a).linear ℝ hx).map_zero,
      (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, fibrewise conjugation `tmulConjCLE (E x)` is the constant model
conjugation `Complexification.conjCLE F`. -/
@[simp]
theorem inCoordinates_tmulConjCLE [∀ x, ContinuousNeg (E x)] (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y)
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (tmulConjCLE (E x) : ℂ ⊗[ℝ] E x →SL[starRingEnd ℂ] ℂ ⊗[ℝ] E x) =
      (Complexification.conjCLE F :
        Complexification F →SL[starRingEnd ℂ] Complexification F) := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    trivializationAt_complexification_symmL_complex hx, ContinuousLinearEquiv.coe_coe,
    coe_tmulConjCLE, Complexification.coe_conjCLE]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hx',
    trivializationAt_complexification]
  ext <;>
    simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx,
      ((trivializationAt F E a).linear ℝ hx).map_neg,
      (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `tmulConjCLM (E x)` (viewed over `ℝ`) is constant. -/
@[simp]
theorem inCoordinates_tmulConjCLM [∀ x, IsTopologicalAddGroup (E x)] (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y)
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      (tmulConjCLM (E x)) =
      (Complexification.ofRealLI F).toContinuousLinearMap.comp (Complexification.reCLM F) -
        ((Complex.smulIEquiv (Complexification F)).toContinuousLinearMap.comp
          (Complexification.ofRealLI F).toContinuousLinearMap).comp
            (Complexification.imCLM F) := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    sub_apply, trivializationAt_complexification_symmL hx, tmulConjCLM_apply,
    ContinuousLinearEquiv.coe_coe, Complex.smulIEquiv_apply, Complexification.reCLM_apply,
    Complexification.imCLM_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx',
    trivializationAt_complexification]
  ext <;>
    simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx,
      ((trivializationAt F E a).linear ℝ hx).map_neg,
      (trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `complexificationEquivProd (E x)` is the constant equivalence
`Complexification.equivProd F`. -/
@[simp]
theorem inCoordinates_complexificationEquivProd (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) (F × F) (E ×ᵇ E) a x a x
      (complexificationEquivProd (E x) : ℂ ⊗[ℝ] E x →L[ℝ] E x × E x) =
      (Complexification.equivProd F : Complexification F →L[ℝ] F × F) := by
  have hxp : x ∈ (trivializationAt (F × F) (E ×ᵇ E) a).baseSet := ⟨hx, hx⟩
  have hprod : trivializationAt (F × F) (E ×ᵇ E) a =
      (trivializationAt F E a).prod (trivializationAt F E a) := rfl
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    trivializationAt_complexification_symmL hx, ContinuousLinearEquiv.coe_coe,
    Complexification.equivProd_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hxp, hprod,
    complexificationEquivProd_apply, Trivialization.prod_apply' ℝ hx hx]
  ext <;> simp [(trivializationAt F E a).apply_mk_symm hx]

/-- Read in preferred frames, `(complexificationEquivProd (E x)).symm` is
`(Complexification.equivProd F).symm`. -/
@[simp]
theorem inCoordinates_complexificationEquivProd_symm (a : B) {x : B}
    (hx : x ∈ (trivializationAt F E a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (F × F) (E ×ᵇ E) (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a x a x
      ((complexificationEquivProd (E x)).symm : E x × E x →L[ℝ] ℂ ⊗[ℝ] E x) =
      ((Complexification.equivProd F).symm : F × F →L[ℝ] Complexification F) := by
  have hx' : x ∈ (trivializationAt (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) a).baseSet := hx
  have hxp : x ∈ (trivializationAt (F × F) (E ×ᵇ E) a).baseSet := ⟨hx, hx⟩
  have hprod : trivializationAt (F × F) (E ×ᵇ E) a =
      (trivializationAt F E a).prod (trivializationAt F E a) := rfl
  refine ContinuousLinearMap.ext fun ⟨v, w⟩ ↦ ?_
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    (trivializationAt (F × F) (E ×ᵇ E) a).symmL_apply hxp, ContinuousLinearEquiv.coe_coe]
  have hsymm :
      (trivializationAt (F × F) (E ×ᵇ E) a).symm x (v, w) =
        ((trivializationAt F E a).symm x v, (trivializationAt F E a).symm x w) := by
    rw [hprod]
    exact (TotalSpace.mk_inj (F := F × F) (E := E ×ᵇ E)).mp
      ((((trivializationAt F E a).prod (trivializationAt F E a)).mk_symm hxp (v, w)).trans
        ((trivializationAt F E a).prod_symm_apply (trivializationAt F E a) x v w))
  rw [hsymm, complexificationEquivProd_symm_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx',
    trivializationAt_complexification, Complexification.equivProd_symm_apply]
  ext <;>
    simp [(trivializationAt F E a).coe_linearMapAt_of_mem hx,
      (trivializationAt F E a).apply_mk_symm hx]

section ContinuousSections

variable [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]

theorem continuous_realPartCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (realPartCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_realPartCLM a hx

theorem continuous_imaginaryPartCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (imaginaryPartCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    fun a _ _ hx ↦ inCoordinates_imaginaryPartCLM a hx

theorem continuous_oneTmulCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
      (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (oneTmulCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_oneTmulCLM a hx

theorem continuous_ITmulCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
      (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (ITmulCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_ITmulCLM a hx

theorem continuous_tmulConjCLE_bundle :
    Continuous (fun x ↦ TotalSpace.mk'
      (Complexification F →SL[starRingEnd ℂ] Complexification F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →SL[starRingEnd ℂ] ℂ ⊗[ℝ] E y) x
      (tmulConjCLE (E x) : ℂ ⊗[ℝ] E x →SL[starRingEnd ℂ] ℂ ⊗[ℝ] E x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_tmulConjCLE a hx

theorem continuous_tmulConjCLM_bundle :
    Continuous (fun x ↦ TotalSpace.mk'
      (Complexification F →L[ℝ] Complexification F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] ℂ ⊗[ℝ] E y) x (tmulConjCLM (E x))) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_tmulConjCLM a hx

theorem continuous_complexificationEquivProd_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F × F)
      (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y) x
      (complexificationEquivProd (E x) : ℂ ⊗[ℝ] E x →L[ℝ] (E ×ᵇ E) x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    fun a _ hx _ ↦ inCoordinates_complexificationEquivProd a hx

theorem continuous_complexificationEquivProd_symm_bundle :
    Continuous (fun x ↦ TotalSpace.mk' ((F × F) →L[ℝ] Complexification F)
      (E := fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y) x
      ((complexificationEquivProd (E x)).symm : (E ×ᵇ E) x →L[ℝ] ℂ ⊗[ℝ] E x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    fun a _ _ hx ↦ inCoordinates_complexificationEquivProd_symm a hx

variable (F E) in
/-- Fibrewise conjugation `z ⊗ₜ v ↦ conj z ⊗ₜ v` as an involutive homeomorphism of the total space
of the complexified bundle `fun x ↦ ℂ ⊗[ℝ] E x`, with no finite-rank assumption. -/
def tmulConjHomeomorph :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₜ
      TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) where
  toFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
  invFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
  left_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
  right_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
  continuous_toFun := by
    have h : Continuous
        (fun p : TotalSpace (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) ↦
          TotalSpace.mk' (Complexification F →L[ℝ] Complexification F)
            (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] ℂ ⊗[ℝ] E y) p.proj (tmulConjCLM (E p.proj))) :=
      continuous_tmulConjCLM_bundle.comp
        (FiberBundle.continuous_proj (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y))
    simpa only [tmulConjCLM_apply] using
      Continuous.clm_bundle_apply (𝕜 := ℝ)
        (F₁ := Complexification F) (F₂ := Complexification F)
        (E₁ := fun y ↦ ℂ ⊗[ℝ] E y) (E₂ := fun y ↦ ℂ ⊗[ℝ] E y) h continuous_id
  continuous_invFun := by
    have h : Continuous
        (fun p : TotalSpace (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) ↦
          TotalSpace.mk' (Complexification F →L[ℝ] Complexification F)
            (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] ℂ ⊗[ℝ] E y) p.proj (tmulConjCLM (E p.proj))) :=
      continuous_tmulConjCLM_bundle.comp
        (FiberBundle.continuous_proj (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y))
    simpa only [tmulConjCLM_apply] using
      Continuous.clm_bundle_apply (𝕜 := ℝ)
        (F₁ := Complexification F) (F₂ := Complexification F)
        (E₁ := fun y ↦ ℂ ⊗[ℝ] E y) (E₂ := fun y ↦ ℂ ⊗[ℝ] E y) h continuous_id

@[simp]
theorem tmulConjHomeomorph_apply (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    tmulConjHomeomorph F E p = ⟨p.proj, tmulConj (E p.proj) p.2⟩ := (rfl)

@[simp]
theorem tmulConjHomeomorph_symm : (tmulConjHomeomorph F E).symm = tmulConjHomeomorph F E := (rfl)

variable (F E) in
/-- The real/imaginary-part homeomorphism between the total space of the complexified bundle
`fun x ↦ ℂ ⊗[ℝ] E x` and the total space of the direct-sum bundle `E ×ᵇ E`, valid without any
finite-rank assumption on `F`. -/
def complexificationTotalSpaceHomeomorphProd :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₜ
      TotalSpace (F × F) (E ×ᵇ E) where
  toFun p := ⟨p.proj, complexificationEquivProd (E p.proj) p.2⟩
  invFun p := ⟨p.proj, (complexificationEquivProd (E p.proj)).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    have h : Continuous
        (fun p : TotalSpace (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y) ↦
          TotalSpace.mk' (Complexification F →L[ℝ] F × F)
            (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y) p.proj
            (complexificationEquivProd (E p.proj) : ℂ ⊗[ℝ] E p.proj →L[ℝ] (E ×ᵇ E) p.proj)) :=
      continuous_complexificationEquivProd_bundle.comp
        (FiberBundle.continuous_proj (Complexification F) (fun y ↦ ℂ ⊗[ℝ] E y))
    exact Continuous.clm_bundle_apply (𝕜 := ℝ)
      (F₁ := Complexification F) (F₂ := F × F)
      (E₁ := fun y ↦ ℂ ⊗[ℝ] E y) (E₂ := E ×ᵇ E) h continuous_id
  continuous_invFun := by
    have h : Continuous
        (fun p : TotalSpace (F × F) (E ×ᵇ E) ↦
          TotalSpace.mk' ((F × F) →L[ℝ] Complexification F)
            (E := fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y) p.proj
            ((complexificationEquivProd (E p.proj)).symm :
              (E ×ᵇ E) p.proj →L[ℝ] ℂ ⊗[ℝ] E p.proj)) :=
      continuous_complexificationEquivProd_symm_bundle.comp
        (FiberBundle.continuous_proj (F × F) (E ×ᵇ E))
    exact Continuous.clm_bundle_apply (𝕜 := ℝ)
      (F₁ := F × F) (F₂ := Complexification F)
      (E₁ := E ×ᵇ E) (E₂ := fun y ↦ ℂ ⊗[ℝ] E y) h continuous_id

@[simp]
theorem complexificationTotalSpaceHomeomorphProd_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    complexificationTotalSpaceHomeomorphProd F E p =
      ⟨p.proj, (realPart (E p.proj) p.2, imaginaryPart (E p.proj) p.2)⟩ := by
  simp [complexificationTotalSpaceHomeomorphProd]

@[simp]
theorem complexificationTotalSpaceHomeomorphProd_symm_apply
    (p : TotalSpace (F × F) (E ×ᵇ E)) :
    (complexificationTotalSpaceHomeomorphProd F E).symm p =
      ⟨p.proj, 1 ⊗ₜ[ℝ] p.2.1 + Complex.I ⊗ₜ[ℝ] p.2.2⟩ := by
  simp [complexificationTotalSpaceHomeomorphProd]

theorem proj_complexificationTotalSpaceHomeomorphProd
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    (complexificationTotalSpaceHomeomorphProd F E p).proj = p.proj := (rfl)

end ContinuousSections

end TrivializationAtAndMorphisms

end TauCeti

end
