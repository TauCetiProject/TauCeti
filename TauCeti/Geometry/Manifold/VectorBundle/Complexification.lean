/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Topology.VectorBundle.Complexification
import TauCeti.Topology.VectorBundle.RestrictScalars
import Mathlib.LinearAlgebra.Span.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# `C^n` complex vector bundles over real manifolds and complexification of `C^n` sections

Over a real charted space `(B, IB)`, fibrewise multiplication by `Complex.I` on a complex vector
bundle `W : B → Type*` defines `TauCeti.smulIDiffeomorph` (specializing
`TauCeti.vectorBundleScalarDiffeomorph`) and `TauCeti.contMDiff_smulIEquiv_bundle`.

For any real `C^n` vector bundle `E : B → Type*` with model fibre `F` whose complexified fibres
`ℂ ⊗[ℝ] E x` carry `TauCeti.IsComplexificationTopology (E x)`, we establish
`TauCeti.instContMDiffVectorBundleComplexification` (without finite rank or `[IsManifold IB n B]`),
`TauCeti.contMDiffWithinAt_complexification_totalSpace_iff`,
`TauCeti.contMDiff_complexification_section_iff`, `TauCeti.tmulConjDiffeomorph`,
`TauCeti.complexificationTotalSpaceDiffeomorphProd`, `ContMDiffSection.complexificationEquiv`,
`ContMDiffSection.complexificationEquivProd`, and `ContMDiffSection.conjEquiv`.
The canonical complex-linear extension of any smooth real bundle map is smooth on the actual
complexification total space (`TauCeti.contMDiff_liftBaseChangeComplex_totalSpace`), with no
injectivity, maximality or finite-rank assumption.

The same original-fibre algebra restricts to native prescribed-support and compactly supported
submodules, with exact support laws and comparisons to the native conjugation-fixed submodule.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2 and §2.6.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Function Set Topology
open scoped Bundle ContDiff Manifold TensorProduct

/-! ### Multiplication by `i` on complex vector bundles over real manifolds -/

namespace TauCeti

section SmulIBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  {n : ℕ∞ω} {W : B → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle ℂ G W]

variable (IB G n W) in
/-- Fibrewise multiplication by `Complex.I` on a complex vector bundle over a real charted space as
a `C^n` diffeomorphism of its total space, requiring neither finite rank nor `ContMDiffVectorBundle`
nor fibrewise topological-group hypotheses. -/
def smulIDiffeomorph : TotalSpace G W ≃ₘ^n⟮IB.prod 𝓘(ℝ, G), IB.prod 𝓘(ℝ, G)⟯ TotalSpace G W :=
  vectorBundleScalarDiffeomorph (fun _ ↦ Complex.I) contMDiff_const (fun _ ↦ Complex.I_ne_zero)

@[simp] theorem smulIDiffeomorph_apply (p : TotalSpace G W) :
    smulIDiffeomorph IB G n W p = ⟨p.proj, Complex.I • p.2⟩ :=
  vectorBundleScalarDiffeomorph_apply _ _ _ p
@[simp] theorem smulIDiffeomorph_symm_apply (p : TotalSpace G W) :
    (smulIDiffeomorph IB G n W).symm p = ⟨p.proj, -Complex.I • p.2⟩ := by simp [smulIDiffeomorph]
/-- Applying `smulIDiffeomorph` twice negates each fibre vector. -/
theorem smulIDiffeomorph_smulIDiffeomorph_apply (p : TotalSpace G W) :
    smulIDiffeomorph IB G n W (smulIDiffeomorph IB G n W p) = ⟨p.proj, -p.2⟩ := by
  rcases p with ⟨x, v⟩; simp [smul_smul]
@[simp] theorem toHomeomorph_smulIDiffeomorph :
    (smulIDiffeomorph IB G n W).toHomeomorph = smulIHomeomorph G W :=
  Homeomorph.ext fun _ ↦ by simp

variable [∀ x, Module ℝ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)] [∀ x, ContinuousConstSMul ℂ (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] [VectorBundle ℝ G W]

omit [IsScalarTower ℝ ℂ G] in
/-- Fibrewise multiplication by `Complex.I` is a `C^n` section of `fun x ↦ W x →L[ℝ] W x`. -/
theorem contMDiff_smulIEquiv_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, G →L[ℝ] G)) n (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x (Complex.smulIEquiv (W x) : W x →L[ℝ] W x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv a hx

omit [IsScalarTower ℝ ℂ G] in
/-- Fibrewise multiplication by `-Complex.I` is a `C^n` section of `fun x ↦ W x →L[ℝ] W x`. -/
theorem contMDiff_smulIEquiv_symm_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, G →L[ℝ] G)) n (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv_symm a hx

end SmulIBundle

/-! ### Complexification of real `C^n` vector bundles -/

section ComplexificationBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- If `E` is a real `C^n` vector bundle over `(B, IB)`, then its complexification
`fun x ↦ ℂ ⊗[ℝ] E x` is a `C^n` vector bundle with model fibre `Complexification F`. Neither
`[IsManifold IB n B]` nor finite rank is needed. -/
instance instContMDiffVectorBundleComplexification [ContMDiffVectorBundle n F E IB] :
    ContMDiffVectorBundle n (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) IB where
  contMDiffOn_coordChangeL := by
    intro e₁' e₂' he₁' he₂'
    obtain ⟨e, he, rfl⟩ := mem_trivializationAtlas_complexification_iff.mp he₁'
    obtain ⟨e', he', rfl⟩ := mem_trivializationAtlas_complexification_iff.mp he₂'
    have : MemTrivializationAtlas e := he
    have : MemTrivializationAtlas e' := he'
    let L : (F →L[ℝ] F) →L[ℝ] (Complexification F →L[ℝ] Complexification F) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Complexification F) (Complexification F) ℝ ℝ).comp
        (ContinuousLinearMap.complexifyₗᵢ F F).toContinuousLinearMap
    rw [e.baseSet_complexification, e'.baseSet_complexification]
    refine ((L.contDiff (n := n)).contMDiff.comp_contMDiffOn
      (contMDiffOn_coordChangeL (IB := IB) (n := n) e e')).congr fun b hb ↦ ?_
    simp [L, e.coordChangeL_real_complexification e' hb, ContinuousLinearMap.complexifyₗᵢ_apply]

section RegularityCharacterization

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- A map into the total space of `fun x ↦ ℂ ⊗[ℝ] E x` is `C^n` within `s` at `x₀` if and only if
its fibrewise real and imaginary parts into `TotalSpace F E` are `C^n` within `s` at `x₀`. -/
theorem contMDiffWithinAt_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, Complexification F)) n f s x₀ ↔
      ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s x₀ ∧
      ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s x₀ := by
  simp only [Bundle.contMDiffWithinAt_totalSpace_iff, ← and_and_left]
  refine and_congr_right fun hb ↦ ?_
  have hx₀ : (f x₀).proj ∈ (trivializationAt F E (f x₀).proj).baseSet :=
    mem_baseSet_trivializationAt F E (f x₀).proj
  have he : ∀ᶠ y in 𝓝[s] x₀, (f y).proj ∈ (trivializationAt F E (f x₀).proj).baseSet :=
    hb.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt F E (f x₀).proj).open_baseSet.mem_nhds hx₀)
  constructor
  · intro hf
    refine ⟨((Complexification.reCLM F).contDiff.comp_contMDiffWithinAt hf).congr_of_eventuallyEq
      (he.mono fun y hy ↦ by simp [trivializationAt_complexification,
        Trivialization.linearMapAt_apply, hy])
      (by simp [trivializationAt_complexification, Trivialization.linearMapAt_apply, hx₀]),
      ((Complexification.imCLM F).contDiff.comp_contMDiffWithinAt hf).congr_of_eventuallyEq
      (he.mono fun y hy ↦ by simp [trivializationAt_complexification,
        Trivialization.linearMapAt_apply, hy])
      (by simp [trivializationAt_complexification, Trivialization.linearMapAt_apply, hx₀])⟩
  · rintro ⟨hre, him⟩
    refine (((Complexification.equivProd F).symm :
      F × F →L[ℝ] Complexification F).contDiff.comp_contMDiffWithinAt
        (hre.prodMk_space him)).congr_of_eventuallyEq
      (he.mono fun y hy ↦ by
        ext <;> simp [trivializationAt_complexification, Trivialization.linearMapAt_apply, hy])
      (by ext <;> simp [trivializationAt_complexification, Trivialization.linearMapAt_apply, hx₀])

/-- Pointwise version of `contMDiffWithinAt_complexification_totalSpace_iff`. -/
theorem contMDiffAt_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, Complexification F)) n f x₀ ↔
      ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) x₀ ∧
      ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) x₀ := by
  simp_rw [← contMDiffWithinAt_univ, contMDiffWithinAt_complexification_totalSpace_iff]

/-- Domain version of `contMDiffWithinAt_complexification_totalSpace_iff`. -/
theorem contMDiffOn_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {s : Set M} :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, Complexification F)) n f s ↔
      ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s ∧
      ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s := by
  simp only [ContMDiffOn, contMDiffWithinAt_complexification_totalSpace_iff, forall_and]

/-- Global version of `contMDiffWithinAt_complexification_totalSpace_iff`. -/
theorem contMDiff_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} :
    ContMDiff IM (IB.prod 𝓘(ℝ, Complexification F)) n f ↔
      ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) ∧
      ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) := by
  simp only [ContMDiff, contMDiffAt_complexification_totalSpace_iff, forall_and]

/-- A section `s : ∀ x, ℂ ⊗[ℝ] E x` is `C^n` if and only if its real and imaginary parts are `C^n`
sections of `E`. -/
theorem contMDiff_complexification_section_iff {s : ∀ x, ℂ ⊗[ℝ] E x} :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F)) n
        (fun x ↦ TotalSpace.mk' (Complexification F) x (s x)) ↔
      ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ realPart (E x) (s x)) ∧
      ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ imaginaryPart (E x) (s x)) :=
  contMDiff_complexification_totalSpace_iff

end RegularityCharacterization

variable (IB F n E) in
/-- Fibrewise complex conjugation `z ⊗ₜ v ↦ conj z ⊗ₜ v` as an involutive `C^n` diffeomorphism of
the total space of `fun x ↦ ℂ ⊗[ℝ] E x`, requiring neither `ContMDiffVectorBundle` nor finite rank
nor fibrewise topological-group hypotheses. -/
def tmulConjDiffeomorph :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₘ^n⟮
      IB.prod 𝓘(ℝ, Complexification F), IB.prod 𝓘(ℝ, Complexification F)⟯
      TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) :=
  have hcont : ContMDiff (IB.prod 𝓘(ℝ, Complexification F)) (IB.prod 𝓘(ℝ, Complexification F)) n
      (fun p : TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ↦
        (⟨p.proj, tmulConj (E p.proj) p.2⟩ :
          TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x)) := by
    obtain ⟨hre, him⟩ := (contMDiff_complexification_totalSpace_iff (F := F) (E := E)).mp
      (contMDiff_id (I := IB.prod 𝓘(ℝ, Complexification F)) (n := n))
    refine (contMDiff_complexification_totalSpace_iff (F := F) (E := E)).mpr
      ⟨by simpa using hre, ?_⟩
    simpa [neg_one_smul] using (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace him
  { toFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
    invFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
    left_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
    right_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
    contMDiff_toFun := hcont, contMDiff_invFun := hcont }

variable (IB F n E) in
/-- The real/imaginary-part `C^n` diffeomorphism between the total space of `fun x ↦ ℂ ⊗[ℝ] E x`
and the total space of `E ×ᵇ E`. -/
def complexificationTotalSpaceDiffeomorphProd :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₘ^n⟮
      IB.prod 𝓘(ℝ, Complexification F), IB.prod 𝓘(ℝ, F × F)⟯
      TotalSpace (F × F) (E ×ᵇ E) where
  toFun p := ⟨p.proj, complexificationEquivProd (E p.proj) p.2⟩
  invFun p := ⟨p.proj, (complexificationEquivProd (E p.proj)).symm p.2⟩
  left_inv := fun ⟨x, u⟩ ↦
    congrArg (TotalSpace.mk x) ((complexificationEquivProd (E x)).symm_apply_apply u)
  right_inv := fun ⟨x, v⟩ ↦
    congrArg (TotalSpace.mk x) ((complexificationEquivProd (E x)).apply_symm_apply v)
  contMDiff_toFun := by
    rw [Equiv.coe_fn_mk]; intro p₀
    let e₀ := trivializationAt F E p₀.proj
    obtain ⟨hb, hp₀⟩ := Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, Complexification F)) (n := n) (x := p₀))
    refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨hb, (((Complexification.equivProd F :
      Complexification F →L[ℝ] F × F).contDiff (n := n)).comp_contMDiffAt
        hp₀).congr_of_eventuallyEq ?_⟩
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E p₀.proj))] with p hp
    have hp' : p.proj ∈ e₀.baseSet := hp
    dsimp only [Function.comp_def, id_eq]
    rw [FiberBundle.trivializationAt_prod F E F E p₀.proj,
      complexificationEquivProd_apply, Trivialization.prod_apply' ℝ hp' hp']
    simp [e₀, trivializationAt_complexification,
      (trivializationAt F E p₀.proj).coe_linearMapAt_of_mem hp']
  contMDiff_invFun := by
    rw [Equiv.coe_fn_symm_mk]; intro p₀
    let e₀ := trivializationAt F E p₀.proj
    obtain ⟨hb, hp₀⟩ := Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, F × F)) (n := n) (x := p₀))
    refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨hb, ((((Complexification.equivProd F).symm :
      F × F →L[ℝ] Complexification F).contDiff (n := n)).comp_contMDiffAt
        hp₀).congr_of_eventuallyEq ?_⟩
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E p₀.proj))] with ⟨x, v₁, v₂⟩ hp
    have hx : x ∈ e₀.baseSet := hp
    dsimp only [Function.comp_def, id_eq]
    rw [FiberBundle.trivializationAt_prod F E F E p₀.proj, Trivialization.prod_apply' ℝ hx hx]
    ext <;> simp [e₀, trivializationAt_complexification,
      (trivializationAt F E p₀.proj).coe_linearMapAt_of_mem hx]

@[simp] theorem tmulConjDiffeomorph_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    tmulConjDiffeomorph IB F n E p = ⟨p.proj, tmulConj (E p.proj) p.2⟩ := (rfl)
@[simp] theorem tmulConjDiffeomorph_symm :
    (tmulConjDiffeomorph IB F n E).symm = tmulConjDiffeomorph IB F n E := (rfl)
@[simp] theorem toHomeomorph_tmulConjDiffeomorph :
    (tmulConjDiffeomorph IB F n E).toHomeomorph = tmulConjHomeomorph F E :=
  Homeomorph.ext fun _ ↦ by simp
@[simp] theorem complexificationTotalSpaceDiffeomorphProd_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    complexificationTotalSpaceDiffeomorphProd IB F n E p =
      ⟨p.proj, (realPart (E p.proj) p.2, imaginaryPart (E p.proj) p.2)⟩ :=
  congrArg (TotalSpace.mk p.proj) (complexificationEquivProd_apply p.2)
@[simp] theorem complexificationTotalSpaceDiffeomorphProd_symm_apply
    (p : TotalSpace (F × F) (E ×ᵇ E)) :
    (complexificationTotalSpaceDiffeomorphProd IB F n E).symm p =
      ⟨p.proj, 1 ⊗ₜ[ℝ] p.2.1 + Complex.I ⊗ₜ[ℝ] p.2.2⟩ :=
  congrArg (TotalSpace.mk p.proj) (complexificationEquivProd_symm_apply p.2)
theorem proj_complexificationTotalSpaceDiffeomorphProd
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    (complexificationTotalSpaceDiffeomorphProd IB F n E p).proj = p.proj := (rfl)
@[simp] theorem toHomeomorph_complexificationTotalSpaceDiffeomorphProd :
    (complexificationTotalSpaceDiffeomorphProd IB F n E).toHomeomorph =
      complexificationTotalSpaceHomeomorphProd F E :=
  Homeomorph.ext fun _ ↦ by simp

variable [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]

/-- Fibrewise real part is a `C^n` section of `fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y`. -/
theorem contMDiff_realPartCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (realPartCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_realPartCLM a hx

/-- Fibrewise imaginary part is a `C^n` section of `fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y`. -/
theorem contMDiff_imaginaryPartCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (imaginaryPartCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_imaginaryPartCLM a hx

/-- Real inclusion `v ↦ 1 ⊗ₜ v` is a `C^n` section of `fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y`. -/
theorem contMDiff_oneTmulCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
        (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (oneTmulCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_oneTmulCLM a hx

/-- Imaginary inclusion `v ↦ I ⊗ₜ v` is a `C^n` section of `fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y`. -/
theorem contMDiff_ITmulCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
        (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (ITmulCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_ITmulCLM a hx

/-- Fibrewise conjugation is a `C^n` section of the real endomorphism bundle. -/
theorem contMDiff_tmulConjCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] Complexification F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] ℂ ⊗[ℝ] E y) x (tmulConjCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦
    inCoordinates_tmulConjCLM a (by rwa [baseSet_trivializationAt_complexification] at hx)

/-- `(realPart, imaginaryPart)` is a `C^n` section of `fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y`. -/
theorem contMDiff_complexificationEquivProd_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] F × F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F × F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y) x
        (complexificationEquivProd (E x) : ℂ ⊗[ℝ] E x →L[ℝ] (E ×ᵇ E) x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦
    inCoordinates_complexificationEquivProd a
      (by rwa [baseSet_trivializationAt_complexification] at hx)

/-- `(v, w) ↦ 1 ⊗ₜ v + I ⊗ₜ w` is a `C^n` section of `fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y`. -/
theorem contMDiff_complexificationEquivProd_symm_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, (F × F) →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' ((F × F) →L[ℝ] Complexification F)
        (E := fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y) x
        ((complexificationEquivProd (E x)).symm : (E ×ᵇ E) x →L[ℝ] ℂ ⊗[ℝ] E x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦
    inCoordinates_complexificationEquivProd_symm a
      (by rwa [baseSet_trivializationAt_complexification] at hx)

end ComplexificationBundle

end TauCeti

/-! ### Global `C^n` sections of the complexified bundle -/

namespace ContMDiffSection

open TauCeti

section ComplexificationSections

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners ℝ EB HB) {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ∞ω)
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- Fibrewise real part as an `ℝ`-linear map from `C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x` to `C^n`
sections of `E`. -/
def realPartLinearMap :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ →ₗ[ℝ] Cₛ^n⟮IB; F, E⟯ where
  toFun σ := ⟨fun x ↦ realPart (E x) (σ x),
    ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).1⟩
  map_add' σ τ := ext fun x ↦ map_add (realPart (E x)) (σ x) (τ x)
  map_smul' r σ := ext fun x ↦ map_smul (realPart (E x)) r (σ x)

/-- Fibrewise imaginary part as an `ℝ`-linear map from `C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x` to
`C^n` sections of `E`. -/
def imaginaryPartLinearMap :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ →ₗ[ℝ] Cₛ^n⟮IB; F, E⟯ where
  toFun σ := ⟨fun x ↦ imaginaryPart (E x) (σ x),
    ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).2⟩
  map_add' σ τ := ext fun x ↦ map_add (imaginaryPart (E x)) (σ x) (τ x)
  map_smul' r σ := ext fun x ↦ map_smul (imaginaryPart (E x)) r (σ x)

/-- Real inclusion `s ↦ (x ↦ 1 ⊗ₜ s x)` as an `ℝ`-linear map on `C^n` sections. -/
def oneTmulLinearMap :
    Cₛ^n⟮IB; F, E⟯ →ₗ[ℝ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ where
  toFun s := ⟨fun x ↦ 1 ⊗ₜ[ℝ] s x, (contMDiff_complexification_section_iff (F := F)).mpr
    ⟨by simpa using s.contMDiff, by simpa using (0 : Cₛ^n⟮IB; F, E⟯).contMDiff⟩⟩
  map_add' s t := ext fun x ↦ TensorProduct.tmul_add 1 (s x) (t x)
  map_smul' r s := ext fun x ↦ TensorProduct.tmul_smul r (1 : ℂ) (s x)

/-- Imaginary inclusion `s ↦ (x ↦ I ⊗ₜ s x)` as an `ℝ`-linear map on `C^n` sections. -/
def ITmulLinearMap :
    Cₛ^n⟮IB; F, E⟯ →ₗ[ℝ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ where
  toFun s := ⟨fun x ↦ Complex.I ⊗ₜ[ℝ] s x, (contMDiff_complexification_section_iff (F := F)).mpr
    ⟨by simpa using (0 : Cₛ^n⟮IB; F, E⟯).contMDiff, by simpa using s.contMDiff⟩⟩
  map_add' s t := ext fun x ↦ TensorProduct.tmul_add Complex.I (s x) (t x)
  map_smul' r s := ext fun x ↦ TensorProduct.tmul_smul r Complex.I (s x)

section BasicSimp

variable {IB F n E}

@[simp] theorem realPartLinearMap_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) (x : B) :
    realPartLinearMap IB F n E σ x = realPart (E x) (σ x) := (rfl)
@[simp] theorem imaginaryPartLinearMap_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) (x : B) :
    imaginaryPartLinearMap IB F n E σ x = imaginaryPart (E x) (σ x) := (rfl)
@[simp] theorem oneTmulLinearMap_apply (s : Cₛ^n⟮IB; F, E⟯) (x : B) :
    oneTmulLinearMap IB F n E s x = 1 ⊗ₜ[ℝ] s x := (rfl)
@[simp] theorem ITmulLinearMap_apply (s : Cₛ^n⟮IB; F, E⟯) (x : B) :
    ITmulLinearMap IB F n E s x = Complex.I ⊗ₜ[ℝ] s x := (rfl)
theorem I_smul_oneTmulLinearMap (s : Cₛ^n⟮IB; F, E⟯) :
    Complex.I • oneTmulLinearMap IB F n E s = ITmulLinearMap IB F n E s :=
  ext fun x ↦ by simp [TensorProduct.smul_tmul']
@[simp] theorem realPartLinearMap_oneTmulLinearMap (s : Cₛ^n⟮IB; F, E⟯) :
    realPartLinearMap IB F n E (oneTmulLinearMap IB F n E s) = s := ext fun x ↦ by simp
@[simp] theorem realPartLinearMap_ITmulLinearMap (s : Cₛ^n⟮IB; F, E⟯) :
    realPartLinearMap IB F n E (ITmulLinearMap IB F n E s) = 0 := ext fun x ↦ by simp
@[simp] theorem imaginaryPartLinearMap_oneTmulLinearMap (s : Cₛ^n⟮IB; F, E⟯) :
    imaginaryPartLinearMap IB F n E (oneTmulLinearMap IB F n E s) = 0 := ext fun x ↦ by simp
@[simp] theorem imaginaryPartLinearMap_ITmulLinearMap (s : Cₛ^n⟮IB; F, E⟯) :
    imaginaryPartLinearMap IB F n E (ITmulLinearMap IB F n E s) = s := ext fun x ↦ by simp
@[simp] theorem oneTmulLinearMap_realPartLinearMap_add_ITmulLinearMap_imaginaryPartLinearMap
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    oneTmulLinearMap IB F n E (realPartLinearMap IB F n E σ) +
      ITmulLinearMap IB F n E (imaginaryPartLinearMap IB F n E σ) = σ :=
  ext fun x ↦ by simp

end BasicSimp

/-- Fibrewise complex conjugation `z ⊗ₜ v ↦ conj z ⊗ₜ v` as a conjugate-linear equivalence on
`C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x`. -/
def conjEquiv :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ ≃ₗ⋆[ℂ]
      Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ :=
  let c (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
      Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ :=
    ⟨fun x ↦ tmulConj (E x) (σ x), (contMDiff_complexification_section_iff (F := F)).mpr
      ⟨by simpa using ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).1,
       by simpa using
         ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).2.neg_section⟩⟩
  { toFun := c
    invFun := c
    map_add' σ τ := ext fun x ↦ map_add (tmulConj (E x)) (σ x) (τ x)
    map_smul' z σ := ext fun x ↦ map_smulₛₗ (tmulConj (E x)) z (σ x)
    left_inv σ := ext fun x ↦ tmulConj_tmulConj (E x) (σ x)
    right_inv σ := ext fun x ↦ tmulConj_tmulConj (E x) (σ x) }

/-- Real-linear isomorphism between `C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x` and pairs of `C^n`
sections of `E`, given by `(realPartLinearMap, imaginaryPartLinearMap)`. -/
def complexificationEquivProd :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ ≃ₗ[ℝ]
      Cₛ^n⟮IB; F, E⟯ × Cₛ^n⟮IB; F, E⟯ where
  toFun σ := (realPartLinearMap IB F n E σ, imaginaryPartLinearMap IB F n E σ)
  map_add' σ τ := Prod.ext (map_add _ σ τ) (map_add _ σ τ)
  map_smul' r σ := Prod.ext (map_smul _ r σ) (map_smul _ r σ)
  invFun p := oneTmulLinearMap IB F n E p.1 + ITmulLinearMap IB F n E p.2
  left_inv σ := by simp
  right_inv := fun ⟨_, _⟩ ↦ Prod.ext (by simp) (by simp)

/-- The canonical `ℂ`-linear isomorphism
`ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯ ≃ₗ[ℂ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯` sending `z ⊗ₜ s`
to `x ↦ z ⊗ₜ s x` and decomposing `σ` as `1 ⊗ₜ Re σ + I ⊗ₜ Im σ`. -/
def complexificationEquiv :
    ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯ ≃ₗ[ℂ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ :=
  { (oneTmulLinearMap IB F n E).liftBaseChange ℂ with
    toFun := (oneTmulLinearMap IB F n E).liftBaseChange ℂ
    invFun σ :=
      1 ⊗ₜ[ℝ] realPartLinearMap IB F n E σ + Complex.I ⊗ₜ[ℝ] imaginaryPartLinearMap IB F n E σ
    left_inv u := by
      obtain ⟨s, t, rfl⟩ := exists_one_tmul_add_I_tmul u
      simp [I_smul_oneTmulLinearMap]
    right_inv σ := by simp [I_smul_oneTmulLinearMap] }

variable {IB F n E}

@[simp] theorem conjEquiv_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) (x : B) :
    conjEquiv IB F n E σ x = tmulConj (E x) (σ x) := (rfl)
@[simp] theorem conjEquiv_symm : (conjEquiv IB F n E).symm = conjEquiv IB F n E := (rfl)
@[simp] theorem complexificationEquivProd_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    complexificationEquivProd IB F n E σ =
      (realPartLinearMap IB F n E σ, imaginaryPartLinearMap IB F n E σ) := (rfl)
@[simp] theorem complexificationEquivProd_symm_apply
    (p : Cₛ^n⟮IB; F, E⟯ × Cₛ^n⟮IB; F, E⟯) :
    (complexificationEquivProd IB F n E).symm p =
      oneTmulLinearMap IB F n E p.1 + ITmulLinearMap IB F n E p.2 := (rfl)
/-- The closed support of a complexified section is exactly the union of its real and
imaginary coordinate supports. No smooth-bundle assumption is needed. -/
theorem tsupport_complexificationEquivProd
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    σ.tsupport = (complexificationEquivProd IB F n E σ).1.tsupport ∪
      (complexificationEquivProd IB F n E σ).2.tsupport := by
  simp only [complexificationEquivProd_apply]
  rw [tsupport_def, tsupport_def, tsupport_def, ← closure_union]
  congr 1
  ext x
  have hz : σ x = 0 ↔ realPart (E x) (σ x) = 0 ∧ imaginaryPart (E x) (σ x) = 0 := by
    simpa only [map_zero] using (complexification_ext_iff (u := σ x) (v := 0))
  simpa only [Set.mem_ofPred_eq, Set.mem_union, realPartLinearMap_apply,
    imaginaryPartLinearMap_apply] using hz.not.trans not_and_or

/-- Real projection can only decrease a section's closed support. -/
theorem tsupport_realPartLinearMap_subset
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    (realPartLinearMap IB F n E σ).tsupport ⊆ σ.tsupport := by
  rw [tsupport_complexificationEquivProd]
  simp only [complexificationEquivProd_apply]
  exact subset_union_left

/-- Imaginary projection can only decrease a section's closed support. -/
theorem tsupport_imaginaryPartLinearMap_subset
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    (imaginaryPartLinearMap IB F n E σ).tsupport ⊆ σ.tsupport := by
  rw [tsupport_complexificationEquivProd]
  simp only [complexificationEquivProd_apply]
  exact subset_union_right

/-- Including a real section preserves its exact closed support. -/
@[simp] theorem tsupport_oneTmulLinearMap (σ : Cₛ^n⟮IB; F, E⟯) :
    (oneTmulLinearMap IB F n E σ).tsupport = σ.tsupport := by
  rw [tsupport_complexificationEquivProd]
  simp only [complexificationEquivProd_apply, realPartLinearMap_oneTmulLinearMap,
    imaginaryPartLinearMap_oneTmulLinearMap, tsupport_zero, Set.union_empty]

/-- Including a real section in the imaginary summand preserves its exact closed support. -/
@[simp] theorem tsupport_ITmulLinearMap (σ : Cₛ^n⟮IB; F, E⟯) :
    (ITmulLinearMap IB F n E σ).tsupport = σ.tsupport := by
  rw [tsupport_complexificationEquivProd]
  simp only [complexificationEquivProd_apply, realPartLinearMap_ITmulLinearMap,
    imaginaryPartLinearMap_ITmulLinearMap, tsupport_zero, Set.empty_union]

theorem complexificationEquiv_tmul_eq_smul (z : ℂ) (s : Cₛ^n⟮IB; F, E⟯) :
    complexificationEquiv IB F n E (z ⊗ₜ[ℝ] s) = z • oneTmulLinearMap IB F n E s :=
  LinearMap.liftBaseChange_tmul ℂ (oneTmulLinearMap IB F n E) z s
@[simp] theorem complexificationEquiv_tmul (z : ℂ) (s : Cₛ^n⟮IB; F, E⟯) (x : B) :
    complexificationEquiv IB F n E (z ⊗ₜ[ℝ] s) x = z ⊗ₜ[ℝ] s x := by
  simp [complexificationEquiv_tmul_eq_smul, TensorProduct.smul_tmul']
@[simp] theorem complexificationEquiv_symm_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    (complexificationEquiv IB F n E).symm σ =
      1 ⊗ₜ[ℝ] realPartLinearMap IB F n E σ +
        Complex.I ⊗ₜ[ℝ] imaginaryPartLinearMap IB F n E σ := (rfl)
@[simp] theorem realPartLinearMap_complexificationEquiv (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) :
    realPartLinearMap IB F n E (complexificationEquiv IB F n E u) =
      realPart Cₛ^n⟮IB; F, E⟯ u := by
  obtain ⟨s, t, rfl⟩ := exists_one_tmul_add_I_tmul u; ext x; simp
@[simp] theorem imaginaryPartLinearMap_complexificationEquiv (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) :
    imaginaryPartLinearMap IB F n E (complexificationEquiv IB F n E u) =
      imaginaryPart Cₛ^n⟮IB; F, E⟯ u := by
  obtain ⟨s, t, rfl⟩ := exists_one_tmul_add_I_tmul u; ext x; simp
@[simp] theorem realPart_complexificationEquiv_apply (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) (x : B) :
    realPart (E x) (complexificationEquiv IB F n E u x) = realPart Cₛ^n⟮IB; F, E⟯ u x := by
  rw [← realPartLinearMap_apply, realPartLinearMap_complexificationEquiv]
@[simp] theorem imaginaryPart_complexificationEquiv_apply (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) (x : B) :
    imaginaryPart (E x) (complexificationEquiv IB F n E u x) =
      imaginaryPart Cₛ^n⟮IB; F, E⟯ u x := by
  rw [← imaginaryPartLinearMap_apply, imaginaryPartLinearMap_complexificationEquiv]
@[simp] theorem conjEquiv_complexificationEquiv (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) :
    conjEquiv IB F n E (complexificationEquiv IB F n E u) =
      complexificationEquiv IB F n E (tmulConj Cₛ^n⟮IB; F, E⟯ u) := by
  obtain ⟨s, t, rfl⟩ := exists_one_tmul_add_I_tmul u; ext x; simp [TensorProduct.neg_tmul]

end ComplexificationSections

/-! ### Supported real/complex section comparisons -/

section SupportedComplexificationSections

open TopologicalSpace

variable {n : ℕ∞}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]

/-- The real projection on native compactly supported sections, preserving original fibres. -/
def CompactlySupported.realPart : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)
  →ₗ[ℝ]
    compactlySupported I F n V :=
  (realPartLinearMap I F n V).restrict fun σ hσ ↦ by
    apply mem_compactlySupported.mpr
    apply (mem_compactlySupported.mp hσ).of_isClosed_subset (isClosed_tsupport _)
    exact tsupport_realPartLinearMap_subset σ

/-- The CompactlySupported.ITmul projection on native compactly supported sections. -/
def CompactlySupported.imaginaryPart : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ]
  V x) →ₗ[ℝ]
    compactlySupported I F n V :=
  (imaginaryPartLinearMap I F n V).restrict fun σ hσ ↦ by
    apply mem_compactlySupported.mpr
    apply (mem_compactlySupported.mp hσ).of_isClosed_subset (isClosed_tsupport _)
    exact tsupport_imaginaryPartLinearMap_subset σ

/-- Real inclusion, restricting the existing native all-section map. -/
def CompactlySupported.oneTmul : compactlySupported I F n V →ₗ[ℝ]
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) :=
  (oneTmulLinearMap I F n V).restrict fun σ hσ ↦ by
    simpa only [mem_compactlySupported, tsupport_oneTmulLinearMap] using hσ

/-- Imaginary inclusion, restricting the existing native all-section map. -/
def CompactlySupported.ITmul : compactlySupported I F n V →ₗ[ℝ]
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) :=
  (ITmulLinearMap I F n V).restrict fun σ hσ ↦ by
    simpa only [mem_compactlySupported, tsupport_ITmulLinearMap] using hσ

/-- Forgetting support recovers the native all-section real projection. -/
@[simp] theorem CompactlySupported.coe_realPart (σ : compactlySupported I (Complexification F) n
    (fun x ↦ ℂ ⊗[ℝ] V x)) : (CompactlySupported.realPart σ).val = realPartLinearMap I F n V σ.val
      := by
  simp only [CompactlySupported.realPart, LinearMap.coe_restrict_apply]

/-- Forgetting support recovers the native all-section imaginary projection. -/
@[simp] theorem CompactlySupported.coe_imaginaryPart (σ : compactlySupported I (Complexification
  F) n
    (fun x ↦ ℂ ⊗[ℝ] V x)) : (CompactlySupported.imaginaryPart σ).val = imaginaryPartLinearMap I F
      n V σ.val := by
  simp only [CompactlySupported.imaginaryPart, LinearMap.coe_restrict_apply]

/-- Forgetting support recovers the native all-section real inclusion. -/
@[simp] theorem CompactlySupported.coe_oneTmul (σ : compactlySupported I F n V) :
    (CompactlySupported.oneTmul σ).val = oneTmulLinearMap I F n V σ.val := by
  simp only [CompactlySupported.oneTmul, LinearMap.coe_restrict_apply]

/-- Forgetting support recovers the native all-section imaginary inclusion. -/
@[simp] theorem CompactlySupported.coe_ITmul (σ : compactlySupported I F n V) :
    (CompactlySupported.ITmul σ).val = ITmulLinearMap I F n V σ.val := by
  simp only [CompactlySupported.ITmul, LinearMap.coe_restrict_apply]

/-- Real algebraic identification of compact tests with pairs of original real tests. -/
def CompactlySupported.complexificationEquivProd : compactlySupported I (Complexification F) n
  (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₗ[ℝ]
    compactlySupported I F n V × compactlySupported I F n V :=
  { CompactlySupported.realPart.prod CompactlySupported.imaginaryPart with
    invFun := fun p ↦ CompactlySupported.oneTmul p.1 + CompactlySupported.ITmul p.2
    left_inv := by
      intro φ
      apply Subtype.ext
      ext x
      simp only [CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply,
        CompactlySupported.coe_ITmul, ITmulLinearMap_apply,
        Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply]
      simpa only [LinearMap.toFun_eq_coe, LinearMap.prod_apply, Function.prod,
        CompactlySupported.coe_realPart, realPartLinearMap_apply,
          CompactlySupported.coe_imaginaryPart, imaginaryPartLinearMap_apply] using
        one_tmul_realPart_add_I_tmul_imaginaryPart (V x) (φ.val x)
    right_inv := by
      intro p
      apply Prod.ext <;> apply Subtype.ext <;> ext x <;> simp }

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.complexificationEquivProd_apply
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.complexificationEquivProd φ = (CompactlySupported.realPart φ,
      CompactlySupported.imaginaryPart φ) := by rfl

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.complexificationEquivProd_symm_apply (p : compactlySupported I
  F n V × compactlySupported I F n V) :
    CompactlySupported.complexificationEquivProd.symm p = CompactlySupported.oneTmul p.1 +
      CompactlySupported.ITmul p.2 := by rfl

/-- The closed support is exactly the union of the coordinate supports. -/
theorem CompactlySupported.tsupport_eq_union_realPart_imaginaryPart
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    φ.val.tsupport = (CompactlySupported.realPart φ).val.tsupport ∪
      (CompactlySupported.imaginaryPart φ).val.tsupport := by
  simpa only [ContMDiffSection.complexificationEquivProd_apply, CompactlySupported.coe_realPart,
    CompactlySupported.coe_imaginaryPart] using
    ContMDiffSection.tsupport_complexificationEquivProd φ.val

/-- A support bound holds exactly when it holds for both original real coordinates. -/
theorem SupportedIn.mem_iff_complexificationEquivProd (K : Set M)
    (φ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    φ ∈ supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ↔
      ContMDiffSection.complexificationEquivProd I F n V φ ∈ (supportedIn I F n V K).prod
        (supportedIn I F n V K) := by
  simp only [mem_supportedIn, Submodule.mem_prod, ContMDiffSection.complexificationEquivProd_apply]
  rw [tsupport_complexificationEquivProd]
  simp only [ContMDiffSection.complexificationEquivProd_apply, union_subset_iff]

/-- The real pair identification on the native prescribed-support submodules. -/
def SupportedIn.complexificationEquivProd (K : Set M) :
    supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ≃ₗ[ℝ]
      supportedIn I F n V K × supportedIn I F n V K :=
  ((ContMDiffSection.complexificationEquivProd I F n V).ofSubmodules _
    ((supportedIn I F n V K).prod (supportedIn I F n V K)) (by
      ext p
      constructor
      · rintro ⟨φ, hφ, rfl⟩
        exact (SupportedIn.mem_iff_complexificationEquivProd (n := n) K φ).mp hφ
      · intro hp
        refine ⟨(ContMDiffSection.complexificationEquivProd I F n V).symm p, ?_,
          (ContMDiffSection.complexificationEquivProd I F n V).apply_symm_apply p⟩
        exact (SupportedIn.mem_iff_complexificationEquivProd (n := n) K _).mpr (by simpa using
          hp))).trans
    (Submodule.prodEquiv _ _)

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.coe_complexificationEquivProd_apply (K : Set M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    ((SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ).1.val,
      (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ).2.val) =
      ContMDiffSection.complexificationEquivProd I F n V φ.val := by rfl


/-- Support forgetting into the exact real module underlying the native complex section module. -/
def CompactlySupported.toComplexSectionRealLinearMap :
    @LinearMap ℝ ℝ _ _ (RingHom.id ℝ)
      (compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x))
      Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ _ _ _
      (Module.complexToReal Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) where
  toFun φ := φ.val
  map_add' φ ψ := Submodule.coe_add φ ψ
  map_smul' r φ := by
    rw [Submodule.coe_smul]
    -- The target is exactly Module.complexToReal; compare the original real action with
    -- its complex coefficient action before the induced real action.
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r φ.val).trans (Complex.coe_smul r φ.val)

/-- The native real-points submodule pulled back along support forgetting. -/
def CompactlySupported.realPointsConj : Submodule ℝ
    (compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :=
  (TauCeti.realPoints (ContMDiffSection.conjEquiv I F n V).toLinearMap).comap
    (CompactlySupported.toComplexSectionRealLinearMap (n := n) (I := I) (F := F) (V := V))

/-- Membership is the stated native fixed-point condition. -/
@[simp] theorem CompactlySupported.mem_realPointsConj
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    φ ∈ CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V) ↔
      ContMDiffSection.conjEquiv I F n V φ.val = φ.val := by
  simp [CompactlySupported.realPointsConj, TauCeti.mem_realPoints,
    CompactlySupported.toComplexSectionRealLinearMap]

/-- Real tests identify with the pullback of the native real-points submodule. -/
def CompactlySupported.realPointsConjEquiv : compactlySupported I F n V ≃ₗ[ℝ]
    CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V) where
  toFun φ := ⟨CompactlySupported.oneTmul φ, by
    rw [CompactlySupported.mem_realPointsConj]
    ext x
    simp [ContMDiffSection.conjEquiv_apply]⟩
  invFun φ := CompactlySupported.realPart φ.val
  left_inv φ := by
    apply Subtype.ext
    ext x
    simp
  right_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    have hfix := congrArg (fun σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ ↦ σ x)
      ((CompactlySupported.mem_realPointsConj φ.val).mp φ.property)
    have hfix' : tmulConj (V x) (φ.val.val x) = φ.val.val x := by
      simpa only [ContMDiffSection.conjEquiv_apply] using hfix
    obtain ⟨v, hv⟩ := (tmulConj_eq_self_iff (V x) (φ.val.val x)).mp hfix'
    simp [hv]
  map_add' φ ψ := Subtype.ext (map_add CompactlySupported.oneTmul φ ψ)
  map_smul' r φ := Subtype.ext (map_smul CompactlySupported.oneTmul r φ)

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.coe_realPointsConjEquiv_apply (φ : compactlySupported I F n V) :
    (CompactlySupported.realPointsConjEquiv (n := n) (I := I) (F := F) (V := V) φ).val =
      CompactlySupported.oneTmul φ := by rfl

/-- The inverse fixed-point comparison is the existing compact-test real projection. -/
@[simp] theorem CompactlySupported.realPointsConjEquiv_symm_apply
    (φ : CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V)) :
    (CompactlySupported.realPointsConjEquiv (n := n) (I := I) (F := F) (V := V)).symm φ =
      CompactlySupported.realPart φ.val := by rfl

/-- Real projection satisfies the stated coordinate law. -/
@[simp] theorem CompactlySupported.realPart_oneTmul (φ : compactlySupported I F n V) :
  CompactlySupported.realPart (n := n) (CompactlySupported.oneTmul φ) = φ := by
  apply Subtype.ext
  ext x
  simp

/-- Imaginary projection satisfies the stated coordinate law. -/
@[simp] theorem CompactlySupported.imaginaryPart_oneTmul (φ : compactlySupported I F n V) :
  CompactlySupported.imaginaryPart (n := n) (CompactlySupported.oneTmul φ) = 0 := by
  apply Subtype.ext
  ext x
  simp

/-- Real projection satisfies the stated coordinate law. -/
@[simp] theorem CompactlySupported.realPart_ITmul (φ : compactlySupported I F n V) :
  CompactlySupported.realPart (n := n) (CompactlySupported.ITmul φ) = 0 := by
  apply Subtype.ext
  ext x
  simp

/-- Imaginary projection satisfies the stated coordinate law. -/
@[simp] theorem CompactlySupported.imaginaryPart_ITmul (φ : compactlySupported I F n V) :
  CompactlySupported.imaginaryPart (n := n) (CompactlySupported.ITmul φ) = φ := by
  apply Subtype.ext
  ext x
  simp

/-- Reconstruction has precisely the union of the two original supports. -/
theorem CompactlySupported.tsupport_complexificationEquivProd_symm (p : compactlySupported I F n V
  × compactlySupported I F n V) :
    (CompactlySupported.complexificationEquivProd.symm p).val.tsupport = p.1.val.tsupport ∪
      p.2.val.tsupport := by
  have h := congrArg (fun q : compactlySupported I F n V × compactlySupported I F n V ↦
      q.1.val.tsupport ∪ q.2.val.tsupport)
        (CompactlySupported.complexificationEquivProd.apply_symm_apply p)
  exact (CompactlySupported.tsupport_eq_union_realPart_imaginaryPart _).trans h

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.complexificationEquivProd_fst_apply (K : Set M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) (x : M) :
    (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ).1.val x =
      TauCeti.realPart (V x) (φ.val x) := by
  simpa only [ContMDiffSection.complexificationEquivProd_apply, realPartLinearMap_apply] using
    congrArg (fun p : Cₛ^n⟮I; F, V⟯ × Cₛ^n⟮I; F, V⟯ ↦ p.1 x)
      (SupportedIn.coe_complexificationEquivProd_apply (n := n) K φ)

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.complexificationEquivProd_snd_apply (K : Set M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) (x : M) :
    (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ).2.val x =
      TauCeti.imaginaryPart (V x) (φ.val x) := by
  simpa only [ContMDiffSection.complexificationEquivProd_apply, imaginaryPartLinearMap_apply] using
    congrArg (fun p : Cₛ^n⟮I; F, V⟯ × Cₛ^n⟮I; F, V⟯ ↦ p.2 x)
      (SupportedIn.coe_complexificationEquivProd_apply (n := n) K φ)

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.complexificationEquivProd_symm_apply (K : Set M)
    (p : supportedIn I F n V K × supportedIn I F n V K) (x : M) :
    ((SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K).symm p).val x =
      1 ⊗ₜ[ℝ] p.1.val x + Complex.I ⊗ₜ[ℝ] p.2.val x := by
  rw [← one_tmul_realPart_add_I_tmul_imaginaryPart (V x)
    (((SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K).symm p).val x)]
  have h := (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V)
    K).apply_symm_apply p
  have hr := congrArg (fun q : supportedIn I F n V K × supportedIn I F n V K ↦ q.1.val x) h
  have hi := congrArg (fun q : supportedIn I F n V K × supportedIn I F n V K ↦ q.2.val x) h
  rw [SupportedIn.complexificationEquivProd_fst_apply] at hr
  rw [SupportedIn.complexificationEquivProd_snd_apply] at hi
  rw [hr, hi]

/-- The same native real-points submodule, now pulled back to the prescribed support stage. -/
def SupportedIn.realPointsConj (K : Compacts M) : Submodule ℝ
    (supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :=
  (TauCeti.realPoints (ContMDiffSection.conjEquiv I F n V).toLinearMap).comap
    ((CompactlySupported.toComplexSectionRealLinearMap (n := n) (I := I) (F := F) (V := V)).comp
      (ofSupportedIn K))

/-- Membership is the stated native fixed-point condition. -/
@[simp] theorem SupportedIn.mem_realPointsConj (K : Compacts M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    φ ∈ SupportedIn.realPointsConj (n := n) (I := I) (F := F) (V := V) K ↔
      ContMDiffSection.conjEquiv I F n V φ.val = φ.val := by
  simp [SupportedIn.realPointsConj, TauCeti.mem_realPoints,
    CompactlySupported.toComplexSectionRealLinearMap]

/-- The original real support stage identifies with the native fixed subspace at that stage. -/
def SupportedIn.realPointsConjEquiv (K : Compacts M) : supportedIn I F n V K ≃ₗ[ℝ]
    SupportedIn.realPointsConj (n := n) (I := I) (F := F) (V := V) K where
  toFun φ := ⟨(SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K).symm
    (φ, 0), by
    rw [SupportedIn.mem_realPointsConj]
    ext x
    simp⟩
  invFun φ := (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ.val).1
  left_inv φ := by simp
  right_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContMDiffSection.ext
    intro x
    let ψ : CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V) :=
      ⟨ofSupportedIn K φ.val, by
        simpa only [CompactlySupported.mem_realPointsConj, ofSupportedIn_apply] using
          (SupportedIn.mem_realPointsConj K φ.val).mp φ.property⟩
    have h := congrArg (fun θ : CompactlySupported.realPointsConj
        (n := n) (I := I) (F := F) (V := V) ↦ θ.val.val x)
      ((CompactlySupported.realPointsConjEquiv (n := n) (I := I)
        (F := F) (V := V)).apply_symm_apply ψ)
    simpa only [CompactlySupported.coe_realPointsConjEquiv_apply,
      CompactlySupported.realPointsConjEquiv_symm_apply, CompactlySupported.coe_oneTmul,
        oneTmulLinearMap_apply,
      CompactlySupported.coe_realPart, realPartLinearMap_apply,
        SupportedIn.complexificationEquivProd_symm_apply,
      SupportedIn.complexificationEquivProd_fst_apply, Submodule.coe_zero,
      ContMDiffSection.coe_zero, Pi.zero_apply, TensorProduct.tmul_zero, add_zero,
      ofSupportedIn_apply, ψ] using h
  map_add' φ ψ := by
    apply Subtype.ext
    simpa using map_add (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V)
      K).symm (φ, 0) (ψ, 0)
  map_smul' r φ := by
    apply Subtype.ext
    simpa using map_smul (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V :=
      V) K).symm r (φ, 0)

/-- The inverse stage fixed-point comparison is its original real coordinate. -/
@[simp] theorem SupportedIn.realPointsConjEquiv_symm_apply (K : Compacts M)
    (φ : SupportedIn.realPointsConj (n := n) (I := I) (F := F) (V := V) K) :
    (SupportedIn.realPointsConjEquiv (n := n) (I := I) (F := F) (V := V) K).symm φ =
      (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ.val).1 :=
  by rfl

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.coe_realPointsConjEquiv_apply (K : Compacts M) (φ : supportedIn I F n
  V K) :
    (SupportedIn.realPointsConjEquiv (n := n) K φ).val = (SupportedIn.complexificationEquivProd (n
      := n) (I := I) (F := F) (V := V) K).symm (φ, 0) := by rfl

/-- The fixed-subspace inclusion commutes with native inclusion of a compact support stage. -/
theorem SupportedIn.realPointsConjEquiv_ofSupportedIn (K : Compacts M) (φ : supportedIn I F n V K) :
    ofSupportedIn K (SupportedIn.realPointsConjEquiv (n := n) K φ).val =
      (CompactlySupported.realPointsConjEquiv (n := n) (ofSupportedIn K φ)).val := by
  apply Subtype.ext
  ext x
  simp [SupportedIn.coe_realPointsConjEquiv_apply, CompactlySupported.realPointsConjEquiv]

/-- The pair map commutes with native inclusion of a compact support stage. -/
 theorem SupportedIn.complexificationEquivProd_ofSupportedIn (K : Compacts M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (ofSupportedIn K (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K
      φ).1,
      ofSupportedIn K (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K
        φ).2) =
      CompactlySupported.complexificationEquivProd (n := n) (ofSupportedIn K φ) := by
  apply Prod.ext <;> apply Subtype.ext <;> apply ContMDiffSection.ext <;> intro x
  · simp only [ofSupportedIn_apply, SupportedIn.complexificationEquivProd_fst_apply,
      CompactlySupported.complexificationEquivProd_apply, CompactlySupported.coe_realPart,
        realPartLinearMap_apply]
  · simp only [ofSupportedIn_apply, SupportedIn.complexificationEquivProd_snd_apply,
      CompactlySupported.complexificationEquivProd_apply, CompactlySupported.coe_imaginaryPart,
        imaginaryPartLinearMap_apply]


/-- Reconstruction commutes with native inclusion of a compact support stage. -/
theorem SupportedIn.complexificationEquivProd_symm_ofSupportedIn (K : Compacts M)
    (p : supportedIn I F n V K × supportedIn I F n V K) :
    ofSupportedIn K ((SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V)
      K).symm p) =
      CompactlySupported.complexificationEquivProd.symm (ofSupportedIn K p.1, ofSupportedIn K p.2)
        := by
  apply CompactlySupported.complexificationEquivProd.injective
  rw [← SupportedIn.complexificationEquivProd_ofSupportedIn]
  simp only [LinearEquiv.apply_symm_apply]

end SupportedComplexificationSections

end ContMDiffSection

namespace TauCeti

variable {XB HB B F G : Type*} [NormedAddCommGroup XB] [NormedSpace ℝ XB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ XB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G]
  {W V : B → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace F W)] [FiberBundle F W] [VectorBundle ℝ F W]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] W x)] [∀ x, IsComplexificationTopology (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace G V)] [FiberBundle G V]
  [∀ x, IsTopologicalAddGroup (V x)]
  {n : ℕ∞ω}

section SmoothExtension

variable [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] [VectorBundle ℂ G V]
  [∀ x, ContinuousConstSMul ℂ (V x)]

local instance : VectorBundle ℝ G V := VectorBundle.restrictScalars ℝ ℂ G V

/-- Complex-linear extension of a smooth real bundle map is smooth on the actual
complexification total space. It is the canonical native base-change lift in each fiber. -/
theorem contMDiff_liftBaseChangeComplex_totalSpace (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V))) :
    ContMDiff (IB.prod 𝓘(ℝ, Complexification F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] W x) ↦
        (⟨p.proj, (i p.proj).liftBaseChangeComplex p.2⟩ : TotalSpace G V)) := by
  obtain ⟨hre, him⟩ := (contMDiff_complexification_totalSpace_iff (IB := IB) (F := F)
    (E := W)).mp (contMDiff_id (I := IB.prod 𝓘(ℝ, Complexification F)) (n := n))
  have hreal := hi.comp hre
  have himag := hi.comp him
  have hI := (contMDiff_const (I := IB.prod 𝓘(ℝ, Complexification F))
    (c := Complex.I)).smul_totalSpace himag
  simpa only [ContinuousLinearMap.liftBaseChangeComplex_apply, Function.comp_def, id_eq] using
    ContMDiff.add_sectionAlong hreal hI

end SmoothExtension

end TauCeti

end
