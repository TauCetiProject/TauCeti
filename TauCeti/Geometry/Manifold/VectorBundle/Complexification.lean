/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Topology.VectorBundle.Complexification

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

/-- Fibrewise multiplication by `Complex.I` is a `C^n` section of `fun x ↦ W x →L[ℝ] W x`. -/
theorem contMDiff_smulIEquiv_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, G →L[ℝ] G)) n (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x (Complex.smulIEquiv (W x) : W x →L[ℝ] W x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv a hx

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

end ContMDiffSection

end
