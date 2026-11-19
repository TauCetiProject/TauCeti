/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Analysis.Distribution.TestFunction.Postcomp

/-!
# Algebra of compactly supported complexified sections

The native compactly supported and prescribed-support submodules identify with real pairs.
These algebraic maps, conjugation and the real quarter-turn are defined at every regularity
order, including analytic order. No topology on the section submodules or chart cover is needed.
The fixed submodules are pullbacks of the existing native `TauCeti.realPoints`.
-/

public section
noncomputable section
open Bundle Set TopologicalSpace TauCeti ContMDiffSection
open scoped ContDiff Manifold TensorProduct Topology Distributions

namespace ContMDiffSection

section Algebra

open TopologicalSpace

variable {n : ℕ∞ω}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]

/-- The closed support of a complexified section is exactly the union of its real and
imaginary coordinate supports. No smooth-bundle assumption is needed. -/
theorem tsupport_eq_union_complexificationEquivProd
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    σ.tsupport = (complexificationEquivProd I F n V σ).1.tsupport ∪
      (complexificationEquivProd I F n V σ).2.tsupport := by
  simp only [complexificationEquivProd_apply]
  rw [tsupport_def, tsupport_def, tsupport_def, ← closure_union]
  congr 1
  ext x
  have hz : σ x = 0 ↔ realPart (V x) (σ x) = 0 ∧ imaginaryPart (V x) (σ x) = 0 := by
    simpa only [map_zero] using (complexification_ext_iff (u := σ x) (v := 0))
  simpa only [Set.mem_ofPred_eq, Set.mem_union, realPartLinearMap_apply,
    imaginaryPartLinearMap_apply] using hz.not.trans not_and_or

/-- Real projection can only decrease a section's closed support. -/
theorem tsupport_realPartLinearMap_subset
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    (realPartLinearMap I F n V σ).tsupport ⊆ σ.tsupport := by
  rw [tsupport_eq_union_complexificationEquivProd]
  simp only [complexificationEquivProd_apply]
  exact subset_union_left

/-- Imaginary projection can only decrease a section's closed support. -/
theorem tsupport_imaginaryPartLinearMap_subset
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    (imaginaryPartLinearMap I F n V σ).tsupport ⊆ σ.tsupport := by
  rw [tsupport_eq_union_complexificationEquivProd]
  simp only [complexificationEquivProd_apply]
  exact subset_union_right

/-- Including a real section preserves its exact closed support. -/
@[simp] theorem tsupport_oneTmulLinearMap (σ : Cₛ^n⟮I; F, V⟯) :
    (oneTmulLinearMap I F n V σ).tsupport = σ.tsupport := by
  rw [tsupport_eq_union_complexificationEquivProd]
  simp only [complexificationEquivProd_apply, realPartLinearMap_oneTmulLinearMap,
    imaginaryPartLinearMap_oneTmulLinearMap, tsupport_zero, Set.union_empty]

/-- Including a real section in the imaginary summand preserves its exact closed support. -/
@[simp] theorem tsupport_ITmulLinearMap (σ : Cₛ^n⟮I; F, V⟯) :
    (ITmulLinearMap I F n V σ).tsupport = σ.tsupport := by
  rw [tsupport_eq_union_complexificationEquivProd]
  simp only [complexificationEquivProd_apply, realPartLinearMap_ITmulLinearMap,
    imaginaryPartLinearMap_ITmulLinearMap, tsupport_zero, Set.empty_union]

/-- The real projection on native compactly supported sections, preserving original fibres. -/
def CompactlySupported.realPart : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)
  →ₗ[ℝ]
    compactlySupported I F n V :=
  (realPartLinearMap I F n V).restrict fun σ hσ ↦ by
    apply mem_compactlySupported.mpr
    apply (mem_compactlySupported.mp hσ).of_isClosed_subset (isClosed_tsupport _)
    exact tsupport_realPartLinearMap_subset σ

/-- The imaginary projection on native compactly supported sections. -/
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
    ContMDiffSection.tsupport_eq_union_complexificationEquivProd φ.val

/-- A support bound holds exactly when it holds for both original real coordinates. -/
theorem SupportedIn.mem_iff_complexificationEquivProd (K : Set M)
    (φ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    φ ∈ supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ↔
      ContMDiffSection.complexificationEquivProd I F n V φ ∈ (supportedIn I F n V K).prod
        (supportedIn I F n V K) := by
  simp only [mem_supportedIn, Submodule.mem_prod, ContMDiffSection.complexificationEquivProd_apply]
  rw [tsupport_eq_union_complexificationEquivProd]
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


/-- Native tensor conjugation as a real linear equivalence preserving support. -/
def CompactlySupported.conjEquiv :
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₗ[ℝ]
      compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) := by
  let L := CompactlySupported.complexificationEquivProd (n := n) (I := I) (F := F) (V := V)
  exact (L.trans ((LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.neg ℝ))).trans L.symm

/-- The real quarter-turn on native complexified sections preserving support. -/
def CompactlySupported.smulIEquiv :
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₗ[ℝ]
      compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) := by
  let L := CompactlySupported.complexificationEquivProd (n := n) (I := I) (F := F) (V := V)
  exact (L.trans ((LinearEquiv.prodComm ℝ _ _).trans
    ((LinearEquiv.neg ℝ).prodCongr (LinearEquiv.refl ℝ _)))).trans L.symm

/-- The real equivalence has the native original-fibre action. -/
@[simp] theorem CompactlySupported.conjEquiv_apply
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) (x : M) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ).val x =
      tmulConj (V x) (φ.val x) := by
  simp only [CompactlySupported.conjEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.neg_apply]
  rw [CompactlySupported.complexificationEquivProd_symm_apply]
  simp only [CompactlySupported.complexificationEquivProd_apply,
    Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
    CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply,
    CompactlySupported.coe_ITmul, ITmulLinearMap_apply,
    Submodule.coe_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
    CompactlySupported.coe_realPart, realPartLinearMap_apply,
    CompactlySupported.coe_imaginaryPart, imaginaryPartLinearMap_apply]
  apply complexification_ext <;> simp

/-- The real equivalence has the native original-fibre action. -/
@[simp] theorem CompactlySupported.smulIEquiv_apply
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) (x : M) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ).val x =
      Complex.I • φ.val x := by
  simp only [CompactlySupported.smulIEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.neg_apply, LinearEquiv.prodComm_apply, Prod.swap]
  rw [CompactlySupported.complexificationEquivProd_symm_apply]
  simp only [CompactlySupported.complexificationEquivProd_apply,
    Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
    CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply,
    CompactlySupported.coe_ITmul, ITmulLinearMap_apply,
    Submodule.coe_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
    CompactlySupported.coe_realPart, realPartLinearMap_apply,
    CompactlySupported.coe_imaginaryPart, imaginaryPartLinearMap_apply]
  conv_rhs =>
    rw [← one_tmul_realPart_add_I_tmul_imaginaryPart (V x) (φ.val x),
      I_smul_one_tmul_add_I_tmul]

/-- Conjugation preserves exact closed support. -/
@[simp] theorem CompactlySupported.tsupport_conjEquiv (φ : compactlySupported I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ).val.tsupport =
      φ.val.tsupport := by
  rw [tsupport_def, tsupport_def]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, CompactlySupported.conjEquiv_apply]
  exact not_congr (map_eq_zero_iff (tmulConj (V x))
    (Function.LeftInverse.injective (tmulConj_tmulConj (V x))))

/-- The quarter-turn preserves exact closed support. -/
@[simp] theorem CompactlySupported.tsupport_smulIEquiv (φ : compactlySupported I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ).val.tsupport =
      φ.val.tsupport := by
  rw [tsupport_def, tsupport_def]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, CompactlySupported.smulIEquiv_apply]
  apply not_congr
  constructor
  · intro h
    have h' := congrArg (fun u : ℂ ⊗[ℝ] V x ↦ -Complex.I • u) h
    simpa [smul_smul] using h'
  · intro h
    rw [h, smul_zero]

/-- Native supported conjugation squares to the identity. -/
@[simp] theorem CompactlySupported.conjEquiv_conjEquiv (φ : compactlySupported I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V)
      (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ) = φ := by
  apply Subtype.ext
  ext x
  simp only [CompactlySupported.conjEquiv_apply, tmulConj_tmulConj]

/-- Native supported multiplication by i squares to negation. -/
@[simp] theorem CompactlySupported.smulIEquiv_smulIEquiv (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V)
      (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ) = -φ := by
  apply Subtype.ext
  ext x
  simp [CompactlySupported.smulIEquiv_apply, smul_smul]

/-- Native tensor conjugation as a real linear equivalence preserving support. -/
def SupportedIn.conjEquiv (K : Set M) :
    supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ≃ₗ[ℝ]
      supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K := by
  let L := SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K
  exact (L.trans ((LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.neg ℝ))).trans L.symm

/-- The real quarter-turn on native complexified sections preserving support. -/
def SupportedIn.smulIEquiv (K : Set M) :
    supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ≃ₗ[ℝ]
      supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K := by
  let L := SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K
  exact (L.trans ((LinearEquiv.prodComm ℝ _ _).trans
    ((LinearEquiv.neg ℝ).prodCongr (LinearEquiv.refl ℝ _)))).trans L.symm

/-- The real equivalence has the native original-fibre action. -/
@[simp] theorem SupportedIn.conjEquiv_apply (K : Set M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) (x : M) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ).val x =
      tmulConj (V x) (φ.val x) := by
  simp only [SupportedIn.conjEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.neg_apply]
  rw [SupportedIn.complexificationEquivProd_symm_apply]
  simp only [Submodule.coe_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
    SupportedIn.complexificationEquivProd_fst_apply,
    SupportedIn.complexificationEquivProd_snd_apply]
  apply complexification_ext <;> simp

/-- The real equivalence has the native original-fibre action. -/
@[simp] theorem SupportedIn.smulIEquiv_apply (K : Set M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) (x : M) :
    (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ).val x =
      Complex.I • φ.val x := by
  simp only [SupportedIn.smulIEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.neg_apply, LinearEquiv.prodComm_apply, Prod.swap]
  rw [SupportedIn.complexificationEquivProd_symm_apply]
  simp only [Submodule.coe_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
    SupportedIn.complexificationEquivProd_fst_apply,
    SupportedIn.complexificationEquivProd_snd_apply]
  conv_rhs =>
    rw [← one_tmul_realPart_add_I_tmul_imaginaryPart (V x) (φ.val x),
      I_smul_one_tmul_add_I_tmul]

/-- Conjugation preserves exact closed support. -/
@[simp] theorem SupportedIn.tsupport_conjEquiv (K : Set M) (φ : supportedIn I (Complexification F)
  n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ).val.tsupport =
      φ.val.tsupport := by
  rw [tsupport_def, tsupport_def]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, SupportedIn.conjEquiv_apply]
  exact not_congr (map_eq_zero_iff (tmulConj (V x))
    (Function.LeftInverse.injective (tmulConj_tmulConj (V x))))

/-- The quarter-turn preserves exact closed support. -/
@[simp] theorem SupportedIn.tsupport_smulIEquiv (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ).val.tsupport =
      φ.val.tsupport := by
  rw [tsupport_def, tsupport_def]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, SupportedIn.smulIEquiv_apply]
  apply not_congr
  constructor
  · intro h
    have h' := congrArg (fun u : ℂ ⊗[ℝ] V x ↦ -Complex.I • u) h
    simpa [smul_smul] using h'
  · intro h
    rw [h, smul_zero]

/-- Native supported conjugation squares to the identity. -/
@[simp] theorem SupportedIn.conjEquiv_conjEquiv (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K
      (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ) = φ := by
  apply Subtype.ext
  ext x
  simp only [SupportedIn.conjEquiv_apply, tmulConj_tmulConj]

/-- Native supported multiplication by i squares to negation. -/
@[simp] theorem SupportedIn.smulIEquiv_smulIEquiv (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K
      (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ) = -φ := by
  apply Subtype.ext
  ext x
  simp [SupportedIn.smulIEquiv_apply, smul_smul]

/-- The inverse action has the expected real algebraic formula. -/
@[simp] theorem CompactlySupported.conjEquiv_symm_apply (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V)).symm φ =
      CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ := by
  apply (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V)).injective
  rw [LinearEquiv.apply_symm_apply, CompactlySupported.conjEquiv_conjEquiv]

/-- The inverse action has the expected real algebraic formula. -/
@[simp] theorem CompactlySupported.smulIEquiv_symm_apply (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V)).symm φ =
      -CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ := by
  apply (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V)).injective
  rw [LinearEquiv.apply_symm_apply, map_neg, CompactlySupported.smulIEquiv_smulIEquiv, neg_neg]

/-- The inverse action has the expected real algebraic formula. -/
@[simp] theorem SupportedIn.conjEquiv_symm_apply (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K).symm φ =
      SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ := by
  apply (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K).injective
  rw [LinearEquiv.apply_symm_apply, SupportedIn.conjEquiv_conjEquiv]

/-- The inverse action has the expected real algebraic formula. -/
@[simp] theorem SupportedIn.smulIEquiv_symm_apply (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K).symm φ =
      -SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ := by
  apply (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K).injective
  rw [LinearEquiv.apply_symm_apply, map_neg, SupportedIn.smulIEquiv_smulIEquiv, neg_neg]

/-- The algebraic action in original real-pair coordinates. -/
theorem CompactlySupported.complexificationEquivProd_conjEquiv
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.complexificationEquivProd
      (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ) =
      (CompactlySupported.realPart φ, -CompactlySupported.imaginaryPart φ) := by
  apply Prod.ext <;> apply Subtype.ext <;> ext x <;>
    simp [CompactlySupported.conjEquiv_apply]

/-- The algebraic action in original real-pair coordinates. -/
theorem CompactlySupported.complexificationEquivProd_smulIEquiv
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.complexificationEquivProd
      (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ) =
      (-CompactlySupported.imaginaryPart φ, CompactlySupported.realPart φ) := by
  apply Prod.ext <;> apply Subtype.ext <;> ext x <;>
    simp [CompactlySupported.smulIEquiv_apply]

end Algebra

end ContMDiffSection
