/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import TauCeti.Algebra.Star.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification

/-!
# Algebra of compactly supported complexified sections

The native compactly supported and prescribed-support submodules identify with real pairs.
These algebraic maps, conjugation and the real quarter-turn are defined at every regularity
order, including analytic order. No topology on the section submodules or chart cover is needed.
The actions restrict the native all-section actions, with exact support preservation proved
once at section level. The fixed submodules are pullbacks of the existing native
`TauCeti.realPoints`.
-/

public section
noncomputable section
open Bundle Set TopologicalSpace TauCeti ContMDiffSection
open scoped ContDiff Manifold TensorProduct Topology

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

/-- A native complexified section is compactly supported exactly when both coordinates are. -/
theorem CompactlySupported.mem_iff_complexificationEquivProd
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    σ ∈ compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ↔
      ContMDiffSection.complexificationEquivProd I F n V σ ∈
        (compactlySupported I F n V).prod (compactlySupported I F n V) := by
  simp only [mem_compactlySupported, Submodule.mem_prod,
    ContMDiffSection.complexificationEquivProd_apply]
  rw [tsupport_eq_union_complexificationEquivProd]
  simp only [ContMDiffSection.complexificationEquivProd_apply]
  constructor
  · intro h
    exact ⟨h.of_isClosed_subset (isClosed_tsupport _) subset_union_left,
      h.of_isClosed_subset (isClosed_tsupport _) subset_union_right⟩
  · rintro ⟨hr, hi⟩
    exact hr.union hi

/-- The native all-section pair equivalence restricted to its compact-support submodules. -/
def CompactlySupported.complexificationEquivProd : compactlySupported I (Complexification F) n
    (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₗ[ℝ]
      compactlySupported I F n V × compactlySupported I F n V :=
  ((ContMDiffSection.complexificationEquivProd I F n V).ofSubmodules _
    ((compactlySupported I F n V).prod (compactlySupported I F n V)) (by
      ext p
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact (CompactlySupported.mem_iff_complexificationEquivProd σ).mp hσ
      · intro hp
        refine ⟨(ContMDiffSection.complexificationEquivProd I F n V).symm p, ?_,
          (ContMDiffSection.complexificationEquivProd I F n V).apply_symm_apply p⟩
        exact (CompactlySupported.mem_iff_complexificationEquivProd _).mpr (by simpa using
          hp))).trans
    (Submodule.prodEquiv _ _)

/-- Support forgetting commutes with the native all-section coordinate equivalence. -/
theorem CompactlySupported.coe_complexificationEquivProd_apply
    (σ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    ((CompactlySupported.complexificationEquivProd σ).1.val,
      (CompactlySupported.complexificationEquivProd σ).2.val) =
        ContMDiffSection.complexificationEquivProd I F n V σ.val := by rfl

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.complexificationEquivProd_apply
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.complexificationEquivProd φ = (CompactlySupported.realPart φ,
      CompactlySupported.imaginaryPart φ) := by
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [ContMDiffSection.complexificationEquivProd_apply,
      CompactlySupported.coe_realPart] using
      congrArg Prod.fst (CompactlySupported.coe_complexificationEquivProd_apply φ)
  · simpa only [ContMDiffSection.complexificationEquivProd_apply,
      CompactlySupported.coe_imaginaryPart] using
      congrArg Prod.snd (CompactlySupported.coe_complexificationEquivProd_apply φ)

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.complexificationEquivProd_symm_apply (p : compactlySupported I
  F n V × compactlySupported I F n V) :
    CompactlySupported.complexificationEquivProd.symm p = CompactlySupported.oneTmul p.1 +
      CompactlySupported.ITmul p.2 := by
  apply Subtype.ext
  simp only [CompactlySupported.complexificationEquivProd, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofSubmodules_symm_apply,
    Submodule.prodEquiv_symm_apply_coe, ContMDiffSection.complexificationEquivProd_symm_apply,
    Submodule.coe_add, CompactlySupported.coe_oneTmul, CompactlySupported.coe_ITmul]


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
private def toComplexSectionRealLinearMap :
    @LinearMap ℝ ℝ _ _ (RingHom.id ℝ)
      Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯
      Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ _ _ _
      (Module.complexToReal Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) where
  toFun φ := φ
  map_add' _ _ := rfl
  map_smul' r φ := by
    -- The target is exactly Module.complexToReal; compare the original real action with
    -- its complex coefficient action before the induced real action.
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r φ).trans (Complex.coe_smul r φ)

/-- The native real-points submodule pulled back along support forgetting. -/
def CompactlySupported.realPointsConj : Submodule ℝ
    (compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :=
  (TauCeti.realPoints (ContMDiffSection.conjEquiv I F n V).toLinearMap).comap
    ((ContMDiffSection.toComplexSectionRealLinearMap (n := n) (I := I) (F := F) (V := V)).comp
      (compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)).subtype)

/-- Membership is the stated native fixed-point condition. -/
@[simp] theorem CompactlySupported.mem_realPointsConj
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    φ ∈ CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V) ↔
      ContMDiffSection.conjEquiv I F n V φ.val = φ.val := by
  simp [CompactlySupported.realPointsConj, TauCeti.mem_realPoints,
    ContMDiffSection.toComplexSectionRealLinearMap]

/-- Real tests identify with the pullback of the native real-points submodule. -/
def CompactlySupported.realPointsConjEquiv : compactlySupported I F n V ≃ₗ[ℝ]
    CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V) where
  toFun φ := ⟨CompactlySupported.oneTmul φ, by
    rw [CompactlySupported.mem_realPointsConj]
    ext x
    simp⟩
  invFun φ := CompactlySupported.realPart φ.val
  left_inv φ := by
    apply Subtype.ext
    ext x
    simp
  right_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [CompactlySupported.coe_oneTmul, CompactlySupported.coe_realPart] using
      oneTmulLinearMap_realPartLinearMap_of_conjEquiv_eq
        ((CompactlySupported.mem_realPointsConj φ.val).mp φ.property)
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
  exact (CompactlySupported.tsupport_eq_union_realPart_imaginaryPart _).trans
    (by simpa only [CompactlySupported.complexificationEquivProd_apply] using h)

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
def SupportedIn.realPointsConj (K : Set M) : Submodule ℝ
    (supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :=
  (TauCeti.realPoints (ContMDiffSection.conjEquiv I F n V).toLinearMap).comap
    ((ContMDiffSection.toComplexSectionRealLinearMap (n := n) (I := I) (F := F) (V := V)).comp
      (supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K).subtype)

/-- Membership is the stated native fixed-point condition. -/
@[simp] theorem SupportedIn.mem_realPointsConj (K : Set M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    φ ∈ SupportedIn.realPointsConj (n := n) (I := I) (F := F) (V := V) K ↔
      ContMDiffSection.conjEquiv I F n V φ.val = φ.val := by
  simp [SupportedIn.realPointsConj, TauCeti.mem_realPoints,
    ContMDiffSection.toComplexSectionRealLinearMap]

/-- The original real support stage identifies with the native fixed subspace at that stage. -/
def SupportedIn.realPointsConjEquiv (K : Set M) : supportedIn I F n V K ≃ₗ[ℝ]
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
    ext x
    have h := congrArg (fun σ : Cₛ^n⟮I; Complexification F, fun y ↦ ℂ ⊗[ℝ] V y⟯ ↦ σ x)
      (oneTmulLinearMap_realPartLinearMap_of_conjEquiv_eq
        ((SupportedIn.mem_realPointsConj K φ.val).mp φ.property))
    simpa only [SupportedIn.complexificationEquivProd_symm_apply,
      SupportedIn.complexificationEquivProd_fst_apply, Submodule.coe_zero,
      ContMDiffSection.coe_zero, Pi.zero_apply, TensorProduct.tmul_zero, add_zero,
      oneTmulLinearMap_apply, realPartLinearMap_apply] using h
  map_add' φ ψ := by
    apply Subtype.ext
    simpa using map_add (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V)
      K).symm (φ, 0) (ψ, 0)
  map_smul' r φ := by
    apply Subtype.ext
    simpa using map_smul (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V :=
      V) K).symm r (φ, 0)

/-- The inverse stage fixed-point comparison is its original real coordinate. -/
@[simp] theorem SupportedIn.realPointsConjEquiv_symm_apply (K : Set M)
    (φ : SupportedIn.realPointsConj (n := n) (I := I) (F := F) (V := V) K) :
    (SupportedIn.realPointsConjEquiv (n := n) (I := I) (F := F) (V := V) K).symm φ =
      (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ.val).1 :=
  by rfl

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.coe_realPointsConjEquiv_apply (K : Set M) (φ : supportedIn I F n
  V K) :
    (SupportedIn.realPointsConjEquiv (n := n) K φ).val = (SupportedIn.complexificationEquivProd (n
      := n) (I := I) (F := F) (V := V) K).symm (φ, 0) := by rfl

/-- The fixed-subspace inclusion commutes with native inclusion of a compact support stage. -/
theorem SupportedIn.realPointsConjEquiv_ofSupportedIn (K : Compacts M) (φ : supportedIn I F n V K) :
    ofSupportedIn K (SupportedIn.realPointsConjEquiv (n := n) (I := I)
      (F := F) (V := V) (K : Set M) φ).val =
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


/-- Native all-section conjugation preserves exact closed support. -/
@[simp] theorem tsupport_conjEquiv
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    (ContMDiffSection.conjEquiv I F n V σ).tsupport = σ.tsupport := by
  rw [tsupport_def, tsupport_def]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, ContMDiffSection.conjEquiv_apply]
  exact not_congr (map_eq_zero_iff (tmulConj (V x))
    (Function.LeftInverse.injective (tmulConj_tmulConj (V x))))

/-- Multiplication by i preserves native section support. -/
@[simp] theorem tsupport_I_smul
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    (Complex.I • σ).tsupport = σ.tsupport :=
  tsupport_smul_of_normedAlgebra Complex.I σ Complex.I_ne_zero

private def smulIRealLinearEquiv :
    Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ ≃ₗ[ℝ]
      Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ :=
  (LinearEquiv.smulOfNeZero ℂ
    Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ Complex.I
      Complex.I_ne_zero).restrictScalars ℝ

/-- Restriction of the native all-section action to its support submodule. -/
def CompactlySupported.conjEquiv :
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₗ[ℝ]
      compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) :=
  ((ContMDiffSection.conjEquiv I F n V).restrictScalarsₛₗ ℝ).ofSubmodules _ _
    (map_compactlySupported_of_tsupport_eq _ (fun σ ↦ by
      simpa only [LinearEquiv.coe_restrictScalarsₛₗ] using ContMDiffSection.tsupport_conjEquiv σ))

/-- Forgetting support recovers the original native section action. -/
theorem CompactlySupported.coe_conjEquiv_apply (φ : compactlySupported I (Complexification F) n
  (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ).val =
      ContMDiffSection.conjEquiv I F n V φ.val := by
  simp only [CompactlySupported.conjEquiv, LinearEquiv.ofSubmodules_apply,
    LinearEquiv.coe_restrictScalarsₛₗ]

/-- The restricted action evaluates in the original native fibre. -/
@[simp] theorem CompactlySupported.conjEquiv_apply (φ : compactlySupported I (Complexification F)
  n (fun x ↦ ℂ ⊗[ℝ] V x)) (x : M) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ).val x =
      tmulConj (V x) (φ.val x) := by
  rw [CompactlySupported.coe_conjEquiv_apply]
  exact ContMDiffSection.conjEquiv_apply _ _

/-- The restriction preserves the native section's exact closed support. -/
@[simp] theorem CompactlySupported.tsupport_conjEquiv (φ : compactlySupported I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ).val.tsupport =
      φ.val.tsupport := by
  rw [CompactlySupported.coe_conjEquiv_apply, ContMDiffSection.tsupport_conjEquiv]

/-- Restriction of the native all-section action to its support submodule. -/
def CompactlySupported.smulIEquiv :
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₗ[ℝ]
      compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) :=
  (smulIRealLinearEquiv (n := n) (I := I) (F := F) (V := V)).ofSubmodules _ _
    (map_compactlySupported_of_tsupport_eq _ (fun σ ↦ by
      simpa only [smulIRealLinearEquiv, LinearEquiv.restrictScalars_apply,
        LinearEquiv.smulOfNeZero_apply] using tsupport_I_smul σ))

/-- Forgetting support recovers the original native section action. -/
theorem CompactlySupported.coe_smulIEquiv_apply (φ : compactlySupported I (Complexification F) n
  (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ).val =
      Complex.I • φ.val := by
  simp only [CompactlySupported.smulIEquiv, LinearEquiv.ofSubmodules_apply,
    smulIRealLinearEquiv, LinearEquiv.restrictScalars_apply, LinearEquiv.smulOfNeZero_apply]

/-- The restricted action evaluates in the original native fibre. -/
@[simp] theorem CompactlySupported.smulIEquiv_apply (φ : compactlySupported I (Complexification F)
  n (fun x ↦ ℂ ⊗[ℝ] V x)) (x : M) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ).val x =
      Complex.I • φ.val x := by
  rw [CompactlySupported.coe_smulIEquiv_apply]
  simp only [coe_smul_of_normedAlgebra, Pi.smul_apply]

/-- The restriction preserves the native section's exact closed support. -/
@[simp] theorem CompactlySupported.tsupport_smulIEquiv (φ : compactlySupported I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ).val.tsupport =
      φ.val.tsupport := by
  rw [CompactlySupported.coe_smulIEquiv_apply, tsupport_I_smul]

/-- Supported conjugation is the restriction of the native involution. -/
@[simp] theorem CompactlySupported.conjEquiv_conjEquiv (φ : compactlySupported I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V)
      (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ) = φ := by
  apply Subtype.ext
  rw [CompactlySupported.coe_conjEquiv_apply, CompactlySupported.coe_conjEquiv_apply]
  simpa only [ContMDiffSection.conjEquiv_symm] using
    (ContMDiffSection.conjEquiv I F n V).symm_apply_apply φ.val

/-- The supported quarter-turn inherits the native scalar square. -/
@[simp] theorem CompactlySupported.smulIEquiv_smulIEquiv (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V)
      (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ) = -φ := by
  apply Subtype.ext
  rw [CompactlySupported.coe_smulIEquiv_apply, CompactlySupported.coe_smulIEquiv_apply,
    smul_smul, Complex.I_mul_I, neg_one_smul, Submodule.coe_neg]

/-- The inverse of the restricted action has the native algebraic formula. -/
@[simp] theorem CompactlySupported.conjEquiv_symm_apply (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V)).symm φ =
      CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) φ := by
  apply (CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V)).injective
  rw [LinearEquiv.apply_symm_apply, CompactlySupported.conjEquiv_conjEquiv]


/-- The inverse of the restricted action has the native algebraic formula. -/
@[simp] theorem CompactlySupported.smulIEquiv_symm_apply (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V)).symm φ =
      -CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) φ := by
  apply (CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V)).injective
  rw [LinearEquiv.apply_symm_apply, map_neg, CompactlySupported.smulIEquiv_smulIEquiv, neg_neg]

/-- Restriction of the native all-section action to its support submodule. -/
def SupportedIn.conjEquiv (K : Set M) :
    supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ≃ₗ[ℝ]
      supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K :=
  ((ContMDiffSection.conjEquiv I F n V).restrictScalarsₛₗ ℝ).ofSubmodules _ _
    (map_supportedIn_of_tsupport_eq _ (fun σ ↦ by
      simpa only [LinearEquiv.coe_restrictScalarsₛₗ] using ContMDiffSection.tsupport_conjEquiv σ) K)

/-- Forgetting support recovers the original native section action. -/
theorem SupportedIn.coe_conjEquiv_apply (K : Set M) (φ : supportedIn I (Complexification F) n (fun
  x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ).val =
      ContMDiffSection.conjEquiv I F n V φ.val := by
  simp only [SupportedIn.conjEquiv, LinearEquiv.ofSubmodules_apply,
    LinearEquiv.coe_restrictScalarsₛₗ]

/-- The restricted action evaluates in the original native fibre. -/
@[simp] theorem SupportedIn.conjEquiv_apply (K : Set M) (φ : supportedIn I (Complexification F) n
  (fun x ↦ ℂ ⊗[ℝ] V x) K) (x : M) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ).val x =
      tmulConj (V x) (φ.val x) := by
  rw [SupportedIn.coe_conjEquiv_apply]
  exact ContMDiffSection.conjEquiv_apply _ _

/-- The restriction preserves the native section's exact closed support. -/
@[simp] theorem SupportedIn.tsupport_conjEquiv (K : Set M) (φ : supportedIn I (Complexification F)
  n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ).val.tsupport =
      φ.val.tsupport := by
  rw [SupportedIn.coe_conjEquiv_apply, ContMDiffSection.tsupport_conjEquiv]

/-- Restriction of the native all-section action to its support submodule. -/
def SupportedIn.smulIEquiv (K : Set M) :
    supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ≃ₗ[ℝ]
      supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K :=
  (smulIRealLinearEquiv (n := n) (I := I) (F := F) (V := V)).ofSubmodules _ _
    (map_supportedIn_of_tsupport_eq _ (fun σ ↦ by
      simpa only [smulIRealLinearEquiv, LinearEquiv.restrictScalars_apply,
        LinearEquiv.smulOfNeZero_apply] using tsupport_I_smul σ) K)

/-- Forgetting support recovers the original native section action. -/
theorem SupportedIn.coe_smulIEquiv_apply (K : Set M) (φ : supportedIn I (Complexification F) n
  (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ).val =
      Complex.I • φ.val := by
  simp only [SupportedIn.smulIEquiv, LinearEquiv.ofSubmodules_apply,
    smulIRealLinearEquiv, LinearEquiv.restrictScalars_apply, LinearEquiv.smulOfNeZero_apply]

/-- The restricted action evaluates in the original native fibre. -/
@[simp] theorem SupportedIn.smulIEquiv_apply (K : Set M) (φ : supportedIn I (Complexification F) n
  (fun x ↦ ℂ ⊗[ℝ] V x) K) (x : M) :
    (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ).val x =
      Complex.I • φ.val x := by
  rw [SupportedIn.coe_smulIEquiv_apply]
  simp only [coe_smul_of_normedAlgebra, Pi.smul_apply]

/-- The restriction preserves the native section's exact closed support. -/
@[simp] theorem SupportedIn.tsupport_smulIEquiv (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ).val.tsupport =
      φ.val.tsupport := by
  rw [SupportedIn.coe_smulIEquiv_apply, tsupport_I_smul]

/-- Supported conjugation is the restriction of the native involution. -/
@[simp] theorem SupportedIn.conjEquiv_conjEquiv (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K
      (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ) = φ := by
  apply Subtype.ext
  rw [SupportedIn.coe_conjEquiv_apply, SupportedIn.coe_conjEquiv_apply]
  simpa only [ContMDiffSection.conjEquiv_symm] using
    (ContMDiffSection.conjEquiv I F n V).symm_apply_apply φ.val

/-- The supported quarter-turn inherits the native scalar square. -/
@[simp] theorem SupportedIn.smulIEquiv_smulIEquiv (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K
      (SupportedIn.smulIEquiv (n := n) (I := I) (F := F) (V := V) K φ) = -φ := by
  apply Subtype.ext
  rw [SupportedIn.coe_smulIEquiv_apply, SupportedIn.coe_smulIEquiv_apply,
    smul_smul, Complex.I_mul_I, neg_one_smul, Submodule.coe_neg]

/-- The inverse of the restricted action has the native algebraic formula. -/
@[simp] theorem SupportedIn.conjEquiv_symm_apply (K : Set M) (φ : supportedIn I (Complexification
  F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K).symm φ =
      SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K φ := by
  apply (SupportedIn.conjEquiv (n := n) (I := I) (F := F) (V := V) K).injective
  rw [LinearEquiv.apply_symm_apply, SupportedIn.conjEquiv_conjEquiv]


/-- The inverse of the restricted action has the native algebraic formula. -/
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
