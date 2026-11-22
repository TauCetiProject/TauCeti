/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.MapTopology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution

/-!
# Complexified Hom coefficients on smooth sections and native test sections

`ContMDiffSection.homComplexificationEquiv` identifies complexified real Hom sections
with complex-linear Hom sections. The identification preserves support and compact stages
at every differentiability order. `TauCeti.BundleTest.homComplexificationCLE` is the real
continuous linear equivalence for the existing native smooth test-section topologies.

The fibre models may be incomplete or infinite dimensional. The native test topology
requires a locally compact base model and smooth bundles; no boundaryless assumption is used.
Specializing the target bundle to `DensityBundle I M` gives density-valued test coefficients,
without introducing a complex scalar action on the native test-section carrier.
-/

public section

noncomputable section
open Bundle FiberBundle Set TauCeti ContMDiffSection
open scoped TensorProduct ContDiff Manifold Topology

namespace ContMDiffSection
universe uM uF uG uV uL uE uH uι
variable {M : Type uM} [TopologicalSpace M]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : M → Type uV} {L : M → Type uL}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace G L)] [FiberBundle G L] [VectorBundle ℝ G L]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]
  [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] {n : ℕ∞ω}

/-- Complexification of real bundle Hom sections as complex-linear Hom sections. -/
def homComplexificationEquiv :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯ ≃ₗ[ℝ]
      Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
        fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯ :=
  mapEquiv (fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
    x).toLinearEquiv.restrictScalars ℝ)
    (by simpa only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
      using
      (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) (IB := I) (n
        := n)))
    (by simpa only [LinearEquiv.restrictScalars_symm_apply,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
      (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L) (IB := I)
        (n := n)))

/-- The Hom coefficient identification on sections supported in any given set. -/
def SupportedIn.homComplexificationEquiv (K : Set M) :
    supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ≃ₗ[ℝ]
    supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K :=
  mapSupportedInEquiv (I := I) (n := n)
    (F := Complexification (F →L[ℝ] G))
    (G := Complexification F →L[ℂ] Complexification G)
    (V := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
    (W := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
      x).toLinearEquiv.restrictScalars ℝ)
    (by simpa only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
      using
      (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) (IB := I) (n
        := n)))
    (by simpa only [LinearEquiv.restrictScalars_symm_apply,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
      (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L) (IB := I)
        (n := n))) K

/-- The Hom coefficient identification on compactly supported sections. -/
def CompactlySupported.homComplexificationEquiv :
    compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃ₗ[ℝ]
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  mapCompactlySupportedEquiv (fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V)
    (L := L) x).toLinearEquiv.restrictScalars ℝ)
    (by simpa only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
      using
      (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) (IB := I) (n
        := n)))
    (by simpa only [LinearEquiv.restrictScalars_symm_apply,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
      (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L) (IB := I)
        (n := n)))

/-- The section equivalence is the existing fibrewise Hom complexification map. -/
@[simp]
theorem homComplexificationEquiv_apply (s :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯) (x : M) :
    homComplexificationEquiv (F := F) (G := G) s x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s x) := by
  simp only [homComplexificationEquiv, mapEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- The coefficient identification preserves topological support exactly. -/
@[simp]
theorem tsupport_homComplexificationEquiv (s :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯) :
    (homComplexificationEquiv (F := F) (G := G) s).tsupport = s.tsupport :=
  tsupport_mapEquiv _ _ _ s

/-- Compactly supported coefficients have the same fibrewise formula. -/
@[simp]
theorem CompactlySupported.homComplexificationEquiv_apply (s : compactlySupported I
  (Complexification (F →L[ℝ] G)) n
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) := by
  simp only [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv,
    mapEquiv_apply, LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]


/-- The inverse section equivalence is the inverse fibrewise Hom complexification map. -/
@[simp]
theorem homComplexificationEquiv_symm_apply (s :
    Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
      fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯) (x : M) :
    (homComplexificationEquiv (F := F) (G := G)).symm s x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s x) := by
  simp only [homComplexificationEquiv, mapEquiv_symm, mapEquiv_apply,
    LinearEquiv.restrictScalars_symm_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv]

/-- Real and imaginary compactly supported real Hom coefficients. -/
def CompactlySupported.homComplexificationEquivProd :
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) ≃ₗ[ℝ]
    compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x) ×
      compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x) :=
  (CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L :=
    L)).symm.trans
    (CompactlySupported.complexificationEquivProd (I := I) (n := n)
      (F := F →L[ℝ] G) (V := fun x ↦ V x →L[ℝ] L x))

/-- The compact-support identification preserves topological support exactly. -/
@[simp]
theorem CompactlySupported.tsupport_homComplexificationEquiv (s : compactlySupported I
  (Complexification (F →L[ℝ] G)) n
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val.tsupport =
      s.val.tsupport := by
  simpa only [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv,
    ContMDiffSection.homComplexificationEquiv] using
      ContMDiffSection.tsupport_homComplexificationEquiv s.val

/-- The coefficient identification commutes with the native compact-stage inclusion. -/
theorem CompactlySupported.homComplexificationEquiv_ofSupportedIn (K : TopologicalSpace.Compacts M)
    (s : supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K) :
    CompactlySupported.homComplexificationEquiv (F := F) (G := G) (ofSupportedIn K s) =
      ofSupportedIn K (SupportedIn.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
        (V := V) (L := L) (K : Set M) s) := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  simp only [CompactlySupported.homComplexificationEquiv_apply, ofSupportedIn_apply,
    SupportedIn.homComplexificationEquiv, coe_mapSupportedInEquiv, mapEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- Multiplying compact Hom coefficients by the real quarter-turn multiplies the resulting
complex-linear Hom value by `I`. -/
theorem CompactlySupported.homComplexificationEquiv_smulI
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.smulIEquiv (I := I) (n := n) s)).val x =
      Complex.I • (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x := by
  simp only [CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe, CompactlySupported.smulIEquiv_apply]
  exact map_smul homComplexificationLinearEquiv Complex.I _

/-- Conjugating the coefficients and the input conjugates the resulting Hom value. -/
theorem CompactlySupported.homComplexificationEquiv_conj
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) (v : ℂ ⊗[ℝ] V x) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.conjEquiv (I := I) (n := n) s)).val x (tmulConj (V x) v) =
      tmulConj (L x) ((CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x v)
        := by
  simp only [CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe, CompactlySupported.conjEquiv_apply]
  exact homComplexificationLinearEquiv_conj _ _

/-- Including real Hom coefficients and evaluating on an included real vector gives the
inclusion of the original real Hom value. -/
theorem CompactlySupported.homComplexificationEquiv_oneTmul_apply
    (s : compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x))
    (x : M) (v : V x) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G) (CompactlySupported.oneTmul
      s)).val x
      (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (s.val x v) := by
  simp only [CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe, CompactlySupported.coe_oneTmul,
    oneTmulLinearMap_apply, homComplexificationLinearEquiv_tmul_apply_tmul, one_mul]

/-- Coefficients supplied by the real conjugation-fixed submodule evaluate on included real
vectors by the original real Hom formula. -/
theorem CompactlySupported.homComplexificationEquiv_realPoints_apply
    (s : compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x))
    (x : M) (v : V x) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.realPointsConjEquiv (I := I) (n := n) s).val).val x
        (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (s.val x v) := by
  rw [CompactlySupported.coe_realPointsConjEquiv_apply]
  exact CompactlySupported.homComplexificationEquiv_oneTmul_apply s x v

/-- Forward fixed-support evaluation is the existing native fibrewise Hom comparison. -/
@[simp]
theorem SupportedIn.homComplexificationEquiv_apply (K : Set M)
    (s : supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K) (x : M) :
    (SupportedIn.homComplexificationEquiv (F := F) (G := G) K s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) := by
  simp only [SupportedIn.homComplexificationEquiv, coe_mapSupportedInEquiv, mapEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- Inverse fixed-support evaluation is the inverse native fibrewise Hom comparison. -/
@[simp]
theorem SupportedIn.homComplexificationEquiv_symm_apply (K : Set M)
    (s : supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K) (x : M) :
    ((SupportedIn.homComplexificationEquiv (F := F) (G := G) K).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) := by
  simp only [SupportedIn.homComplexificationEquiv, coe_mapSupportedInEquiv_symm, mapEquiv_symm,
    mapEquiv_apply, LinearEquiv.restrictScalars_symm_apply,
    ContinuousLinearEquiv.coe_symm_toLinearEquiv]

/-- Inverse compact-support evaluation is the inverse native fibrewise Hom comparison. -/
@[simp]
theorem CompactlySupported.homComplexificationEquiv_symm_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) :
    ((CompactlySupported.homComplexificationEquiv (F := F) (G := G)).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) := by
  simp only [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv_symm,
    mapEquiv_symm, mapEquiv_apply, LinearEquiv.restrictScalars_symm_apply,
    ContinuousLinearEquiv.coe_symm_toLinearEquiv]

/-- Splitting compact Hom coefficients returns the real and imaginary parts of the inverse
coefficient identification, as native compactly supported real Hom sections. -/
@[simp]
theorem CompactlySupported.homComplexificationEquivProd_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) :
    CompactlySupported.homComplexificationEquivProd (F := F) (G := G) s =
      (CompactlySupported.realPart ((CompactlySupported.homComplexificationEquiv
        (F := F) (G := G)).symm s), CompactlySupported.imaginaryPart
        ((CompactlySupported.homComplexificationEquiv (F := F) (G := G)).symm s)) := by
  simp only [CompactlySupported.homComplexificationEquivProd, LinearEquiv.trans_apply,
    CompactlySupported.complexificationEquivProd_apply]

/-- Recombining real and imaginary compact Hom sections includes the first with coefficient1
and the second with coefficientI, then applies the native Hom comparison. -/
@[simp]
theorem CompactlySupported.homComplexificationEquivProd_symm_apply
    (s : compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x) ×
      compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x)) :
    (CompactlySupported.homComplexificationEquivProd (F := F) (G := G)).symm s =
      CompactlySupported.homComplexificationEquiv (F := F) (G := G)
        (CompactlySupported.oneTmul s.1 + CompactlySupported.ITmul s.2) := by
  simp only [CompactlySupported.homComplexificationEquivProd, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, CompactlySupported.complexificationEquivProd_symm_apply]

/-- Recombined Hom coefficients evaluate on an included real vector by the real value plus
`I` times the imaginary value. -/
theorem CompactlySupported.homComplexificationEquivProd_symm_apply_oneTmul
    (s : compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x) ×
      compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x)) (x : M) (v : V x) :
    ((CompactlySupported.homComplexificationEquivProd (F := F) (G := G)).symm s).val x
      (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (s.1.val x v) + Complex.I ⊗ₜ[ℝ] (s.2.val x v) := by
  rw [CompactlySupported.homComplexificationEquivProd_symm_apply,
    CompactlySupported.homComplexificationEquiv_apply, bundleHomComplexificationEquiv_coe]
  simp only [Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
    CompactlySupported.coe_oneTmul,
    CompactlySupported.coe_ITmul, oneTmulLinearMap_apply, ITmulLinearMap_apply,
    map_add, add_apply, homComplexificationLinearEquiv_tmul_apply_tmul,
    mul_one]

/-- The split real and imaginary Hom coefficients are the two real coordinates of evaluation
on an included real vector, for every native fibre. -/
theorem CompactlySupported.homComplexificationEquivProd_apply_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) (v : V x) :
    ((CompactlySupported.homComplexificationEquivProd (F := F) (G := G) s).1.val x v,
      (CompactlySupported.homComplexificationEquivProd (F := F) (G := G) s).2.val x v) =
      (TauCeti.realPart (L x) (s.val x (1 ⊗ₜ[ℝ] v)),
        TauCeti.imaginaryPart (L x) (s.val x (1 ⊗ₜ[ℝ] v))) := by
  let u := ((CompactlySupported.homComplexificationEquiv (F := F) (G := G)).symm s).val x
  have he : homComplexificationLinearEquiv u = s.val x := by
    have h := congrArg (fun t ↦ t.val x)
      ((CompactlySupported.homComplexificationEquiv (F := F) (G := G)).apply_symm_apply s)
    simpa only [CompactlySupported.homComplexificationEquiv_apply,
      bundleHomComplexificationEquiv_coe] using h
  have hr := homComplexificationLinearEquiv_apply_realPart u (1 ⊗ₜ[ℝ] v)
  have hi := homComplexificationLinearEquiv_apply_imaginaryPart u (1 ⊗ₜ[ℝ] v)
  rw [he] at hr hi
  simp only [realPart_tmul, imaginaryPart_tmul, Complex.one_re, Complex.one_im, one_smul,
    zero_smul, map_zero, sub_zero, add_zero] at hr hi
  apply Prod.ext
  · simpa only [CompactlySupported.homComplexificationEquivProd_apply,
      CompactlySupported.coe_realPart, realPartLinearMap_apply] using hr.symm
  · simpa only [CompactlySupported.homComplexificationEquivProd_apply,
      CompactlySupported.coe_imaginaryPart, imaginaryPartLinearMap_apply] using hi.symm

/-- The first split Hom coefficient is the real part of evaluation on a real vector. -/
theorem CompactlySupported.homComplexificationEquivProd_fst_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) (v : V x) :
    (CompactlySupported.homComplexificationEquivProd (F := F) (G := G) s).1.val x v =
      TauCeti.realPart (L x) (s.val x (1 ⊗ₜ[ℝ] v)) :=
  congrArg Prod.fst (CompactlySupported.homComplexificationEquivProd_apply_apply s x v)

/-- The second split Hom coefficient is the imaginary part of evaluation on a real vector. -/
theorem CompactlySupported.homComplexificationEquivProd_snd_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) (v : V x) :
    (CompactlySupported.homComplexificationEquivProd (F := F) (G := G) s).2.val x v =
      TauCeti.imaginaryPart (L x) (s.val x (1 ⊗ₜ[ℝ] v)) :=
  congrArg Prod.snd (CompactlySupported.homComplexificationEquivProd_apply_apply s x v)

section Frames
variable [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G L I] [IsManifold I n M]
  {ι : Type uι} (e : ι → Trivialization F (π F V)) (d : ι → Trivialization G (π G L))
  [∀ i, MemTrivializationAtlas (e i)] [∀ i, MemTrivializationAtlas (d i)]
  (U : ι → TopologicalSpace.Opens M)
  (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet ∩ (d i).baseSet)

omit [IsManifold I n M] in
/-- In arbitrary common frame domains the Hom coefficient identification has the existing
continuous model map as its frame expression. -/
theorem homComplexificationEquiv_frameCoordinates (i : ι)
    (s : Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯)
    (x : U i) :
    ((e i).complexification.continuousLinearMap
      (RingHom.id ℂ) (d i).complexification).frameCoordinates
      (by
        simpa only [Trivialization.baseSet_continuousLinearMap,
          Trivialization.baseSet_complexification] using (hU i))
      (homComplexificationEquiv (F := F) (G := G) s) x =
    Complexification.continuousLinearMapEquiv F G
      ((((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification).frameCoordinates
        (by
          simpa only [Trivialization.baseSet_complexification,
            Trivialization.baseSet_continuousLinearMap] using (hU i)) s x) := by
  simpa only [Trivialization.frameCoordinates_apply, homComplexificationEquiv_apply] using
    bundleHomComplexificationEquiv_in_trivializations (e i) (d i) (hU i x.property) (s x)

omit [IsManifold I n M] in
/-- The inverse coefficient identification in arbitrary common frames is the inverse model map. -/
theorem homComplexificationEquiv_symm_frameCoordinates (i : ι)
    (s : Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
      fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯) (x : U i) :
    (((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification).frameCoordinates
      (by
        simpa only [Trivialization.baseSet_complexification,
          Trivialization.baseSet_continuousLinearMap] using (hU i))
      ((homComplexificationEquiv (F := F) (G := G)).symm s) x =
    (Complexification.continuousLinearMapEquiv F G).symm
      (((e i).complexification.continuousLinearMap
        (RingHom.id ℂ) (d i).complexification).frameCoordinates
        (by
          simpa only [Trivialization.baseSet_continuousLinearMap,
            Trivialization.baseSet_complexification] using (hU i)) s x) := by
  have h := homComplexificationEquiv_frameCoordinates e d U hU i
    ((homComplexificationEquiv (F := F) (G := G)).symm s) x
  have h' := congrArg (Complexification.continuousLinearMapEquiv F G).symm h
  simpa only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using h'.symm

/-- Hom coefficient transport for arbitrary common atlas frames and their native
support-stage topologies. -/
def SupportedIn.homComplexificationCLE (K : Set M) :
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ≃L[ℝ]
    supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K := by
  let φ := fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
    x).toLinearEquiv.restrictScalars ℝ
  refine mapSupportedInCLE (I := I) (n := n) φ
    (by
      simpa only [φ, LinearEquiv.restrictScalars_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv] using
        (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
          (IB := I) (n := n)))
    (by
      simpa only [φ, LinearEquiv.restrictScalars_symm_apply,
        ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
        (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L)
          (IB := I) (n := n)))
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).symm.toContinuousLinearMap.restrictScalars
        ℝ)
    ?_ ?_ K
  · intro i s x
    simpa only [φ, ContMDiffSection.homComplexificationEquiv,
      ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe] using homComplexificationEquiv_frameCoordinates e d U hU i s x
  · intro i s x
    simpa only [φ, ContMDiffSection.homComplexificationEquiv,
      ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe] using
      homComplexificationEquiv_symm_frameCoordinates e d U hU i s x

/-- Hom coefficient transport for arbitrary common atlas frames and their native final
locally convex topologies. -/
def CompactlySupported.homComplexificationCLE :
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℝ]
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) := by
  let φ := fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
    x).toLinearEquiv.restrictScalars ℝ
  refine mapCompactlySupportedCLE (I := I) (n := n) φ
    (by
      simpa only [φ, LinearEquiv.restrictScalars_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv] using
        (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
          (IB := I) (n := n)))
    (by
      simpa only [φ, LinearEquiv.restrictScalars_symm_apply,
        ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
        (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L)
          (IB := I) (n := n)))
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).symm.toContinuousLinearMap.restrictScalars
        ℝ)
    ?_ ?_
  · intro i s x
    simpa only [φ, ContMDiffSection.homComplexificationEquiv,
      ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe] using homComplexificationEquiv_frameCoordinates e d U hU i s x
  · intro i s x
    simpa only [φ, ContMDiffSection.homComplexificationEquiv,
      ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe] using
      homComplexificationEquiv_symm_frameCoordinates e d U hU i s x

/-- The continuous Hom comparison retains exactly the existing algebraic equivalence. -/
@[simp]
theorem SupportedIn.homComplexificationCLE_toLinearEquiv (K : Set M) :
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    (SupportedIn.homComplexificationCLE e d U hU K).toLinearEquiv =
      SupportedIn.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) K := by
  simp only [SupportedIn.homComplexificationCLE, mapSupportedInCLE_toLinearEquiv,
    SupportedIn.homComplexificationEquiv]

/-- The continuous Hom comparison retains exactly the existing algebraic equivalence. -/
@[simp]
theorem CompactlySupported.homComplexificationCLE_toLinearEquiv :
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    (CompactlySupported.homComplexificationCLE e d U hU).toLinearEquiv =
      CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) := by
  simp only [CompactlySupported.homComplexificationCLE, mapCompactlySupportedCLE_toLinearEquiv,
    CompactlySupported.homComplexificationEquiv]

/-- Forward continuous Hom transport evaluates by the native fibre map. -/
@[simp]
theorem SupportedIn.homComplexificationCLE_apply (K : Set M)
    (s : supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K) (x : M) :
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    (SupportedIn.homComplexificationCLE e d U hU K s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) := by
  let _ := frameTopology (I := I) (n := n)
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
    Trivialization.baseSet_continuousLinearMap] using hU _i)
  let _ := frameTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
    Trivialization.baseSet_complexification] using hU _i)
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv, SupportedIn.homComplexificationCLE_toLinearEquiv]
  exact SupportedIn.homComplexificationEquiv_apply K s x

/-- Inverse continuous Hom transport evaluates by the inverse native fibre map. -/
@[simp]
theorem SupportedIn.homComplexificationCLE_symm_apply (K : Set M)
    (s : supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K) (x : M) :
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := frameTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    ((SupportedIn.homComplexificationCLE e d U hU K).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) := by
  let _ := frameTopology (I := I) (n := n)
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
    Trivialization.baseSet_continuousLinearMap] using hU _i)
  let _ := frameTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
    Trivialization.baseSet_complexification] using hU _i)
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    SupportedIn.homComplexificationCLE_toLinearEquiv]
  exact SupportedIn.homComplexificationEquiv_symm_apply K s x

/-- Forward continuous Hom transport evaluates by the native fibre map. -/
@[simp]
theorem CompactlySupported.homComplexificationCLE_apply
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    (CompactlySupported.homComplexificationCLE e d U hU s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) := by
  let _ := compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
    Trivialization.baseSet_continuousLinearMap] using hU _i)
  let _ := compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
    Trivialization.baseSet_complexification] using hU _i)
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv,
    CompactlySupported.homComplexificationCLE_toLinearEquiv]
  exact CompactlySupported.homComplexificationEquiv_apply s x

/-- Inverse continuous Hom transport evaluates by the inverse native fibre map. -/
@[simp]
theorem CompactlySupported.homComplexificationCLE_symm_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU _i)
    let _ := compactlySupportedTopology (I := I) (n := n)
      (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
      (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU _i)
    ((CompactlySupported.homComplexificationCLE e d U hU).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) := by
  let _ := compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_complexification,
    Trivialization.baseSet_continuousLinearMap] using hU _i)
  let _ := compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (fun _i ↦ by simpa only [Trivialization.baseSet_continuousLinearMap,
    Trivialization.baseSet_complexification] using hU _i)
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    CompactlySupported.homComplexificationCLE_toLinearEquiv]
  exact CompactlySupported.homComplexificationEquiv_symm_apply s x

end Frames
section Tests
variable [LocallyCompactSpace E]
  [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ G L I] [IsManifold I ∞ M]

/-- Hom coefficients as a real continuous linear equivalence of native smooth test sections.
It is the arbitrary-frame compact equivalence transported through the existing native wrappers. -/
def _root_.TauCeti.BundleTest.homComplexificationCLE :
    BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℝ]
    BundleTest I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) := by
  let e := fun a : M ↦ trivializationAt F V a
  let d := fun a : M ↦ trivializationAt G L a
  let U : M → TopologicalSpace.Opens M := fun a ↦
    ⟨(e a).baseSet ∩ (d a).baseSet, (e a).open_baseSet.inter (d a).open_baseSet⟩
  let hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet ∩ (d a).baseSet := fun _ ↦ Subset.rfl
  let source := fun a ↦ ((e a).continuousLinearMap (RingHom.id ℝ) (d a)).complexification
  let target := fun a ↦ (e a).complexification.continuousLinearMap
    (RingHom.id ℂ) (d a).complexification
  have hs : ∀ a, (U a : Set M) ⊆ (source a).baseSet := fun a ↦ by
    simpa only [source, Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] using hU a
  have ht : ∀ a, (U a : Set M) ⊆ (target a).baseSet := fun a ↦ by
    simpa only [target, Trivialization.baseSet_continuousLinearMap,
      Trivialization.baseSet_complexification] using hU a
  have hcover : ∀ x : M, ∃ a, x ∈ U a := fun x ↦
    ⟨x, mem_baseSet_trivializationAt F V x, mem_baseSet_trivializationAt G L x⟩
  let _ := compactlySupportedTopology (I := I) (n := ∞) source U hs
  let _ := compactlySupportedTopology (I := I) (n := ∞) target U ht
  exact ((BundleTest.ofCompactlySupportedCLE (I := I) source U hs hcover).symm.trans
    (CompactlySupported.homComplexificationCLE (I := I) (n := ∞) e d U hU)).trans
      (BundleTest.ofCompactlySupportedCLE (I := I) target U ht hcover)

/-- The native Hom equivalence retains the original algebraic coefficient identification and
the original two carrier wrappers. -/
@[simp]
theorem _root_.TauCeti.BundleTest.homComplexificationCLE_toLinearEquiv :
    (TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G)
      (V := V) (L := L)).toLinearEquiv =
    ((BundleTest.ofCompactlySupported I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))).symm.trans
      (CompactlySupported.homComplexificationEquiv (I := I) (n := ∞)
        (F := F) (G := G) (V := V) (L := L))).trans
      (BundleTest.ofCompactlySupported I (Complexification F →L[ℂ] Complexification G)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) := by
  simp only [TauCeti.BundleTest.homComplexificationCLE,
    ContinuousLinearEquiv.trans_toLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
    BundleTest.ofCompactlySupportedCLE_toLinearEquiv,
    CompactlySupported.homComplexificationCLE_toLinearEquiv]

/-- Native forward evaluation is the original fibrewise Hom complexification map. -/
@[simp]
theorem _root_.TauCeti.BundleTest.homComplexificationCLE_apply
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x =
      bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x (s x) := by
  simp only [TauCeti.BundleTest.homComplexificationCLE, ContinuousLinearEquiv.trans_apply,
    BundleTest.ofCompactlySupportedCLE_apply, CompactlySupported.homComplexificationCLE_apply,
    BundleTest.ofCompactlySupportedCLE_symm_apply]

/-- Evaluating the native comparison on a complexified vector is the intrinsic Hom coefficient
formula; this bridges native bundle wrappers to the existing algebraic comparison. -/
theorem _root_.TauCeti.BundleTest.homComplexificationCLE_apply_apply
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) (v : ℂ ⊗[ℝ] V x) :
    TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x v =
      homComplexificationLinearEquiv (s x) v := by
  rw [TauCeti.BundleTest.homComplexificationCLE_apply, bundleHomComplexificationEquiv_coe]

/-- Native inverse evaluation is the inverse original fibrewise Hom complexification map. -/
@[simp]
theorem _root_.TauCeti.BundleTest.homComplexificationCLE_symm_apply
    (s : BundleTest I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) :
    (TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G)).symm s x =
      (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).symm (s x) := by
  simp only [TauCeti.BundleTest.homComplexificationCLE, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, BundleTest.ofCompactlySupportedCLE_apply,
    CompactlySupported.homComplexificationCLE_symm_apply,
    BundleTest.ofCompactlySupportedCLE_symm_apply]

/-- Native Hom coefficient transport preserves topological support exactly. -/
theorem _root_.TauCeti.BundleTest.tsupport_homComplexificationCLE
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    closure {x | TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x ≠ 0} =
      closure {x | s x ≠ 0} := by
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [TauCeti.BundleTest.homComplexificationCLE_apply]
  simpa only [ContinuousLinearEquiv.coe_toLinearEquiv] using
    ((bundleHomComplexificationEquiv (F := F) (G := G)
      (V := V) (L := L) x).toLinearEquiv.map_ne_zero_iff
      (x := s x))

end Tests

end ContMDiffSection
