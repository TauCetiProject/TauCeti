/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.CompactSupport
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

/-- The fibrewise Hom complexification comparison `bundleHomComplexificationEquiv`, as the real
linear equivalence of fibres consumed by section transport (`ContMDiffSection.mapEquiv`). -/
def _root_.TauCeti.bundleHomComplexificationLinearEquiv (x : M) :
    (ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃ₗ[ℝ] ((ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
    x).toLinearEquiv.restrictScalars ℝ

@[simp]
theorem _root_.TauCeti.bundleHomComplexificationLinearEquiv_apply (x : M)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    bundleHomComplexificationLinearEquiv (F := F) (G := G) x u =
      bundleHomComplexificationEquiv (F := F) (G := G) x u :=
  (rfl)

@[simp]
theorem _root_.TauCeti.bundleHomComplexificationLinearEquiv_symm_apply (x : M)
    (u : (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :
    (bundleHomComplexificationLinearEquiv (F := F) (G := G) x).symm u =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm u :=
  (rfl)

/-- The fibrewise Hom comparison is smooth on total spaces, in the form `mapEquiv` consumes. -/
theorem _root_.TauCeti.contMDiff_bundleHomComplexificationLinearEquiv :
    ContMDiff (I.prod 𝓘(ℝ, Complexification (F →L[ℝ] G)))
      (I.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification G)) n
      (fun p : TotalSpace (Complexification (F →L[ℝ] G)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ↦
        (⟨p.proj, bundleHomComplexificationLinearEquiv (F := F) (G := G) p.proj p.snd⟩ :
          TotalSpace (Complexification F →L[ℂ] Complexification G)
            (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)))) :=
  contMDiff_bundleHomComplexificationEquiv

/-- The inverse fibrewise Hom comparison is smooth on total spaces, in the form `mapEquiv`
consumes. -/
theorem _root_.TauCeti.contMDiff_bundleHomComplexificationLinearEquiv_symm :
    ContMDiff (I.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification G))
      (I.prod 𝓘(ℝ, Complexification (F →L[ℝ] G))) n
      (fun p : TotalSpace (Complexification F →L[ℂ] Complexification G)
          (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) ↦
        (⟨p.proj, (bundleHomComplexificationLinearEquiv (F := F) (G := G) p.proj).symm p.snd⟩ :
          TotalSpace (Complexification (F →L[ℝ] G)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)))) :=
  contMDiff_bundleHomComplexificationEquiv_symm

/-- Complexification of real bundle Hom sections as complex-linear Hom sections. -/
def homComplexificationEquiv :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯ ≃ₗ[ℝ]
      Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
        fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯ :=
  mapEquiv (bundleHomComplexificationLinearEquiv (F := F) (G := G))
    contMDiff_bundleHomComplexificationLinearEquiv
    contMDiff_bundleHomComplexificationLinearEquiv_symm

/-- The Hom coefficient identification on sections supported in any given set. -/
def SupportedIn.homComplexificationEquiv (K : Set M) :
    supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ≃ₗ[ℝ]
    supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K :=
  mapSupportedInEquiv (I := I) (n := n)
    (F := Complexification (F →L[ℝ] G)) (G := Complexification F →L[ℂ] Complexification G)
    (V := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) (W := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (bundleHomComplexificationLinearEquiv (F := F) (G := G))
    contMDiff_bundleHomComplexificationLinearEquiv
    contMDiff_bundleHomComplexificationLinearEquiv_symm K

/-- The Hom coefficient identification on compactly supported sections. -/
def CompactlySupported.homComplexificationEquiv :
    compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃ₗ[ℝ]
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  mapCompactlySupportedEquiv (bundleHomComplexificationLinearEquiv (F := F) (G := G))
    contMDiff_bundleHomComplexificationLinearEquiv
    contMDiff_bundleHomComplexificationLinearEquiv_symm

/-- The section equivalence is the existing fibrewise Hom complexification map. -/
@[simp]
theorem homComplexificationEquiv_apply (s :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯) (x : M) :
    homComplexificationEquiv (F := F) (G := G) s x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s x) := by
  simp only [homComplexificationEquiv, mapEquiv_apply,
    bundleHomComplexificationLinearEquiv_apply]

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
    mapEquiv_apply, bundleHomComplexificationLinearEquiv_apply]


/-- The inverse section equivalence is the inverse fibrewise Hom complexification map. -/
@[simp]
theorem homComplexificationEquiv_symm_apply (s :
    Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
      fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯) (x : M) :
    (homComplexificationEquiv (F := F) (G := G)).symm s x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s x) := by
  simp only [homComplexificationEquiv, mapEquiv_symm, mapEquiv_apply,
    bundleHomComplexificationLinearEquiv_symm_apply]

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
  rw [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv]
  exact tsupport_mapEquiv _ _ _ s.val

/-- The coefficient identification commutes with the native compact-stage inclusion. -/
theorem CompactlySupported.homComplexificationEquiv_ofSupportedIn (K : TopologicalSpace.Compacts M)
    (s : supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K) :
    CompactlySupported.homComplexificationEquiv (F := F) (G := G) (ofSupportedIn K s) =
      ofSupportedIn K (SupportedIn.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
        (V := V) (L := L) (K : Set M) s) :=
  mapCompactlySupportedEquiv_ofSupportedIn _ _ _ K s

/-- Multiplying compact Hom coefficients by the real quarter-turn multiplies the resulting
complex-linear Hom value by `I`. -/
theorem CompactlySupported.homComplexificationEquiv_smulIEquiv_apply
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.smulIEquiv (I := I) (n := n) s)).val x =
      Complex.I • (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x := by
  simp only [CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe, CompactlySupported.smulIEquiv_apply]
  exact map_smul homComplexificationLinearEquiv Complex.I _

/-- Conjugating the coefficients and the input conjugates the resulting Hom value. -/
theorem CompactlySupported.homComplexificationEquiv_conjEquiv_apply
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
theorem CompactlySupported.homComplexificationEquiv_realPointsConjEquiv_apply
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
    bundleHomComplexificationLinearEquiv_apply]

/-- Inverse fixed-support evaluation is the inverse native fibrewise Hom comparison. -/
@[simp]
theorem SupportedIn.homComplexificationEquiv_symm_apply (K : Set M)
    (s : supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K) (x : M) :
    ((SupportedIn.homComplexificationEquiv (F := F) (G := G) K).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) := by
  simp only [SupportedIn.homComplexificationEquiv, coe_mapSupportedInEquiv_symm, mapEquiv_symm,
    mapEquiv_apply, bundleHomComplexificationLinearEquiv_symm_apply]

/-- Inverse compact-support evaluation is the inverse native fibrewise Hom comparison. -/
@[simp]
theorem CompactlySupported.homComplexificationEquiv_symm_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) :
    ((CompactlySupported.homComplexificationEquiv (F := F) (G := G)).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) := by
  simp only [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv_symm,
    mapEquiv_symm, mapEquiv_apply, bundleHomComplexificationLinearEquiv_symm_apply]

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

/-- Recombining real and imaginary compact Hom sections includes the first with coefficient `1`
and the second with coefficient `Complex.I`, then applies the native Hom comparison. -/
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

omit [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)] in
include hU in
/-- The common frame domains lie in the base sets of the complexified real Hom frames. -/
theorem subset_baseSet_complexification_continuousLinearMap (i : ι) :
    (U i : Set M) ⊆ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification.baseSet := by
  simpa only [Trivialization.baseSet_complexification,
    Trivialization.baseSet_continuousLinearMap] using hU i

omit [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)] in
include hU in
/-- The common frame domains lie in the base sets of the Hom frames of the complexified frames. -/
theorem subset_baseSet_continuousLinearMap_complexification (i : ι) :
    (U i : Set M) ⊆
      ((e i).complexification.continuousLinearMap (RingHom.id ℂ)
        (d i).complexification).baseSet := by
  simpa only [Trivialization.baseSet_continuousLinearMap,
    Trivialization.baseSet_complexification] using hU i

/-- The frame topology of complexified real Hom sections in the complexified real Hom frames. -/
abbrev homFrameTopology :
    TopologicalSpace Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯ :=
  frameTopology (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
    (subset_baseSet_complexification_continuousLinearMap e d U hU)

/-- The frame topology of complex-linear Hom sections in the Hom frames of the complexified
frames. -/
abbrev complexHomFrameTopology :
    TopologicalSpace Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
      fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯ :=
  frameTopology
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (subset_baseSet_continuousLinearMap_complexification e d U hU)

/-- The final locally convex topology of compactly supported complexified real Hom sections in
the complexified real Hom frames. -/
abbrev homCompactlySupportedTopology :
    TopologicalSpace (compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :=
  compactlySupportedTopology
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification) U
    (subset_baseSet_complexification_continuousLinearMap e d U hU)

/-- The final locally convex topology of compactly supported complex-linear Hom sections in the
Hom frames of the complexified frames. -/
abbrev complexHomCompactlySupportedTopology :
    TopologicalSpace (compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) :=
  compactlySupportedTopology
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (subset_baseSet_continuousLinearMap_complexification e d U hU)

omit [IsManifold I n M] in
/-- In arbitrary common frame domains the Hom coefficient identification has the existing
continuous model map as its frame expression. -/
theorem frameCoordinates_homComplexificationEquiv (i : ι)
    (s : Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯)
    (x : U i) :
    ((e i).complexification.continuousLinearMap
      (RingHom.id ℂ) (d i).complexification).frameCoordinates
      (subset_baseSet_continuousLinearMap_complexification e d U hU i)
      (homComplexificationEquiv (F := F) (G := G) s) x =
    (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ
      ((((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification).frameCoordinates
        (subset_baseSet_complexification_continuousLinearMap e d U hU i) s x) := by
  simpa only [Trivialization.frameCoordinates_apply, homComplexificationEquiv_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe] using
    bundleHomComplexificationEquiv_in_trivializations (e i) (d i) (hU i x.property) (s x)

omit [IsManifold I n M] in
/-- The inverse coefficient identification in arbitrary common frames is the inverse model map. -/
theorem frameCoordinates_homComplexificationEquiv_symm (i : ι)
    (s : Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
      fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯) (x : U i) :
    (((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification).frameCoordinates
      (subset_baseSet_complexification_continuousLinearMap e d U hU i)
      ((homComplexificationEquiv (F := F) (G := G)).symm s) x =
    (Complexification.continuousLinearMapEquiv F G).symm.toContinuousLinearMap.restrictScalars ℝ
      (((e i).complexification.continuousLinearMap
        (RingHom.id ℂ) (d i).complexification).frameCoordinates
        (subset_baseSet_continuousLinearMap_complexification e d U hU i) s x) := by
  have h := congrArg (Complexification.continuousLinearMapEquiv F G).symm
    (frameCoordinates_homComplexificationEquiv e d U hU i
      ((homComplexificationEquiv (F := F) (G := G)).symm s) x)
  simpa only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe] using h.symm

/-- Hom coefficient transport for arbitrary common atlas frames and their native
support-stage topologies. -/
def SupportedIn.homComplexificationCLE (K : Set M) :
    let _ := homFrameTopology (I := I) (n := n) e d U hU
    let _ := complexHomFrameTopology (I := I) (n := n) e d U hU
    supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ≃L[ℝ]
    supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K :=
  mapSupportedInCLE (I := I) (n := n)
    (F := Complexification (F →L[ℝ] G)) (G := Complexification F →L[ℂ] Complexification G)
    (V := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) (W := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (bundleHomComplexificationLinearEquiv (F := F) (G := G))
    contMDiff_bundleHomComplexificationLinearEquiv
    contMDiff_bundleHomComplexificationLinearEquiv_symm
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification)
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (subset_baseSet_complexification_continuousLinearMap e d U hU)
    (subset_baseSet_continuousLinearMap_complexification e d U hU)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).symm.toContinuousLinearMap.restrictScalars ℝ)
    (frameCoordinates_homComplexificationEquiv e d U hU)
    (frameCoordinates_homComplexificationEquiv_symm e d U hU) K

/-- Hom coefficient transport for arbitrary common atlas frames and their native final
locally convex topologies. -/
def CompactlySupported.homComplexificationCLE :
    let _ := homCompactlySupportedTopology (I := I) (n := n) e d U hU
    let _ := complexHomCompactlySupportedTopology (I := I) (n := n) e d U hU
    compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℝ]
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  mapCompactlySupportedCLE (I := I) (n := n)
    (F := Complexification (F →L[ℝ] G)) (G := Complexification F →L[ℂ] Complexification G)
    (V := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) (W := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (bundleHomComplexificationLinearEquiv (F := F) (G := G))
    contMDiff_bundleHomComplexificationLinearEquiv
    contMDiff_bundleHomComplexificationLinearEquiv_symm
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id ℝ) (d i)).complexification)
    (fun i ↦ (e i).complexification.continuousLinearMap (RingHom.id ℂ) (d i).complexification) U
    (subset_baseSet_complexification_continuousLinearMap e d U hU)
    (subset_baseSet_continuousLinearMap_complexification e d U hU)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).symm.toContinuousLinearMap.restrictScalars ℝ)
    (frameCoordinates_homComplexificationEquiv e d U hU)
    (frameCoordinates_homComplexificationEquiv_symm e d U hU)

/-- The continuous Hom comparison retains exactly the existing algebraic equivalence. -/
@[simp]
theorem SupportedIn.homComplexificationCLE_toLinearEquiv (K : Set M) :
    let _ := homFrameTopology (I := I) (n := n) e d U hU
    let _ := complexHomFrameTopology (I := I) (n := n) e d U hU
    (SupportedIn.homComplexificationCLE e d U hU K).toLinearEquiv =
      SupportedIn.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) K :=
  mapSupportedInCLE_toLinearEquiv ..

/-- The continuous Hom comparison retains exactly the existing algebraic equivalence. -/
@[simp]
theorem CompactlySupported.homComplexificationCLE_toLinearEquiv :
    let _ := homCompactlySupportedTopology (I := I) (n := n) e d U hU
    let _ := complexHomCompactlySupportedTopology (I := I) (n := n) e d U hU
    (CompactlySupported.homComplexificationCLE e d U hU).toLinearEquiv =
      CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) :=
  mapCompactlySupportedCLE_toLinearEquiv ..

/-- Forward continuous Hom transport evaluates by the native fibre map. -/
@[simp]
theorem SupportedIn.homComplexificationCLE_apply (K : Set M)
    (s : supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K) (x : M) :
    let _ := homFrameTopology (I := I) (n := n) e d U hU
    let _ := complexHomFrameTopology (I := I) (n := n) e d U hU
    (SupportedIn.homComplexificationCLE e d U hU K s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) :=
  mapSupportedInCLE_apply ..

/-- Inverse continuous Hom transport evaluates by the inverse native fibre map. -/
@[simp]
theorem SupportedIn.homComplexificationCLE_symm_apply (K : Set M)
    (s : supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K) (x : M) :
    let _ := homFrameTopology (I := I) (n := n) e d U hU
    let _ := complexHomFrameTopology (I := I) (n := n) e d U hU
    ((SupportedIn.homComplexificationCLE e d U hU K).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) :=
  mapSupportedInCLE_symm_apply ..

/-- Forward continuous Hom transport evaluates by the native fibre map. -/
@[simp]
theorem CompactlySupported.homComplexificationCLE_apply
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    let _ := homCompactlySupportedTopology (I := I) (n := n) e d U hU
    let _ := complexHomCompactlySupportedTopology (I := I) (n := n) e d U hU
    (CompactlySupported.homComplexificationCLE e d U hU s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) :=
  mapCompactlySupportedCLE_apply ..

/-- Inverse continuous Hom transport evaluates by the inverse native fibre map. -/
@[simp]
theorem CompactlySupported.homComplexificationCLE_symm_apply
    (s : compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) :
    let _ := homCompactlySupportedTopology (I := I) (n := n) e d U hU
    let _ := complexHomCompactlySupportedTopology (I := I) (n := n) e d U hU
    ((CompactlySupported.homComplexificationCLE e d U hU).symm s).val x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s.val x) :=
  mapCompactlySupportedCLE_symm_apply ..

end Frames
section Tests
variable [LocallyCompactSpace E]
  [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ G L I] [IsManifold I ∞ M]

/-- Hom coefficients as a real continuous linear equivalence of native smooth test sections.
It is the generic native transport `TauCeti.BundleTest.mapCLE` of the fibrewise Hom
comparison, computed in the preferred common frame domains. -/
def _root_.TauCeti.BundleTest.homComplexificationCLE :
    BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℝ]
    BundleTest I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  let e := fun a : M ↦ trivializationAt F V a
  let d := fun a : M ↦ trivializationAt G L a
  let U : M → TopologicalSpace.Opens M := fun a ↦
    ⟨(e a).baseSet ∩ (d a).baseSet, (e a).open_baseSet.inter (d a).open_baseSet⟩
  have hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet ∩ (d a).baseSet := fun _ ↦ Subset.rfl
  BundleTest.mapCLE (I := I)
    (fun a ↦ ((e a).continuousLinearMap (RingHom.id ℝ) (d a)).complexification)
    (fun a ↦ (e a).complexification.continuousLinearMap (RingHom.id ℂ) (d a).complexification) U
    (subset_baseSet_complexification_continuousLinearMap e d U hU)
    (subset_baseSet_continuousLinearMap_complexification e d U hU)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x, mem_baseSet_trivializationAt G L x⟩)
    (bundleHomComplexificationLinearEquiv (F := F) (G := G))
    contMDiff_bundleHomComplexificationLinearEquiv
    contMDiff_bundleHomComplexificationLinearEquiv_symm
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ)
    (fun _ ↦
      (Complexification.continuousLinearMapEquiv F G).symm.toContinuousLinearMap.restrictScalars ℝ)
    (frameCoordinates_homComplexificationEquiv e d U hU)
    (frameCoordinates_homComplexificationEquiv_symm e d U hU)

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
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) :=
  BundleTest.mapCLE_toLinearEquiv ..

/-- Native forward evaluation is the original fibrewise Hom complexification map. -/
@[simp]
theorem _root_.TauCeti.BundleTest.homComplexificationCLE_apply
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x =
      bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x (s x) :=
  BundleTest.mapCLE_apply ..

/-- Native inverse evaluation is the inverse original fibrewise Hom complexification map. -/
@[simp]
theorem _root_.TauCeti.BundleTest.homComplexificationCLE_symm_apply
    (s : BundleTest I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) (x : M) :
    (TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G)).symm s x =
      (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).symm (s x) :=
  BundleTest.mapCLE_symm_apply ..

/-- Native Hom coefficient transport preserves topological support exactly. -/
theorem _root_.TauCeti.BundleTest.tsupport_homComplexificationCLE
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    closure {x | TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x ≠ 0} =
      closure {x | s x ≠ 0} :=
  BundleTest.tsupport_mapCLE ..

end Tests

end ContMDiffSection
