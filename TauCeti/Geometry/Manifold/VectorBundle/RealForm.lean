/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Smooth conjugation determined by a maximal real form

A smooth real inclusion with maximal totally real image identifies a complex bundle with the
complexification of its real source. Transporting the native tensor conjugation through this
identification gives the smooth fiber involution fixing exactly the given real form.
Maximality is essential: the fixed vectors of a conjugate-linear involution span the complex
fiber. The base is a real charted space, and real and complex scalar structures are explicit.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3, for conjugation along maximal totally
  real boundary conditions.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2 and §2.6.
-/

public noncomputable section

open Bundle FiberBundle Function
open scoped Manifold ContDiff TensorProduct Topology

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

section Equivalence

variable [FiniteDimensional ℝ F]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [∀ x, ContinuousSMul ℝ (V x)]

/-- The canonical complexification equivalence of a finite-rank maximal totally real inclusion.
Continuity of the inverse follows from finite dimensionality over the real scalars. -/
def maximalRealFormComplexificationEquiv (i : ∀ x, W x →L[ℝ] V x)
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (x : B) : (ℂ ⊗[ℝ] W x) ≃L[ℂ] V x :=
  let := FiberBundle.t2Space F W x
  let := FiberBundle.t2Space G V x
  let := VectorBundle.finiteDimensional ℝ F W x
  let : FiniteDimensional ℝ (ℂ ⊗[ℝ] W x) :=
    (complexificationLinearEquivProd (W x)).symm.finiteDimensional
  let e := ((i x).toLinearMap.isBaseChange_complex_of_isMaximalTotallyReal (hinj x) (hmax x)).equiv
  let r := (e.restrictScalars ℝ).toContinuousLinearEquiv
  { toLinearEquiv := e
    continuous_toFun := by
      rw [LinearEquiv.toFun_eq_coe]
      exact r.continuous.congr fun u ↦ by
        simp only [r, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.restrictScalars_apply]
    continuous_invFun := by
      rw [LinearEquiv.invFun_eq_symm]
      exact r.symm.continuous.congr fun u ↦ by
        simp only [r, LinearEquiv.coe_toContinuousLinearEquiv_symm',
          LinearEquiv.restrictScalars_symm_apply] }

/-- The characteristic action of the canonical equivalence on actual tensors. -/
@[simp]
theorem maximalRealFormComplexificationEquiv_tmul (i : ∀ x, W x →L[ℝ] V x)
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (x : B) (c : ℂ) (w : W x) :
    maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax x (c ⊗ₜ[ℝ] w) =
      c • i x w := by
  unfold maximalRealFormComplexificationEquiv
  exact IsBaseChange.equiv_tmul _ c w

/-- Forgetting continuity recovers the canonical native algebraic base-change equivalence. -/
@[simp]
theorem maximalRealFormComplexificationEquiv_toLinearEquiv (i : ∀ x, W x →L[ℝ] V x)
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (x : B) :
    (maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax x).toLinearEquiv =
      ((i x).toLinearMap.isBaseChange_complex_of_isMaximalTotallyReal (hinj x) (hmax x)).equiv := by
  unfold maximalRealFormComplexificationEquiv
  rfl

variable [∀ x, ContinuousConstSMul ℂ (V x)]

/-- The equivalence is the actual canonical continuous complex-linear base-change lift. -/
theorem maximalRealFormComplexificationEquiv_apply (i : ∀ x, W x →L[ℝ] V x)
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (x : B) (u : ℂ ⊗[ℝ] W x) :
    maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax x u =
      (i x).liftBaseChangeComplex u := by
  exact DFunLike.congr_fun ((i x).liftBaseChangeComplex_unique
    (maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax x).toContinuousLinearMap
    (fun w ↦ by simp)) u

end Equivalence

section SmoothEquivalence

variable [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] [VectorBundle ℂ G V]
  [∀ x, ContinuousConstSMul ℂ (V x)] [FiniteDimensional ℝ F]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [∀ x, ContinuousSMul ℝ (V x)]

local instance realFormAmbientVectorBundleReal : VectorBundle ℝ G V :=
  VectorBundle.restrictScalars ℝ ℂ G V

/-- A smooth maximal totally real inclusion induces an actual diffeomorphism from its
complexification onto the ambient complex bundle. Smoothness of the inverse is automatic. -/
def maximalRealFormComplexificationDiffeomorph (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range) :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] W x) ≃ₘ^n⟮
      IB.prod 𝓘(ℝ, Complexification F), IB.prod 𝓘(ℝ, G)⟯ TotalSpace G V :=
  let : FiniteDimensional ℝ (Complexification F) :=
    (Complexification.equivProd F).symm.finiteDimensional
  bundleDiffeomorph (fun x ↦
    (maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax x).restrictScalars' ℝ)
    (by
      simpa only [ContinuousLinearEquiv.coe_restrictScalars',
        maximalRealFormComplexificationEquiv_apply] using
        contMDiff_liftBaseChangeComplex_totalSpace i hi)

/-- The actual bundle diffeomorphism acts by the canonical fiber equivalences. -/
@[simp]
theorem maximalRealFormComplexificationDiffeomorph_apply (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (p : TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] W x)) :
    maximalRealFormComplexificationDiffeomorph i hi hinj hmax p =
      ⟨p.proj, maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax p.proj p.2⟩ := by
  simp only [maximalRealFormComplexificationDiffeomorph, bundleDiffeomorph_apply,
    ContinuousLinearEquiv.coe_restrictScalars']

/-- The smooth inverse acts by the actual inverses of the canonical fiber equivalences. -/
@[simp]
theorem maximalRealFormComplexificationDiffeomorph_symm_apply (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (p : TotalSpace G V) :
    (maximalRealFormComplexificationDiffeomorph i hi hinj hmax).symm p =
      ⟨p.proj, (maximalRealFormComplexificationEquiv (F := F) (G := G) i hinj hmax p.proj).symm
        p.2⟩ := by
  simp only [maximalRealFormComplexificationDiffeomorph, bundleDiffeomorph_symm_apply,
    ContinuousLinearEquiv.coe_restrictScalars'_symm]

/-- The smooth fiber conjugation determined by the given maximal totally real inclusion,
obtained by transporting the native tensor-conjugation diffeomorphism. -/
def maximalRealFormConjugationDiffeomorph (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range) :
    TotalSpace G V ≃ₘ^n⟮IB.prod 𝓘(ℝ, G), IB.prod 𝓘(ℝ, G)⟯ TotalSpace G V :=
  let Φ := maximalRealFormComplexificationDiffeomorph i hi hinj hmax
  (Φ.symm.trans (tmulConjDiffeomorph IB F n W)).trans Φ

/-- On each actual fiber the smooth diffeomorphism is the canonical conjugate-linear map. -/
@[simp]
theorem maximalRealFormConjugationDiffeomorph_apply (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (p : TotalSpace G V) :
    maximalRealFormConjugationDiffeomorph i hi hinj hmax p =
      ⟨p.proj, (i p.proj).toLinearMap.conjugationOfMaximalTotallyReal (hinj p.proj)
        (hmax p.proj) p.2⟩ := by
  simp only [maximalRealFormConjugationDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    maximalRealFormComplexificationDiffeomorph_symm_apply, tmulConjDiffeomorph_apply,
    maximalRealFormComplexificationDiffeomorph_apply]
  rw [LinearMap.conjugationOfMaximalTotallyReal_apply]
  simp only [← ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
    maximalRealFormComplexificationEquiv_toLinearEquiv]

/-- The smooth conjugation is an involution on the actual total space. -/
theorem maximalRealFormConjugationDiffeomorph_involutive (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range) :
    Involutive (maximalRealFormConjugationDiffeomorph i hi hinj hmax) := by
  rintro ⟨x, v⟩
  simp only [maximalRealFormConjugationDiffeomorph_apply]
  exact congrArg (TotalSpace.mk x)
    ((i x).toLinearMap.conjugationOfMaximalTotallyReal_involutive (hinj x) (hmax x) v)

/-- The exact fixed locus is the given real range, rather than an assumed real-point carrier. -/
theorem maximalRealFormConjugationDiffeomorph_eq_self_iff (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (p : TotalSpace G V) :
    maximalRealFormConjugationDiffeomorph i hi hinj hmax p = p ↔
      p.2 ∈ (i p.proj).toLinearMap.range := by
  rcases p with ⟨x, v⟩
  simp only [maximalRealFormConjugationDiffeomorph_apply, TotalSpace.mk.injEq, heq_eq_eq,
    true_and, LinearMap.conjugationOfMaximalTotallyReal_eq_self_iff]


variable (i : ∀ x, W x →L[ℝ] V x)
  (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
    (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
  (hinj : ∀ x, Injective (i x))
  (hmax : ∀ x, IsMaximalTotallyReal
    ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)

/-- The actual smooth bundle involution is conjugate-linear in every fiber. -/
theorem maximalRealFormConjugationDiffeomorph_smul (x : B) (c : ℂ) (v : V x) :
    maximalRealFormConjugationDiffeomorph i hi hinj hmax ⟨x, c • v⟩ =
      ⟨x, star c • (i x).toLinearMap.conjugationOfMaximalTotallyReal (hinj x) (hmax x) v⟩ := by
  rw [maximalRealFormConjugationDiffeomorph_apply, map_smulₛₗ]
  rfl

/-- Any family of conjugate-linear maps fixing the given real inclusion is the actual smooth
conjugation. No continuity or involution hypothesis on the competing family is necessary. -/
theorem maximalRealFormConjugationDiffeomorph_unique
    (K : ∀ x, V x →ₛₗ[starRingEnd ℂ] V x) (hfix : ∀ x w, K x (i x w) = i x w)
    (p : TotalSpace G V) :
    maximalRealFormConjugationDiffeomorph i hi hinj hmax p = ⟨p.proj, K p.proj p.2⟩ := by
  rw [maximalRealFormConjugationDiffeomorph_apply,
    ← (i p.proj).toLinearMap.conjugationOfMaximalTotallyReal_unique
      (hinj p.proj) (hmax p.proj) (K p.proj) (hfix p.proj)]

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [FiniteDimensional ℝ F'] {W' : B → Type*}
  [∀ x, AddCommGroup (W' x)] [∀ x, Module ℝ (W' x)] [∀ x, TopologicalSpace (W' x)]
  [TopologicalSpace (TotalSpace F' W')] [FiberBundle F' W'] [VectorBundle ℝ F' W']
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] W' x)] [∀ x, IsComplexificationTopology (W' x)]
  [∀ x, IsTopologicalAddGroup (W' x)] [∀ x, ContinuousSMul ℝ (W' x)]

/-- Changing the smooth parametrization of the same real ranges does not change the actual
smooth conjugation. The algebraic range comparison also allows distinct source carriers. -/
theorem maximalRealFormConjugationDiffeomorph_congr_range
    (j : ∀ x, W' x →L[ℝ] V x)
    (hj : ContMDiff (IB.prod 𝓘(ℝ, F')) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F' W' ↦ (⟨p.proj, j p.proj p.2⟩ : TotalSpace G V)))
    (hjinj : ∀ x, Injective (j x))
    (hjmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (j x).toLinearMap.range)
    (hrange : ∀ x, (i x).toLinearMap.range = (j x).toLinearMap.range) :
    maximalRealFormConjugationDiffeomorph i hi hinj hmax =
      maximalRealFormConjugationDiffeomorph j hj hjinj hjmax := by
  apply Diffeomorph.ext
  intro p
  simp only [maximalRealFormConjugationDiffeomorph_apply]
  rw [(i p.proj).toLinearMap.conjugationOfMaximalTotallyReal_congr_range
    (hinj p.proj) (hmax p.proj) (j p.proj).toLinearMap (hjinj p.proj) (hjmax p.proj)
    (hrange p.proj)]


variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G'] [NormedSpace ℂ G']
  [IsScalarTower ℝ ℂ G'] {V' : B → Type*}
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)] [∀ x, Module ℂ (V' x)]
  [∀ x, IsScalarTower ℝ ℂ (V' x)] [∀ x, TopologicalSpace (V' x)]
  [TopologicalSpace (TotalSpace G' V')] [FiberBundle G' V'] [VectorBundle ℂ G' V']
  [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousConstSMul ℂ (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)]

local instance realFormAmbientVectorBundleReal' : VectorBundle ℝ G' V' :=
  VectorBundle.restrictScalars ℝ ℂ G' V'

/-- A complex-linear map carrying one real inclusion to another intertwines the actual smooth
conjugations, even for different source and ambient bundles. -/
theorem maximalRealFormConjugationDiffeomorph_natural
    (j : ∀ x, W' x →L[ℝ] V' x)
    (hj : ContMDiff (IB.prod 𝓘(ℝ, F')) (IB.prod 𝓘(ℝ, G')) n
      (fun p : TotalSpace F' W' ↦ (⟨p.proj, j p.proj p.2⟩ : TotalSpace G' V')))
    (hjinj : ∀ x, Injective (j x))
    (hjmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V' x) Complex.I).restrictScalars ℝ) (j x).toLinearMap.range)
    (A : ∀ x, V x →ₗ[ℂ] V' x) (b : ∀ x, W x →ₗ[ℝ] W' x)
    (hreal : ∀ x w, A x (i x w) = j x (b x w)) (p : TotalSpace G V) :
    maximalRealFormConjugationDiffeomorph j hj hjinj hjmax ⟨p.proj, A p.proj p.2⟩ =
      (fun q : TotalSpace G V ↦ (⟨q.proj, A q.proj q.2⟩ : TotalSpace G' V'))
        (maximalRealFormConjugationDiffeomorph i hi hinj hmax p) := by
  calc
    _ = ⟨p.proj, A p.proj ((i p.proj).toLinearMap.conjugationOfMaximalTotallyReal
        (hinj p.proj) (hmax p.proj) p.2)⟩ := by
      rw [maximalRealFormConjugationDiffeomorph_apply,
        (i p.proj).toLinearMap.conjugationOfMaximalTotallyReal_natural
          (hinj p.proj) (hmax p.proj) (j p.proj).toLinearMap (hjinj p.proj) (hjmax p.proj)
          (A p.proj) (b p.proj) (hreal p.proj)]
    _ = _ := (congrArg
      (fun q : TotalSpace G V ↦ (⟨q.proj, A q.proj q.2⟩ : TotalSpace G' V'))
      (maximalRealFormConjugationDiffeomorph_apply i hi hinj hmax p)).symm

end SmoothEquivalence

section Submodule

variable [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] [VectorBundle ℂ G V]
  [∀ x, ContinuousConstSMul ℂ (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ F]
  (L : ∀ x, Submodule ℝ (V x))
  [TopologicalSpace (TotalSpace F (fun x ↦ L x))]
  [FiberBundle F (fun x ↦ L x)] [VectorBundle ℝ F (fun x ↦ L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]

/-- For a maximal totally real subbundle with smooth subtype inclusion, the canonical smooth
conjugation fixes exactly the vectors of the given submodules. The source is the native
submodule bundle, with no additional real-point carrier. -/
theorem maximalRealFormConjugationDiffeomorph_subtype_eq_self_iff
    (hL : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F (fun x ↦ L x) ↦
        (⟨p.proj, (L p.proj).subtypeL p.2⟩ : TotalSpace G V)))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    (p : TotalSpace G V) :
    maximalRealFormConjugationDiffeomorph (fun x ↦ (L x).subtypeL) hL
      (fun _ ↦ Subtype.val_injective) (fun x ↦ by
        simpa only [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using hmax x)
        p = p ↔ p.2 ∈ L p.proj := by
  simpa only [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using
    maximalRealFormConjugationDiffeomorph_eq_self_iff
      (fun x ↦ (L x).subtypeL) hL (fun _ ↦ Subtype.val_injective)
      (fun x ↦ by
        simpa only [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using hmax x) p

end Submodule

end TauCeti
