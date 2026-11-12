/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.LinearAlgebra.TotallyReal.Complex
public import TauCeti.Topology.VectorBundle.RealForm
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Smooth conjugation and projection determined by a maximal real form

A smooth real inclusion with maximal totally real image identifies a complex bundle with the
complexification of its real source. Transporting the native tensor conjugation through this
identification gives the smooth fiber involution fixing exactly the given real form.
Maximality is essential: the fixed vectors of a conjugate-linear involution span the complex
fiber. The base is a real charted space, and real and complex scalar structures are explicit.

For a real subbundle `L` whose fibres are maximal totally real, `V x = L x ⊕ i L x`, and the
projection `P x` of `V x` onto `L x` along `i L x` (`TauCeti.totallyRealProjection`, defined for
topological bundles in `TauCeti.Topology.VectorBundle.RealForm`) is a smooth bundle endomorphism.
This is checked in a local frame `X` of `L`: read in a trivialization, the real frame `X` becomes
a smooth family of complex-linear isomorphisms `ℂᵏ → F`, and `P` is the conjugate by this family
of the coordinatewise real part. The computation is local, so the projection is `C^n` wherever it
is defined on a neighbourhood.

## Main declarations

* `TauCeti.maximalRealFormComplexificationEquiv`: the fiberwise continuous complex-linear
  equivalence `ℂ ⊗[ℝ] W x ≃L[ℂ] V x` of a maximal totally real inclusion.
* `TauCeti.maximalRealFormComplexificationDiffeomorph`: these equivalences as a `C^n`
  diffeomorphism of total spaces.
* `TauCeti.maximalRealFormConjugationDiffeomorph`: the smooth fiber conjugation, with
  `TauCeti.maximalRealFormConjugationDiffeomorph_apply` (its fiber action),
  `TauCeti.maximalRealFormConjugationDiffeomorph_eq_self_iff` (its fixed locus is the given real
  range), `TauCeti.maximalRealFormConjugationDiffeomorph_unique`,
  `TauCeti.maximalRealFormConjugationDiffeomorph_congr_range` and
  `TauCeti.maximalRealFormConjugationDiffeomorph_natural`.
* `TauCeti.maximalRealFormConjugationDiffeomorph_subtype_eq_self_iff`: the case of a subbundle
  given by submodules.
* `TauCeti.contMDiffAt_totallyRealProjection`, `TauCeti.contMDiff_totallyRealProjection`: the
  projection is a smooth bundle endomorphism.

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

/-- The canonical complexification equivalence of a finite-rank maximal totally real inclusion
at one fiber: `ContinuousLinearMap.complexificationEquivOfIsMaximalTotallyReal`, with the
finite rank and Hausdorff fibers supplied by the bundle structures. -/
def maximalRealFormComplexificationEquiv
    (i : ∀ x, W x →L[ℝ] V x) (x : B)
    (hinj : Injective (i x))
    (hmax : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    : (ℂ ⊗[ℝ] W x) ≃L[ℂ] V x :=
  let := FiberBundle.t2Space G V x
  let := VectorBundle.finiteDimensional ℝ F W x
  (i x).complexificationEquivOfIsMaximalTotallyReal hinj hmax

/-- Forgetting continuity recovers the canonical native algebraic base-change equivalence. -/
@[simp]
theorem maximalRealFormComplexificationEquiv_toLinearEquiv
    (i : ∀ x, W x →L[ℝ] V x) (x : B)
    (hinj : Injective (i x))
    (hmax : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range) :
    (maximalRealFormComplexificationEquiv (F := F) (G := G) i x hinj hmax).toLinearEquiv =
      ((i x).toLinearMap.isBaseChange_complex_of_isMaximalTotallyReal hinj hmax).equiv := by
  simp only [maximalRealFormComplexificationEquiv,
    ContinuousLinearMap.complexificationEquivOfIsMaximalTotallyReal_toLinearEquiv]

/-- The characteristic action of the canonical equivalence on actual tensors. -/
@[simp]
theorem maximalRealFormComplexificationEquiv_tmul
    (i : ∀ x, W x →L[ℝ] V x) (x : B)
    (hinj : Injective (i x))
    (hmax : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (c : ℂ) (w : W x) :
    maximalRealFormComplexificationEquiv (F := F) (G := G) i x hinj hmax (c ⊗ₜ[ℝ] w) =
      c • i x w := by
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv, maximalRealFormComplexificationEquiv_toLinearEquiv,
    IsBaseChange.equiv_tmul, ContinuousLinearMap.coe_coe]

variable [∀ x, ContinuousConstSMul ℂ (V x)]

/-- The equivalence is the actual canonical continuous complex-linear base-change lift. -/
theorem maximalRealFormComplexificationEquiv_apply
    (i : ∀ x, W x →L[ℝ] V x) (x : B)
    (hinj : Injective (i x))
    (hmax : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (u : ℂ ⊗[ℝ] W x) :
    maximalRealFormComplexificationEquiv (F := F) (G := G) i x hinj hmax u =
      (i x).liftBaseChangeComplex u :=
  DFunLike.congr_fun ((i x).liftBaseChangeComplex_unique
    (maximalRealFormComplexificationEquiv (F := F) (G := G) i x hinj hmax).toContinuousLinearMap
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
    (maximalRealFormComplexificationEquiv (F := F) (G := G) i x (hinj x)
      (hmax x)).restrictScalars' ℝ)
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
      ⟨p.proj, maximalRealFormComplexificationEquiv (F := F) (G := G) i p.proj (hinj p.proj)
        (hmax p.proj) p.2⟩ := by
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
      ⟨p.proj, (maximalRealFormComplexificationEquiv (F := F) (G := G) i p.proj (hinj p.proj)
        (hmax p.proj)).symm p.2⟩ := by
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

/-- Applying the smooth conjugation twice gives back the input point of the total space. This is
not tagged `@[simp]`: `simp` already proves it from `maximalRealFormConjugationDiffeomorph_apply`
and the fiberwise simp lemma
`LinearMap.conjugationOfMaximalTotallyReal_conjugationOfMaximalTotallyReal`. -/
theorem maximalRealFormConjugationDiffeomorph_apply_apply (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range)
    (p : TotalSpace G V) :
    maximalRealFormConjugationDiffeomorph i hi hinj hmax
      (maximalRealFormConjugationDiffeomorph i hi hinj hmax p) = p := by
  simp only [maximalRealFormConjugationDiffeomorph_apply,
    LinearMap.conjugationOfMaximalTotallyReal_conjugationOfMaximalTotallyReal]

/-- The smooth conjugation is an involution on the actual total space. -/
theorem maximalRealFormConjugationDiffeomorph_involutive (i : ∀ x, W x →L[ℝ] V x)
    (hi : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, G)) n
      (fun p : TotalSpace F W ↦ (⟨p.proj, i p.proj p.2⟩ : TotalSpace G V)))
    (hinj : ∀ x, Injective (i x))
    (hmax : ∀ x, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (i x).toLinearMap.range) :
    Involutive (maximalRealFormConjugationDiffeomorph i hi hinj hmax) :=
  maximalRealFormConjugationDiffeomorph_apply_apply i hi hinj hmax

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
  rw [maximalRealFormConjugationDiffeomorph_apply, map_smulₛₗ, starRingEnd_apply]

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

namespace TauCeti

open Set

section Projection

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {ι : Type*} [Finite ι] {L : ∀ x, Submodule ℝ (V x)}

local instance realFormProjectionVectorBundleReal : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

section Frame

variable {U : Set B} {X : ι → Π x, V x}

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- **The projection onto a totally real subbundle is smooth, locally.** Let `L` have a `C^n`
frame on an open set `U` whose points all have maximal totally real fibres. A field of
endomorphisms equal on `U` to the projection onto `L` along `i L` is `C^n` at each point of `U`. -/
theorem contMDiffAt_totallyRealProjection [ContMDiffVectorBundle n F V IB] (hU : IsOpen U)
    (hX : IsSubbundleFrameOn F L X U) (hXs : ∀ i, CMDiff[U] n (T% (X i)))
    (hL : ∀ y ∈ U,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y))
    {P : ∀ y, V y →L[ℝ] V y} (hP : ∀ y (hy : y ∈ U), P y = totallyRealProjection F (hL y hy))
    {x₀ : B} (hx₀ : x₀ ∈ U) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun y ↦ V y →L[ℝ] V y) x (P x)) x₀ := by
  let := Fintype.ofFinite ι
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set e := trivializationAt F V x₀
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x₀
  let A : B → (ι → ℂ) →L[ℂ] F := IsSubbundleFrameOn.trivOperator ℂ F X x₀
  have hA : ContMDiffAt IB 𝓘(ℝ, (ι → ℂ) →L[ℂ] F) n A x₀ :=
    IsSubbundleFrameOn.contMDiffAt_trivOperator
      (fun i ↦ (hXs i).contMDiffAt (hU.mem_nhds hx₀)) he₀
  have hAapply {y : B} (hy : y ∈ e.baseSet) (c : ι → ℂ) :
      A y c = (e ⟨y, ∑ i, c i • X i y⟩).2 :=
    IsSubbundleFrameOn.trivOperator_apply hy c
  have hA₀ := hX.bijective_trivOperator hx₀ he₀ (hL x₀ hx₀)
  have hleft : (A x₀).HasLeftInverse := by
    let a := LinearEquiv.ofBijective (A x₀ : (ι → ℂ) →ₗ[ℂ] F) hA₀
    refine ⟨(a.toContinuousLinearEquiv.symm : F →L[ℂ] (ι → ℂ)), fun c ↦ ?_⟩
    have : a.toContinuousLinearEquiv c = A x₀ c := rfl
    rw [ContinuousLinearEquiv.coe_coe, ← this, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨Linv, hLinv, hLA⟩ := hA.exists_contMDiffAt_leftInverse hleft
  let R : (ι → ℂ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.pi fun i ↦
    Complex.ofRealCLM ∘L Complex.reCLM ∘L ContinuousLinearMap.proj i
  have hAr : ContMDiffAt IB 𝓘(ℝ, (ι → ℂ) →L[ℝ] F) n (fun y ↦ (A y).restrictScalars ℝ) x₀ :=
    (ContinuousLinearMap.restrictScalarsL ℂ (ι → ℂ) F ℝ ℝ).contDiff.comp_contMDiffAt hA
  have hLr : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] (ι → ℂ)) n (fun y ↦ (Linv y).restrictScalars ℝ) x₀ :=
    (ContinuousLinearMap.restrictScalarsL ℂ F (ι → ℂ) ℝ ℝ).contDiff.comp_contMDiffAt hLinv
  refine (hAr.clm_comp ((contMDiffAt_const (c := R)).clm_comp hLr)).congr_of_eventuallyEq ?_
  filter_upwards [hLA, hU.mem_nhds hx₀, e.open_baseSet.mem_nhds he₀] with y hyL hyU hye
  ext w
  obtain ⟨c, rfl⟩ : ∃ c, A y c = w := (hX.bijective_trivOperator hyU hye (hL y hyU)).2 w
  have hc : Linv y (A y c) = c := hyL c
  have hsymm : e.symm y (A y c) = ∑ i, c i • X i y := by
    rw [hAapply hye, e.symm_apply_apply_mk hye]
  rw [ContinuousLinearMap.inCoordinates_eq hye hye]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hc,
    ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_symm_apply]
  rw [hsymm, Trivialization.continuousLinearEquivAt_apply, hP y hyU, totallyRealProjection_apply,
    (hL y hyU).projection_sum_smul (fun i ↦ hX.apply_mem i hyU), hAapply hye]
  have hR : ∑ i, R c i • X i y = ∑ i, (c i).re • X i y :=
    Finset.sum_congr rfl fun i _ ↦ by
      simp only [R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply]
      rw [← smul_one_smul ℂ (c i).re (X i y), Complex.real_smul, mul_one]
  rw [hR]

end Frame

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- **The projection onto a smooth totally real subbundle is smooth.** If the fibres of a
real subbundle `L` with `C^n` local frames are maximal totally real, the projection onto `L`
along `i L` is a `C^n` section of the endomorphism bundle. -/
theorem contMDiff_totallyRealProjection [ContMDiffVectorBundle n F V IB]
    (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun y ↦ V y →L[ℝ] V y) x (totallyRealProjection F (hL x))) := by
  intro x₀
  let := Fintype.ofFinite ι
  obtain ⟨U, hU, hx₀, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs x₀
  exact contMDiffAt_totallyRealProjection hU hX hXs (fun y _ ↦ hL y) (fun _ _ ↦ rfl) hx₀

end Projection

end TauCeti
