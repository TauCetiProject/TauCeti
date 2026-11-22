/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Nondegenerate points of positive rank on symplectic manifolds

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M` and let `F : M → G` be a
map into a normed space, for instance the momentum map `F = (F₁, …, Fₙ) : M → ℝⁿ` of an integrable
system. At a point `x`, write `U = ker dF_x ⊆ T_x M`. For a linear functional `ℓ` on `G` vanishing
on the image of `dF_x`, the function `ℓ ∘ F` is critical at `x`, so its Hessian is an intrinsic
quadratic form on `T_x M` (`TauCeti.criticalHessian`). Following Eliasson and Bolsinov–Fomenko,
`x` is a **nondegenerate point** of `F`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegeneratePoint`) when these Hessians descend to the
**transversal space** `U ⧸ (U ∩ U^σ)`, the linear symplectic reduction of `(T_x M, σ_x)` along
`U`, and form a nondegenerate family there: their Hamiltonian endomorphisms generate a Cartan
subalgebra of its symplectic Lie algebra. At a critical point the transversal space is all of
`T_x M`, and the notion is that of a nondegenerate rank-zero point.

This file transfers the linear notion `TauCeti.SymplecticForm.IsNondegeneratePoint`, which lives on
a symplectic vector space, to manifolds, and shows that it is intrinsic.

* On a boundaryless manifold, in the preferred chart at `x`, the notion is the linear one for the
  coordinate expression of `F` and the value of `σ` at `x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_iff_comp_extChartAt_symm`).
* It is invariant under symplectic changes of coordinates: for boundaryless manifolds `M` and
  `N`, if `φ : N → M` is `C²` at `y`, has invertible differential there and pulls `σ` back to `τ`
  at `y`, then for `F` which is `C²` at `φ y`, the point `y` is a nondegenerate point of `F ∘ φ`
  for `τ` exactly when `φ y` is one of `F` for `σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_comp_right_iff`). The differential
  `dφ_y` is a linear symplectomorphism carrying `ker d(F ∘ φ)_y` onto `ker dF_(φ y)`, so it induces
  a symplectomorphism of transversal spaces
  (`TauCeti.SymplecticForm.reducedSpaceCongr`), and the second-order chain rule at a critical point
  (`TauCeti.criticalHessian_comp_apply`) identifies the transversal Hessians through it. The same
  holds for a parametrization `φ : E' → M` by a symplectic vector space `(E', ω₀)`, such as a
  Darboux chart, with the linear notion on the source
  (`TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff`), so nondegeneracy may be checked
  in any symplectic coordinates.
* It depends only on the germ of `F`, and on a boundaryless manifold, at a critical point of `F`
  it is nondegeneracy of rank zero
  (`IsNondegenerate.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint`, in the namespace
  `TauCeti.SmoothTwoForm`). Since `dφ_y` is invertible, `y` is critical for `F ∘ φ` exactly when
  `φ y` is critical for `F` (`TauCeti.mvfderiv_comp_eq_zero_iff_of_isInvertible`), so the
  invariance of nondegenerate rank-zero points under symplectic changes of coordinates follows
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegenerateRankZeroPoint_comp_right_iff` and
  `TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_comp_right_iff`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegeneratePoint hσ F x`: `F` is `C²` at `x` and the
  critical Hessians of the functions `ℓ ∘ F`, for `ℓ` vanishing on the image of `dF_x`, descend to
  the transversal space at `x` and form a nondegenerate family there.

## References

* L. H. Eliasson, *Normal forms for Hamiltonian systems with Poisson commuting integrals —
  elliptic case*, Commentarii Mathematici Helvetici 65 (1990), 4–35.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
-/

public section

noncomputable section

open Function Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Nondegenerate points on manifolds -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace SmoothTwoForm.IsNondegenerate

variable (hσ : σ.IsNondegenerate)

/-- A point `x` is a **nondegenerate point** of a map `F : M → G` for a nondegenerate two-form `σ`
when `F` is `C²` at `x` and, writing `U = ker dF_x`, the critical Hessians at `x` of the functions
`ℓ ∘ F`, for `ℓ` vanishing on the image of `dF_x`, descend to the transversal space
`U ⧸ (U ∩ U^σ)` of `(T_x M, σ_x)` and form a nondegenerate family there: their Hamiltonian
endomorphisms generate a Cartan subalgebra of its symplectic Lie algebra. On a boundaryless
manifold, in the preferred chart this is `TauCeti.SymplecticForm.IsNondegeneratePoint`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_iff_comp_extChartAt_symm`), and at a
critical point of `F` it is
`TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegenerateRankZeroPoint`. -/
structure IsNondegeneratePoint (F : M → G) (x : M) : Prop where
  /-- The map is `C²` at the point. -/
  contMDiffAt : ContMDiffAt I 𝓘(ℝ, G) 2 F x
  /-- The critical Hessians of the functions `ℓ ∘ F` with `ℓ ∘ dF_x = 0` vanish on
  `(U ∩ U^σ) × U` for `U = ker dF_x`, so they descend to the transversal space. -/
  polar_criticalHessian_eq_zero : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (mvfderiv I F x) = 0 →
    ∀ w ∈ (mvfderiv I F x).ker ⊓ (hσ.symplecticFormAt x).orthogonal (mvfderiv I F x).ker,
      ∀ u ∈ (mvfderiv I F x).ker,
        QuadraticMap.polar (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap w u = 0
  /-- The transversal Hessians form a nondegenerate family on the transversal space. -/
  isNondegenerateQuadraticFamily :
    ((hσ.symplecticFormAt x).reduction (mvfderiv I F x).ker).IsNondegenerateQuadraticFamily
      fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (mvfderiv I F x) = 0} ↦
        (hσ.symplecticFormAt x).reducedQuadraticForm _
          (criticalHessian I (ℓ.val ∘ F) x).toBilinForm.toQuadraticMap
          (polar_criticalHessian_eq_zero ℓ.val ℓ.property)

variable {hσ} {F : M → G} {x : M}

/-- The manifold notion of a nondegenerate point, unbundled: `F` is `C²` at `x` and the
differential `dF_x` and the critical Hessians of the functions `ℓ ∘ F` are transversally
nondegenerate for `σ` at `x`. This is the manifold counterpart of
`TauCeti.SymplecticForm.isNondegeneratePoint_iff_of_fderiv_eq`. -/
theorem isNondegeneratePoint_iff_isTransversallyNondegenerate :
    hσ.IsNondegeneratePoint F x ↔ ContMDiffAt I 𝓘(ℝ, G) 2 F x ∧
      SymplecticForm.IsTransversallyNondegenerate (hσ.symplecticFormAt x) (mvfderiv I F x)
        fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap :=
  ⟨fun h ↦ ⟨h.contMDiffAt, h.polar_criticalHessian_eq_zero, h.isNondegenerateQuadraticFamily⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- Being a nondegenerate point depends only on the germ of the map at the point. -/
theorem IsNondegeneratePoint.congr_of_eventuallyEq {F' : M → G}
    (h : hσ.IsNondegeneratePoint F x) (hF : F =ᶠ[𝓝 x] F') : hσ.IsNondegeneratePoint F' x := by
  obtain ⟨h₁, h₂⟩ := isNondegeneratePoint_iff_isTransversallyNondegenerate.1 h
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F') x).toBilinForm.toQuadraticMap :=
    funext fun ℓ ↦ by rw [criticalHessian_congr_of_eventuallyEq (hF.fun_comp ℓ)]
  rw [hQ, hF.mvfderiv_eq] at h₂
  exact isNondegeneratePoint_iff_isTransversallyNondegenerate.2
    ⟨h₁.congr_of_eventuallyEq hF.symm, h₂⟩

section Boundaryless

variable [I.Boundaryless]

/-- **Nondegenerate points in the preferred chart.** On a boundaryless manifold, `x` is a
nondegenerate point of `F` exactly when the chart image of `x` is a nondegenerate point, in the
linear sense, of the coordinate expression of `F` in the preferred chart at `x`, for the value of
`σ` at `x` read on the model space. -/
theorem isNondegeneratePoint_iff_comp_extChartAt_symm :
    hσ.IsNondegeneratePoint F x ↔
      SymplecticForm.IsNondegeneratePoint (E := E) (hσ.symplecticFormAt x)
        (F ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦
        hessianQuadraticForm (ℓ ∘ F ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    funext fun ℓ ↦ by rw [toQuadraticMap_toBilinForm_criticalHessian, Function.comp_assoc]
  rw [isNondegeneratePoint_iff_isTransversallyNondegenerate, hQ,
    mvfderiv_eq_fderiv_comp_extChartAt_symm, contMDiffAt_iff_contDiffAt_comp_extChartAt_symm]
  exact (SymplecticForm.isNondegeneratePoint_iff_of_fderiv_eq rfl).symm

/-- **Comparison with rank zero.** On a boundaryless manifold, at a critical point of `F` the
transversal space is the whole tangent space, and `x` is a nondegenerate point exactly when it is
a nondegenerate rank-zero point. -/
theorem isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h : mvfderiv I F x = 0) :
    hσ.IsNondegeneratePoint F x ↔ hσ.IsNondegenerateRankZeroPoint F x := by
  rw [isNondegeneratePoint_iff_comp_extChartAt_symm,
    isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm]
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm] at h
  exact SymplecticForm.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h

/-! ### Symplectic changes of coordinates -/

section Comp

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H' N] {φ : N → M} {y : N}

/-- The common core of the invariance theorems: if `φ` is `C²` at `y` with invertible differential
`dφ_y`, which carries a symplectic form `η` on `T_y N` to `σ` at `φ y`, then the differential of
`F ∘ φ` and the critical Hessians of the functions `ℓ ∘ F ∘ φ` are transversally nondegenerate for
`η` exactly when `φ y` is a nondegenerate point of `F`. -/
private theorem isNondegeneratePoint_iff_comp_right_aux
    (η : SymplecticForm (TangentSpace I' y)) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hη : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      η u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    (ContMDiffAt I' 𝓘(ℝ, G) 2 (F ∘ φ) y ∧
      SymplecticForm.IsTransversallyNondegenerate η (mvfderiv I' (F ∘ φ) y)
        fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I' (ℓ ∘ F ∘ φ) y).toBilinForm.toQuadraticMap) ↔
      hσ.IsNondegeneratePoint F (φ y) := by
  obtain ⟨e, he⟩ := hinv
  have hFd : MDifferentiableAt I 𝓘(ℝ, G) F (φ y) := hF.mdifferentiableAt two_ne_zero
  have hφd : MDifferentiableAt I' I φ y := hφ.mdifferentiableAt two_ne_zero
  -- The differential of `F ∘ φ` is `dF ∘ dφ`.
  have hT : mvfderiv I' (F ∘ φ) y = (mvfderiv I F (φ y)).comp (e : TangentSpace I' y →L[ℝ] _) := by
    rw [mvfderiv_comp y hFd hφd, ← he]
  -- For `ℓ` killing the image of `dF`, the chain rule identifies the Hessians through `dφ_y`.
  have hQ (ℓ : G →L[ℝ] ℝ) (hℓ : ℓ.comp (mvfderiv I F (φ y)) = 0) :
      (criticalHessian I' (ℓ ∘ F ∘ φ) y).toBilinForm.toQuadraticMap =
        (criticalHessian I (ℓ ∘ F) (φ y)).toBilinForm.toQuadraticMap.comp e.toLinearEquiv := by
    have hcrit : φ y ∈ criticalPoints I (ℓ ∘ F) := mem_criticalPoints.2 <|
      ContinuousLinearMap.ext fun v ↦ by simpa [ℓ.mvfderiv_comp_apply hFd] using congr($hℓ v)
    rw [← Function.comp_assoc, toQuadraticMap_toBilinForm_criticalHessian_comp
      (ℓ.contMDiff.contMDiffAt.comp _ hF) hφ hcrit, ← he,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  have hsymp : SymplecticForm.IsSymplectomorphism η (hσ.symplecticFormAt (φ y)) e.toLinearEquiv :=
    SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ by simp [← hη, ← he]
  have key := SymplecticForm.isTransversallyNondegenerate_comp_iff e hsymp
    (mvfderiv I F (φ y)) hQ
  rw [hT, key, isNondegeneratePoint_iff_isTransversallyNondegenerate]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨hF, h⟩, fun ⟨_, h⟩ ↦ ⟨hF.comp y hφ, h⟩⟩

/-- **Invariance under symplectic changes of coordinates.** Let `M` be boundaryless, let `τ` be a
nondegenerate two-form on a boundaryless manifold `N` and let `φ : N → M` be `C²` at `y`, with
invertible differential there, pulling `σ` back to `τ` at `y`. For `F` which is `C²` at `φ y`, the
point `y` is a nondegenerate point of `F ∘ φ` for `τ` exactly when `φ y` is one of `F` for `σ`. -/
theorem isNondegeneratePoint_comp_right_iff [IsManifold I' ∞ N] {τ : SmoothTwoForm I' N}
    (hτ : τ.IsNondegenerate) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hστ : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      SmoothBundleForm.eval₂ τ y u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    hτ.IsNondegeneratePoint (F ∘ φ) y ↔ hσ.IsNondegeneratePoint F (φ y) := by
  refine Iff.trans ?_ (isNondegeneratePoint_iff_comp_right_aux (hτ.symplecticFormAt y) hφ hinv
    (fun u w ↦ (hστ u w).trans (symplecticFormAt_apply hτ y u w).symm) hF)
  exact isNondegeneratePoint_iff_isTransversallyNondegenerate

/-- **Nondegenerate points in symplectic coordinates.** Let `φ : E' → M` be a map from a symplectic
vector space `(E', ω₀)` into the boundaryless manifold `M`, such as the inverse of a Darboux chart,
which is `C²` at `y`, has invertible differential there and pulls `σ` back to `ω₀` at `y`. For `F`
which is `C²` at `φ y`, the point `y` is a nondegenerate point of the coordinate expression `F ∘ φ`,
in the linear sense, exactly when `φ y` is a nondegenerate point of `F`. -/
theorem _root_.TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff
    (ω₀ : SymplecticForm E') {φ : E' → M} {y : E'} (hφ : ContMDiffAt 𝓘(ℝ, E') I 2 φ y)
    (hinv : (mfderiv 𝓘(ℝ, E') I φ y).IsInvertible)
    (hσω : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv 𝓘(ℝ, E') I φ y u)
      (mfderiv 𝓘(ℝ, E') I φ y w) = ω₀ u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    ω₀.IsNondegeneratePoint (F ∘ φ) y ↔ hσ.IsNondegeneratePoint F (φ y) := by
  refine Iff.trans ?_ (isNondegeneratePoint_iff_comp_right_aux ω₀ hφ hinv hσω hF)
  -- On the model space, manifold smoothness, derivatives and Hessians are the usual ones.
  have hT : mvfderiv 𝓘(ℝ, E') (F ∘ φ) y = fderiv ℝ (F ∘ φ) y :=
    ContinuousLinearMap.ext fun v ↦ mvfderiv_eq_fderiv_apply _ y v
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦
      (criticalHessian 𝓘(ℝ, E') (ℓ ∘ F ∘ φ) y).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ (F ∘ φ)) y :=
    funext fun ℓ ↦ by
      rw [criticalHessian_modelSpace, hessianQuadraticForm_def]
      -- The two sides differ only in reading `E'` as `TangentSpace 𝓘(ℝ, E') y`.
      rfl
  rw [SymplecticForm.isNondegeneratePoint_iff_of_fderiv_eq rfl, hT, hQ,
    contMDiffAt_iff_contDiffAt]
  -- The two sides differ only in the instances on `E'` and on `TangentSpace 𝓘(ℝ, E') y`.
  exact Iff.rfl

/-- **Invariance of rank-zero nondegeneracy under symplectic changes of coordinates.** Let `M` be
boundaryless, let `τ` be a nondegenerate two-form on a boundaryless manifold `N` and let
`φ : N → M` be `C²` at `y`, with invertible differential there, pulling `σ` back to `τ` at `y`.
For `F` which is `C²` at `φ y`, the point `y` is a nondegenerate rank-zero point of `F ∘ φ` for `τ`
exactly when `φ y` is one of `F` for `σ`. -/
theorem isNondegenerateRankZeroPoint_comp_right_iff [IsManifold I' ∞ N] {τ : SmoothTwoForm I' N}
    (hτ : τ.IsNondegenerate) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hστ : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      SmoothBundleForm.eval₂ τ y u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    hτ.IsNondegenerateRankZeroPoint (F ∘ φ) y ↔ hσ.IsNondegenerateRankZeroPoint F (φ y) := by
  have h0 := mvfderiv_comp_eq_zero_iff_of_isInvertible (hF.mdifferentiableAt two_ne_zero) hinv
  by_cases h : mvfderiv I F (φ y) = 0
  · rw [← isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h0.2 h),
      ← isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h]
    exact isNondegeneratePoint_comp_right_iff hτ hφ hinv hστ hF
  · exact iff_of_false (fun h' ↦ h (h0.1 h'.mvfderiv_eq_zero)) fun h' ↦ h h'.mvfderiv_eq_zero

/-- **Nondegenerate rank-zero points in symplectic coordinates.** Let `φ : E' → M` be a map from a
symplectic vector space `(E', ω₀)` into the boundaryless manifold `M`, such as the inverse of a
Darboux chart, which is `C²` at `y`, has invertible differential there and pulls `σ` back to `ω₀`
at `y`. For `F` which is `C²` at `φ y`, the point `y` is a nondegenerate rank-zero point of the
coordinate expression `F ∘ φ`, in the linear sense, exactly when `φ y` is a nondegenerate rank-zero
point of `F`. -/
theorem _root_.TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_comp_right_iff
    (ω₀ : SymplecticForm E') {φ : E' → M} {y : E'} (hφ : ContMDiffAt 𝓘(ℝ, E') I 2 φ y)
    (hinv : (mfderiv 𝓘(ℝ, E') I φ y).IsInvertible)
    (hσω : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv 𝓘(ℝ, E') I φ y u)
      (mfderiv 𝓘(ℝ, E') I φ y w) = ω₀ u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    ω₀.IsNondegenerateRankZeroPoint (F ∘ φ) y ↔ hσ.IsNondegenerateRankZeroPoint F (φ y) := by
  -- On the model space, the manifold derivative is the usual one.
  have h0 : fderiv ℝ (F ∘ φ) y = 0 ↔ mvfderiv I F (φ y) = 0 := by
    rw [← mvfderiv_comp_eq_zero_iff_of_isInvertible (hF.mdifferentiableAt two_ne_zero) hinv]
    exact ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦
        (mvfderiv_eq_fderiv_apply _ y v).trans congr($h v),
      fun h ↦ ContinuousLinearMap.ext fun v ↦
        (mvfderiv_eq_fderiv_apply _ y v).symm.trans congr($h v)⟩
  by_cases h : mvfderiv I F (φ y) = 0
  · rw [← SymplecticForm.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h0.2 h),
      ← isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h]
    exact SymplecticForm.isNondegeneratePoint_comp_right_iff ω₀ hφ hinv hσω hF
  · exact iff_of_false (fun h' ↦ h (h0.1 h'.fderiv_eq_zero)) fun h' ↦ h h'.mvfderiv_eq_zero

end Comp

end Boundaryless

end SmoothTwoForm.IsNondegenerate

end TauCeti
