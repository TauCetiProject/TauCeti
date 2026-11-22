/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Nondegenerate rank-zero points on symplectic manifolds

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M` and let `F : M → G` be a
map into a normed space, for instance the momentum map `F = (F₁, …, Fₙ) : M → ℝⁿ` of an integrable
system. A point `x` where the differential of `F` vanishes is a singular point of rank zero. There
the function `ℓ ∘ F` is critical for every linear functional `ℓ` on `G`, so its Hessian is an
intrinsic quadratic form on the tangent space `T_x M` (`TauCeti.criticalHessian`). Following
Williamson and Eliasson, `x` is a **nondegenerate rank-zero point** of `F`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegenerateRankZeroPoint`) when these Hessians form a
nondegenerate family on the symplectic vector space `(T_x M, σ_x)`: their Hamiltonian
endomorphisms generate a Cartan subalgebra of `sp(T_x M, σ_x)`
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`).

This file transfers the linear notion `TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint`, which
lives on a symplectic vector space, to manifolds, and shows that it is intrinsic.

* In the preferred chart at `x`, the notion is the linear one for the coordinate expression of `F`
  and the value of `σ` at `x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm`).
* Its invariance under symplectic changes of coordinates is a special case of that of
  nondegenerate points of positive rank, and is proved with it in
  `TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint.Manifold`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegenerateRankZeroPoint_comp_right_iff` and
  `TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_comp_right_iff`).
* It depends only on the germ of `F`, may be tested on the Hessians of the components when
  `G = ℝⁿ`, and is unchanged by composing `F` with a map whose differential is injective.
* On a surface, a nondegenerate rank-zero point of one Hamiltonian `H` is exactly a nondegenerate
  critical point of `H` in the sense of Morse theory
  (`IsNondegenerate.isNondegenerateRankZeroPoint_iff_isManifoldNondegenerateCriticalPoint`, in
  the namespace `TauCeti.SmoothTwoForm`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegenerateRankZeroPoint hσ F x`: `x` is a `C²`
  critical point of `F` at which the critical Hessians of the functions `ℓ ∘ F` form a
  nondegenerate family on `(T_x M, σ_x)`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G']
  [NormedSpace ℝ G']

namespace SmoothTwoForm.IsNondegenerate

variable (hσ : σ.IsNondegenerate)

/-- A point `x` is a **nondegenerate rank-zero point** of a map `F : M → G` for a nondegenerate
two-form `σ` when `F` is `C²` at `x`, its differential vanishes at `x`, and the critical Hessians
at `x` of the functions `ℓ ∘ F`, for `ℓ` a linear functional on `G`, form a nondegenerate family on
the symplectic vector space `(T_x M, σ_x)`: their Hamiltonian endomorphisms generate a Cartan
subalgebra of `sp(T_x M, σ_x)`. For `G = ℝⁿ` these are the Hessians of the components of `F`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegenerateRankZeroPoint_pi_iff`). -/
@[mk_iff]
structure IsNondegenerateRankZeroPoint (F : M → G) (x : M) : Prop where
  /-- The map is `C²` at the point. -/
  contMDiffAt : ContMDiffAt I 𝓘(ℝ, G) 2 F x
  /-- The differential vanishes at the point. -/
  mvfderiv_eq_zero : mvfderiv I F x = 0
  /-- The critical Hessians of the functions `ℓ ∘ F` form a nondegenerate family. -/
  isNondegenerateQuadraticFamily : (hσ.symplecticFormAt x).IsNondegenerateQuadraticFamily
    fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap

variable {hσ} {F : M → G} {x : M}

/-- Being a nondegenerate rank-zero point depends only on the germ of the map at the point. -/
theorem IsNondegenerateRankZeroPoint.congr_of_eventuallyEq {F' : M → G}
    (h : hσ.IsNondegenerateRankZeroPoint F x) (hF : F =ᶠ[𝓝 x] F') :
    hσ.IsNondegenerateRankZeroPoint F' x := by
  refine ⟨h.contMDiffAt.congr_of_eventuallyEq hF.symm, ?_, ?_⟩
  · rw [← hF.mvfderiv_eq]
    exact h.mvfderiv_eq_zero
  · convert h.isNondegenerateQuadraticFamily using 4 with ℓ
    exact criticalHessian_congr_of_eventuallyEq (hF.fun_comp ℓ).symm

/-- A nondegenerate rank-zero point may be tested on any family of quadratic forms on the tangent
space that, at a `C²` critical point, spans the same space as the critical Hessians of the
functions `ℓ ∘ F`. -/
theorem isNondegenerateRankZeroPoint_iff_of_span_eq {κ : Type*}
    {Q : κ → QuadraticForm ℝ (TangentSpace I x)}
    (h : ContMDiffAt I 𝓘(ℝ, G) 2 F x → mvfderiv I F x = 0 →
      Submodule.span ℝ (range fun ℓ : G →L[ℝ] ℝ ↦
        (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) = Submodule.span ℝ (range Q)) :
    hσ.IsNondegenerateRankZeroPoint F x ↔ ContMDiffAt I 𝓘(ℝ, G) 2 F x ∧ mvfderiv I F x = 0 ∧
      (hσ.symplecticFormAt x).IsNondegenerateQuadraticFamily Q := by
  rw [isNondegenerateRankZeroPoint_iff]
  exact and_congr_right fun hF ↦ and_congr_right fun h0 ↦
    SymplecticForm.isNondegenerateQuadraticFamily_iff_of_span_eq (h hF h0)

/-! ### The preferred chart -/

section Boundaryless

variable [I.Boundaryless]

/-- **Nondegenerate rank-zero points in the preferred chart.** On a boundaryless manifold, `x` is a
nondegenerate rank-zero point of `F` exactly when the chart image of `x` is a nondegenerate
rank-zero point, in the linear sense, of the coordinate expression of `F` in the preferred chart at
`x`, for the value of `σ` at `x` read on the model space. -/
theorem isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm :
    hσ.IsNondegenerateRankZeroPoint F x ↔
      SymplecticForm.IsNondegenerateRankZeroPoint (E := E) (hσ.symplecticFormAt x)
        (F ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  constructor
  · intro h
    refine ⟨h.contMDiffAt.contDiffAt_comp_extChartAt_symm, ?_, ?_⟩
    · rw [← mvfderiv_eq_fderiv_comp_extChartAt_symm]
      exact h.mvfderiv_eq_zero
    · have h' := h.isNondegenerateQuadraticFamily
      simp only [toQuadraticMap_toBilinForm_criticalHessian, Function.comp_assoc] at h'
      exact h'
  · intro h
    refine ⟨contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 h.contDiffAt, ?_, ?_⟩
    · rw [mvfderiv_eq_fderiv_comp_extChartAt_symm]
      exact h.fderiv_eq_zero
    · simp only [toQuadraticMap_toBilinForm_criticalHessian, Function.comp_assoc]
      exact h.isNondegenerateQuadraticFamily

/-- **Nondegenerate rank-zero points in coordinates.** For `F = (F₁, …, Fₙ) : M → ℝⁿ` on a
boundaryless manifold, a point is a nondegenerate rank-zero point exactly when it is a `C²` critical
point of `F` at which the critical Hessians of the components `Fᵢ` form a nondegenerate family. -/
theorem isNondegenerateRankZeroPoint_pi_iff {ι : Type*} [Fintype ι] {F : M → ι → ℝ} :
    hσ.IsNondegenerateRankZeroPoint F x ↔ ContMDiffAt I 𝓘(ℝ, ι → ℝ) 2 F x ∧
      mvfderiv I F x = 0 ∧ (hσ.symplecticFormAt x).IsNondegenerateQuadraticFamily
        fun i ↦ (criticalHessian I (F · i) x).toBilinForm.toQuadraticMap := by
  refine isNondegenerateRankZeroPoint_iff_of_span_eq fun hF _ ↦ ?_
  simp only [toQuadraticMap_toBilinForm_criticalHessian, Function.comp_assoc]
  exact span_range_hessianQuadraticForm_pi hF.contDiffAt_comp_extChartAt_symm

/-- **Invariance under reparametrization of the values.** On a boundaryless manifold, composing `F`
with a `C²` map `g` whose differential at `F x` is injective preserves and reflects nondegenerate
rank-zero points. -/
theorem isNondegenerateRankZeroPoint_comp_iff [FiniteDimensional ℝ G'] {g : G → G'}
    (hg : ContDiffAt ℝ 2 g (F x)) (hinj : Injective (fderiv ℝ g (F x)))
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F x) :
    hσ.IsNondegenerateRankZeroPoint (g ∘ F) x ↔ hσ.IsNondegenerateRankZeroPoint F x := by
  rw [isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm,
    isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm, Function.comp_assoc]
  exact SymplecticForm.isNondegenerateRankZeroPoint_comp_iff (by simpa using hg)
    (by simpa using hinj) hF.contDiffAt_comp_extChartAt_symm

/-- **Nondegenerate rank-zero points of one Hamiltonian on a symplectic surface.** On a boundaryless
two-dimensional manifold, a point is a nondegenerate rank-zero point of a function `H` exactly when
it is a nondegenerate critical point of `H` in the sense of Morse theory. -/
theorem isNondegenerateRankZeroPoint_iff_isManifoldNondegenerateCriticalPoint
    (hE : finrank ℝ E = 2) {H : M → ℝ} :
    hσ.IsNondegenerateRankZeroPoint H x ↔ IsManifoldNondegenerateCriticalPoint I H x := by
  rw [isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm,
    isManifoldNondegenerateCriticalPoint_iff]
  exact SymplecticForm.isNondegenerateRankZeroPoint_iff_isNondegenerateCriticalPoint hE

end Boundaryless

end SmoothTwoForm.IsNondegenerate

end TauCeti
