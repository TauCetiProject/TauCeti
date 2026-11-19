/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint

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

* In the preferred chart at `x`, the notion is the linear one for the coordinate expression of `F`
  and the value of `σ` at `x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_iff_comp_extChartAt_symm`).
* It is invariant under symplectic changes of coordinates: if `φ : N → M` is `C²` at `y`, has
  invertible differential there and pulls `σ` back to `τ` at `y`, then `y` is a nondegenerate
  point of `F ∘ φ` for `τ` exactly when `φ y` is one of `F` for `σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_comp_right_iff`). The differential
  `dφ_y` is a linear symplectomorphism carrying `ker d(F ∘ φ)_y` onto `ker dF_(φ y)`, so it induces
  a symplectomorphism of transversal spaces
  (`TauCeti.SymplecticForm.reducedSpaceCongr`), and the second-order chain rule at a critical point
  (`TauCeti.criticalHessian_comp_apply`) identifies the transversal Hessians through it. The same
  holds for a parametrization `φ : E' → M` by a symplectic vector space `(E', ω₀)`, such as a
  Darboux chart, with the linear notion on the source
  (`TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff`), so nondegeneracy may be checked
  in any symplectic coordinates.
* It depends only on the germ of `F`, and at a critical point of `F` it is nondegeneracy of rank
  zero (`IsNondegenerate.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint`, in the namespace
  `TauCeti.SmoothTwoForm`).

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

/-! ### Transversal nondegeneracy of a linear map and a family of quadratic forms -/

namespace SymplecticForm

variable {V V' G : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [FiniteDimensional ℝ V] [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V']
  [FiniteDimensional ℝ V'] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The common content of the linear and the manifold notion of a nondegenerate point, for the
differential `T` of the map and the Hessians `Q ℓ` of the functions `ℓ ∘ F`: the forms `Q ℓ` with
`ℓ ∘ T = 0` descend to the reduced space of `ker T` and form a nondegenerate family there. -/
private def IsTransversallyNondegenerate (ω₁ : SymplecticForm V) (T : V →L[ℝ] G)
    (Q : (G →L[ℝ] ℝ) → QuadraticForm ℝ V) : Prop :=
  ∃ hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω₁.orthogonal T.ker, ∀ u ∈ T.ker,
      QuadraticMap.polar (Q ℓ) w u = 0,
    (ω₁.reduction T.ker).IsNondegenerateQuadraticFamily
      fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦ ω₁.reducedQuadraticForm _ (Q ℓ.1) (hQ ℓ.1 ℓ.2)

/-- The linear notion of a nondegenerate point, unbundled. -/
private theorem isNondegeneratePoint_iff_isTransversallyNondegenerate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ω₁ : SymplecticForm E}
    {F : E → G} {x : E} :
    ω₁.IsNondegeneratePoint F x ↔ ContDiffAt ℝ 2 F x ∧
      IsTransversallyNondegenerate ω₁ (fderiv ℝ F x)
        fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- A functional kills the image of `T ∘ e` exactly when it kills the image of `T`. -/
private theorem comp_comp_eq_zero_iff (e : V ≃L[ℝ] V') (T : V' →L[ℝ] G) (ℓ : G →L[ℝ] ℝ) :
    ℓ.comp (T.comp (e : V →L[ℝ] V')) = 0 ↔ ℓ.comp T = 0 := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ by
    rw [← ContinuousLinearMap.comp_assoc, h, ContinuousLinearMap.zero_comp]⟩
  simpa using congr($h (e.symm v))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- `e` carries `ker (T ∘ e)` onto `ker T`. -/
private theorem map_ker_comp (e : V ≃L[ℝ] V') (T : V' →L[ℝ] G) :
    (T.comp (e : V →L[ℝ] V')).ker.map (e.toLinearEquiv : V →ₗ[ℝ] V') = T.ker := by
  ext v'
  rw [Submodule.mem_map_equiv]
  simp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- The descent condition of a quadratic form `R` on `V'` along `ker T` holds exactly when it holds
for its pullback `R ∘ e` along `ker (T ∘ e)`, for a linear symplectomorphism `e`: `e` carries
`U ∩ U^ω₁` onto `U' ∩ U'^ω₂`, for `U = ker (T ∘ e)` and `U' = ker T`. -/
private theorem forall_polar_comp_eq_zero_iff {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm V'}
    (e : V ≃L[ℝ] V') (he : IsSymplectomorphism ω₁ ω₂ e.toLinearEquiv) (T : V' →L[ℝ] G)
    (R : QuadraticForm ℝ V') :
    (∀ w ∈ (T.comp (e : V →L[ℝ] V')).ker ⊓ ω₁.orthogonal (T.comp (e : V →L[ℝ] V')).ker,
        ∀ u ∈ (T.comp (e : V →L[ℝ] V')).ker,
          QuadraticMap.polar (R.comp (e.toLinearEquiv : V →ₗ[ℝ] V')) w u = 0) ↔
      ∀ w ∈ T.ker ⊓ ω₂.orthogonal T.ker, ∀ u ∈ T.ker, QuadraticMap.polar R w u = 0 := by
  have hker (v : V) : v ∈ (T.comp (e : V →L[ℝ] V')).ker ↔ e v ∈ T.ker := by simp
  have horth (v : V) : v ∈ ω₁.orthogonal (T.comp (e : V →L[ℝ] V')).ker ↔
      e v ∈ ω₂.orthogonal T.ker := by
    rw [← map_ker_comp e T, ← he.map_orthogonal, Submodule.mem_map_equiv]
    simp
  simp only [Submodule.mem_inf, hker, horth]
  constructor
  · intro h w' hw' u' hu'
    obtain ⟨w, rfl⟩ := e.surjective w'
    obtain ⟨u, rfl⟩ := e.surjective u'
    simpa [QuadraticMap.polar, map_add] using h w hw' u hu'
  · intro h w hw u hu
    simpa [QuadraticMap.polar, map_add] using h _ hw _ hu

/-- **Transport of transversal nondegeneracy along a linear symplectomorphism.** Let
`e : V ≃ V'` carry `ω₁` to `ω₂` and let `T : V' → G` be linear. If the forms `Q' ℓ` on `V` are the
pullbacks along `e` of the forms `Q ℓ` on `V'` whenever `ℓ ∘ T = 0`, then `(T ∘ e, Q')` is
transversally nondegenerate for `ω₁` exactly when `(T, Q)` is for `ω₂`: `e` carries `ker (T ∘ e)`
onto `ker T` and induces a symplectomorphism of the reduced spaces through which the reduced
forms correspond. -/
private theorem isTransversallyNondegenerate_comp_iff {ω₁ : SymplecticForm V}
    {ω₂ : SymplecticForm V'} (e : V ≃L[ℝ] V') (he : IsSymplectomorphism ω₁ ω₂ e.toLinearEquiv)
    (T : V' →L[ℝ] G) {Q : (G →L[ℝ] ℝ) → QuadraticForm ℝ V'}
    {Q' : (G →L[ℝ] ℝ) → QuadraticForm ℝ V}
    (hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → Q' ℓ = (Q ℓ).comp (e.toLinearEquiv : V →ₗ[ℝ] V')) :
    IsTransversallyNondegenerate ω₁ (T.comp (e : V →L[ℝ] V')) Q' ↔
      IsTransversallyNondegenerate ω₂ T Q := by
  have hdesc : (∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (T.comp (e : V →L[ℝ] V')) = 0 →
        ∀ w ∈ (T.comp (e : V →L[ℝ] V')).ker ⊓ ω₁.orthogonal (T.comp (e : V →L[ℝ] V')).ker,
          ∀ u ∈ (T.comp (e : V →L[ℝ] V')).ker, QuadraticMap.polar (Q' ℓ) w u = 0) ↔
      ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω₂.orthogonal T.ker, ∀ u ∈ T.ker,
        QuadraticMap.polar (Q ℓ) w u = 0 := by
    refine forall_congr' fun ℓ ↦ ?_
    rw [comp_comp_eq_zero_iff]
    refine imp_congr_right fun hℓT ↦ ?_
    rw [hQ ℓ hℓT]
    exact forall_polar_comp_eq_zero_iff e he T (Q ℓ)
  have hc := isSymplectomorphism_reducedSpaceCongr e.toLinearEquiv he (map_ker_comp e T)
  -- Reindexing the functionals killing the image of `T ∘ e` by those killing the image of `T`.
  let r : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ≃
      {ℓ : G →L[ℝ] ℝ // ℓ.comp (T.comp (e : V →L[ℝ] V')) = 0} :=
    Equiv.subtypeEquivRight fun ℓ ↦ (comp_comp_eq_zero_iff e T ℓ).symm
  -- The reduced forms of the `Q' ℓ` are those of the `Q ℓ`, read through the induced map.
  have key (hD : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω₂.orthogonal T.ker,
      ∀ u ∈ T.ker, QuadraticMap.polar (Q ℓ) w u = 0) :
      (ω₁.reduction (T.comp (e : V →L[ℝ] V')).ker).IsNondegenerateQuadraticFamily
          (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (T.comp (e : V →L[ℝ] V')) = 0} ↦
            ω₁.reducedQuadraticForm _ (Q' ℓ.1) (hdesc.2 hD ℓ.1 ℓ.2)) ↔
        (ω₂.reduction T.ker).IsNondegenerateQuadraticFamily
          fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦
            ω₂.reducedQuadraticForm _ (Q ℓ.1) (hD ℓ.1 ℓ.2) := by
    rw [← isNondegenerateQuadraticFamily_comp_iff hc]
    refine isNondegenerateQuadraticFamily_iff_of_span_eq (congrArg _ ?_)
    refine (r.surjective.range_comp _).symm.trans (congrArg range (funext fun ℓ ↦ ?_))
    rw [Function.comp_apply, reducedQuadraticForm_comp_reducedSpaceCongr
      (hQe := (forall_polar_comp_eq_zero_iff e he T _).2 (hD ℓ.1 ℓ.2))]
    congr 1
    exact hQ ℓ.1 ℓ.2
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨hdesc.1 h₁, (key (hdesc.1 h₁)).1 h₂⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨hdesc.2 h₁, (key h₁).2 h₂⟩⟩

end SymplecticForm

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
          (criticalHessian I (ℓ.1 ∘ F) x).toBilinForm.toQuadraticMap
          (polar_criticalHessian_eq_zero ℓ.1 ℓ.2)

variable {hσ} {F : M → G} {x : M}

/-- The manifold notion of a nondegenerate point, unbundled. -/
private theorem isNondegeneratePoint_iff_isTransversallyNondegenerate :
    hσ.IsNondegeneratePoint F x ↔ ContMDiffAt I 𝓘(ℝ, G) 2 F x ∧
      SymplecticForm.IsTransversallyNondegenerate (hσ.symplecticFormAt x) (mvfderiv I F x)
        fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

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
  exact SymplecticForm.isNondegeneratePoint_iff_isTransversallyNondegenerate.symm

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
        (criticalHessian I (ℓ ∘ F) (φ y)).toBilinForm.toQuadraticMap.comp
          (e.toLinearEquiv : TangentSpace I' y →ₗ[ℝ] TangentSpace I (φ y)) := by
    have hcrit : φ y ∈ criticalPoints I (ℓ ∘ F) := by
      refine mem_criticalPoints.2 (ContinuousLinearMap.ext fun v ↦ ?_)
      rw [ℓ.mvfderiv_comp_apply hFd]
      simpa using congr($hℓ v)
    ext u
    simp [← Function.comp_assoc,
      criticalHessian_comp_apply rfl (ℓ.contMDiff.contMDiffAt.comp _ hF) hφ hcrit, ← he]
  have hsymp : SymplecticForm.IsSymplectomorphism η (hσ.symplecticFormAt (φ y)) e.toLinearEquiv :=
    SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ by simp [← hη, ← he]
  have key := SymplecticForm.isTransversallyNondegenerate_comp_iff e hsymp
    (mvfderiv I F (φ y)) hQ
  rw [hT, key, isNondegeneratePoint_iff_isTransversallyNondegenerate]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨hF, h⟩, fun ⟨_, h⟩ ↦ ⟨hF.comp y hφ, h⟩⟩

/-- **Invariance under symplectic changes of coordinates.** Let `τ` be a nondegenerate two-form on
a boundaryless manifold `N` and let `φ : N → M` be `C²` at `y`, with invertible differential there,
pulling `σ` back to `τ` at `y`. For `F` which is `C²` at `φ y`, the point `y` is a nondegenerate
point of `F ∘ φ` for `τ` exactly when `φ y` is one of `F` for `σ`. -/
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
vector space `(E', ω₀)`, such as the inverse of a Darboux chart, which is `C²` at `y`, has
invertible differential there and pulls `σ` back to `ω₀` at `y`. For `F` which is `C²` at `φ y`,
the point `y` is a nondegenerate point of the coordinate expression `F ∘ φ`, in the linear sense,
exactly when `φ y` is a nondegenerate point of `F`. -/
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
      rw [toQuadraticMap_toBilinForm_criticalHessian]
      simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
        Function.comp_id, id_eq]
      -- The two sides differ only in the instances on `TangentSpace 𝓘(ℝ, E') y` and on `E'`.
      rfl
  rw [SymplecticForm.isNondegeneratePoint_iff_isTransversallyNondegenerate, hT, hQ,
    contMDiffAt_iff_contDiffAt]
  -- The two sides differ only in the instances on `E'` and on `TangentSpace 𝓘(ℝ, E') y`.
  exact Iff.rfl

end Comp

end Boundaryless

end SmoothTwoForm.IsNondegenerate

end TauCeti
