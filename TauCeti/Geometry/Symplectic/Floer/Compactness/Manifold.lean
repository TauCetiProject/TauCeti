/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Compactness of Floer solutions in a chart of a manifold

Let `ω` be a two-form on a manifold `M` modelled on a finite-dimensional real inner product space
`E`, and let `u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` for a perturbation
`K = K_s ds + K_t dt` and a domain-dependent almost complex structure `J(z, x)` on the tangent
spaces of `M`. This file reads such solutions in the extended chart `ψ = extChartAt I x₀` at a
point `x₀` and transfers the compactness theorem off finitely many bubbling points of
`TauCeti.Geometry.Symplectic.Floer.Compactness` to them.

* **The equation in a chart.** Write `T_x = dψ_x : T_x M → E` and `S_y = d(ψ⁻¹)_y : E → T_{ψ⁻¹ y} M`
  for the derivatives of the chart and its inverse. If `u z` lies in the chart, the chart reading
  `ψ ∘ u` solves the coordinate equation
  `∂ₜ(ψ ∘ u) - T X_{K_t}(u) = T J(z, u) S (∂ₛ(ψ ∘ u) - T X_{K_s}(u))`
  (`TauCeti.SmoothTwoForm.fderiv_extChartAt_comp_stdComplexLineImag_sub`): the structure
  `T J S` and the vector fields `T X_{K_s}`, `T X_{K_t}` are the data of `J` and `K` read in the
  chart.
* **Energy in a chart.** On a compact window `D × K` of domain points and chart points where the
  structures are tamed by `ω`, the chart coefficients of `ω` (`TauCeti.RoughForm.inChartAt`) and
  the chart structure give one taming constant. Hence the Floer energy density bounds the chart
  derivative, `‖∂ₛ(ψ ∘ u)‖² ≤ A ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t}) + B`
  (`SmoothTwoForm.exists_forall_norm_fderiv_extChartAt_comp_stdComplexLineReal_sq_le`).
* **Compactness in a chart.** If the chart data are `C²`, a sequence of `C³` solutions with images
  in a fixed compact set of chart points and bounded Floer energy has a subsequence whose chart
  readings converge locally uniformly off a finite set `Z` of bubbling points, with derivatives
  bounded on compact subsets away from `Z`, and at each point of `Z` Floer energy at least a fixed
  threshold `δ` concentrates; in particular `#Z * δ` is at most the energy bound. The maps
  themselves converge pointwise in `M` off `Z`
  (`SmoothTwoForm.exists_pos_forall_tendstoLocallyUniformlyOn_extChartAt_comp_subseq_off_finset`).
  This applies the coordinate theorem
  `TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm_sq_le`
  with the Floer energy density of the maps in `M` as energy density.

The images are assumed to stay in a compact set of one chart. Covering a closed target by finitely
many charts, and the a priori estimates that keep small discs of the domain inside one chart, are
not treated here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the inhomogeneous equation).
-/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

section Chart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {Ks Kt : ℝ × ℝ → M → ℝ} {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- **The Floer equation in a chart.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` at
`z` for the structure `J(z, u z)`, with `u` differentiable at `z` and `u z` in the source of the
extended chart `ψ = extChartAt I x₀`. With `T = dψ_(u z)` and `S` the derivative of `ψ⁻¹` at
`ψ (u z)`, the chart reading `ψ ∘ u` satisfies
`∂ₜ(ψ ∘ u) - T X_{K_t} = T J S (∂ₛ(ψ ∘ u) - T X_{K_s})`. -/
theorem fderiv_extChartAt_comp_stdComplexLineImag_sub (ω : SmoothTwoForm I M) (x₀ : M)
    {u : ℝ × ℝ → M} {z : ℝ × ℝ} (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hz : u z ∈ (extChartAt I x₀).source)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    fderiv ℝ (extChartAt I x₀ ∘ u) z stdComplexLineImag -
        mvfderiv I (extChartAt I x₀) (u z) (ω.hamiltonianVectorField (Kt z) (u z)) =
      mvfderiv I (extChartAt I x₀) (u z) (J z (u z)
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ (u z))
          (fderiv ℝ (extChartAt I x₀ ∘ u) z stdComplexLineReal -
            mvfderiv I (extChartAt I x₀) (u z)
              (ω.hamiltonianVectorField (Ks z) (u z))))) := by
  -- The chart reading is differentiated by the chain rule, `S` inverts `T`, and the perturbed
  -- derivative is `J`-linear.
  have hd (v : ℝ × ℝ) : fderiv ℝ (extChartAt I x₀ ∘ u) z v =
      mvfderiv I (extChartAt I x₀) (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v) :=
    (mvfderiv_eq_fderiv_apply _ z v).symm.trans (mvfderiv_comp_apply z
      (mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hz)) hu v)
  have hST (a : TangentSpace I (u z)) :
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ (u z))
        (mvfderiv I (extChartAt I x₀) (u z) a) = a := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hz) a)
  have hP := h.apply_stdComplexLineImag
  simp only [ContinuousLinearMap.coe_coe, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag] at hP
  rw [hd, hd, ← map_sub, ← map_sub, hST, ← hP]

/-- Tameness at the chart points `y ∈ K`, read at the points `x` of the chart with `ψ x ∈ K`. -/
private theorem tames_of_mem_extChartAt_source {ω : SmoothTwoForm I M} {x₀ x : M} {z : ℝ × ℝ}
    {K : Set E}
    (htame : ∀ y ∈ K, ∀ v : TangentSpace I ((extChartAt I x₀).symm y), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ ω _ v (J z _ v))
    (hx : x ∈ (extChartAt I x₀).source) (hxK : extChartAt I x₀ x ∈ K) (v : TangentSpace I x)
    (hv : v ≠ 0) : 0 < SmoothBundleForm.eval₂ ω x v (J z x v) := by
  have h := htame _ hxK
  rw [(extChartAt I x₀).left_inv hx] at h
  exact h v hv

variable [FiniteDimensional ℝ E]

/-- **The Floer energy bounds the derivative in a chart.** Let `D ⊆ ℝ × ℝ` and `K ⊆ E` be compact,
with `K` in the target of the extended chart `ψ = extChartAt I x₀`. Suppose that the chart
structure `T J(z, ψ⁻¹ y) S` and the chart vector field `T X_{K_s}(z, ψ⁻¹ y)` are continuous on
`D × K`, and that `J(z, ψ⁻¹ y)` is tamed by `ω` for `(z, y) ∈ D × K`. There are constants
`A, B ≥ 0` such that every solution `u` of the Floer equation at `z ∈ D` with `ψ (u z) ∈ K`
satisfies `‖∂ₛ(ψ ∘ u)(z)‖² ≤ A ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t}) + B`. -/
theorem exists_forall_norm_fderiv_extChartAt_comp_stdComplexLineReal_sq_le (ω : SmoothTwoForm I M)
    (x₀ : M) {D : Set (ℝ × ℝ)} {K : Set E} (hD : IsCompact D) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hJ : ContinuousOn (fun q : (ℝ × ℝ) × E ↦
      (mvfderiv I (extChartAt I x₀) ((extChartAt I x₀).symm q.2) ∘L
        (J q.1 ((extChartAt I x₀).symm q.2)).toLinearMap.toContinuousLinearMap ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) q.2 : E →L[ℝ] E)) (D ×ˢ K))
    (hX : ContinuousOn (fun q : (ℝ × ℝ) × E ↦
      mvfderiv I (extChartAt I x₀) ((extChartAt I x₀).symm q.2)
        (ω.hamiltonianVectorField (Ks q.1) ((extChartAt I x₀).symm q.2))) (D ×ˢ K))
    (htame : ∀ z ∈ D, ∀ y ∈ K, ∀ v : TangentSpace I ((extChartAt I x₀).symm y), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ ω _ v (J z _ v)) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, z ∈ D →
      u z ∈ (extChartAt I x₀).source → extChartAt I x₀ (u z) ∈ K →
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap →
      ‖fderiv ℝ (extChartAt I x₀ ∘ u) z stdComplexLineReal‖ ^ 2 ≤
        A * ω.floerEnergyDensity Ks Kt u z + B := by
  set ψ := extChartAt I x₀
  set Jc : (ℝ × ℝ) × E → E →L[ℝ] E := fun q ↦
    (mvfderiv I ψ (ψ.symm q.2) ∘L (J q.1 (ψ.symm q.2)).toLinearMap.toContinuousLinearMap ∘L
      mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) q.2 : E →L[ℝ] E)
  -- The chart coefficients `ω.inChartAt x₀ y` of `ω`, read as bilinear forms `(ξ, η) ↦ ω_y(ξ, η)`.
  set L : (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.compL ℝ E (E [⋀^Fin 1]→L[ℝ] ℝ) (E →L[ℝ] ℝ)
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
          (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ)
        (n := 1)).toContinuousLinearMap with hL
  have hLapply (f : E [⋀^Fin 2]→L[ℝ] ℝ) (ξ η : E) : L f ξ η = f ![ξ, η] := by
    have hη : (fun _ : Fin 1 ↦ η) = ![η] := by
      ext i
      fin_cases i
      rfl
    simp [hL, hη]
  set b : (ℝ × ℝ) × E → E →L[ℝ] E →L[ℝ] ℝ := fun q ↦
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip (Jc q)).comp (L (RoughForm.inChartAt ω.1 x₀ q.2))
    with hb
  have hbapply (q : (ℝ × ℝ) × E) (ξ η : E) :
      b q ξ η = RoughForm.inChartAt ω.1 x₀ q.2 ![ξ, Jc q η] := by
    simp [hb, hLapply]
  -- At a point `x` of the chart, `b (z, ψ x)` evaluated on `T a` and `T c` is `ω_x(a, J c)`.
  have hbT (z : ℝ × ℝ) {x : M} (hx : x ∈ ψ.source) (a c : TangentSpace I x) :
      b (z, ψ x) (mvfderiv I ψ x a) (mvfderiv I ψ x c) =
        SmoothBundleForm.eval₂ ω x a (J z x c) := by
    have hST : mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) (ψ x) (mvfderiv I ψ x c) = c := by
      rw [mvfderiv_apply_eq_mfderiv_apply]
      exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) hx) c)
    -- The chart structure carries `T c` to `T (J c)`.
    have hJT : Jc (z, ψ x) (mvfderiv I ψ x c) = mvfderiv I ψ x (J z x c) := by
      have h1 : Jc (z, ψ x) (mvfderiv I ψ x c) = mvfderiv I ψ (ψ.symm (ψ x))
          (J z (ψ.symm (ψ x)) (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) (ψ x)
            (mvfderiv I ψ x c))) := rfl
      rw [h1, hST, ψ.left_inv hx]
    rw [hbapply, hJT, SmoothBundleForm.eval₂_apply, RoughForm.apply_eq_inChartAt_mvfderiv ω.1 hx]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hcont : ContinuousOn b (D ×ˢ K) :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
      (L.continuous.comp_continuousOn ((ω.isSmoothForm.continuousOn_inChartAt x₀).comp
        continuousOn_snd fun q hq ↦ hKt hq.2))
  -- A uniform taming constant in the chart, and a bound for the chart vector field.
  obtain ⟨c, hc, hbc⟩ := (hD.prod hK).exists_pos_forall_mul_norm_sq_le hcont fun q hq ξ hξ ↦ by
    obtain ⟨z, y⟩ := q
    obtain ⟨hz, hy⟩ := hq
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ ψ.source, ψ x = y :=
      ⟨ψ.symm y, ψ.map_target (hKt hy), ψ.right_inv (hKt hy)⟩
    have hTS : mvfderiv I ψ x (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) (ψ x) ξ) = ξ :=
      (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans
        congr($(mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I) hx) ξ)
    have hb := hbT z hx (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) (ψ x) ξ)
      (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) (ψ x) ξ)
    rw [hTS] at hb
    rw [hb]
    exact tames_of_mem_extChartAt_source (htame z hz) hx hy _ fun h0 ↦
      hξ (hTS.symm.trans ((congrArg (mvfderiv I ψ x) h0).trans (map_zero _)))
  obtain ⟨B₀, hB₀⟩ := (hD.prod hK).exists_bound_of_continuousOn hX
  refine ⟨2 / c, by positivity, 2 * B₀ ^ 2, by positivity, fun u z hz hsrc hK' hu h ↦ ?_⟩
  set a := ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal
  set T := mvfderiv I ψ (u z)
  have hXB : ‖T (ω.hamiltonianVectorField (Ks z) (u z))‖ ≤ B₀ := by
    have h' := hB₀ (z, ψ (u z)) ⟨hz, hK'⟩
    simp only at h'
    rwa [(extChartAt I x₀).left_inv hsrc] at h'
  -- The chart derivative is `T a` plus the chart vector field, and `c ‖T a‖²` is at most the
  -- energy density `ω(a, J a)`.
  have hd : fderiv ℝ (ψ ∘ u) z stdComplexLineReal =
      T a + T (ω.hamiltonianVectorField (Ks z) (u z)) := by
    have hch := (mvfderiv_eq_fderiv_apply (ψ ∘ u) z stdComplexLineReal).symm.trans
      (mvfderiv_comp_apply z (mdifferentiableAt_extChartAt
        (by simpa only [ψ, extChartAt_source] using hsrc)) hu stdComplexLineReal)
    rw [hch, ← map_add,
      show a = _ from perturbedMFDeriv_apply_stdComplexLineReal ω Ks Kt u z, sub_add_cancel]
  have hE : c * ‖T a‖ ^ 2 ≤ ω.floerEnergyDensity Ks Kt u z := by
    have hP := h.apply_stdComplexLineImag
    simp only [ContinuousLinearMap.coe_coe] at hP
    rw [floerEnergyDensity_def, hP, ← hbT z hsrc]
    exact hbc _ ⟨hz, hK'⟩ _
  rw [hd]
  calc ‖T a + T (ω.hamiltonianVectorField (Ks z) (u z))‖ ^ 2
      ≤ (‖T a‖ + B₀) ^ 2 := by
        gcongr
        exact (norm_add_le _ _).trans (by linarith)
    _ ≤ 2 * ‖T a‖ ^ 2 + 2 * B₀ ^ 2 := by nlinarith [sq_nonneg (‖T a‖ - B₀)]
    _ ≤ 2 / c * ω.floerEnergyDensity Ks Kt u z + 2 * B₀ ^ 2 := by
        have : 2 * ‖T a‖ ^ 2 ≤ 2 / c * ω.floerEnergyDensity Ks Kt u z := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc]
          linarith
        linarith

end Chart

section Compactness

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- **Floer solutions in a chart converge off finitely many bubbling points.** Let
`ψ = extChartAt I x₀` be the extended chart at `x₀`, let `D ⊆ ℝ × ℝ` and `K ⊆ E` be compact with
`K` in the chart target, and let `W ⊆ (ℝ × ℝ) × E` be an open set containing `D × K` on which the
chart structure `T J(z, ψ⁻¹ y) S` and the chart vector fields `T X_{K_s}(z, ψ⁻¹ y)` and
`T X_{K_t}(z, ψ⁻¹ y)` are `C²`. Suppose that `J(z, ψ⁻¹ y)` is tamed by `ω` for `(z, y) ∈ D × K`.
There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of the Floer
equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on an open set `Ω ⊆ D`, with values in the chart and
chart points in `K`, and with Floer energy `∫_Ω ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ e`. Then there
are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ e`, and a continuous `v : Ω \ Z → K`
such that along `φ` every disc about a point of `Z` eventually carries Floer energy at least `δ`,
the differentials of the chart readings `ψ ∘ u_{φ n}` are uniformly bounded on every compact subset
of `Ω \ Z`, `ψ ∘ u_{φ n} → v` locally uniformly on `Ω \ Z`, and `u_{φ n} → ψ⁻¹ ∘ v` pointwise on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_extChartAt_comp_subseq_off_finset
    (ω : SmoothTwoForm I M) (x₀ : M) {W : Set ((ℝ × ℝ) × E)} {D : Set (ℝ × ℝ)} {K : Set E}
    (hW : IsOpen W) (hD : IsCompact D) (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target)
    (hDKW : D ×ˢ K ⊆ W)
    (hJ : ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × E ↦
      (mvfderiv I (extChartAt I x₀) ((extChartAt I x₀).symm q.2) ∘L
        (J q.1 ((extChartAt I x₀).symm q.2)).toLinearMap.toContinuousLinearMap ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) q.2 : E →L[ℝ] E)) W)
    (hXs : ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × E ↦
      mvfderiv I (extChartAt I x₀) ((extChartAt I x₀).symm q.2)
        (ω.hamiltonianVectorField (Ks q.1) ((extChartAt I x₀).symm q.2))) W)
    (hXt : ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × E ↦
      mvfderiv I (extChartAt I x₀) ((extChartAt I x₀).symm q.2)
        (ω.hamiltonianVectorField (Kt q.1) ((extChartAt I x₀).symm q.2))) W)
    (htame : ∀ z ∈ D, ∀ y ∈ K, ∀ v : TangentSpace I ((extChartAt I x₀).symm y), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ ω _ v (J z _ v)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃e : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω ((extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' K)) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ e) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → E), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ e ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ B, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (extChartAt I x₀ ∘ u (φ n)) y‖ ≤ B) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ extChartAt I x₀ ∘ u (φ n)) v atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 ((extChartAt I x₀).symm (v y))) := by
  set ψ := extChartAt I x₀
  set Jc : (ℝ × ℝ) × E → E →L[ℝ] E := fun q ↦
    (mvfderiv I ψ (ψ.symm q.2) ∘L (J q.1 (ψ.symm q.2)).toLinearMap.toContinuousLinearMap ∘L
      mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) q.2 : E →L[ℝ] E)
  set Xs : (ℝ × ℝ) × E → E := fun q ↦
    mvfderiv I ψ (ψ.symm q.2) (ω.hamiltonianVectorField (Ks q.1) (ψ.symm q.2))
  set Xt : (ℝ × ℝ) × E → E := fun q ↦
    mvfderiv I ψ (ψ.symm q.2) (ω.hamiltonianVectorField (Kt q.1) (ψ.symm q.2))
  -- The Hamiltonian one-form read in the chart.
  set X : (ℝ × ℝ) × E → ℝ × ℝ →L[ℝ] E := fun q ↦
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Xs q) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Xt q) with hX_def
  have hX : ContDiffOn ℝ 2 X W :=
    (contDiffOn_const.smulRight hXs).add (contDiffOn_const.smulRight hXt)
  have hXapply (q : (ℝ × ℝ) × E) :
      X q stdComplexLineReal = Xs q ∧ X q stdComplexLineImag = Xt q := by
    simp [hX_def, stdComplexLineReal_eq, stdComplexLineImag_eq]
  -- The chart structure squares to `-1`, since `S` and `T` are inverse to each other.
  have hJsq : ∀ z ∈ D, ∀ y ∈ K, ∀ w, Jc (z, y) (Jc (z, y) w) = -w := by
    intro z _ y hy w
    have hST (a : TangentSpace I (ψ.symm y)) :
        mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) y (mvfderiv I ψ (ψ.symm y) a) = a := by
      rw [mvfderiv_apply_eq_mfderiv_apply]
      exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (hKt hy)) a)
    have hTS : mvfderiv I ψ (ψ.symm y) (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) y w) = w :=
      (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans
        congr($(mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (hKt hy)) w)
    have h1 : Jc (z, y) (Jc (z, y) w) = mvfderiv I ψ (ψ.symm y) (J z (ψ.symm y)
        (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) y (mvfderiv I ψ (ψ.symm y) (J z (ψ.symm y)
          (mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) y w))))) := rfl
    rw [h1, hST, AlmostComplexStructure.apply_apply, map_neg, hTS]
  obtain ⟨A, hA0, B, hB0, hpt⟩ :=
    ω.exists_forall_norm_fderiv_extChartAt_comp_stdComplexLineReal_sq_le x₀ hD hK hKt
      (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW) htame
  obtain ⟨δ, hδ, hconv⟩ :=
    Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm_sq_le hW hJ hX hD
      hK hDKW hJsq hA0 hB0
  refine ⟨δ, hδ, fun Ω u e hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  have hsrc (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : u k z ∈ ψ.source := (huK k hz).1
  have hmd (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z :=
    ((hu k).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hz)
  -- The chart readings are `C³` solutions of the coordinate equation with values in `K`.
  have hv (k : ℕ) : ContDiffOn ℝ 3 (ψ ∘ u k) Ω := by
    refine contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_extChartAt (n := 3)).comp (hu k)
      fun z hz ↦ ?_)
    simpa only [ψ, extChartAt_source, mem_preimage] using hsrc k hz
  have hcoord (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      fderiv ℝ (ψ ∘ u k) z stdComplexLineImag - X (z, (ψ ∘ u k) z) stdComplexLineImag =
        Jc (z, (ψ ∘ u k) z)
          (fderiv ℝ (ψ ∘ u k) z stdComplexLineReal - X (z, (ψ ∘ u k) z) stdComplexLineReal) := by
    have h := ω.fderiv_extChartAt_comp_stdComplexLineImag_sub x₀ (hmd k hz) (hsrc k hz)
      (hfl k z hz)
    have h1 : Jc (z, (ψ ∘ u k) z) = (mvfderiv I ψ (ψ.symm (ψ (u k z))) ∘L
        (J z (ψ.symm (ψ (u k z)))).toLinearMap.toContinuousLinearMap ∘L
        mfderivWithin 𝓘(ℝ, E) I ψ.symm (range I) (ψ (u k z)) : E →L[ℝ] E) := rfl
    rw [(hXapply _).1, (hXapply _).2, h1]
    simp only [Xs, Xt, Function.comp_apply]
    rw [ψ.left_inv (hsrc k hz)]
    exact h
  have hf0 (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) : 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z := by
    have hP := (hfl k z hz).apply_stdComplexLineImag
    simp only [ContinuousLinearMap.coe_coe] at hP
    rw [floerEnergyDensity_def, hP]
    rcases eq_or_ne (ω.perturbedMFDeriv Ks Kt (u k) z stdComplexLineReal) 0 with h0 | h0
    · have h00 : SmoothBundleForm.eval₂ ω (u k z) 0 0 = 0 := by
        rw [SmoothBundleForm.eval₂_apply]
        exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl
      simp only [h0, map_zero, h00, le_refl]
    · exact (tames_of_mem_extChartAt_source (htame z (hΩD hz)) (hsrc k hz) (huK k hz).2 _ h0).le
  obtain ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim⟩ :=
    hconv hΩ hΩD hv (fun k z hz ↦ hcoord k z hz) (fun k z hz ↦ (huK k hz).2) hf0
      (fun k z hz ↦ hpt (hΩD hz) (hsrc k hz) (huK k hz).2 (hmd k hz) (hfl k z hz)) hint hE
  refine ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim, fun y hy ↦ ?_⟩
  -- Pointwise, `u = ψ⁻¹ ∘ (ψ ∘ u)` on `Ω`, and `ψ⁻¹` is continuous on the chart target.
  have h := (continuousAt_extChartAt_symm'' (I := I) (hKt (hvK hy))).tendsto.comp
    (hlim.tendsto_at hy)
  refine h.congr fun n ↦ ?_
  exact ψ.left_inv (hsrc (φ n) hy.1)

end Compactness

end TauCeti.SmoothTwoForm
