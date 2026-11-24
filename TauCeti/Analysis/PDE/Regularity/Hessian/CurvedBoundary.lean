/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.ChangeOfVariables
public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.ContinuousCoefficient
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Flattening
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.InnerProductSpace.Coercive
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The Calderón–Zygmund estimate up to a `C²` boundary for continuous coefficients

Let `E` be a finite-dimensional real inner product space, `1 < p < ∞`, and let `Ω ⊆ ℝ × E` be open.
This file proves the `W^{2,p}` estimate up to the boundary for strong solutions of the
non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` in `Ω`, `u = 0` on `∂Ω`,

whose principal coefficients are continuous up to the boundary and elliptic there, and whose
lower-order coefficients are bounded:

* `TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_isChangeOfVariables`: the
  estimate `‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ C (‖f‖ + ‖∇u‖ + ‖u‖)` for a compact `K` inside an open set `U`
  on which a change of variables of order two straightens `Ω` to a half-space, for solutions
  vanishing on `∂Ω ∩ U`; it is the curved counterpart of the estimate near a flat boundary portion
  (`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace`);
* near a boundary portion which, in rigid coordinates, is the graph of a `C²` function, the
  estimate `‖D²u‖_{Lᵖ(Ω ∩ V)} ≤ C (‖f‖ + ‖∇u‖ + ‖u‖)` holds on a neighbourhood `V` of each of its
  points (`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`);
* on a bounded open set with `C²` boundary, `‖D²u‖_{Lᵖ(Ω)} ≤ C (‖f‖ + ‖∇u‖ + ‖u‖)` for every
  `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solving the equation
  (`TauCeti.exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`).

Norms without a subscript are those of `Lᵖ(Ω)`. As in the flat case, the principal coefficients
`A` need only be measurable on `Ω`, continuous within `Ω` at the points where the estimate is taken
and elliptic there, and need not be symmetric. The constants depend on the domain, the
coefficients and `p`, not on `u` or `f`. The global estimate is Gilbarg–Trudinger's
Theorem 9.13 with the gradient term still on the right; an interpolation inequality for `‖∇u‖`
removes it, and it is the a priori estimate behind the solvability of the Dirichlet problem in
`W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` (Gilbarg–Trudinger, Theorem 9.15). The boundary of `Ω` is described
as in Evans, Appendix C.1, by a height function of class `C²`; the estimate itself only uses
that the flattening chart is a change of variables of order two.

## The argument

This is the proof of Gilbarg–Trudinger, Theorem 9.13, by flattening the boundary.

* **Flattening.** Let `Φ` map the part of `U'` in the half-space `H = {a < x.fst}` onto `Ω ∩ U`,
  with inverse `Ψ`. Then `v = u ∘ Φ` solves an equation of the same form on `H ∩ U'`
  (`TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq`), with principal part
  `DΨ ∘ A ∘ DΨ†` and a first-order coefficient involving `A` and `D²Ψ`. The principal part is again
  continuous and elliptic at the points of `Ψ(K)`. The new first-order coefficient is bounded once
  `A` is: since `A` is continuous within `Ω` at the points of `K`, it is bounded near `K`, and the
  chart is first restricted there. Zero boundary values are carried along by cutting off
  (`TauCeti.Wkp.IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_w1pCompL`).
* **The flat estimate.** The flat estimate on `H ∩ U'`, for the compact set `Ψ(K)`, bounds
  `‖D²v‖_{Lᵖ(H ∩ Ψ(K))}` by the `Lᵖ` norms of `f ∘ Φ`, `∇v` and `v`.
* **Back to `Ω`.** Since `u = v ∘ Ψ`, the chain rule bounds `‖D²u‖` by `‖D²v ∘ Ψ‖` and
  `‖∇v ∘ Ψ‖` (`TauCeti.Wkp.norm_iteratedGradient_compL_le_ae`), and precomposition with a change of
  variables is bounded on `Lᵖ` (`TauCeti.Wkp.IsChangeOfVariables.lpNorm_comp_le`), as are `∇v`
  and `v` by `∇u` and `u`.
* **Graphs.** In rigid coordinates `e` the map `Φ = e⁻¹ ∘ G⁻¹`, with `G` graph flattening by
  the height function, carries a neighbourhood of `0` in the half-space `{0 < x.fst}` onto `Ω`
  near the boundary point; `Φ` and its inverse `Ψ = G ∘ e` are changes of variables of order two
  (`TauCeti.exists_isChangeOfVariables_normalHalfSpace_of_contDiff`).
* **Covering.** Interior points are handled by the same flat estimate on a ball inside `Ω` and
  inside a half-space. Finitely many of the neighbourhoods cover the compact closure of `Ω`, and
  the `Lᵖ` norm on `Ω` is at most the sum of those on the pieces.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (straightening the boundary) and Theorem 9.13 with its proof.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1 (`C²` boundaries).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace Filter
open scoped ENNReal NNReal Gradient ContDiff Topology

namespace TauCeti

open Wkp

section Transport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {mu : Measure F} [mu.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Omega U U' Ω' : Opens F} {Φ Ψ : F → F} {L L' c c' : ℝ}

/-- **Zero boundary values along a straightening chart.** Let `Φ` be a change of variables of order
two from `Ω'` into `Ω ∩ U`, with continuous left inverse `Ψ` mapping `Ω ∩ U` into `Ω'`, and let
`Φ` be continuous on an open `U'` that it maps into `U`. If `χ u ∈ W₀^{1,p}(Ω)` for every smooth `χ`
compactly supported in `U`, then `ψ (u ∘ Φ) ∈ W₀^{1,p}(Ω')` for every smooth `ψ` compactly
supported in `U'`. -/
private theorem exists_w1p0_value_ae_eq_mul_value_compL
    (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ U) Φ L c) (hp : p ≠ ⊤) (hΦc : ContinuousOn Φ U')
    (hΦU' : MapsTo Φ U' U) (hΨc : ContinuousOn Ψ (Omega ⊓ U : Opens F))
    (hΨmaps : MapsTo Ψ (Omega ⊓ U : Opens F) Ω') (hΨΦ : LeftInvOn Ψ Φ Ω') {u : Wkp mu Omega p 2}
    (hu0 : ∀ χ : F → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∃ w : W1p0 mu Omega p,
        W1p.value (w : W1p mu Omega p) =ᵐ[mu.restrict Omega] fun x => χ x * value 2 u x)
    (ψ : F → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U') :
    ∃ w : W1p0 mu Ω' p, W1p.value (w : W1p mu Ω' p) =ᵐ[mu.restrict Ω']
      fun x => ψ x * value 2 (compL hΦ (restrictL inf_le_left 2 u)) x := by
  have hΦ1 : IsChangeOfVariables 1 Ω' (Omega ⊓ U) Φ L c := hΦ.mono one_le_two
  obtain ⟨w, hw⟩ := hΦ1.exists_w1p0_value_ae_eq_mul_value_w1pCompL hp hΦc hΨc hΨmaps hΨΦ hΦU'
    (u := lowerOrder 1 u) (fun χ hχ hχc hχs => by
      simpa only [value_lowerOrder_one] using hu0 χ hχ hχc hχs) ψ hψ hψc hψs
  refine ⟨w, hw.trans ?_⟩
  filter_upwards [hΦ1.value_w1pCompL_ae hp (W1p.restrictL inf_le_left (lowerOrder 1 u)),
    hΦ.ae_comp (W1p.value_restrictL_ae inf_le_left (lowerOrder 1 u)),
    value_compL_ae hΦ (restrictL inf_le_left 2 u),
    hΦ.ae_comp (value_restrictL_ae inf_le_left 2 u)] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, value_lowerOrder_one]

/-- **The equation along a straightening chart.** If `u` solves
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c₀ u = f` on `Ω`, then `u ∘ Φ` solves the transformed equation of
`TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq` on `Ω'`, for mutually
inverse changes of variables `Φ` and `Ψ` of order two between `Ω'` and `Ω ∩ U`. -/
private theorem ae_traceCLM_comp_iteratedGradient_compL_restrictL_eq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ F) (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ U) Φ L c)
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ U) Ω' Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ (Omega ⊓ U : Opens F)) (hp : p ≠ ⊤) {u : Wkp mu Omega p 2}
    {A : F → F →L[ℝ] F} {b : F → F} {c₀ f : F → ℝ}
    (hu : ∀ᵐ y ∂mu.restrict Omega, traceCLM ℝ F (A y ∘L iteratedGradient 1 u y) +
      ⟪b y, iteratedGradient 0 (lowerOrder 1 u) y⟫_ℝ + c₀ y * value 2 u y = f y) :
    ∀ᵐ x ∂mu.restrict Ω',
      traceCLM ℝ F ((fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint) ∘L
          iteratedGradient 1 (compL hΦ (restrictL inf_le_left 2 u)) x) +
        ⟪fderiv ℝ Ψ (Φ x) (b (Φ x)) +
            ∑ i, fderiv ℝ (fderiv ℝ Ψ) (Φ x) (e i) ((A (Φ x)).adjoint (e i)),
          iteratedGradient 0 (lowerOrder 1 (compL hΦ (restrictL inf_le_left 2 u))) x⟫_ℝ +
        c₀ (Φ x) * value 2 (compL hΦ (restrictL inf_le_left 2 u)) x = f (Φ x) := by
  refine PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq e hΦ hΨ hΦΨ hp _ ?_
  have hD : ((Omega ⊓ U : Opens F) : Set F) ⊆ Omega := fun x hx => hx.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hD hu,
    iteratedGradient_restrictL_ae inf_le_left 1 u,
    iteratedGradient_restrictL_ae inf_le_left 0 (lowerOrder 1 u),
    value_restrictL_ae inf_le_left 2 u] with y h1 h2 h3 h4
  rw [lowerOrder_restrictL, h2, h3, h4]
  exact h1

/-- **The Hessian back along a straightening chart.** Let `Ψ` be a change of variables of order two
from `Ω ∩ U` into `Ω'` with constants `L' ≥ 0` and `c'`, and let `u` restrict on `Ω ∩ U` to
`v ∘ Ψ`. Then for every compact `K ⊆ U`,
`‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ L'² c'^(-1/p) ‖D²v‖_{Lᵖ(Ω' ∩ Ψ(K))} + L' c'^(-1/p) ‖∇v‖_{Lᵖ(Ω')}`. -/
private theorem lpNorm_iteratedGradient_inter_le (hL' : 0 ≤ L')
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ U) Ω' Ψ L' c') (hp : p ≠ ⊤) {K : Set F}
    (hK : IsCompact K) (hKU : K ⊆ U) (u : Wkp mu Omega p 2) (v : Wkp mu Ω' p 2)
    (hv : compL hΨ v = restrictL inf_le_left 2 u) :
    lpNorm (iteratedGradient 1 u) p (mu.restrict ((Omega : Set F) ∩ K)) ≤
      L' ^ 2 * (c'⁻¹ ^ (1 / p).toReal *
          lpNorm (iteratedGradient 1 v) p (mu.restrict ((Ω' : Set F) ∩ Ψ '' K))) +
        L' * (c'⁻¹ ^ (1 / p).toReal * ‖iteratedGradient 0 (lowerOrder 1 v)‖) := by
  have hsub : (Omega : Set F) ∩ K ⊆ (Omega ⊓ U : Opens F) := fun y hy => ⟨hy.1, hKU hy.2⟩
  have hS : MeasurableSet ((Omega : Set F) ∩ K) :=
    Omega.isOpen.measurableSet.inter hK.isClosed.measurableSet
  -- Pointwise, by the chain rule for `u = v ∘ Ψ`.
  have hpt : ∀ᵐ y ∂mu.restrict ((Omega : Set F) ∩ K), ‖iteratedGradient 1 u y‖ ≤
      ‖L' ^ 2 * ‖iteratedGradient 1 v (Ψ y)‖ +
        L' * ‖iteratedGradient 0 (lowerOrder 1 v) (Ψ y)‖‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
        (norm_iteratedGradient_compL_le_ae hΨ hp v),
      ae_restrict_of_ae_restrict_of_subset hsub
        (iteratedGradient_restrictL_ae inf_le_left 1 u)] with y h1 h2
    rw [hv, h2] at h1
    rwa [Real.norm_of_nonneg (by positivity)]
  -- Both terms on the right are compositions with `Ψ`, bounded on `Lᵖ`.
  have hmaps1 : MapsTo Ψ ((Omega : Set F) ∩ K) ((Ω' : Set F) ∩ Ψ '' K) := fun y hy =>
    ⟨hΨ.mapsTo (hsub hy), mem_image_of_mem Ψ hy.2⟩
  have hmaps2 : MapsTo Ψ ((Omega : Set F) ∩ K) Ω' := fun y hy => hΨ.mapsTo (hsub hy)
  have hv1 : MemLp (iteratedGradient 1 v) p (mu.restrict ((Ω' : Set F) ∩ Ψ '' K)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hm1 := (hΨ.memLp_comp hS hsub hmaps1 hv1).norm.const_mul (L' ^ 2)
  have hm2 := (hΨ.memLp_comp hS hsub hmaps2
    (Lp.memLp (iteratedGradient 0 (lowerOrder 1 v)))).norm.const_mul L'
  rw [Lp.norm_def, toReal_eLpNorm]
  calc lpNorm (iteratedGradient 1 u) p (mu.restrict ((Omega : Set F) ∩ K))
      ≤ 1 * lpNorm (fun y => L' ^ 2 * ‖iteratedGradient 1 v (Ψ y)‖ +
          L' * ‖iteratedGradient 0 (lowerOrder 1 v) (Ψ y)‖) p
          (mu.restrict ((Omega : Set F) ∩ K)) :=
        lpNorm_le_mul_lpNorm_of_ae_le_mul ((Lp.aestronglyMeasurable _).mono_measure
          (Measure.restrict_mono inter_subset_left le_rfl))
          (hm1.add hm2) (by simpa only [one_mul] using hpt)
    _ ≤ lpNorm (fun y => L' ^ 2 * ‖iteratedGradient 1 v (Ψ y)‖) p
          (mu.restrict ((Omega : Set F) ∩ K)) +
        lpNorm (fun y => L' * ‖iteratedGradient 0 (lowerOrder 1 v) (Ψ y)‖) p
          (mu.restrict ((Omega : Set F) ∩ K)) := by
      rw [one_mul]
      exact lpNorm_add_le hm1 Fact.out
    _ ≤ _ := by
      gcongr
      · exact hΨ.lpNorm_le_of_ae_le_mul_comp hS hsub hmaps1 (sq_nonneg L')
          hm1.aestronglyMeasurable hv1
          (ae_of_all _ fun y => by rw [norm_mul, norm_norm, Real.norm_of_nonneg (sq_nonneg L')])
      · exact hΨ.lpNorm_le_of_ae_le_mul_comp hS hsub hmaps2 hL' hm2.aestronglyMeasurable
          (Lp.memLp _) (ae_of_all _ fun y => by rw [norm_mul, norm_norm, Real.norm_of_nonneg hL'])

end Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The flat estimate for the pulled-back equation.** In the setting of
`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_isChangeOfVariables`, with
`A` bounded by `Λ` on `Ω ∩ U`, the coefficients of the equation for `u ∘ Φ` on `H ∩ U'` satisfy
the hypotheses of the flat estimate on the compact set `Ψ(K)`. -/
private theorem exists_lpNorm_iteratedGradient_le_of_pullback (hp : 1 < p) (hp_top : p ≠ ⊤)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (WithLp 2 (ℝ × E))) (a : ℝ)
    {Omega U U' : Opens (WithLp 2 (ℝ × E))} {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {L L' c c' : ℝ} (hΦ : IsChangeOfVariables 2 U' U Φ L c)
    (hΨ : IsChangeOfVariables 2 U U' Ψ L' c') (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (himage : Φ '' ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U') =
      (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKU : K ⊆ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))) {Λ : ℝ}
    (hAΛ : ∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ U, ‖A y‖ ≤ Λ)
    (hcont : ∀ x ∈ K, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ K, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c₀ : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c₀ (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c₀ x| ≤ γ) :
    ∃ C : ℝ, ∀ (v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a ⊓ U') p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict
        (normalHalfSpace (E := E) a ⊓ U' : Opens (WithLp 2 (ℝ × E))))),
      (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U' →
        ∃ w : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a ⊓ U') p,
          W1p.value (w : W1p volume (normalHalfSpace a ⊓ U') p) =ᵐ[volume.restrict
            (normalHalfSpace (E := E) a ⊓ U' : Opens (WithLp 2 (ℝ × E)))]
            fun x => ψ x * Wkp.value 2 v x) →
      (∀ᵐ x ∂volume.restrict (normalHalfSpace (E := E) a ⊓ U' : Opens (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E))
            ((fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint) ∘L
              iteratedGradient 1 v x) +
          ⟪fderiv ℝ Ψ (Φ x) (b (Φ x)) +
              ∑ i, fderiv ℝ (fderiv ℝ Ψ) (Φ x) (e i) ((A (Φ x)).adjoint (e i)),
            iteratedGradient 0 (lowerOrder 1 v) x⟫_ℝ + c₀ (Φ x) * value 2 v x = f x) →
      lpNorm (iteratedGradient 1 v) p (volume.restrict
          ((normalHalfSpace (E := E) a ⊓ U' : Opens (WithLp 2 (ℝ × E))) ∩ Ψ '' K)) ≤
        C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 v)‖ + ‖value 2 v‖) := by
  set Ω' : Opens (WithLp 2 (ℝ × E)) := normalHalfSpace (E := E) a ⊓ U'
  have hΩ'm : MeasurableSet (Ω' : Set (WithLp 2 (ℝ × E))) := Ω'.isOpen.measurableSet
  have hΦ' := (hΦ.inf_of_image_eq hΨ hΨΦ himage).1
  have hΦmaps := hΦ'.mapsTo
  have hΦc : ContinuousOn Φ U' := hΦ.differentiableOn.continuousOn
  have hD : ((Omega ⊓ U : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) ⊆ Omega :=
    fun y hy => hy.1
  -- Composition with `Φ` preserves almost-everywhere properties and measurability.
  have hac : (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))).map Φ ≪
      volume.restrict (Omega : Set (WithLp 2 (ℝ × E))) :=
    (Measure.absolutelyContinuous_of_le_smul (hΦ'.map_restrict_le volume)).trans
      (Measure.restrict_mono hD le_rfl).absolutelyContinuous
  have hAΦ := (hA.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable
  have hA' := PDE.aestronglyMeasurable_comp_comp_adjoint hΨ hΩ'm (hΦc.mono fun x hx => hx.2)
    (fun x hx => (hΦmaps hx).2) hAΦ
  have hb' := PDE.aestronglyMeasurable_fderiv_apply_add_sum e hΨ hΩ'm (hΦc.mono fun x hx => hx.2)
    (fun x hx => (hΦmaps hx).2) hAΦ ((hb.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable)
  refine exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace hp hp_top a
    (Omega := Ω') (U := U') (β := L' * β + Fintype.card ι * (L' * Λ))
    (by simp [Ω'])
    (hK.image_of_continuousOn (hΨ.differentiableOn.continuousOn.mono hKU))
    ((hΨ.mapsTo.mono_left hKU).image_subset)
    hA' ?_ ?_ hb' ?_ ((hc.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable)
    (hΦ'.ae_comp (ae_restrict_of_ae_restrict_of_subset hD hcγ))
  · rintro _ ⟨y, hy, rfl⟩
    have hyx : Φ (Ψ y) = y := hΦΨ (hKU hy)
    exact PDE.continuousWithinAt_comp_comp_adjoint hΨ
      (hΦc.continuousAt (U'.isOpen.mem_nhds (hΨ.mapsTo (hKU hy)))).continuousWithinAt
      (by rw [hyx]; exact hKU hy) (fun x hx => (hΦmaps hx).1) (by rw [hyx]; exact hcont y hy)
  · rintro _ ⟨y, hy, rfl⟩ hcl
    have hyx : Φ (Ψ y) = y := hΦΨ (hKU hy)
    have hyΩ : y ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) := by
      have h := ((hΦc.continuousAt (U'.isOpen.mem_nhds (hΨ.mapsTo (hKU hy)))).continuousWithinAt
        (s := Ω')).mem_closure_image hcl
      rw [hyx] at h
      exact closure_mono (hΦmaps.image_subset.trans hD) h
    obtain ⟨lam, hlam, hA₀⟩ := hell y hy hyΩ
    refine ⟨lam / (‖fderiv ℝ Φ (Ψ y)‖ + 1) ^ 2, by positivity, fun ξ => ?_⟩
    have h := ContinuousLinearMap.mul_norm_sq_le_inner_comp_comp_adjoint
      (IsChangeOfVariables.fderiv_comp_fderiv_eq_id hΦ hΨ hΨΦ hΦΨ (hΨ.mapsTo (hKU hy))) hlam.le
      (A₀ := A y) hA₀ ξ
    rw [hyx] at h ⊢
    exact h
  · filter_upwards [hΦ'.ae_comp (ae_restrict_of_ae_restrict_of_subset hD hbβ),
      ae_restrict_mem hΩ'm] with x hx hxΩ'
    exact PDE.norm_fderiv_apply_add_sum_le e hΨ (hΦmaps hxΩ').2 (hAΛ _ (hΦmaps hxΩ')) hx

/-- The arithmetic combining the estimates in
`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_isChangeOfVariables`. -/
private theorem le_mul_add_add_of_le_add {Y X F G V f g w κ κ' L L' C₀ : ℝ} (hκ : 0 ≤ κ)
    (hκ' : 0 ≤ κ') (hL : 0 ≤ L) (hL' : 0 ≤ L') (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) (hV0 : 0 ≤ V)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hw : 0 ≤ w) (hX : X ≤ C₀ * (F + G + V)) (hF : F ≤ κ * f)
    (hG : G ≤ L * (κ * g)) (hV : V ≤ κ * w) (hY : Y ≤ L' ^ 2 * (κ' * X) + L' * (κ' * G)) :
    Y ≤ (L' ^ 2 * κ' * max C₀ 0 + L' * κ') * (κ * (1 + L)) * (f + g + w) := by
  have hX' : X ≤ max C₀ 0 * (F + G + V) :=
    hX.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  have hsum : F + G + V ≤ κ * (1 + L) * (f + g + w) := by
    nlinarith [mul_nonneg (mul_nonneg hκ hL) hf, mul_nonneg (mul_nonneg hκ hL) hw,
      mul_nonneg hκ hg]
  have h1 : L' ^ 2 * (κ' * X) ≤ L' ^ 2 * κ' * max C₀ 0 * (F + G + V) := by
    have := mul_le_mul_of_nonneg_left hX' (by positivity : 0 ≤ L' ^ 2 * κ')
    linarith
  have h2 : L' * (κ' * G) ≤ L' * κ' * (F + G + V) := by
    have := mul_nonneg (mul_nonneg hL' hκ') (add_nonneg hF0 hV0)
    nlinarith
  calc Y ≤ (L' ^ 2 * κ' * max C₀ 0 + L' * κ') * (F + G + V) := by linarith
    _ ≤ _ := by
      rw [mul_assoc _ (κ * (1 + L))]
      exact mul_le_mul_of_nonneg_left hsum (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg L') hκ')
        (le_max_right C₀ 0)) (mul_nonneg hL' hκ'))

/-- **The estimate for bounded principal coefficients.** The statement of
`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_isChangeOfVariables`, under the
additional hypotheses that `A` is bounded on `Ω ∩ U` and that the constants `L` and `L'` are
nonnegative. -/
private theorem exists_lpNorm_iteratedGradient_le_of_norm_le (hp : 1 < p) (hp_top : p ≠ ⊤)
    (a : ℝ) {Omega U U' : Opens (WithLp 2 (ℝ × E))}
    {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {L L' c c' : ℝ} (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hΦ : IsChangeOfVariables 2 U' U Φ L c) (hΨ : IsChangeOfVariables 2 U U' Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (himage : Φ '' ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U') =
      (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKU : K ⊆ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))) {Λ : ℝ}
    (hAΛ : ∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ U, ‖A y‖ ≤ Λ)
    (hcont : ∀ x ∈ K, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ K, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c₀ : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c₀ (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c₀ x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => ψ x * Wkp.value 2 u x) →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c₀ x * Wkp.value 2 u x = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K)) ≤
        C * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, hC₀⟩ := exists_lpNorm_iteratedGradient_le_of_pullback hp hp_top
    (stdOrthonormalBasis ℝ (WithLp 2 (ℝ × E))) a hΦ hΨ hΨΦ hΦΨ himage hK hKU hA hAΛ hcont hell hb
    hbβ hc hcγ
  -- Restrict the chart to the flat side `Ω' = H ∩ U'` and the curved side `D = Ω ∩ U`.
  obtain ⟨hΦ', hΨ'⟩ := hΦ.inf_of_image_eq hΨ hΨΦ himage
  have hΦΩ : MapsTo Φ (normalHalfSpace (E := E) a ⊓ U' : Opens (WithLp 2 (ℝ × E))) Omega :=
    fun x hx => (hΦ'.mapsTo hx).1
  have hκ : 0 ≤ c⁻¹ ^ (1 / p).toReal := Real.rpow_nonneg (inv_nonneg.2 hΦ.pos.le) _
  have hκ' : 0 ≤ c'⁻¹ ^ (1 / p).toReal := Real.rpow_nonneg (inv_nonneg.2 hΨ.pos.le) _
  refine ⟨(L' ^ 2 * c'⁻¹ ^ (1 / p).toReal * max C₀ 0 + L' * c'⁻¹ ^ (1 / p).toReal) *
    (c⁻¹ ^ (1 / p).toReal * (1 + L)), fun u f hu0 heq => ?_⟩
  -- The right-hand side `f ∘ Φ` on the flat side, and the estimate there.
  have hfΦ : MemLp (fun x => f (Φ x)) p (volume.restrict
      ((normalHalfSpace (E := E) a ⊓ U' : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))) :=
    hΦ'.memLp_comp (normalHalfSpace (E := E) a ⊓ U').isOpen.measurableSet subset_rfl hΦΩ
      (Lp.memLp f)
  have hest := hC₀ _ (hfΦ.toLp _)
    (exists_w1p0_value_ae_eq_mul_value_compL hΦ' hp_top hΦ.differentiableOn.continuousOn
      hΦ.mapsTo (hΨ.differentiableOn.continuousOn.mono fun y hy => hy.2) hΨ'.mapsTo
      (hΨΦ.mono fun x hx => hx.2) hu0)
    (by
      filter_upwards [ae_traceCLM_comp_iteratedGradient_compL_restrictL_eq
        (stdOrthonormalBasis ℝ (WithLp 2 (ℝ × E))) hΦ' hΨ'
        (hΦΨ.mono fun y hy => hy.2) hp_top heq, hfΦ.coeFn_toLp] with x h1 h2
      rwa [h2])
  -- The three terms on the right of the flat estimate, in terms of `u` and `f`.
  have hF : ‖hfΦ.toLp _‖ ≤ c⁻¹ ^ (1 / p).toReal * ‖f‖ := by
    rw [Lp.norm_toLp, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
    exact hΦ'.lpNorm_comp_le (normalHalfSpace (E := E) a ⊓ U').isOpen.measurableSet subset_rfl
      hΦΩ (Lp.memLp f)
  -- The lower-order terms of `u ∘ Φ`, bounded on `Ω ∩ U` and then on `Ω`.
  have hD : volume.restrict ((Omega ⊓ U : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) ≤
      volume.restrict Omega := Measure.restrict_mono_set _ (SetLike.coe_subset_coe.2 inf_le_left)
  have hG : ‖iteratedGradient 0 (lowerOrder 1 (compL hΦ' (restrictL inf_le_left 2 u)))‖ ≤
      L * (c⁻¹ ^ (1 / p).toReal * ‖iteratedGradient 0 (lowerOrder 1 u)‖) := by
    have h := norm_gradient_firstOrder_compL_le hΦ' hL (restrictL inf_le_left 2 u)
    rw [gradient_firstOrder_one, gradient_firstOrder_one, lowerOrder_restrictL] at h
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hκ) hL)
    exact (Lp.norm_eq_lpNorm_of_ae_eq EventuallyEq.rfl).trans_le (lpNorm_le_norm_of_ae_eq_of_le hD
      (iteratedGradient_restrictL_ae inf_le_left 0 (lowerOrder 1 u)))
  have hV : ‖value 2 (compL hΦ' (restrictL inf_le_left 2 u))‖ ≤
      c⁻¹ ^ (1 / p).toReal * ‖value 2 u‖ := by
    refine (norm_value_compL_le hΦ' _).trans (mul_le_mul_of_nonneg_left ?_ hκ)
    exact (Lp.norm_eq_lpNorm_of_ae_eq EventuallyEq.rfl).trans_le (lpNorm_le_norm_of_ae_eq_of_le hD
      (value_restrictL_ae inf_le_left 2 u))
  -- Back to `Ω`, along `Ψ`.
  have hlhs := lpNorm_iteratedGradient_inter_le hL' hΨ' hp_top hK hKU u _
    (compL_compL_of_rightInvOn hΦ' hΨ' (hΦΨ.mono fun y hy => hy.2) _)
  exact le_mul_add_add_of_le_add hκ hκ' hL hL' (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hest hF hG hV hlhs

/-- **The Calderón–Zygmund estimate near a straightened boundary portion.** Let `1 < p < ∞`, let
`Ω, U, U' ⊆ ℝ × E` be open, and let `Φ` and `Ψ` be mutually inverse changes of variables of order
two between `U'` and `U` such that `Φ` maps the part of `U'` in the half-space `H = {a < x.fst}`
onto `Ω ∩ U`. Let `K ⊆ U` be compact, let `A` be a measurable field of endomorphisms of `ℝ × E`,
continuous within `Ω` at every point of `K` and elliptic at every point of `K` in the closure of
`Ω`, and let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on `Ω`. Then
there is a constant `C` such that every `u ∈ W^{2,p}(Ω)` with `ψ u ∈ W^{1,p}_0(Ω)` for every smooth
`ψ` compactly supported in `U` (zero boundary values on `∂Ω ∩ U`) and solving

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω`

satisfies `‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`. The set `K` may meet
`∂Ω`, and nothing is assumed about `∂Ω` outside `U`. -/
theorem exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_isChangeOfVariables
    (hp : 1 < p) (hp_top : p ≠ ⊤) (a : ℝ) {Omega U U' : Opens (WithLp 2 (ℝ × E))}
    {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {L L' c c' : ℝ}
    (hΦ : IsChangeOfVariables 2 U' U Φ L c) (hΨ : IsChangeOfVariables 2 U U' Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (himage : Φ '' ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U') =
      (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKU : K ⊆ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ K, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ K, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c₀ : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c₀ (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c₀ x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => ψ x * Wkp.value 2 u x) →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c₀ x * Wkp.value 2 u x = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K)) ≤
        C * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  -- `A` is bounded on `Ω ∩ W` for an open `W ⊇ K`: near each point of `K` by continuity within
  -- `Ω`, and then on a finite subcover.
  have hloc (x : WithLp 2 (ℝ × E)) (hx : x ∈ K) : ∃ t : Set (WithLp 2 (ℝ × E)), IsOpen t ∧
      x ∈ t ∧ ∀ y ∈ t, y ∈ (Omega : Set (WithLp 2 (ℝ × E))) → ‖A y‖ ≤ ‖A x‖ + 1 := by
    have h := ContinuousWithinAt.norm (f := A) (hcont x hx)
    obtain ⟨t, ht, htO, hxt⟩ := _root_.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
      (h.tendsto.eventually_lt_const (lt_add_one ‖A x‖)))
    exact ⟨t, htO, hxt, fun y hy hyΩ => (ht y hy hyΩ).le⟩
  choose! t ht hxt hAt using hloc
  obtain ⟨I, hIK, hKI⟩ := hK.elim_nhds_subcover t fun x hx => (ht x hx).mem_nhds (hxt x hx)
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨⋃ x ∈ I, t x, isOpen_biUnion fun x hx => ht x (hIK x hx)⟩
  have hAW : ∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ (U ⊓ W : Opens (WithLp 2 (ℝ × E))),
      ‖A y‖ ≤ ∑ x ∈ I, (‖A x‖ + 1) := fun y hy => by
    obtain ⟨x, hxI, hyx⟩ := mem_iUnion₂.1 hy.2.2
    exact (hAt x (hIK x hxI) y hyx hy.1).trans
      (Finset.single_le_sum (f := fun x => ‖A x‖ + 1) (fun x _ => by positivity) hxI)
  -- Restrict the chart to `U ∩ W`, with nonnegative constants.
  obtain ⟨U'₁, hΦ₁, hΨ₁, hΨΦ₁, hΦΨ₁, himage₁⟩ :=
    hΦ.exists_inf_of_image_eq hΨ hΨΦ hΦΨ himage W
  obtain ⟨C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_norm_le hp hp_top a (le_max_right L 0)
    (le_max_right L' 0) (hΦ₁.mono_const (le_max_left L 0) hΦ₁.pos le_rfl)
    (hΨ₁.mono_const (le_max_left L' 0) hΨ₁.pos le_rfl) hΨΦ₁ hΦΨ₁ himage₁ hK
    (fun x hx => ⟨hKU hx, hKI hx⟩) hA hAW hcont hell hb hbβ hc hcγ
  exact ⟨C, fun u f hu0 heq => hC u f (fun ψ hψ hψc hψs => hu0 ψ hψ hψc fun x hx => (hψs hx).1)
    heq⟩

/-- **The Calderón–Zygmund estimate near a `C²` boundary graph.** Let `1 < p < ∞` and let
`Ω ⊆ ℝ × E` be open. Suppose that inside the normal cylinder of half-height `h₀` and radius `r₀`,
in rigid coordinates `e` centred at `e⁻¹ 0`, `Ω` is the region `{φ(y) < t}` above the graph of a
`C²` function `φ : E → ℝ` with `φ 0 = 0`, so that `e⁻¹ 0` is a boundary point. Let `W` be an open
neighbourhood of `e⁻¹ 0`, let `A` be a measurable field of endomorphisms of `ℝ × E`, continuous
within `Ω` at every point of `W` and elliptic at every point of `W` in the closure of `Ω`, and let
`b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on `Ω`. Then there are an
open neighbourhood `V` of `e⁻¹ 0` and a constant `C` such that every `u ∈ W^{2,p}(Ω)` with
`ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` compactly supported in `W` (zero boundary values on
`∂Ω ∩ W`) and solving

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω`

satisfies `‖D²u‖_{Lᵖ(Ω ∩ V)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`. -/
theorem exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph
    (hp : 1 < p) (hp_top : p ≠ ⊤) {Omega W : Opens (WithLp 2 (ℝ × E))}
    {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ}
    {h₀ r₀ : ℝ} (hh₀ : 0 < h₀) (hr₀ : 0 < r₀) (hφ0 : φ 0 = 0) (hφ : ContDiff ℝ 2 φ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hW : e.symm 0 ∈ W)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ W, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ W, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c₀ : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c₀ (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c₀ x| ≤ γ) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), e.symm 0 ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
          ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict
              (Omega : Set (WithLp 2 (ℝ × E)))] fun x => ψ x * Wkp.value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
            ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c₀ x * Wkp.value 2 u x =
              f x) →
        lpNorm (Wkp.iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V)) ≤
          C * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  -- Flatten the boundary by `Φ = e⁻¹ ∘ G⁻¹`, `G` graph flattening by `φ`, with inverse `G ∘ e`.
  obtain ⟨U', U, L, h0, -, hΦ, hΨ, himage⟩ :=
    exists_isChangeOfVariables_normalHalfSpace_of_contDiff one_le_two hh₀ hr₀ hφ0 hφ hgraph
  set G := graphFlattening φ hφ.continuous
  have hΦ0 : (e.symm ∘ G.symm) 0 = e.symm 0 := by simp [G, hφ0]
  -- Restrict the chart to `U ∩ W` and take a closed ball about `e⁻¹ 0` inside it.
  obtain ⟨U'₂, hΦ₂, hΨ₂, hΨΦ₂, hΦΨ₂, himage₂⟩ :=
    hΦ.exists_inf_of_image_eq hΨ (fun x _ => by simp) (fun y _ => by simp) himage W
  obtain ⟨ρ, hρ, hρU⟩ := nhds_basis_closedBall.mem_iff.1
    ((U ⊓ W).isOpen.mem_nhds ⟨hΦ0 ▸ hΦ.mapsTo h0, hW⟩)
  obtain ⟨C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_isChangeOfVariables
    hp hp_top 0 hΦ₂ hΨ₂ hΨΦ₂ hΦΨ₂ himage₂ (isCompact_closedBall _ ρ) hρU hA
    (fun x hx => hcont x (hρU hx).2) (fun x hx => hell x (hρU hx).2) hb hbβ hc hcγ
  refine ⟨⟨ball (e.symm 0) ρ, isOpen_ball⟩, mem_ball_self hρ, C, fun u f hu0 heq => ?_⟩
  refine (lpNorm_mono_measure ((Lp.memLp _).mono_measure
    (Measure.restrict_mono inter_subset_left le_rfl))
    (Measure.restrict_mono (inter_subset_inter_right _ ball_subset_closedBall) le_rfl)).trans
    (hC u f (fun ψ hψ hψc hψs => hu0 ψ hψ hψc fun x hx => (hψs hx).2) heq)

/-- **The estimate near an interior point.** For `x ∈ Ω`, the `W^{2,p}` estimate holds on `Ω ∩ V`
for a ball `V` about `x`. This is the half-space estimate on a ball inside `Ω` and inside a
half-space, where no boundary condition is needed. -/
private theorem exists_lpNorm_iteratedGradient_le_of_mem (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))} {x : WithLp 2 (ℝ × E)}
    (hx : x ∈ (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ y, ContinuousWithinAt A Omega y)
    (hell : ∀ y ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A y ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), x ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
          ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
              fun x => ψ x * value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
            ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
        lpNorm (iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V)) ≤
          C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
  -- Inside `B(x, ρ) ⊆ Ω`, the domain agrees with the half-space `{x.fst - ρ < y.fst}`.
  let B : Opens (WithLp 2 (ℝ × E)) := ⟨ball x ρ, isOpen_ball⟩
  have hBH : (B : Set (WithLp 2 (ℝ × E))) ⊆ normalHalfSpace (E := E) (x.fst - ρ) := fun y hy => by
    have h := (WithLp.norm_fst_le _ (y - x)).trans_lt (mem_ball_iff_norm.1 hy)
    rw [Real.norm_eq_abs, WithLp.sub_fst] at h
    rw [SetLike.mem_coe, mem_normalHalfSpace]
    linarith [abs_lt.1 h]
  have hΩB : (Omega : Set (WithLp 2 (ℝ × E))) ∩ B =
      (normalHalfSpace (E := E) (x.fst - ρ) : Set (WithLp 2 (ℝ × E))) ∩ B := by
    have hBΩ : (B : Set (WithLp 2 (ℝ × E))) ⊆ Omega := hρΩ
    rw [inter_eq_right.2 hBΩ, inter_eq_right.2 hBH]
  obtain ⟨C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace hp
    hp_top (x.fst - ρ) hΩB (isCompact_closedBall x (ρ / 2))
    (closedBall_subset_ball (half_lt_self hρ)) hA (fun y _ => hcont y) (fun y _ hy => hell y hy)
    hb hbβ hc hcγ
  refine ⟨⟨ball x (ρ / 2), isOpen_ball⟩, mem_ball_self (half_pos hρ), C, fun u f hu0 heq => ?_⟩
  have hmem : MemLp (iteratedGradient 1 u) p
      (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ closedBall x (ρ / 2))) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  exact (lpNorm_mono_measure hmem
    (Measure.restrict_mono (inter_subset_inter_right _ ball_subset_closedBall) le_rfl)).trans
      (hC u f (fun ψ hψ hψc _ => hu0 ψ hψ hψc) heq)

/-- **The estimate near a point of the closure.** Under the hypotheses of
`TauCeti.exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`, with `A`
continuous within `Ω` everywhere, every point `x` of the closure of `Ω` has an open neighbourhood
`V` on whose part in `Ω` the `W^{2,p}` estimate holds for solutions in `W^{1,p}_0(Ω)`: by the
interior estimate at points of `Ω`, by flattening the boundary at points of `∂Ω`. -/
private theorem exists_lpNorm_iteratedGradient_le_of_mem_closure (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))}
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont' : ∀ x, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {x : WithLp 2 (ℝ × E)} (hx : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), x ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        firstOrder 1 u ∈ w1p0Submodule volume Omega p →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
            ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
        lpNorm (iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V)) ≤
          C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  -- Zero boundary values give `ψ u ∈ W^{1,p}_0(Ω)` for every smooth compactly supported `ψ`.
  have hu0 : ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p → ∀ ψ : WithLp 2 (ℝ × E) → ℝ,
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => ψ x * value 2 u x := fun u hu ψ hψ hψc => by
    simpa only [value_firstOrder] using
      W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hu
  by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
  · obtain ⟨V, hV, C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_mem hp hp_top hxΩ hA hcont'
      hell hb hbβ hc hcγ
    exact ⟨V, hV, C, fun u f hu heq => hC u f (hu0 u hu) heq⟩
  · obtain ⟨e, φ, h₀, r₀, hex, hh₀, hr₀, hφ0, hφ, hgraph⟩ :=
      hbdry x ⟨hx, by rwa [Omega.isOpen.interior_eq]⟩
    have hx₀ : e.symm 0 = x := by rw [← hex, e.symm_apply_apply]
    obtain ⟨V, hV, C, hC⟩ :=
      exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph hp hp_top
        (W := ⊤) hh₀ hr₀ hφ0 hφ hgraph trivial hA (fun y _ => hcont' y)
        (fun y _ hy => hell y hy) hb hbβ hc hcγ
    exact ⟨V, hx₀ ▸ hV, C, fun u f hu heq => hC u f (fun ψ hψ hψc _ => hu0 u hu ψ hψ hψc) heq⟩

/-- **The global Calderón–Zygmund estimate on a bounded `C²` domain for continuous coefficients.**
Let `1 < p < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary: at every boundary
point `x`, in rigid coordinates `e` with `e x = 0`, inside a normal cylinder, `Ω` is the region
above the graph of a `C²` function `φ` with `φ 0 = 0`. Let `A` be a field of endomorphisms of
`ℝ × E`, measurable on `Ω` and continuous within `Ω` at every point of the closure of `Ω`, with
`A x` elliptic at every such point: `λₓ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫` for some `λₓ > 0`. Let `b` and `c` be
measurable with `‖b x‖ ≤ β` and `|c x| ≤ γ` for almost every `x ∈ Ω`. Then there is a constant `C`,
independent of `u` and `f`, such that every `u ∈ W^{2,p}(Ω)` with `u ∈ W^{1,p}_0(Ω)` solving
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω` satisfies

`‖D²u‖_{Lᵖ(Ω)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`.

This is Gilbarg–Trudinger's Theorem 9.13 with the gradient term still on the right; an
interpolation inequality removes it. -/
theorem exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
      ‖iteratedGradient 1 u‖ ≤ C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  -- Continuity within `Ω` is automatic away from the closure of `Ω`.
  have hcont' : ∀ x, ContinuousWithinAt A Omega x := fun x => by
    by_cases hx : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))
    · exact hcont x hx
    · exact continuousWithinAt_of_notMem_closure hx
  -- Every point of the closure of `Ω` has a neighbourhood `V` on whose part in `Ω` the estimate
  -- holds.
  have hloc := fun x hx => exists_lpNorm_iteratedGradient_le_of_mem_closure hp hp_top hbdry hA
    hcont' hell hb hbβ hc hcγ (x := x) hx
  -- Finitely many such neighbourhoods cover the compact closure of `Ω`; sum the estimates.
  choose! V hxV C hC using hloc
  obtain ⟨t, htΩ, hcover⟩ := hΩ.isCompact_closure.elim_nhds_subcover (fun x => (V x : Set _))
    fun x hx => (V x).isOpen.mem_nhds (hxV x hx)
  refine ⟨∑ x ∈ t, C x, fun u f hu heq => ?_⟩
  have hcoverΩ : (Omega : Set (WithLp 2 (ℝ × E))) ⊆
      ⋃ x ∈ t, (Omega : Set (WithLp 2 (ℝ × E))) ∩ V x := fun y hy => by
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover (subset_closure hy))
    exact mem_iUnion₂.2 ⟨x, hxt, hy, hyx⟩
  calc ‖iteratedGradient 1 u‖
      = lpNorm (iteratedGradient 1 u) p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
        Lp.norm_eq_lpNorm_of_ae_eq (Filter.EventuallyEq.refl _ _)
    _ ≤ ∑ x ∈ t, lpNorm (iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V x)) :=
        lpNorm_restrict_le_sum_of_subset_biUnion hp.le hcoverΩ fun x _ =>
          (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    _ ≤ ∑ x ∈ t, C x * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) :=
        Finset.sum_le_sum fun x hxt => hC x (htΩ x hxt) u f hu heq
    _ = _ := (Finset.sum_mul _ _ _).symm

end TauCeti
