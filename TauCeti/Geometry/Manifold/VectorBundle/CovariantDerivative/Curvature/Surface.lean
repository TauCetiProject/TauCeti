/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Chart
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Mixed covariant derivatives on a parametrized surface

Let `f` be a parametrized surface in a manifold, a map of two real parameters `(q, r)`, and let
`W` be a vector field along it, so that `W q r` is a tangent vector at `f q r`. Covariant
differentiation along the two families of parameter curves gives two operators `D_q` and `D_r` on
such fields. They do not commute: their commutator is the curvature of the connection,

`D_q D_r W - D_r D_q W = R(∂_q f, ∂_r f) W`,

for any smooth connection on the tangent bundle, with no metric or torsion hypothesis. This is
the identity behind the second variation of energy and behind the fact that the variation field of
a family of geodesics is a Jacobi field.

The proof reads everything in the chart at the point `f u v`. With `w` and `φ` the chart readings
of the field and of the surface and `Γ` the Christoffel map of the chart, `D_q D_r W` reads as
`∂_q ∂_r w + ∂_q(Γ(w, ∂_r φ)) + Γ(∂_r w + Γ(w, ∂_r φ), ∂_q φ)`. Second partial derivatives
commute, and the terms which are not symmetric in the two parameters are exactly the chart formula
for the curvature tensor (`CovariantDerivative.curvatureTensor_symm_trivializationAt`).

## Main results

* `CovariantDerivative.alongCurve_alongCurve_sub_alongCurve_alongCurve`: the commutator of the two
  covariant derivatives along a `C²` field on a parametrized surface is the curvature tensor.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 7.5.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 4, Lemma 4.1.
-/

public section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  {f : ℝ → ℝ → M} {W : ∀ q r, TangentSpace I (f q r)} {u v : ℝ}

/-- **The mixed covariant derivative in the chart at the point.** For a `C²` vector field `W`
along a parametrized surface `f`, the covariant derivative along the first-parameter curve of the
covariant derivatives along the second-parameter curves, read in the chart at `f u v`. -/
private theorem alongCurve_alongCurve_eq_symmL
    (hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v))
    {φ w : ℝ × ℝ → E} (hφdef : φ = fun z ↦ extChartAt I (f u v) (f z.1 z.2))
    (hwdef : w = fun z ↦ (trivializationAt E (TangentSpace I) (f u v)).continuousLinearMapAt ℝ
      (f z.1 z.2) (W z.1 z.2)) :
    letI e := trivializationAt E (TangentSpace I) (f u v)
    letI Γ := christoffelMap (finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet))
    alongCurve cov (fun q ↦ f q v) (fun q ↦ alongCurve cov (f q) (W q) v) u =
      e.symmL ℝ (f u v) (deriv (fun q ↦ deriv (fun r ↦ w (q, r)) v) u +
        (mvfderiv I Γ (f u v) (curveVelocity I (fun q ↦ f q v) u) (w (u, v))
            (deriv (fun r ↦ φ (u, r)) v) +
          Γ (f u v) (deriv (fun q ↦ w (q, v)) u) (deriv (fun r ↦ φ (u, r)) v) +
          Γ (f u v) (w (u, v)) (deriv (fun q ↦ deriv (fun r ↦ φ (q, r)) v) u)) +
        Γ (f u v) (deriv (fun r ↦ w (u, r)) v + Γ (f u v) (w (u, v)) (deriv (fun r ↦ φ (u, r)) v))
          (deriv (fun q ↦ φ (q, v)) u)) := by
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  set Γ := christoffelMap (finBasis ℝ E) hcov
  have : ContMDiffCovariantDerivativeOn E ∞ cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov e.open_baseSet
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hΓ : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) Γ (f u v) :=
    ((contMDiffOn_christoffelMap (n := ∞) (finBasis ℝ E) hcov).contMDiffAt
      (e.open_baseSet.mem_nhds hbase)).mdifferentiableAt (by simp)
  have hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ f z.1 z.2) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp (u, v) hW
  -- The chart readings of the surface and of the field are `C²`.
  have hφ : ContDiffAt ℝ 2 φ (u, v) := hφdef ▸ contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (mem_chart_source H (f u v))).comp (u, v) hf)
  have hw : ContDiffAt ℝ 2 w (u, v) :=
    hwdef ▸ hW.contDiffAt_continuousLinearMapAt_trivializationAt
  -- Near `u`, the field is `C²` at the points `(q, v)`, which lie over the chart at `f u v`.
  have hslice : ∀ᶠ q in 𝓝 u, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (q, v) ∧ f q v ∈ e.baseSet :=
    ((continuous_id.prodMk continuous_const).tendsto u).eventually
      (((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hW).and
        (hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)))
  -- There the inner covariant derivatives read in the chart at `f u v` by the coordinate formula.
  have hinner : sectionCoord (F := E) (fun q ↦ f q v) (fun q ↦ alongCurve cov (f q) (W q) v)
      (f u v) =ᶠ[𝓝 u]
      fun q ↦ deriv (fun r ↦ w (q, r)) v + Γ (f q v) (w (q, v)) (deriv (fun r ↦ φ (q, r)) v) := by
    have hcoord (q : ℝ) : sectionCoord (F := E) (f q) (W q) (f u v) = fun r ↦ w (q, r) :=
      funext fun r ↦ by rw [sectionCoord_apply, hwdef]
    filter_upwards [hslice] with q ⟨hq, hqb⟩
    have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
        (fun r ↦ TotalSpace.mk' E (f q r) (W q r)) v :=
      hq.comp v (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) q)).contMDiffAt
    have hfq : MDifferentiableAt 𝓘(ℝ, ℝ) I (f q) v :=
      ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp v hcurve).mdifferentiableAt
        (by norm_num)
    have hV : DifferentiableAt ℝ (sectionCoord (F := E) (f q) (W q) (f q v)) v :=
      differentiableAt_sectionCoord (f q) (W q) (hcurve.mdifferentiableAt (by norm_num))
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _)
    rw [sectionCoord_apply, ← alongCurveWithin_univ,
      ← symmL_alongCurveInChartWithin cov (f q) (W q) hqb uniqueDiffWithinAt_univ
        hfq.mdifferentiableWithinAt hV.differentiableWithinAt,
      e.continuousLinearMapAt_symmL (R := ℝ) hqb, alongCurveInChartWithin_apply,
      derivWithin_univ, derivWithin_univ, Function.comp_def, hcoord q, hφdef]
  -- The derivative in `q` of the coordinate formula, by the product rule.
  have hfu : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ f q v) u :=
    (hf.comp u (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 2) v)).contMDiffAt)
      |>.mdifferentiableAt (by norm_num)
  have hΓq : HasDerivAt (fun q ↦ Γ (f q v))
      (mvfderiv I Γ (f u v) (curveVelocity I (fun q ↦ f q v) u)) u :=
    hasDerivAt_comp_curve hΓ (hasMFDerivAt_curveVelocity hfu)
  have hw₁ : HasDerivAt (fun q ↦ w (q, v)) (deriv (fun q ↦ w (q, v)) u) u :=
    (DifferentiableAt.comp (g := w) (f := fun q : ℝ ↦ (q, v)) u
      (hw.differentiableAt (by norm_num)) (differentiableAt_id.prodMk (differentiableAt_const v))
      ).hasDerivAt
  have hA : HasDerivAt
      (fun q ↦ deriv (fun r ↦ w (q, r)) v + Γ (f q v) (w (q, v)) (deriv (fun r ↦ φ (q, r)) v))
      _ u := hw.differentiableAt_deriv_snd.hasDerivAt.add
    ((hΓq.clm_apply hw₁).clm_apply hφ.differentiableAt_deriv_snd.hasDerivAt)
  rw [alongCurve_apply, alongCurveInChartWithin_apply, derivWithin_univ, derivWithin_univ,
    hinner.deriv_eq, hinner.eq_of_nhds, hA.deriv, Function.comp_def, add_apply, hφdef]

/-- **Mixed covariant derivatives commute up to curvature.** For a `C²` vector field `W` along a
parametrized surface `f`, the covariant derivative along the first-parameter curves of the
covariant derivatives along the second-parameter curves, minus the same derivatives taken in the
other order, is the curvature: `D_q D_r W - D_r D_q W = R(∂_q f, ∂_r f) W`. No metric or torsion
hypothesis on the connection is needed. -/
theorem alongCurve_alongCurve_sub_alongCurve_alongCurve
    (hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    alongCurve cov (fun q ↦ f q v) (fun q ↦ alongCurve cov (f q) (W q) v) u -
        alongCurve cov (f u) (fun r ↦ alongCurve cov (fun q ↦ f q r) (fun q ↦ W q r) u) v =
      cov.curvatureTensor (f u v) (curveVelocity I (fun q ↦ f q v) u) (curveVelocity I (f u) v)
        (W u v) := by
  have hW' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.2 z.1) (W z.2 z.1)) (v, u) :=
    hW.comp (v, u) (contMDiff_iff_contDiff.mpr
      (by fun_prop : ContDiff ℝ 2 fun z : ℝ × ℝ ↦ (z.2, z.1))).contMDiffAt
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  set Γ := christoffelMap (finBasis ℝ E) hcov
  set φ : ℝ × ℝ → E := fun z ↦ extChartAt I (f u v) (f z.1 z.2) with hφdef
  set w : ℝ × ℝ → E := fun z ↦ e.continuousLinearMapAt ℝ (f z.1 z.2) (W z.1 z.2) with hwdef
  rw [alongCurve_alongCurve_eq_symmL cov hW hφdef hwdef,
    alongCurve_alongCurve_eq_symmL cov (f := fun a b ↦ f b a) (W := fun a b ↦ W b a)
      (u := v) (v := u) hW' (φ := fun z ↦ φ (z.2, z.1)) (w := fun z ↦ w (z.2, z.1)) rfl rfl]
  dsimp only
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ f z.1 z.2) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp (u, v) hW
  -- Read the velocities and the field at `(u, v)` in the chart at `f u v`.
  have hvel {γ : ℝ → M} {t : ℝ} (hγt : γ t ∈ e.baseSet) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
      curveVelocity I γ t = e.symmL ℝ (γ t) (deriv (fun r ↦ extChartAt I (f u v) (γ r)) t) := by
    have h := derivWithin_extChartAt_comp (x := f u v) γ hγt uniqueDiffWithinAt_univ
      (hasMFDerivAt_curveVelocity hγ).hasMFDerivWithinAt
    rw [derivWithin_univ, Function.comp_def] at h
    rw [h, e.symmL_continuousLinearMapAt (R := ℝ) hγt]
  have hWuv : W u v = e.symmL ℝ (f u v) (w (u, v)) :=
    (e.symmL_continuousLinearMapAt (R := ℝ) hbase _).symm
  have hφ : ContDiffAt ℝ 2 φ (u, v) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (mem_chart_source H (f u v))).comp (u, v) hf)
  have hw : ContDiffAt ℝ 2 w (u, v) := hW.contDiffAt_continuousLinearMapAt_trivializationAt
  rw [hvel (γ := fun q ↦ f q v) hbase
      ((hf.comp u (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 2) v)).contMDiffAt)
        |>.mdifferentiableAt (by norm_num)),
    hvel (γ := f u) hbase
      ((hf.comp v (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) u)).contMDiffAt)
        |>.mdifferentiableAt (by norm_num)), hWuv]
  simp only [e.symmL_apply (R := ℝ) hbase]
  rw [curvatureTensor_symm_trivializationAt cov (finBasis ℝ E) (f u v) (mem_extChartAt_source _),
    ← map_sub, e.symmL_apply (R := ℝ) hbase,
    ← deriv_deriv_comm (by rwa [minSmoothness_of_isRCLikeNormedField] : ContDiffAt ℝ _ w _),
    ← deriv_deriv_comm (by rwa [minSmoothness_of_isRCLikeNormedField] : ContDiffAt ℝ _ φ _)]
  congr 1
  simp only [hφdef, map_add, add_apply]
  abel

end CovariantDerivative
