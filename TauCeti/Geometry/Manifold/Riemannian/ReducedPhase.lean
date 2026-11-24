/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.LocalFlow
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Local reduced phase endpoints

In signed square-root time `s`, the reduced action has coordinate integrand
`(1 / 2) * G (s, y) v v + 2 * s ^ 2 * R (s, y)`. The phase field contains the scalar force and
both time and space derivatives of the metric. Its acceleration pairs with the metric to give
the Euler covector. Smooth invertible coefficients produce a jointly smooth local endpoint
family with initial position `y` and velocity `2Z`; relative ODE uniqueness also applies at a
closed initial endpoint.

`TauCeti.Manifold.exists_contMDiffOn_reducedEulerFamily` applies this construction
to the native chart metric and scalar curvature of `g (T - s ^ 2)`, and carries the position curve
back to the manifold. The metric coefficients and actual scalar curvature are assumed jointly
smooth on the stated open domain. The resulting manifold family has native velocity `2Z` at
zero and is jointly smooth throughout a common open product domain.

The coordinate regularity and flow theorems work on real normed spaces. Invertibility of the
metric as a map to the continuous dual supplies completeness for the ODE construction.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, equation 6.5 and Lemma 6.8.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The covector in the coordinate Euler equation for the square-root-time reduced action. -/
def reducedPhaseCovector (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E) (v : E) : E →L[ℝ] ℝ :=
  (2 * z.1 ^ 2) • (fderiv ℝ R z).comp (ContinuousLinearMap.inr ℝ ℝ E) -
    (fderiv ℝ G z (1, 0)) v - (fderiv ℝ G z (0, v)) v +
    (1 / 2 : ℝ) •
      (((ContinuousLinearMap.apply ℝ ℝ v).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)).comp
        ((fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ ℝ E)))

/-- Evaluation of the Euler covector on a spatial direction. -/
@[simp]
theorem reducedPhaseCovector_apply (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E) (v w : E) :
    reducedPhaseCovector G R z v w =
      2 * z.1 ^ 2 * fderiv ℝ R z (0, w) - fderiv ℝ G z (1, 0) v w -
        fderiv ℝ G z (0, v) v w + (1 / 2 : ℝ) * fderiv ℝ G z (0, w) v v :=
  (rfl)

/-- The position-velocity phase field, with the native inverse of the coordinate metric. -/
def reducedPhase (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (q : ℝ × (E × E)) : E × E :=
  (q.2.2, (G (q.1, q.2.1)).inverse
    (reducedPhaseCovector G R (q.1, q.2.1) q.2.2))

/-- The position component of the phase field is the current velocity. -/
@[simp]
theorem reducedPhase_fst (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (q : ℝ × (E × E)) :
    (reducedPhase G R q).1 = q.2.2 :=
  (rfl)

/-- The velocity component is the inverse metric applied to the Euler covector. -/
@[simp]
theorem reducedPhase_snd (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (q : ℝ × (E × E)) :
    (reducedPhase G R q).2 =
      (G (q.1, q.2.1)).inverse (reducedPhaseCovector G R (q.1, q.2.1) q.2.2) :=
  (rfl)

/-- Smoothness of the actual phase on an open coordinate domain. -/
theorem contDiffOn_reducedPhase (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (U : Set (ℝ × E)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hInv : ∀ z ∈ U, (G z).IsInvertible) :
    ContDiffOn ℝ ∞ (reducedPhase G R)
      {q : ℝ × (E × E) | (q.1, q.2.1) ∈ U} := by
  let W : Set (ℝ × (E × E)) := {q | (q.1, q.2.1) ∈ U}
  let P : ℝ × (E × E) → ℝ × E := fun q ↦ (q.1, q.2.1)
  let V : ℝ × (E × E) → E := fun q ↦ q.2.2
  -- Cache the canonical operator-space instances before the next derivative-space layer.
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (ℝ × E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (ℝ × E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hP : ContDiff ℝ ∞ P := contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hV : ContDiff ℝ ∞ V := contDiff_snd.comp contDiff_snd
  have hPU : MapsTo P W U := fun _ h ↦ by simpa only [W, P, mem_ofPred_eq] using h
  have hDG : ContDiffOn ℝ ∞ (fun q ↦ fderiv ℝ G (P q)) W :=
    (hG.fderiv_of_isOpen hU (by simp)).comp hP.contDiffOn hPU
  have hDR : ContDiffOn ℝ ∞ (fun q ↦ fderiv ℝ R (P q)) W :=
    (hR.fderiv_of_isOpen hU (by simp)).comp hP.contDiffOn hPU
  have hInv' : ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) U := by
    intro z hz
    have : CompleteSpace E :=
      ContinuousLinearMap.completeSpace_of_isInvertible (hInv z hz)
    exact (hInv z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hG z hz)
  have hRsp : ContDiffOn ℝ ∞
      (fun q ↦ (fderiv ℝ R (P q)).comp (ContinuousLinearMap.inr ℝ ℝ E)) W :=
    hDR.clm_comp contDiffOn_const
  have hTime : ContDiffOn ℝ ∞ (fun q ↦ (fderiv ℝ G (P q) (1, 0)) (V q)) W :=
    (hDG.clm_apply contDiffOn_const).clm_apply hV.contDiffOn
  have hSpace : ContDiffOn ℝ ∞
      (fun q ↦ (fderiv ℝ G (P q) (0, V q)) (V q)) W :=
    (hDG.clm_apply (contDiffOn_const.prodMk hV.contDiffOn)).clm_apply hV.contDiffOn
  have hQuad : ContDiffOn ℝ ∞
      (fun q ↦ ((ContinuousLinearMap.apply ℝ ℝ (V q)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (V q))).comp
        ((fderiv ℝ G (P q)).comp (ContinuousLinearMap.inr ℝ ℝ E))) W := by
    have hflip := (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff.comp_contDiffOn
      (hDG.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E)))
    have hquad := ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff.comp_contDiffOn
      (hflip.clm_apply hV.contDiffOn)).clm_apply hV.contDiffOn
    exact hquad.congr fun q _ ↦ by ext w; rfl
  have hC : ContDiffOn ℝ ∞ (fun q ↦ reducedPhaseCovector G R (P q) (V q)) W :=
    ((((contDiffOn_const.mul (contDiffOn_fst.pow 2)).smul hRsp).sub hTime).sub hSpace).add
      ((contDiffOn_const (c := (1 / 2 : ℝ))).smul hQuad)
  exact hV.contDiffOn.prodMk
    ((hInv'.comp hP.contDiffOn hPU).clm_apply hC)

/-- Pairing the phase acceleration with the metric recovers its defining Euler covector. -/
theorem reducedPhase_pairing (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E) (hinv : (G z).IsInvertible) (v w : E) :
    G z (reducedPhase G R (z.1, (z.2, v))).2 w =
      2 * z.1 ^ 2 * fderiv ℝ R z (0, w) - fderiv ℝ G z (1, 0) v w -
        fderiv ℝ G z (0, v) v w + (1 / 2 : ℝ) * fderiv ℝ G z (0, w) v v := by
  simp only [reducedPhase_snd, Prod.mk.eta,
    hinv.self_apply_inverse, reducedPhaseCovector_apply]

/-- The suspended reduced phase has a smooth local flow with its actual clock and domain. -/
private theorem exists_local_reducedPhase_clockFlow
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hInv : ∀ z ∈ U, (G z).IsInvertible)
    (z₀ : ℝ × (E × E)) (hz₀ : (z₀.1, z₀.2.1) ∈ U) :
    ∃ Φ : (ℝ × (E × E)) → ℝ → (ℝ × (E × E)),
      ∃ W ∈ nhds z₀, IsOpen W ∧ ∃ a b : ℝ, 0 ∈ Ioo a b ∧
        ContDiffOn ℝ ∞ (fun p : (ℝ × (E × E)) × ℝ ↦ Φ p.1 p.2) (W ×ˢ Ioo a b) ∧
        (∀ z, Φ z 0 = z) ∧
        ∀ z ∈ W, ∀ t ∈ Ioo a b,
          (Φ z t).1 = z.1 + t ∧ ((Φ z t).1, (Φ z t).2.1) ∈ U ∧
          HasDerivAt (Φ z) ((1, reducedPhase G R (Φ z t))) t := by
  have : CompleteSpace E :=
    ContinuousLinearMap.completeSpace_of_isInvertible (hInv (z₀.1, z₀.2.1) hz₀)
  let S : Set (ℝ × (E × E)) := {q | (q.1, q.2.1) ∈ U}
  let A : (ℝ × (E × E)) → (ℝ × (E × E)) :=
    fun q ↦ (1, reducedPhase G R q)
  have hA : ContDiffOn ℝ ∞ A S :=
    contDiffOn_const.prodMk (contDiffOn_reducedPhase G R U hU hG hR hInv)
  obtain ⟨Φ, V, hV, hbase, hflow, hΦ0, -, hderiv⟩ :=
    ODE.exists_contDiffOn_localFlow (n := (⊤ : ℕ∞)) (v := A) (a := z₀) hA (hU.preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)) |>.mem_nhds hz₀)
  have hΦ := hflow.contDiffAt (hV.mem_nhds hbase)
  have hstay : ∀ᶠ p in nhds (z₀, 0), Φ p.1 p.2 ∈ S := by
    apply hΦ.continuousAt.eventually_mem
    rw [hΦ0]
    exact (hU.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mem_nhds hz₀
  have hboth := (hderiv.and hstay).and (hV.mem_nhds hbase)
  rw [nhds_prod_eq, eventually_prod_iff] at hboth
  obtain ⟨w, hw, j, hj, hprop⟩ := hboth
  obtain ⟨a, b, h0, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 hj
  let W := interior {z | w z}
  have hW : W ∈ nhds z₀ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hw)
  have hΦW : ContDiffOn ℝ ∞ (fun p : (ℝ × (E × E)) × ℝ ↦ Φ p.1 p.2)
      (W ×ˢ Ioo a b) := by
    exact hflow.mono fun p hp ↦ (hprop (interior_subset hp.1) (hab hp.2)).2
  refine ⟨Φ, W, hW, isOpen_interior, a, b, h0, hΦW, hΦ0, ?_⟩
  intro z hz t ht
  have hclock (u : ℝ) (hu : u ∈ Ioo a b) :
      HasDerivAt (fun r ↦ (Φ z r).1 - r) 0 u := by
    have hfst : HasDerivAt (fun r ↦ (Φ z r).1) 1 u :=
      (ContinuousLinearMap.fst ℝ ℝ (E × E)).hasFDerivAt.comp_hasDerivAt
        u (hprop (interior_subset hz) (hab hu)).1.1
    simpa only [sub_self] using hfst.fun_sub (hasDerivAt_id' u)
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu ↦ (hclock u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hclock u hu).deriv) ht h0
  simp only [hΦ0, sub_zero] at hc
  exact ⟨by linarith, (hprop (interior_subset hz) (hab ht)).1.2,
    (hprop (interior_subset hz) (hab ht)).1.1⟩

/-- The reduced phase has a smooth local family with initial position `y` and velocity `2Z`.
The phase stays in the coordinate domain on a common interval. A competing solution with the
same initial state has the same germ, including relative germs at closed endpoints. -/
theorem exists_contDiffOn_localReducedPhase
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hInv : ∀ z ∈ U, (G z).IsInvertible) (y Z₀ : E) (hy : (0, y) ∈ U) :
    ∃ β : E → ℝ → E × E, ∃ W ∈ nhds Z₀, IsOpen W ∧ ∃ a b : ℝ, 0 ∈ Ioo a b ∧
      ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ β p.1 p.2) (W ×ˢ Ioo a b) ∧
      (∀ Z, β Z 0 = (y, (2 : ℝ) • Z)) ∧
      ∀ Z ∈ W,
        (∀ s ∈ Ioo a b, (s, (β Z s).1) ∈ U ∧
          HasDerivAt (β Z) (reducedPhase G R (s, β Z s)) s) ∧
        ∀ (J : Set ℝ), OrdConnected J → 0 ∈ J → ∀ η : ℝ → E × E,
          η 0 = (y, (2 : ℝ) • Z) →
          (∀ᶠ s in 𝓝[J] 0, HasDerivWithinAt η (reducedPhase G R (s, η s)) J s) →
          η =ᶠ[𝓝[J] 0] β Z := by
  let ι : E → ℝ × (E × E) := fun Z ↦ (0, (y, (2 : ℝ) • Z))
  obtain ⟨Φ, V, hV, hVo, a, b, hab, hΦ, hΦ0, hΦode⟩ :=
    exists_local_reducedPhase_clockFlow G R U hU hG hR hInv (ι Z₀) hy
  let β : E → ℝ → E × E := fun Z s ↦ (Φ (ι Z) s).2
  have hι : ContDiff ℝ ∞ ι :=
    contDiff_const.prodMk (contDiff_const.prodMk (contDiff_const.smul contDiff_id))
  have hβ : ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ β p.1 p.2)
      ((ι ⁻¹' V) ×ˢ Ioo a b) :=
    contDiff_snd.comp_contDiffOn
      (hΦ.comp ((hι.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun _ h ↦ ⟨h.1, h.2⟩))
  have hβ0 (Z : E) : β Z 0 = (y, (2 : ℝ) • Z) := by simp only [β, hΦ0, ι]
  refine ⟨β, ι ⁻¹' V, hι.continuous.continuousAt.preimage_mem_nhds hV,
    hVo.preimage hι.continuous, a, b, hab, hβ, hβ0, ?_⟩
  intro Z hZ
  have hode (s : ℝ) (hs : s ∈ Ioo a b) :
      (s, (β Z s).1) ∈ U ∧ HasDerivAt (β Z) (reducedPhase G R (s, β Z s)) s := by
    obtain ⟨hclock, hmem, hderiv⟩ := hΦode (ι Z) hZ s hs
    have hclock' : (Φ (ι Z) s).1 = s := by simpa only [ι, zero_add] using hclock
    refine ⟨by simpa only [hclock', β] using hmem, ?_⟩
    have hd := (ContinuousLinearMap.snd ℝ ℝ (E × E)).hasFDerivAt.comp_hasDerivAt s hderiv
    have hstate : Φ (ι Z) s = (s, β Z s) := Prod.ext hclock' rfl
    simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', hstate, Prod.snd] using hd
  refine ⟨hode, ?_⟩
  intro J hJ hJ0 η hη0 hη
  have hS : IsOpen {q : ℝ × (E × E) | (q.1, q.2.1) ∈ U} :=
    hU.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hfield : ContDiffAt ℝ 1 (reducedPhase G R) (0, β Z 0) :=
    ((contDiffOn_reducedPhase G R U hU hG hR hInv).contDiffAt
      (hS.mem_nhds (hode 0 hab).1)).of_le (by simp)
  have hβderiv : ∀ᶠ s in 𝓝[J] 0,
      HasDerivWithinAt (β Z) (reducedPhase G R (s, β Z s)) J s := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hab.1 hab.2)] with s hs
    exact (hode s hs).2.hasDerivWithinAt
  have hinit : η 0 = β Z 0 := hη0.trans (hβ0 Z).symm
  rw [← hinit] at hfield
  exact hfield.ode_eventuallyEq_nhdsWithin hJ hJ0 hinit hη hβderiv

end TauCeti.Manifold

namespace TauCeti.Manifold

open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The native moving metric read in a spatial chart at backward square time. -/
def squareTimeChartMetric
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (T : ℝ) (x : M) (z : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g (T - z.1 ^ 2)).toNondegenerateMetric.chartMetric x z.2

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Evaluation of the square-time metric coefficients in the chosen spatial chart. -/
theorem squareTimeChartMetric_apply
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (T : ℝ) (x : M) (z : ℝ × E) :
    squareTimeChartMetric g T x z =
      (g (T - z.1 ^ 2)).toNondegenerateMetric.chartMetric x z.2 :=
  (rfl)

/-- The scalar curvature of the native moving metric, in the same square-time chart. -/
def squareTimeChartScalar
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (T : ℝ) (x : M) (z : ℝ × E) : ℝ :=
  (g (T - z.1 ^ 2)).scalarCurvature ((extChartAt I x).symm z.2)

/-- Evaluation of the square-time scalar coefficient at the inverse chart point. -/
theorem squareTimeChartScalar_apply
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (T : ℝ) (x : M) (z : ℝ × E) :
    squareTimeChartScalar g T x z =
      (g (T - z.1 ^ 2)).scalarCurvature ((extChartAt I x).symm z.2) :=
  (rfl)

/-- A smooth family of native metric coefficients and its actual scalar curvature produces a
normalised local reduced Euler family. Its curves start at `x` with velocity `2Z`, solve the
coordinate phase equation on a common interval, and depend smoothly on `Z` and time throughout an
open product domain. The regularity hypotheses concern the actual metric and scalar curvature. -/
theorem exists_contMDiffOn_reducedEulerFamily
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (T : ℝ) (x : M) (Z₀ : E) (U : Set (ℝ × E)) (hU : IsOpen U)
    (hchart : ∀ z ∈ U, z.2 ∈ (extChartAt I x).target)
    (h0 : (0, extChartAt I x x) ∈ U)
    (hG : ContDiffOn ℝ ∞ (squareTimeChartMetric g T x) U)
    (hR : ContDiffOn ℝ ∞ (squareTimeChartScalar g T x) U) :
    ∃ (Γ : E → ℝ → M) (β : E → ℝ → E × E), ∃ W ∈ nhds Z₀,
      IsOpen W ∧ ∃ a b : ℝ, 0 ∈ Ioo a b ∧
        ContMDiffOn 𝓘(ℝ, E × ℝ) I ∞ (fun p : E × ℝ ↦ Γ p.1 p.2) (W ×ˢ Ioo a b) ∧
        (∀ Z, Γ Z 0 = x ∧ β Z 0 = (extChartAt I x x, (2 : ℝ) • Z)) ∧
        (∀ Z t, Γ Z t = (extChartAt I x).symm (β Z t).1) ∧
        ∀ Z ∈ W,
          curveVelocity I (Γ Z) 0 = (2 : ℝ) • Z ∧
          (∀ s ∈ Ioo a b, (s, (β Z s).1) ∈ U ∧
            HasDerivAt (β Z)
              (reducedPhase (squareTimeChartMetric g T x) (squareTimeChartScalar g T x)
                (s, β Z s)) s) ∧
          ∀ (J : Set ℝ), OrdConnected J → 0 ∈ J → ∀ η : ℝ → E × E,
            η 0 = (extChartAt I x x, (2 : ℝ) • Z) →
            (∀ᶠ s in 𝓝[J] 0, HasDerivWithinAt η
              (reducedPhase (squareTimeChartMetric g T x) (squareTimeChartScalar g T x)
                (s, η s)) J s) → η =ᶠ[𝓝[J] 0] β Z := by
  obtain ⟨β, W, hW, hWo, a, b, hab, hβ, hβ0, hβode⟩ :=
    exists_contDiffOn_localReducedPhase (squareTimeChartMetric g T x)
      (squareTimeChartScalar g T x) U hU hG hR
      (fun z hz ↦ by
        rw [squareTimeChartMetric_apply]
        exact ContinuousLinearMap.isInvertible_of_separatingLeft
          ((g (T - z.1 ^ 2)).toNondegenerateMetric.nondegenerate_chartMetric (hchart z hz)).1)
      (extChartAt I x x) Z₀ h0
  let Γ : E → ℝ → M := fun Z s ↦ (extChartAt I x).symm (β Z s).1
  have hΓ0 (Z : E) : Γ Z 0 = x := by simp [Γ, hβ0]
  have htarget : (extChartAt I x).target ∈ nhds (extChartAt I x x) := by
    have hpair : Continuous (fun y : E ↦ ((0 : ℝ), y)) :=
      continuous_const.prodMk continuous_id
    have hpre := hpair.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
    exact mem_of_superset hpre fun y hy ↦ hchart (0, y) hy
  have hΓ : ContMDiffOn 𝓘(ℝ, E × ℝ) I ∞ (fun p : E × ℝ ↦ Γ p.1 p.2)
      (W ×ˢ Ioo a b) :=
    (contMDiffOn_extChartAt_symm x).comp
      (contDiff_fst.comp_contDiffOn hβ).contMDiffOn
      (fun p hp ↦ hchart _ ((hβode p.1 hp.1).1 p.2 hp.2).1)
  refine ⟨Γ, β, W, hW, hWo, a, b, hab, hΓ, fun Z ↦ ⟨hΓ0 Z, hβ0 Z⟩,
    fun _ _ ↦ rfl, ?_⟩
  intro Z hZ
  obtain ⟨hode, huniq⟩ := hβode Z hZ
  have hcoord : HasDerivAt (fun s ↦ (β Z s).1) ((2 : ℝ) • Z) 0 := by
    have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0 (hode 0 hab).2
    simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', reducedPhase_fst, hβ0] using hd
  exact ⟨TauCeti.Manifold.curveVelocity_chartInverse_eq x htarget
    (congrArg Prod.fst (hβ0 Z)) hcoord, hode, huniq⟩

end TauCeti.Manifold
