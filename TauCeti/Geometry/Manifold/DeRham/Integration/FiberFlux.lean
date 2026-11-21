/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.SliceMoment
public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Orientation
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The pairing of a closed current with a taming form over a σ-compact preconnected surface

Let `M` be a σ-compact preconnected oriented surface, for example an embedded pseudoholomorphic
curve `C`, and let `M × ℂ` be a tubular neighbourhood of it with trivial normal line, oriented as
the product of the orientation of `M` and the standard orientation of `ℂ`. A compactly supported
two-form `T` on `M × ℂ` has a **fibre flux** through each normal fibre `{x} × ℂ`,

`RoughForm.fiberFlux T x = ∫_ℂ T(x, w)((0, 1), (0, i)) dw`

(`TauCeti.RoughForm.fiberFlux`), the total mass of the normal slice `μ_x` of
`TauCeti.Analysis.Calculus.DifferentialForm.SliceMoment` at `x`. In Taubes's analysis of
Seiberg–Witten solutions concentrating along `C`, the role of `T` is played by the dilated cutoff
curvature current, whose mass is controlled by its pairing with a taming form `Ω = K π^*β + dη`,
where `β` is an area form on the curve and `π : M × ℂ → M` the projection. The results here apply
to that current once it is identified with a smooth compactly supported closed two-form with
constant fibre flux `m`; that identification is not done here. For such a `T` this file proves
that the pairing is topological:

`∫_{M × ℂ} T ∧ (K π^*β + dη) = K m ∫_M β`

(`TauCeti.integralTopForm_wedge_smul_mpullback_fst_add_mextDerivₗ`), which is
`T(Ω) = K m area(C)` when `∫_M β = area(C)`.

The proof replaces a partition of unity on the curve by de Rham theory on `M`.

* **One chart.** If `θ` is supported in a chart of `M`, then the inverse chart of `M` times the
  identity of `ℂ` is a chart of `M × ℂ` containing the support of `T ∧ π^*θ`. In it the coefficient
  of `T ∧ π^*θ` on the product frame `(b₀, 0), (b₁, 0), (0, 1), (0, i)` is the slice density of
  `T` times the coefficient of `θ` on `b`
  (`TauCeti.wedge_compContinuousLinearMap_fst_apply`), so Fubini's theorem gives
  `∫ T ∧ π^*θ = m ∫ θ` when the flux is `m` over the support of `θ`
  (`TauCeti.integralTopForm_wedge_mpullback_fst_of_tsupport_subset_chart`). No closedness is needed.
* **The whole base.** Fix such a `θ` with `∫_M θ = 1`. On a preconnected surface, for a compactly
  supported `β` the form `β - (∫_M β) θ` has integral zero, so it is exact
  (`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`), and so is its pullback.
  Since `T` is closed and compactly supported, its wedge with an exact form is a compactly
  supported exact form, which integrates to zero by Stokes' theorem
  (`TauCeti.integralTopForm_wedge_eq_zero_of_mem_exactForms`). Hence
  `∫ T ∧ π^*β = (∫_M β) ∫ T ∧ π^*θ = m ∫_M β`
  (`TauCeti.integralTopForm_wedge_mpullback_fst`). The same argument kills `∫ T ∧ dη`.

## Main definitions and results

* `TauCeti.RoughForm.fiberFlux`: the flux of a two-form on `M × ℂ` through a normal fibre.
* `TauCeti.integralTopForm_wedge_mpullback_fst_of_tsupport_subset_chart`: `∫ T ∧ π^*θ = m ∫ θ`
  for `θ` supported in one chart of the base.
* `TauCeti.integralTopForm_wedge_mpullback_fst`: `∫ T ∧ π^*β = m ∫_M β` for a closed `T` and a
  compactly supported `β` over a preconnected base.
* `TauCeti.integralTopForm_wedge_smul_mpullback_fst_add_mextDerivₗ`: the taming pairing
  `∫ T ∧ (K π^*β + dη) = K m ∫_M β`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4 and §6.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The flux of a two-form `T` on `M × ℂ` through the normal fibre `{x} × ℂ`: the integral over
`ℂ` of its value on the frame `(0, 1), (0, i)` of the fibre. -/
def RoughForm.fiberFlux (T : RoughForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2) (x : M) : ℝ :=
  ∫ w : ℂ, T (x, w) ![((0 : E), (1 : ℂ)), (0, Complex.I)]

theorem RoughForm.fiberFlux_def (T : RoughForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2) (x : M) :
    RoughForm.fiberFlux T x = ∫ w : ℂ, T (x, w) ![((0 : E), (1 : ℂ)), (0, Complex.I)] :=
  (rfl)

section chart

/-- The wedge `T ∧ π^*θ` of a two-form on `M × ℂ` with the pullback of a two-form on `M` is
supported in the support of `T` and over the support of `θ`. -/
private theorem tsupport_wedge_mpullback_fst_subset (T : RoughForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2)
    (θ : RoughForm I M ℝ 2) :
    _root_.tsupport (α := (E × ℂ) [⋀^Fin (2 + 2)]→L[ℝ] ℝ)
        (RoughForm.wedge T (mpullback (I.prod 𝓘(ℝ, ℂ)) I Prod.fst θ)) ⊆
      _root_.tsupport (α := (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) T ∩
        Prod.fst ⁻¹' _root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) θ := by
  rw [RoughForm.wedge_def]
  exact subset_inter (RoughForm.tsupport_wedgeWith_subset_left _ _ _)
    ((RoughForm.tsupport_wedgeWith_subset_right _ _ _).trans
      (RoughForm.tsupport_mpullback_subset_preimage continuous_fst θ))

variable [IsManifold I ∞ M]

variable [I.Boundaryless]

/-- In the chart `(extChartAt I x₀).symm × id` of `M × ℂ`, the coefficient of `T ∧ π^*θ` on the
product frame `(b₀, 0), (b₁, 0), (0, 1), (0, i)` is the slice density of `T` times the coefficient
of `θ` on `b`. -/
private theorem mpullback_extChartAt_prod_symm_wedge_apply
    (T : RoughForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2) (θ : RoughForm I M ℝ 2) (x₀ : M) (w₀ : ℂ)
    {y : E × ℂ} (hy : y.1 ∈ (extChartAt I x₀).target) (b : Module.Basis (Fin 2) ℝ E) :
    mpullback 𝓘(ℝ, E × ℂ) (I.prod 𝓘(ℝ, ℂ)) (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, w₀)).symm
        (RoughForm.wedge T (mpullback (I.prod 𝓘(ℝ, ℂ)) I Prod.fst θ)) y
        ((b.prod Complex.basisOneI).reindex finSumFinEquiv) =
      T ((extChartAt I x₀).symm y.1, y.2) ![((0 : E), (1 : ℂ)), (0, Complex.I)] *
        mpullback 𝓘(ℝ, E) I (extChartAt I x₀).symm θ y.1 b := by
  -- The derivative of the inverse chart is that of the inverse chart of `M` on the base and the
  -- identity on the fibre.
  have hD (v : E × ℂ) : mfderiv 𝓘(ℝ, E × ℂ) (I.prod 𝓘(ℝ, ℂ))
      (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, w₀)).symm y v =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y.1 v.1, v.2) := by
    have hz : y ∈ (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, w₀)).target := by
      rw [extChartAt_prod_target]
      exact ⟨hy, by simp⟩
    rw [mfderiv_extChartAt_symm_prod_apply hz, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, mfderiv_id]
    -- The fibre factor is the identity of `TangentSpace 𝓘(ℝ, ℂ) y.2`, which is `ℂ` only up to
    -- unfolding, so `ContinuousLinearMap.id_apply` does not match syntactically; it holds by `rfl`.
    rfl
  -- The pullback of `π^*θ` is the pullback of `θ` composed with the projection to `E`.
  have hθ : mpullback 𝓘(ℝ, E × ℂ) (I.prod 𝓘(ℝ, ℂ)) (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, w₀)).symm
      (mpullback (I.prod 𝓘(ℝ, ℂ)) I Prod.fst θ) y =
      (mpullback 𝓘(ℝ, E) I (extChartAt I x₀).symm θ y.1).compContinuousLinearMap
        (ContinuousLinearMap.fst ℝ E ℂ) := by
    -- The tangent spaces of `E × ℂ` and of `E` are these spaces themselves, but only up to
    -- unfolding `TangentSpace`, so the evaluation lemmas are applied with `erw`.
    refine ContinuousAlternatingMap.ext fun (v : Fin 2 → E × ℂ) ↦ ?_
    erw [ContinuousAlternatingMap.compContinuousLinearMap_apply, mpullback_apply, mpullback_apply,
      mpullback_apply]
    simp only [hD, mfderiv_fst]
    rfl
  rw [mpullback_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply']
  -- Read both pulled-back forms as alternating maps on the model `E × ℂ` rather than on its
  -- tangent space, the type in which `wedge_compContinuousLinearMap_fst_apply` is stated.
  change ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (mpullback 𝓘(ℝ, E × ℂ) (I.prod 𝓘(ℝ, ℂ)) (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, w₀)).symm T y :
        (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ)
      (mpullback 𝓘(ℝ, E × ℂ) (I.prod 𝓘(ℝ, ℂ)) (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, w₀)).symm
        (mpullback (I.prod 𝓘(ℝ, ℂ)) I Prod.fst θ) y : (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ)
      ((b.prod Complex.basisOneI).reindex finSumFinEquiv) = _
  rw [hθ]
  -- `pairedWedge` with multiplication is the wedge product of real-valued forms.
  refine (DFunLike.congr_fun (ContinuousAlternatingMap.wedge_def (E := E × ℂ) _ _).symm _).trans
    ((wedge_compContinuousLinearMap_fst_apply b _ _).trans ?_)
  -- As above, the frame vectors of `E × ℂ` are tangent vectors only up to unfolding.
  erw [mpullback_apply_pair, hD, hD, (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y.1).map_zero]
  rfl

variable [FiniteDimensional ℝ E]

/-- Over a point `a` of the chart target of `M`, the fibre integral of the chart coefficient of
`T ∧ π^*θ` on `M × ℂ` is the flux of `T` times the chart coefficient of `θ` on `M`, provided that
the flux is `m` over the support of `θ`. -/
private theorem integral_signAt_mul_mpullback_wedge_eq {k : ℕ}
    (l : Manifold.OrientationLift I M (Fin k)) (h2 : Fintype.card (Fin 2) = Module.finrank ℝ ℂ)
    (T : RoughForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2) (θ : RoughForm I M ℝ 2) (x₀ : M) {m : ℝ}
    (hm : ∀ x ∈ _root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) θ, RoughForm.fiberFlux T x = m)
    {a : E} (ha : a ∈ (extChartAt I x₀).target) (b : Module.Basis (Fin 2) ℝ E) :
    ∫ w : ℂ, ((l.prod (Manifold.OrientationLift.ofHasGroupoid (I := 𝓘(ℝ, ℂ)) (M := ℂ)
        Complex.orientation h2)).signAt (x₀, 0)
          ((extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, 0)).symm (a, w)) : ℝ) *
        mpullback 𝓘(ℝ, E × ℂ) (I.prod 𝓘(ℝ, ℂ)) (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, 0)).symm
          (RoughForm.wedge T (mpullback (I.prod 𝓘(ℝ, ℂ)) I Prod.fst θ)) (a, w)
          ((b.prod Complex.basisOneI).reindex finSumFinEquiv) =
      m * ((l.signAt x₀ ((extChartAt I x₀).symm a) : ℝ) *
        mpullback 𝓘(ℝ, E) I (extChartAt I x₀).symm θ a b) := by
  -- Pointwise, the product chart sign is that of `M` and the coefficient splits.
  refine (integral_congr_ae (g := fun w ↦ (l.signAt x₀ ((extChartAt I x₀).symm a) : ℝ) *
      (T ((extChartAt I x₀).symm a, w) ![((0 : E), (1 : ℂ)), (0, Complex.I)] *
        mpullback 𝓘(ℝ, E) I (extChartAt I x₀).symm θ a b)) (ae_of_all _ fun w ↦
    congrArg₂ (fun (s : ℤˣ) t ↦ (s : ℝ) * t) (l.prod_ofHasGroupoid_signAt _ h2 _ _)
      (mpullback_extChartAt_prod_symm_wedge_apply T θ x₀ 0 (y := (a, w)) ha b))).trans ?_
  rw [integral_const_mul, integral_mul_const, ← RoughForm.fiberFlux_def]
  by_cases hθa : θ ((extChartAt I x₀).symm a) = 0
  · have h0 : mpullback 𝓘(ℝ, E) I (extChartAt I x₀).symm θ a b = 0 := by
      -- `b` is a frame of `E`, a tangent space of the model only up to unfolding.
      erw [mpullback_apply, hθa]
      rfl
    rw [h0]
    ring
  · rw [hm _ (subset_tsupport _ hθa)]
    ring

/-- **The pairing of a two-form with a pulled-back base form, in one chart of the base.** Let `T`
be a compactly supported smooth two-form on `M × ℂ` and `θ` a compactly supported smooth two-form
on a surface `M`, supported in the source of the chart at `x₀`. If the flux of `T` through the
fibre `{x} × ℂ` is `m` at every point `x` of the support of `θ`, then
`∫_{M × ℂ} T ∧ π^*θ = m ∫_M θ`, for the product of an orientation of `M` and the standard
orientation of `ℂ`. -/
theorem integralTopForm_wedge_mpullback_fst_of_tsupport_subset_chart
    (o : Manifold.Orientation I M (Fin 2)) {T : SmoothForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2}
    (hT : IsCompact (_root_.tsupport (α := (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) T.1))
    {θ : SmoothForm I M ℝ 2} {x₀ : M}
    (hθ : IsCompact (_root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) θ.1))
    (hθx : _root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) θ.1 ⊆ (chartAt H x₀).source) {m : ℝ}
    (hm : ∀ x ∈ _root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) θ.1, RoughForm.fiberFlux T.1 x = m) :
    integralTopForm (o.prod (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
        (by simp [Complex.finrank_real_complex])))
      (RoughForm.wedge T.1 (SmoothForm.mpullback Prod.fst contMDiff_fst θ).1) =
      m * integralTopForm o θ.1 := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  have h2 : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by simp [Complex.finrank_real_complex]
  let lC := Manifold.OrientationLift.ofHasGroupoid (I := 𝓘(ℝ, ℂ)) (M := ℂ) Complex.orientation h2
  rw [Manifold.Orientation.model_eq_mk, Manifold.Orientation.prod_mk, SmoothForm.coe_mpullback]
  -- Positive bases of `E` and of `E × ℂ`.
  let b := (Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)).adjustToOrientation
    l.modelOrientation
  have hb : b.orientation = l.modelOrientation := Module.Basis.orientation_adjustToOrientation _ _
  let B := (b.prod Complex.basisOneI).reindex finSumFinEquiv
  have hB : B.orientation = (l.prod lC).modelOrientation := by
    rw [Manifold.OrientationLift.prod_modelOrientation,
      Manifold.OrientationLift.ofHasGroupoid_modelOrientation, ← hb]
    exact (Orientation.prod_basis_orientation b Complex.basisOneI _ _).symm
  set φ := RoughForm.wedge T.1 (mpullback (I.prod 𝓘(ℝ, ℂ)) I Prod.fst θ.1) with hφ
  have hφs : IsSmoothForm (I.prod 𝓘(ℝ, ℂ)) 0 φ := by
    rw [hφ, ← SmoothForm.coe_mpullback (hf := contMDiff_fst), ← SmoothForm.coe_wedge]
    exact (SmoothForm.wedge T (SmoothForm.mpullback Prod.fst contMDiff_fst θ)).isSmoothForm.of_le
      (by simp)
  -- The support of `φ` is compact and lies in the product chart at `(x₀, 0)`.
  have hsupp := tsupport_wedge_mpullback_fst_subset (I := I) T.1 θ.1
  have hc : IsCompact (_root_.tsupport (α := (E × ℂ) [⋀^Fin (2 + 2)]→L[ℝ] ℝ) φ) :=
    hT.of_isClosed_subset (isClosed_tsupport _) (hsupp.trans inter_subset_left)
  have hs : _root_.tsupport (α := (E × ℂ) [⋀^Fin (2 + 2)]→L[ℝ] ℝ) φ ⊆
      (chartAt (ModelProd H ℂ) (x₀, (0 : ℂ))).source := by
    refine hsupp.trans fun p hp ↦ ?_
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod,
      chartAt_self_eq, OpenPartialHomeomorph.refl_source, mem_univ, and_true] using hθx hp.2
  -- The product chart has target `target × ℂ`, with the product Haar measure.
  have htarget : (extChartAt (I.prod 𝓘(ℝ, ℂ)) (x₀, (0 : ℂ))).target =
      (extChartAt I x₀).target ×ˢ univ := by
    rw [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.prod_target,
      PartialEquiv.refl_target]
  have hmeas : B.addHaar = b.addHaar.prod (volume : Measure ℂ) := by
    simp only [B, Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar,
      Complex.addHaar_basisOneI]
  have hint := ((l.prod lC).integrable_signedInChartAt_iff_mpullback φ B (x₀, 0) B.addHaar).mp
    ((l.prod lC).integrable_signedInChartAt hφs B (x₀, 0) hc
      (by simpa only [extChartAt_source] using hs))
  rw [htarget, hmeas] at hint
  -- Fubini's theorem in the product chart.
  rw [integralTopForm_of_tsupport_subset_chart (l.prod lC) hφs hc (x₀, 0) hs B hB,
    integralTopForm_of_tsupport_subset_chart l (θ.isSmoothForm.of_le (by simp)) hθ x₀ hθx b hb,
    htarget, hmeas, setIntegral_prod _ hint, ← integral_const_mul]
  refine setIntegral_congr_fun (isOpen_extChartAt_target x₀).measurableSet fun a ha ↦ ?_
  simpa only [Measure.restrict_univ] using
    integral_signAt_mul_mpullback_wedge_eq l h2 T.1 θ.1 x₀ hm ha b

end chart

section global

variable [IsManifold I ∞ M] [I.Boundaryless] [FiniteDimensional ℝ E] [T2Space M]

/-- **The pairing of a closed two-form with a pulled-back base form.** Let `M` be a σ-compact
preconnected oriented surface and `T` a compactly supported closed two-form on `M × ℂ` whose flux
through every fibre `{x} × ℂ` is `m`. Then `∫_{M × ℂ} T ∧ π^*β = m ∫_M β` for every compactly
supported two-form `β` on `M`, for the product of the orientation of `M` and the standard
orientation of `ℂ`. -/
theorem integralTopForm_wedge_mpullback_fst [SigmaCompactSpace M] [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin 2)) {T : SmoothForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2}
    (hT : T ∈ compactlySupportedClosedForms (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) 2) {m : ℝ}
    (hm : ∀ x, RoughForm.fiberFlux T.1 x = m) {β : SmoothForm I M ℝ 2}
    (hβ : β ∈ compactlySupportedForms I M 2) :
    integralTopForm (o.prod (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
        (by simp [Complex.finrank_real_complex])))
      (SmoothForm.wedge T (SmoothForm.mpullback Prod.fst contMDiff_fst β)).1 =
      m * integralTopForm o β.1 := by
  set oP := o.prod (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
    (by simp [Complex.finrank_real_complex]))
  have hTc := ((mem_compactlySupportedClosedForms _).mp hT).1
  -- Over an empty base, both integrals vanish.
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Subsingleton.elim (SmoothForm.wedge T (SmoothForm.mpullback Prod.fst contMDiff_fst β)).1 0,
      Subsingleton.elim β.1 0, integralTopForm_zero, integralTopForm_zero, mul_zero]
  -- A bump form `θ` of integral one supported in the chart at some point `x₀`.
  obtain ⟨x₀⟩ := hM
  obtain ⟨θ, hθx, hθ⟩ := exists_compactlySupportedClosedForms_integralTopForm_eq_one o x₀
    (chart_source_mem_nhds H x₀)
  have hθc := ((mem_compactlySupportedClosedForms I).mp θ.2).1
  -- `β - (∫ β) θ` has integral zero, so it is exact.
  set c := integralTopForm o β.1
  have hex : β - c • θ.1 ∈ exactForms I M 2 := by
    refine exactCompactlySupportedForms_le_exactForms I 2
      ((mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o
        (sub_mem hβ (Submodule.smul_mem _ c hθc))).mpr ?_)
    rw [integralTopForm_sub_of_mem_compactlySupportedForms o hβ (Submodule.smul_mem _ c hθc),
      Submodule.coe_smul, integralTopForm_smul, hθ, mul_one, sub_self]
  -- Its pullback is exact, so it pairs to zero with `T`.
  have h0 := integralTopForm_wedge_eq_zero_of_mem_exactForms oP
    (closedForms.mpullback_mem_exactForms (I := I.prod 𝓘(ℝ, ℂ)) (I' := I)
      (Prod.fst : M × ℂ → M) contMDiff_fst 2
      ⟨_, mem_closedForms_of_finrank_le I (by simp [o.card_eq.symm]) (β - c • θ.1)⟩ hex) hT
  rw [SmoothForm.wedge_comm_of_even even_two, closedForms.coe_mpullback, map_sub, map_smul,
    map_sub, map_smul] at h0
  set X := SmoothForm.wedge T (SmoothForm.mpullback Prod.fst contMDiff_fst β)
  set Y := SmoothForm.wedge T (SmoothForm.mpullback Prod.fst contMDiff_fst θ.1)
  -- The pairing of `T` with `π^*θ` is computed in the chart at `x₀`.
  have hY : integralTopForm oP Y.1 = m := by
    rw [SmoothForm.coe_wedge, integralTopForm_wedge_mpullback_fst_of_tsupport_subset_chart o
      ((mem_compactlySupportedForms _).mp hTc) ((mem_compactlySupportedForms I).mp hθc) hθx
      (fun x _ ↦ hm x), hθ, mul_one]
  rw [integralTopForm_sub_of_mem_compactlySupportedForms oP
    (SmoothForm.wedge_mem_compactlySupportedForms_of_left_mem hTc _)
    (Submodule.smul_mem _ c (SmoothForm.wedge_mem_compactlySupportedForms_of_left_mem hTc _)),
    Submodule.coe_smul, integralTopForm_smul, hY] at h0
  linarith

/-- **The taming pairing of a closed current of transverse flux `m`.** Let `M` be a σ-compact
preconnected oriented surface and `T` a compactly supported closed two-form on `M × ℂ` whose flux
through every fibre `{x} × ℂ` is `m`. For a compactly supported two-form `β` on `M`, a one-form `η`
on `M × ℂ` and a constant `K`, the two-form `Ω = K π^*β + dη` pairs with `T` to

`∫_{M × ℂ} T ∧ (K π^*β + dη) = K m ∫_M β`,

for the product of the orientation of `M` and the standard orientation of `ℂ`. -/
theorem integralTopForm_wedge_smul_mpullback_fst_add_mextDerivₗ [SigmaCompactSpace M]
    [PreconnectedSpace M] (o : Manifold.Orientation I M (Fin 2))
    {T : SmoothForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 2}
    (hT : T ∈ compactlySupportedClosedForms (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) 2) {m : ℝ}
    (hm : ∀ x, RoughForm.fiberFlux T.1 x = m) (K : ℝ) {β : SmoothForm I M ℝ 2}
    (hβ : β ∈ compactlySupportedForms I M 2) (η : SmoothForm (I.prod 𝓘(ℝ, ℂ)) (M × ℂ) ℝ 1) :
    integralTopForm (o.prod (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
        (by simp [Complex.finrank_real_complex])))
      (SmoothForm.wedge T (K • SmoothForm.mpullback Prod.fst contMDiff_fst β +
        mextDerivₗ (I.prod 𝓘(ℝ, ℂ)) (F := ℝ) 1 η)).1 =
      K * m * integralTopForm o β.1 := by
  have hTc := ((mem_compactlySupportedClosedForms _).mp hT).1
  set X := SmoothForm.wedge T (SmoothForm.mpullback Prod.fst contMDiff_fst β)
  set Y := SmoothForm.wedge T (mextDerivₗ (I.prod 𝓘(ℝ, ℂ)) (F := ℝ) 1 η) with hY
  rw [SmoothForm.wedge_comm_of_even even_two] at hY
  rw [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
    integralTopForm_add _ ((X.isSmoothForm.smul K).of_le (by simp)) (Y.isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms _).mp (Submodule.smul_mem _ K
        (SmoothForm.wedge_mem_compactlySupportedForms_of_left_mem hTc _)))
      ((mem_compactlySupportedForms _).mp
        (SmoothForm.wedge_mem_compactlySupportedForms_of_left_mem hTc _)),
    integralTopForm_smul, integralTopForm_wedge_mpullback_fst o hT hm hβ,
    hY, integralTopForm_wedge_eq_zero_of_mem_exactForms _
      (by rw [exactForms_succ]; exact ⟨η, rfl⟩) hT]
  ring

end global

end TauCeti
