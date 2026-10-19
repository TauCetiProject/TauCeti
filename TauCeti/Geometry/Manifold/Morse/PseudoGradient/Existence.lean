/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Basic
public import TauCeti.Geometry.Manifold.VectorField.ModelChart
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Existence of adapted pseudo-gradients

A smooth function whose critical points on a compact set `K` are nondegenerate has a smooth
pseudo-gradient on a neighbourhood of `K`, equal to the linear Morse-chart field on smaller charts
around the critical points of `K` (`IsCompact.exists_contMDiff_pseudoGradientOn_nhds`). This local
form does not require the ambient manifold to be compact and imposes no condition on critical
points away from `K`; it supplies pseudo-gradients on compact level bands for the deformation and
handle-attachment constructions of Morse theory. Taking `K` to be the whole of a compact
boundaryless manifold, modelled on a finite-dimensional real normed space, every Morse function
has a pseudo-gradient field adapted to it (`TauCeti.IsMorse.exists_isAdaptedPseudoGradient`).

The proof follows Audin and Damian. Near each critical point the field is the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` of a Morse chart, pulled back to the manifold (`TauCeti.MorseChart.field`). Near a
regular point it is a constant field in a chart, chosen in a direction in which `f` decreases
(`TauCeti.chartConstField`). These local fields are glued by Mathlib's
partition-of-unity theorem for sections with values in fibrewise convex sets,
`exists_contMDiffSection_forall_mem_convex_of_local`. The convex set at a point asks for
`df(X) < 0` on a closed regular core, and for equality with the Morse field if the point lies in a
closed neighbourhood of a critical point. These neighbourhoods are chosen pairwise disjoint, which
is possible because nondegenerate critical points are isolated, so a compact set contains only
finitely many of them. Continuity enlarges the strict-decrease locus around the regular core; its
union with the interiors of the critical-point neighbourhoods is the returned neighbourhood of
`K`.

## Main declarations

* `TauCeti.MorseChart.field`: the linear field of a Morse chart, on the manifold, with
  `TauCeti.MorseChart.mvfderiv_field_apply_lt_zero` and `TauCeti.MorseChart.mfderiv_eq_zero_iff`.
* `TauCeti.MorseChart.hessianQuadraticForm_quadratic` and
  `TauCeti.MorseChart.hessianQuadraticForm_extChartAt`: the Hessian of the quadratic normal form,
  and the Hessian of `f` at the centre of a Morse chart, read in the preferred chart.
* `IsCompact.exists_contMDiff_pseudoGradientOn_nhds`: existence of a pseudo-gradient near a
  compact set whose critical points are nondegenerate, and its Morse-function specialization
  `TauCeti.IsMorse.exists_contMDiff_pseudoGradientOn_nhds`.
* `TauCeti.IsMorse.exists_isAdaptedPseudoGradient`: existence of adapted pseudo-gradients.

The chart calculus used here is general and lives in
`TauCeti/Geometry/Manifold/MFDeriv/ModelChart.lean` and
`TauCeti/Geometry/Manifold/VectorField/ModelChart.lean`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.2.3 and its proof.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

namespace MorseChart

section Basic

variable (φ : MorseChart E f x)

/-- The quadratic normal form of a Morse chart, as a function on the model space. -/
noncomputable def quadratic (z : E) : ℝ :=
  f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * (φ.coord z i) ^ 2

/-- On the source of a Morse chart, `f` is the quadratic normal form read in the chart. -/
theorem eqOn_quadratic : EqOn f (φ.quadratic ∘ φ.toChart) φ.toChart.source := fun y hy ↦ by
  simp only [comp_apply, quadratic]
  exact φ.eq_quadratic y hy

/-- The negative gradient `z ↦ L⁻¹ (-(wᵢ (L z)ᵢ)ᵢ)` of the quadratic normal form, read in the
coordinates of the Morse chart. -/
noncomputable def linearField (z : E) : E :=
  φ.coord.symm fun i ↦ -(φ.weight i * φ.coord z i)

/-- The linear field of a Morse chart, as a vector field on the model space. -/
noncomputable def linearVectorField : (z : E) → TangentSpace 𝓘(ℝ, E) z := φ.linearField

/-- The pullback to the manifold of the linear field of a Morse chart. -/
noncomputable def field : (y : M) → TangentSpace 𝓘(ℝ, E) y :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart φ.linearVectorField

/-- Restricting a Morse chart to an open neighbourhood of its centre does not change its field. -/
@[simp]
theorem restr_field {s : Set M} (hs : IsOpen s) (hx : x ∈ s) : (φ.restr hs hx).field = φ.field := by
  have hlin : (φ.restr hs hx).linearField = φ.linearField := by
    ext z
    simp only [linearField, restr_coord, restr_weight]
  rw [field, field, linearVectorField, linearVectorField, hlin, restr_toChart,
    OpenPartialHomeomorph.restr_apply]

/-- In the coordinates of the Morse chart, the field is `z ↦ (-wᵢ zᵢ)ᵢ`. -/
theorem coord_mfderiv_field {y : M} (hy : y ∈ φ.toChart.source) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (φ.field y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  rw [field, mfderiv_mpullback_apply φ.mem_maximalAtlas _ hy]
  simp [linearVectorField, linearField]

end Basic

section FiniteDimensional

variable [FiniteDimensional ℝ E] (φ : MorseChart E f x)

/-- The coordinate change of a Morse chart, as a continuous linear equivalence. -/
noncomputable def coordL : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  φ.coord.toContinuousLinearEquiv

/-- `coordL` is `coord`. -/
@[simp]
theorem coordL_apply (z : E) : φ.coordL z = φ.coord z := by
  simp [coordL]

/-- The inverse of `coordL` is the inverse of `coord`. -/
@[simp]
theorem coordL_symm_apply (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.coordL.symm z = φ.coord.symm z := by
  simp [coordL]

/-- Coordinates of small sup norm are coordinates of points of the chart. -/
theorem exists_pos_forall_norm_lt_mem_target :
    ∃ r > 0, ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target := by
  have h0 : (0 : Fin (Module.finrank ℝ E) → ℝ) ∈ φ.coordL.symm ⁻¹' φ.toChart.target := by
    rw [mem_preimage, map_zero, ← φ.apply_self]
    exact φ.toChart.map_source φ.mem_source
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
    (φ.toChart.open_target.preimage φ.coordL.symm.continuous) 0 h0
  exact ⟨r, hr, fun z hz ↦ by simpa using hball (mem_ball_zero_iff.2 hz)⟩

/-- The derivative of the quadratic normal form. -/
theorem hasFDerivAt_quadratic (z : E) :
    HasFDerivAt φ.quadratic
      ((∑ i, (φ.weight i * φ.coord z i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
          (φ.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))) z := by
  have h := (hasFDerivAt_diagonalQuadratic (f x) φ.weight (φ.coordL z)).comp z
    φ.coordL.hasFDerivAt
  convert h using 1
  · ext v
    simp [quadratic, sq]
  · simp

/-- The derivative of the quadratic normal form is `v ↦ Σᵢ wᵢ (L z)ᵢ (L v)ᵢ`. -/
theorem fderiv_quadratic_apply (z v : E) :
    fderiv ℝ φ.quadratic z v = ∑ i, φ.weight i * φ.coord z i * φ.coord v i := by
  rw [(φ.hasFDerivAt_quadratic z).fderiv]
  simp

/-- The quadratic normal form is differentiable. -/
theorem differentiableAt_quadratic (z : E) : DifferentiableAt ℝ φ.quadratic z :=
  (φ.hasFDerivAt_quadratic z).differentiableAt

/-- The quadratic normal form has a single critical point, the origin. -/
theorem fderiv_quadratic_eq_zero_iff {z : E} : fderiv ℝ φ.quadratic z = 0 ↔ z = 0 := by
  constructor
  · intro h0
    have hz : φ.coord z = 0 := by
      ext i
      have := congrArg (fun T : E →L[ℝ] ℝ ↦ T (φ.coord.symm (Pi.single i (φ.weight i))))
        h0
      simp only [fderiv_quadratic_apply, LinearEquiv.apply_symm_apply,
        zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
      simp only [Pi.single_eq_same] at this
      rcases φ.weight_eq_neg_one_or_eq_one i with hw | hw <;> rw [hw] at this <;> simpa using this
    simpa using congrArg φ.coord.symm hz
  · rintro rfl
    ext v
    simp [fderiv_quadratic_apply]

/-- The derivative of the quadratic normal form is a continuous linear function of the point,
`z ↦ Σᵢ wᵢ (L z)ᵢ (L ·)ᵢ`. -/
private theorem exists_fderiv_quadratic_eq :
    ∃ B : E →L[ℝ] E →L[ℝ] ℝ, fderiv ℝ φ.quadratic = B ∧
      ∀ u, B u u = ∑ i, φ.weight i * φ.coord u i ^ 2 := by
  set ℓ : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
      (φ.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))
  refine ⟨∑ i, φ.weight i • (ℓ i).smulRight (ℓ i), ?_, fun u ↦ ?_⟩
  · ext z v
    simp [ℓ, φ.fderiv_quadratic_apply, coordL_apply, mul_assoc]
  · simp [ℓ, coordL_apply, sq]

/-- **The Hessian of the quadratic normal form** `f x + (1/2) Σᵢ wᵢ (L z)ᵢ²` is `Σᵢ wᵢ (L u)ᵢ²`, at
every point. -/
theorem hessianQuadraticForm_quadratic (z u : E) :
    hessianQuadraticForm φ.quadratic z u = ∑ i, φ.weight i * φ.coord u i ^ 2 := by
  obtain ⟨B, hB, hBu⟩ := φ.exists_fderiv_quadratic_eq
  rw [hessianQuadraticForm_apply, hB, B.fderiv, hBu]

/-- The quadratic normal form is smooth. -/
theorem contDiff_quadratic : ContDiff ℝ ∞ φ.quadratic := by
  obtain ⟨B, hB, -⟩ := φ.exists_fderiv_quadratic_eq
  rw [contDiff_infty_iff_fderiv, hB]
  exact ⟨fun z ↦ φ.differentiableAt_quadratic z, B.contDiff⟩

/-- The derivative of the quadratic normal form along the linear field is `-Σᵢ (L z)ᵢ²`. -/
theorem fderiv_quadratic_linearField (z : E) :
    fderiv ℝ φ.quadratic z (φ.linearField z) = -∑ i, (φ.coord z i) ^ 2 := by
  rw [fderiv_quadratic_apply]
  simp only [linearField, LinearEquiv.apply_symm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases φ.weight_eq_neg_one_or_eq_one i with hw | hw <;> rw [hw] <;> ring

/-- The linear field of a Morse chart is smooth. -/
theorem contDiff_linearField : ContDiff ℝ ∞ φ.linearField := by
  have h1 : ContDiff ℝ ∞ (fun z : E ↦ fun i ↦ -(φ.weight i * φ.coordL z i)) :=
    contDiff_pi.2 fun i ↦
      (contDiff_const.mul ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp φ.coordL.contDiff)).neg
  have : φ.linearField = φ.coordL.symm ∘ fun z i ↦ -(φ.weight i * φ.coordL z i) := by
    ext z
    simp [linearField, coordL]
  rw [this]
  exact φ.coordL.symm.contDiff.comp h1

/-- The derivative of `f` along the field of a Morse chart is `-Σᵢ (L (ψ y))ᵢ²`. -/
theorem mvfderiv_field_apply {y : M} (hy : y ∈ φ.toChart.source) :
    mvfderiv 𝓘(ℝ, E) f y (φ.field y) = -∑ i, (φ.coord (φ.toChart y) i) ^ 2 := by
  rw [field, mvfderiv_mpullback_apply φ.mem_maximalAtlas φ.eqOn_quadratic _ hy
    (φ.differentiableAt_quadratic _)]
  exact φ.fderiv_quadratic_linearField _

/-- `f` strictly decreases along the field away from the centre of the chart. -/
theorem mvfderiv_field_apply_lt_zero {y : M} (hy : y ∈ φ.toChart.source) (hyx : y ≠ x) :
    mvfderiv 𝓘(ℝ, E) f y (φ.field y) < 0 := by
  rw [φ.mvfderiv_field_apply hy, neg_lt_zero]
  have hne : φ.coord (φ.toChart y) ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff, φ.toChart_eq_zero_iff hy]
    exact hyx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
    ⟨i, Finset.mem_univ _, by simpa using (sq_pos_of_ne_zero hi : (0 : ℝ) < _)⟩

/-- The centre is the only critical point of `f` in the source of a Morse chart. -/
theorem mfderiv_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ y = x := by
  rw [mfderiv_eq_zero_iff_of_eqOn
      (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) φ.eqOn_quadratic hy
      (φ.differentiableAt_quadratic _),
    φ.fderiv_quadratic_eq_zero_iff, φ.toChart_eq_zero_iff hy]

end FiniteDimensional

section IsManifold

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] (φ : MorseChart E f x)

/-- **The Hessian in the preferred chart.** At the centre `x` of a Morse chart `φ`, the Hessian of
`f` read in the preferred chart at `x` is `v ↦ Σᵢ wᵢ (L (dφ v))ᵢ²`, where `dφ` is the derivative of
the Morse chart at `x`. -/
theorem hessianQuadraticForm_extChartAt (v : E) :
    hessianQuadraticForm (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) (extChartAt 𝓘(ℝ, E) x x) v =
      ∑ i, φ.weight i * φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x v) i ^ 2 := by
  set ψ := extChartAt 𝓘(ℝ, E) x
  -- In the preferred chart, `f` is the normal form composed with the transition map `τ`.
  set τ : E → E := φ.toChart ∘ ψ.symm
  have hτa : τ (ψ x) = 0 := by simp [τ, ψ]
  have hsrc : ∀ᶠ z in 𝓝 (ψ x), ψ.symm z ∈ φ.toChart.source :=
    (continuousAt_extChartAt_symm x).preimage_mem_nhds
      (by simpa [ψ] using φ.toChart.open_source.mem_nhds φ.mem_source)
  have hev : f ∘ ψ.symm =ᶠ[𝓝 (ψ x)] φ.quadratic ∘ τ := by
    filter_upwards [hsrc] with z hz
    exact φ.eqOn_quadratic hz
  have hτ : ContDiffAt ℝ 2 τ (ψ x) := by
    have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.toChart (ψ.symm (ψ x)) := by
      simpa [ψ] using (contMDiffOn_of_mem_maximalAtlas φ.mem_maximalAtlas).contMDiffAt
        (φ.toChart.open_source.mem_nhds φ.mem_source)
    have h2 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ.symm (ψ x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    exact ((h1.comp _ h2).contDiffAt).of_le (by norm_cast)
  have hcrit : fderiv ℝ φ.quadratic (τ (ψ x)) = 0 := by
    rw [hτa]
    exact φ.fderiv_quadratic_eq_zero_iff.2 rfl
  -- The chart of the model space is the identity, so `φ` read in charts is `τ`.
  have hD : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x = fderiv ℝ τ (ψ x) := by
    rw [(φ.mdifferentiableAt_toChart φ.mem_source).mfderiv, modelWithCornersSelf_coe, range_id,
      fderivWithin_univ, writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      id_comp]
    -- The casts `tangentSpaceCastModel` between the tangent spaces and `E` are identities.
    rfl
  rw [hessianQuadraticForm_congr_of_eventuallyEq hev,
    hessianQuadraticForm_comp ((φ.contDiff_quadratic.of_le (by norm_cast)).contDiffAt) hτ hcrit,
    QuadraticMap.comp_apply, hessianQuadraticForm_quadratic, hD]
  -- The two sides differ only in reading `v` in `E` or in the tangent space `T_x M = E`.
  rfl

/-- The field of a Morse chart is smooth on the source of the chart. -/
theorem contMDiffOn_field :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, φ.field y⟩ : TangentBundle 𝓘(ℝ, E) M)) φ.toChart.source :=
  contMDiffOn_mpullback φ.mem_maximalAtlas φ.contDiff_linearField.contDiffOn

end IsManifold

end MorseChart

section Existence

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

open Filter in
/-- **Existence of a pseudo-gradient near a compact set.** Let `K` be a compact subset of a
regular Hausdorff sigma-compact manifold and let `f` be smooth. If every critical point of `f` in
`K` is nondegenerate,
then on an open neighbourhood `U` of `K` there is a smooth vector field along which `f` strictly
decreases at every regular point. Around each critical point in `K`, the field agrees on the
whole source of a smaller Morse chart with that chart's linear pseudo-gradient field.

The field is defined globally, but no condition is imposed away from `U`. In particular the
ambient manifold need not be compact and `f` may have arbitrary critical points away from `K`. -/
theorem _root_.IsCompact.exists_contMDiff_pseudoGradientOn_nhds [T2Space M] [SigmaCompactSpace M]
    {K : Set M}
    (hK : IsCompact K) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hnd : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    ∃ U ∈ 𝓝ˢ K, IsOpen U ∧
      ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
            (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ x ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 →
            mvfderiv 𝓘(ℝ, E) f x (X x) < 0) ∧
          ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
            ∃ φ : MorseChart E f x, φ.toChart.source ⊆ U ∧
              ∀ y ∈ φ.toChart.source, X y = φ.field y := by
  classical
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  -- The critical points in `K` are isolated, hence finitely many. Choose a Morse chart at each,
  -- and pairwise disjoint closed neighbourhoods `A x` inside these charts.
  let C := criticalPoints 𝓘(ℝ, E) f ∩ K
  have hC : C.Finite := by
    refine (hK.inter_left (isClosed_criticalPoints (hf.of_le (by simp)))).finite ?_
    rw [isDiscrete_iff_nhdsNE]
    rintro x ⟨hx, hxK⟩
    rw [inf_principal_eq_bot]
    filter_upwards [(hnd x hxK
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)).eventually_notMem_criticalPoints]
      with y hy using fun h ↦ hy h.1
  let φ : ∀ x ∈ C, MorseChart E f x := fun x hx ↦
    ((hnd x hx.2 (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.1)).nonempty_morseChart
      (Eventually.of_forall fun _ ↦ hf.contMDiffAt)).some
  obtain ⟨W, hW, hWdisj⟩ := hC.t2_separation
  have hA : ∀ x (hx : x ∈ C), ∃ A, A ∈ 𝓝 x ∧ IsClosed A ∧
      A ⊆ (φ x hx).toChart.source ∩ W x := fun x hx ↦
    exists_mem_nhds_isClosed_subset
      (Filter.inter_mem ((φ x hx).toChart.open_source.mem_nhds (φ x hx).mem_source)
        ((hW x).2.mem_nhds (hW x).1))
  choose A hAn hAc hAsub using hA
  let A' : M → Set M := fun x ↦ if hx : x ∈ C then A x hx else ∅
  have hA' : ∀ x (hx : x ∈ C), A' x = A x hx := fun x hx ↦ by simp [A', hx]
  -- The rest `R` of `K` is compact and regular, so finitely many closed regular neighbourhoods
  -- cover it; `D` is their union.
  let G := ⋃ x ∈ C, interior (A' x)
  have hGo : IsOpen G := isOpen_biUnion fun _ _ ↦ isOpen_interior
  have hcritical_mem_G {x : M} (hxK : x ∈ K)
      (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : x ∈ G := by
    have hxC : x ∈ C := ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hxK⟩
    refine mem_iUnion₂.2 ⟨x, hxC, ?_⟩
    rw [hA' x hxC]
    exact mem_interior_iff_mem_nhds.2 (hAn x hxC)
  let R := K \ G
  have hRc : IsCompact R := hK.diff hGo
  have hRreg : ∀ x ∈ R, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 := by
    intro x hx hzero
    exact hx.2 (hcritical_mem_G hx.1 hzero)
  have hB : ∀ x ∈ R, ∃ B, B ∈ 𝓝 x ∧ IsClosed B ∧
      B ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ := fun x hx ↦
    exists_mem_nhds_isClosed_subset
      ((isClosed_criticalPoints (hf.of_le (by simp))).isOpen_compl.mem_nhds
        (fun hcrit ↦ hRreg x hx (mem_criticalPoints_iff_mfderiv_eq_zero.1 hcrit)))
  choose B hBn hBc hBsub using hB
  let B' : M → Set M := fun x ↦ if hx : x ∈ R then B x hx else ∅
  have hB' : ∀ x (hx : x ∈ R), B' x = B x hx := fun x hx ↦ by simp [B', hx]
  obtain ⟨q, hqR, hq⟩ := hRc.elim_nhds_subcover B' fun x hx ↦ by
    rw [hB' x hx]
    exact hBn x hx
  let D := ⋃ x ∈ q, B' x
  have hDc : IsClosed D := isClosed_biUnion_finset fun x hx ↦ by
    rw [hB' x (hqR x hx)]
    exact hBc x (hqR x hx)
  have hRD : R ⊆ D := hq
  have hDreg : D ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ := by
    rintro y hy
    obtain ⟨x, hxq, hyB⟩ := mem_iUnion₂.1 hy
    rw [hB' x (hqR x hxq)] at hyB
    exact hBsub x (hqR x hxq) hyB
  have hAclosed : IsClosed (⋃ x ∈ C, A' x) :=
    hC.isClosed_biUnion fun x hx ↦ by rw [hA' x hx]; exact hAc x hx
  -- The fibrewise convex constraint: `df(v) < 0` on `D`, and equality with the Morse field on
  -- each `A x`. Locally it is met by a Morse field near some `A x`, by a chart-constant field near
  -- a point of `D` away from all `A x`, and by the zero field away from `D` and all `A x`.
  let ℓ : (y : M) → TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ :=
    fun y ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y
  let t : (y : M) → Set (TangentSpace 𝓘(ℝ, E) y) := fun y ↦
    {v | y ∈ D → ℓ y v < 0} ∩
      ⋂ x, ⋂ (hx : x ∈ C), ⋂ (_ : y ∈ A x hx), {(φ x hx).field y}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    refine Convex.inter ?_ (convex_iInter fun x ↦ convex_iInter fun hx ↦
      convex_iInter fun _ ↦ convex_singleton _)
    by_cases hy : y ∈ D
    · simp only [hy, true_implies]
      exact convex_halfSpace_lt (ℓ y).isLinear 0
    · simp [hy, convex_univ]
  have hloc : ∀ y₀ : M, ∃ V ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) V ∧ ∀ y ∈ V, s y ∈ t y := by
    intro y₀
    by_cases h : ∃ x, ∃ hx : x ∈ C, y₀ ∈ A x hx
    · obtain ⟨x, hx, hy₀⟩ := h
      have hVo : IsOpen ((φ x hx).toChart.source ∩ W x) :=
        (φ x hx).toChart.open_source.inter (hW x).2
      refine ⟨_, hVo.mem_nhds (hAsub x hx hy₀), (φ x hx).field,
        (φ x hx).contMDiffOn_field.mono inter_subset_left, fun y hy ↦ ⟨fun hyD ↦ ?_, ?_⟩⟩
      · have hycrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := by
          simpa only [mem_compl_iff, mem_criticalPoints_iff_mfderiv_eq_zero] using hDreg hyD
        exact (φ x hx).mvfderiv_field_apply_lt_zero hy.1 fun hyx ↦
          hycrit (hyx ▸ mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.1)
      · simp only [mem_iInter, mem_singleton_iff]
        intro x' hx' hy'
        have hxx' : x = x' := by
          by_contra hne
          exact Set.disjoint_left.1 (hWdisj hx hx' hne) hy.2 ((hAsub x' hx' hy').2)
        subst hxx'
        rfl
    · simp only [not_exists] at h
      by_cases hy₀D : y₀ ∈ D
      · have hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0 := by
          simpa only [mem_compl_iff, mem_criticalPoints_iff_mfderiv_eq_zero] using hDreg hy₀D
        obtain ⟨v, V, hV, hVc, hVneg⟩ :=
          exists_mem_nhds_mvfderiv_chartConstField_lt_zero hf hcrit
        refine ⟨_, Filter.inter_mem (hAclosed.isOpen_compl.mem_nhds ?_) hV,
          chartConstField E y₀ v,
          (contMDiffOn_chartConstField y₀ v).mono fun y hy ↦ hVc hy.2,
          fun y hy ↦ ⟨fun _ ↦ hVneg y hy.2, ?_⟩⟩
        · simp only [mem_compl_iff, mem_iUnion, not_exists]
          intro x hx hmem
          rw [hA' x hx] at hmem
          exact h x hx hmem
        · simp only [mem_iInter, mem_singleton_iff]
          intro x hx hyA
          exfalso
          refine hy.1 (mem_iUnion₂.2 ⟨x, hx, ?_⟩)
          rwa [hA' x hx]
      · refine ⟨Dᶜ ∩ (⋃ x ∈ C, A' x)ᶜ,
          Filter.inter_mem (hDc.isOpen_compl.mem_nhds hy₀D)
            (hAclosed.isOpen_compl.mem_nhds ?_), fun _ ↦ 0,
          (Bundle.contMDiff_zeroSection ℝ
            (TangentSpace 𝓘(ℝ, E) : M → Type _)).contMDiffOn,
          fun y hy ↦ ?_⟩
        · simp only [mem_compl_iff, mem_iUnion, not_exists]
          intro x hx hmem
          rw [hA' x hx] at hmem
          exact h x hx hmem
        · refine ⟨fun hyD ↦ (hy.1 hyD).elim, ?_⟩
          simp only [mem_iInter, mem_singleton_iff]
          intro x hx hyA
          exfalso
          exact hy.2 (mem_iUnion₂.2 ⟨x, hx, by rwa [hA' x hx]⟩)
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) (TangentSpace 𝓘(ℝ, E)) t ht hloc
  -- By continuity of `df(s)`, descent on `D ⊇ R` extends to an open set `V`; together with the
  -- interiors `G` of the chart neighbourhoods it gives the open neighbourhood `U` of `K`.
  have hdesc : Continuous (fun y ↦ mvfderiv 𝓘(ℝ, E) f y (s y)) :=
    ((hf.contMDiff_mvfderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp s.contMDiff).continuous
  let V := (fun y ↦ mvfderiv 𝓘(ℝ, E) f y (s y)) ⁻¹' Iio 0
  let U := V ∪ G
  have hVo : IsOpen V := isOpen_Iio.preimage hdesc
  have hUo : IsOpen U := hVo.union hGo
  have hKU : K ⊆ U := by
    intro x hxK
    by_cases hxG : x ∈ G
    · exact Or.inr hxG
    · apply Or.inl
      have hxR : x ∈ R := ⟨hxK, hxG⟩
      exact (hs x).1 (hRD hxR)
  refine ⟨U, mem_nhdsSet_iff_forall.2 fun x hx ↦ hUo.mem_nhds (hKU hx), hUo, s,
    s.contMDiff, ?_, ?_⟩
  · intro y hy hyreg
    rcases hy with hyV | hyG
    · exact hyV
    · obtain ⟨x, hxC, hyA⟩ := mem_iUnion₂.1 hyG
      have hyA' : y ∈ interior (A x hxC) := by rwa [← hA' x hxC]
      have hysource : y ∈ (φ x hxC).toChart.source :=
        (hAsub x hxC (interior_subset hyA')).1
      have hsy : s y = (φ x hxC).field y := by
        have := (hs y).2
        simp only [mem_iInter, mem_singleton_iff] at this
        exact this x hxC (interior_subset hyA')
      rw [hsy]
      exact (φ x hxC).mvfderiv_field_apply_lt_zero hysource fun hyx ↦
        hyreg (hyx ▸ mem_criticalPoints_iff_mfderiv_eq_zero.1 hxC.1)
  · intro x hxK hx
    have hxC : x ∈ C := ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hxK⟩
    let ψ := (φ x hxC).restr isOpen_interior (mem_interior_iff_mem_nhds.2 (hAn x hxC))
    refine ⟨ψ, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
    · rw [MorseChart.restr_source] at hy
      apply Or.inr
      refine mem_iUnion₂.2 ⟨x, hxC, ?_⟩
      rw [hA' x hxC]
      exact hy.2
    rw [MorseChart.restr_source] at hy
    have hyA : y ∈ A x hxC := interior_subset hy.2
    have hsy : s y = (φ x hxC).field y := by
      have := (hs y).2
      simp only [mem_iInter, mem_singleton_iff] at this
      exact this x hxC hyA
    simpa only [ψ, MorseChart.restr_field] using hsy

/-- A Morse function has a smooth pseudo-gradient on a neighbourhood of every compact set. The
field retains the exact linear normal form on smaller Morse charts around the critical points in
that set. -/
theorem IsMorse.exists_contMDiff_pseudoGradientOn_nhds [T2Space M] [SigmaCompactSpace M]
    {K : Set M}
    (hf : IsMorse 𝓘(ℝ, E) f) (hK : IsCompact K) :
    ∃ U ∈ 𝓝ˢ K, IsOpen U ∧
      ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
            (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ x ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 →
            mvfderiv 𝓘(ℝ, E) f x (X x) < 0) ∧
          ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
            ∃ φ : MorseChart E f x, φ.toChart.source ⊆ U ∧
              ∀ y ∈ φ.toChart.source, X y = φ.field y :=
  IsCompact.exists_contMDiff_pseudoGradientOn_nhds hK hf.contMDiff fun _ _ hx ↦
    hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx

/-- **Existence of adapted pseudo-gradients** (Audin--Damian, Proposition 2.2.3). Every Morse
function on a compact manifold has a pseudo-gradient field adapted to it. -/
theorem IsMorse.exists_isAdaptedPseudoGradient [CompactSpace M] [T2Space M]
    (hf : IsMorse 𝓘(ℝ, E) f) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x, IsAdaptedPseudoGradient f X := by
  obtain ⟨U, hU, -, X, hX, hdesc, hchart⟩ :=
    hf.exists_contMDiff_pseudoGradientOn_nhds isCompact_univ
  have hUuniv : U = univ := univ_subset_iff.1 (subset_of_mem_nhdsSet hU)
  refine ⟨X, hX, fun y hy ↦ hdesc y (hUuniv ▸ mem_univ y) hy, fun x hx ↦ ?_⟩
  obtain ⟨φ, -, hφ⟩ := hchart x (mem_univ x) hx
  exact ⟨φ, fun y hy ↦ hφ y hy ▸ φ.coord_mfderiv_field hy⟩

end Existence

end TauCeti
