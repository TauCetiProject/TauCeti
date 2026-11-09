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
  rw [field, mfderiv_mpullback_apply
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) _ hy]
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

/-- The coordinate change of a Morse chart is continuous. -/
theorem continuous_coord : Continuous φ.coord :=
  φ.coordL.continuous.congr φ.coordL_apply

open Filter in
/-- The point with coordinates `w` tends to the critical point as `w` tends to `0`. -/
theorem tendsto_toChart_symm_coord_symm_nhds_zero :
    Tendsto (fun w ↦ φ.toChart.symm (φ.coord.symm w)) (𝓝 0) (𝓝 x) := by
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have h := (φ.toChart.continuousAt_symm (hrT 0 (by simpa using hr))).comp
    (φ.coordL.symm.continuous.continuousAt.congr (.of_forall φ.coordL_symm_apply))
  rwa [ContinuousAt, comp_apply, φ.toChart_symm_coord_symm_zero] at h

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
  rw [field, mvfderiv_mpullback_apply
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) φ.eqOn_quadratic _ hy]
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
      (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) φ.eqOn_quadratic hy,
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

section LocalField

variable {C : Set M} {φ : ∀ c : C, MorseChart E f c} {A : C → Set M} {D : Set M}

/-- Near a point of the neighbourhood `A c₀` of a critical point, the Morse field of `c₀` is a
local candidate for the pseudo-gradient: it decreases `f` at the regular points of `D`, and it
agrees with the Morse field of every `c` at the points of `A c`, because the sets `A c` lie in
pairwise disjoint sets `W c`. -/
private theorem exists_nhds_contMDiffOn_field_of_mem {W : C → Set M}
    (hCcrit : ∀ c : C, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0) (hW : ∀ c, IsOpen (W c))
    (hWdisj : ∀ c c' : C, c ≠ c' → Disjoint (W c) (W c'))
    (hAsub : ∀ c, A c ⊆ (φ c).toChart.source ∩ W c) (hDreg : D ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ)
    {c₀ : C} {y₀ : M} (hy₀ : y₀ ∈ A c₀) :
    ∃ V ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) V ∧
      ∀ y ∈ V, (y ∈ D → mvfderiv 𝓘(ℝ, E) f y (s y) < 0) ∧
        ∀ c, y ∈ A c → s y = (φ c).field y := by
  have hVo : IsOpen ((φ c₀).toChart.source ∩ W c₀) := (φ c₀).toChart.open_source.inter (hW c₀)
  refine ⟨_, hVo.mem_nhds (hAsub c₀ hy₀), (φ c₀).field,
    (φ c₀).contMDiffOn_field.mono inter_subset_left, fun y hy ↦ ⟨fun hyD ↦ ?_, fun c hyA ↦ ?_⟩⟩
  · have hycrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := by
      simpa only [mem_compl_iff, mem_criticalPoints_iff_mfderiv_eq_zero] using hDreg hyD
    exact (φ c₀).mvfderiv_field_apply_lt_zero hy.1 fun hyx ↦ hycrit (hyx ▸ hCcrit c₀)
  · obtain rfl : c₀ = c := by
      by_contra hne
      exact (hWdisj c₀ c hne).le_bot ⟨hy.2, (hAsub c hyA).2⟩
    rfl

/-- Near a point of the regular core `D` that is outside the neighbourhoods `A c`, a constant
field in a chart is a local candidate for the pseudo-gradient. -/
private theorem exists_nhds_contMDiffOn_field_of_mem_of_notMem_iUnion
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hAclosed : IsClosed (⋃ c, A c))
    (hDreg : D ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ) {y₀ : M} (hy₀D : y₀ ∈ D) (hy₀A : y₀ ∉ ⋃ c, A c) :
    ∃ V ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) V ∧
      ∀ y ∈ V, (y ∈ D → mvfderiv 𝓘(ℝ, E) f y (s y) < 0) ∧
        ∀ c, y ∈ A c → s y = (φ c).field y := by
  have hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0 := by
    simpa only [mem_compl_iff, mem_criticalPoints_iff_mfderiv_eq_zero] using hDreg hy₀D
  obtain ⟨v, V, hV, hVc, hVneg⟩ := exists_mem_nhds_mvfderiv_chartConstField_lt_zero hf hcrit
  refine ⟨_, Filter.inter_mem (hAclosed.isOpen_compl.mem_nhds hy₀A) hV, chartConstField E y₀ v,
    (contMDiffOn_chartConstField y₀ v).mono fun y hy ↦ hVc hy.2,
    fun y hy ↦ ⟨fun _ ↦ hVneg y hy.2, fun c hyA ↦ (hy.1 (mem_iUnion.2 ⟨c, hyA⟩)).elim⟩⟩

omit [FiniteDimensional ℝ E] in
/-- Away from the regular core `D` and the neighbourhoods `A c`, the zero field is a local
candidate for the pseudo-gradient. -/
private theorem exists_nhds_contMDiffOn_field_of_notMem_of_notMem_iUnion
    (hDc : IsClosed D) (hAclosed : IsClosed (⋃ c, A c))
    {y₀ : M} (hy₀D : y₀ ∉ D) (hy₀A : y₀ ∉ ⋃ c, A c) :
    ∃ V ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) V ∧
      ∀ y ∈ V, (y ∈ D → mvfderiv 𝓘(ℝ, E) f y (s y) < 0) ∧
        ∀ c, y ∈ A c → s y = (φ c).field y :=
  ⟨_, Filter.inter_mem (hDc.isOpen_compl.mem_nhds hy₀D) (hAclosed.isOpen_compl.mem_nhds hy₀A),
    fun _ ↦ 0, (Bundle.contMDiff_zeroSection ℝ
      (TangentSpace 𝓘(ℝ, E) : M → Type _)).contMDiffOn,
    fun _ hy ↦ ⟨fun hyD ↦ (hy.1 hyD).elim, fun c hyA ↦ (hy.2 (mem_iUnion.2 ⟨c, hyA⟩)).elim⟩⟩

/-- **A pseudo-gradient on a regular core, equal to the Morse fields near the critical points.**
Let `D` be a closed set of regular points and `A c` closed neighbourhoods of finitely many critical
points `c`, inside Morse charts and pairwise disjoint open sets `W c`. Then there is a smooth vector
field along which `f` decreases on `D` and which equals the Morse field of `c` on `A c`. -/
private theorem exists_contMDiff_field_lt_zero_and_eq_field [T2Space M] [SigmaCompactSpace M]
    {W : C → Set M} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hCcrit : ∀ c : C, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0) (hW : ∀ c, IsOpen (W c))
    (hWdisj : ∀ c c' : C, c ≠ c' → Disjoint (W c) (W c'))
    (hAsub : ∀ c, A c ⊆ (φ c).toChart.source ∩ W c) (hDc : IsClosed D)
    (hDreg : D ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ) (hAclosed : IsClosed (⋃ c, A c)) :
    ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ y, (y ∈ D → mvfderiv 𝓘(ℝ, E) f y (s y) < 0) ∧
        ∀ c, y ∈ A c → s y = (φ c).field y := by
  -- The fibrewise convex constraint: `df(v) < 0` on `D`, and equality with the Morse field on
  -- each `A c`.
  let t : (y : M) → Set (TangentSpace 𝓘(ℝ, E) y) := fun y ↦
    {v | y ∈ D → mvfderiv 𝓘(ℝ, E) f y v < 0} ∩
      {v | ∀ c, y ∈ A c → v = (φ c).field y}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    refine Convex.inter ?_ fun v hv w hw a b _ _ hab c hyA ↦ ?_
    · by_cases hy : y ∈ D
      · simp only [hy, true_implies]
        exact convex_halfSpace_lt (mvfderiv 𝓘(ℝ, E) f y).isLinear 0
      · simp [hy, convex_univ]
    · rw [hv c hyA, hw c hyA, ← add_smul, hab, one_smul]
  have hloc : ∀ y₀ : M, ∃ V ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) V ∧ ∀ y ∈ V, s y ∈ t y := by
    intro y₀
    by_cases hA : y₀ ∈ ⋃ c, A c
    · obtain ⟨c, hc⟩ := mem_iUnion.1 hA
      exact exists_nhds_contMDiffOn_field_of_mem hCcrit hW hWdisj hAsub hDreg hc
    · by_cases hy₀D : y₀ ∈ D
      · exact exists_nhds_contMDiffOn_field_of_mem_of_notMem_iUnion hf hAclosed hDreg hy₀D hA
      · exact exists_nhds_contMDiffOn_field_of_notMem_of_notMem_iUnion hDc hAclosed hy₀D hA
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) (TangentSpace 𝓘(ℝ, E)) t ht hloc
  exact ⟨s, s.contMDiff, hs⟩

/-- **The pseudo-gradient property on a neighbourhood of `K`.** Let `s` be a smooth field along
which `f` decreases on `D`, equal to the Morse field of `c` on the neighbourhood `A c` of `c`. If
`K` lies in the union of `D` and the interiors of the `A c`, and every critical point of `f` in `K`
is one of the `c`, then `s` is a pseudo-gradient on an open neighbourhood of `K`, equal to the
Morse field on a smaller Morse chart around each critical point in `K`. -/
private theorem exists_isOpen_pseudoGradientOn_of_field {K : Set M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hCcrit : ∀ c : C, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0)
    (hCK : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 → x ∈ C)
    (hAn : ∀ c : C, A c ∈ 𝓝 (c : M)) (hAsub : ∀ c, A c ⊆ (φ c).toChart.source)
    (hKU : K ⊆ D ∪ ⋃ c, interior (A c))
    {s : (y : M) → TangentSpace 𝓘(ℝ, E) y}
    (hsm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hs : ∀ y, (y ∈ D → mvfderiv 𝓘(ℝ, E) f y (s y) < 0) ∧
      ∀ c, y ∈ A c → s y = (φ c).field y) :
    ∃ U ∈ 𝓝ˢ K, IsOpen U ∧
      ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
            (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ x ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 →
            mvfderiv 𝓘(ℝ, E) f x (X x) < 0) ∧
          ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
            ∃ φ : MorseChart E f x, φ.toChart.source ⊆ U ∧
              ∀ y ∈ φ.toChart.source, X y = φ.field y := by
  -- By continuity of `df(s)`, descent on `D` extends to an open set `V`; together with the
  -- interiors of the chart neighbourhoods it gives the open neighbourhood `U` of `K`.
  have hdesc : Continuous (fun y ↦ mvfderiv 𝓘(ℝ, E) f y (s y)) :=
    ((hf.contMDiff_mvfderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp hsm).continuous
  have hVo : IsOpen ((fun y ↦ mvfderiv 𝓘(ℝ, E) f y (s y)) ⁻¹' Iio 0) := isOpen_Iio.preimage hdesc
  have hGo : IsOpen (⋃ c : C, interior (A c)) := isOpen_iUnion fun _ ↦ isOpen_interior
  have hUo := hVo.union hGo
  refine ⟨_, mem_nhdsSet_iff_forall.2 fun x hx ↦ hUo.mem_nhds ?_, hUo, s, hsm, ?_, ?_⟩
  · rcases hKU hx with hxD | hxG
    · exact Or.inl ((hs x).1 hxD)
    · exact Or.inr hxG
  · intro y hy hyreg
    rcases hy with hyV | hyG
    · exact hyV
    · obtain ⟨c, hyA⟩ := mem_iUnion.1 hyG
      rw [(hs y).2 c (interior_subset hyA)]
      exact (φ c).mvfderiv_field_apply_lt_zero (hAsub c (interior_subset hyA))
        fun hyx ↦ hyreg (hyx ▸ hCcrit c)
  · intro x hxK hx
    let c : C := ⟨x, hCK x hxK hx⟩
    refine ⟨(φ c).restr isOpen_interior (mem_interior_iff_mem_nhds.2 (hAn c)),
      fun y hy ↦ ?_, fun y hy ↦ ?_⟩ <;> rw [MorseChart.restr_source] at hy
    · exact Or.inr (mem_iUnion.2 ⟨c, hy.2⟩)
    · simpa only [MorseChart.restr_field] using (hs y).2 c (interior_subset hy.2)

end LocalField

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
  -- and pairwise disjoint closed neighbourhoods `A c` inside these charts.
  let C := criticalPoints 𝓘(ℝ, E) f ∩ K
  have hCcrit (c : C) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero.1 c.2.1
  have hC : C.Finite := by
    refine (hK.inter_left (isClosed_criticalPoints (hf.of_le (by simp)))).finite ?_
    rw [isDiscrete_iff_nhdsNE]
    rintro x ⟨hx, hxK⟩
    rw [inf_principal_eq_bot]
    filter_upwards [(hnd x hxK
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)).eventually_notMem_criticalPoints]
      with y hy using fun h ↦ hy h.1
  let φ : ∀ c : C, MorseChart E f c := fun c ↦
    ((hnd c c.2.2 (hCcrit c)).nonempty_morseChart
      (Eventually.of_forall fun _ ↦ hf.contMDiffAt)).some
  obtain ⟨W, hW, hWdisj⟩ := hC.t2_separation
  choose A hAn hAc hAsub using fun c : C ↦ exists_mem_nhds_isClosed_subset
    (Filter.inter_mem ((φ c).toChart.open_source.mem_nhds (φ c).mem_source)
      ((hW c).2.mem_nhds (hW c).1))
  have : Finite C := hC.to_subtype
  -- The regular core `R` of `K`, away from the interiors of these neighbourhoods, is compact.
  let R := K \ ⋃ c : C, interior (A c)
  have hRc : IsCompact R := hK.diff (isOpen_iUnion fun _ ↦ isOpen_interior)
  have hCK (x : M) (hxK : x ∈ K) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : x ∈ C :=
    ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hxK⟩
  have hRreg : R ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ := fun x hx hcrit ↦ hx.2 <|
    mem_iUnion.2 ⟨⟨x, hcrit, hx.1⟩, mem_interior_iff_mem_nhds.2 (hAn ⟨x, hcrit, hx.1⟩)⟩
  obtain ⟨s, hsm, hs⟩ := exists_contMDiff_field_lt_zero_and_eq_field hf hCcrit
    (fun c ↦ (hW c).2) (fun c c' h ↦ hWdisj c.2 c'.2 (Subtype.coe_injective.ne h)) hAsub
    hRc.isClosed hRreg (isClosed_iUnion_of_finite hAc)
  exact exists_isOpen_pseudoGradientOn_of_field hf hCcrit hCK hAn (fun c y hy ↦ (hAsub c hy).1)
    (fun x hxK ↦ by
      by_cases hx : x ∈ ⋃ c : C, interior (A c)
      · exact Or.inr hx
      · exact Or.inl ⟨hxK, hx⟩) hsm hs

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
