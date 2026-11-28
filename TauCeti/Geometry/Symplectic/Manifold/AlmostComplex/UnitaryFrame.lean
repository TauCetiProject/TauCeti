/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Unitarization
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Analysis.Matrix.GeneralLinearGroup.Connected
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Topology.UnitInterval.Contractible

/-!
# Unitary trivializations of the tangent bundle along maps from contractible spaces

Let `σ` be a smooth two-form on a manifold `M` modelled on a finite-dimensional space `E`, and `J`
a smooth almost complex structure compatible with `σ`, so that `σ(·, J ·)` is a Riemannian metric
and `(TM, J)` is a complex vector bundle. Let `G` be a complex inner product space with
`dim_ℝ E = 2 dim_ℂ G`, such as `ℂⁿ`. Along a continuous map `f : Y → M` from a contractible
paracompact R₁ space `Y`, for instance a disc or the domain of a cap of a loop, this file
constructs a **unitary frame** of `TM`
(`TauCeti.SmoothTwoForm.Compatible.exists_continuous_unitary_frame`): real-linear isomorphisms
`φ y : G ≃ T_(f y) M`, continuous into the tangent bundle, with

* `φ y (i v) = J (φ y v)`: each `φ y` is complex linear;
* `σ(φ y v, J φ y w) = Re ⟪v, w⟫`: each `φ y` is an isometry for the metric of `J`;
* `σ(φ y v, φ y w) = Im ⟪v, w⟫`: each `φ y` carries the standard symplectic form of `G` to `σ`.

So `f^* TM` has a symplectic trivialization, compatible with `J`. In Hamiltonian Floer theory this
is the trivialization of the tangent bundle over a cap of a contractible orbit in which the
linearized flow along the orbit becomes a path of symplectic matrices, the path whose
Conley–Zehnder index grades the capped orbit. Any two unitary frames along the same map differ by
a family of unitary automorphisms of `G`
(`TauCeti.SymplecticForm.inner_symm_apply_symm_apply_of_unitary`).

More generally every frame of the complex vector bundle `(TM, J)` along a continuous map from any
space is normalized fibrewise to a unitary frame, which only depends on the frame at each point
(`TauCeti.SmoothTwoForm.Compatible.exists_continuous_unitary_frame_of_frame`). Along a loop this
gives a unitary frame that closes up
(`TauCeti.SmoothTwoForm.Compatible.exists_continuous_unitary_frame_loop`): a frame of `(TM, J)`
along the loop, corrected by a path of complex automorphisms joining its two ends, normalized
fibrewise. This is a periodic unitary trivialization along a reference loop, in which the
Conley–Zehnder indices of the orbits graded through cylinders to that loop are read.

The construction starts from a frame of the complex vector bundle `(TM, J)` along `f`
(`TauCeti.ContMDiffAlmostComplexStructure.exists_continuous_frame`), which exists because `Y` is
contractible, and normalizes it
fibrewise by the unitarization of `TauCeti.SymplecticForm.unitarization`: the metric change
transport of the metric it pulls back to `G`. That metric depends continuously on `y`, since `σ`
evaluated on continuous families of tangent vectors is continuous
(`TauCeti.IsSmoothForm.continuous_apply`), and the transport depends continuously on the metric
(`ContinuousLinearMap.continuousOn_metricChangeTransport`).

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (symplectic vector bundles and their unitary trivializations).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (trivializations over caps and the Conley–Zehnder grading).
-/

public section

noncomputable section

open Bundle Filter Module Topology
open scoped ContDiff Manifold InnerProductSpace

-- The real inner product `Re ⟪·, ·⟫` of the model fibre, for which the frames are normalized.
attribute [local instance] InnerProductSpace.complexToReal

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
  {Y : Type*} [TopologicalSpace Y] {f : Y → M}

omit [FiniteDimensional ℝ E] in
/-- The unitarization of a frame of the tangent space at a point only depends on the point and on
the frame there. -/
private theorem unitarization_apply_congr (hJ : σ.Compatible J) {a b : M} (hab : a = b)
    {L : G ≃L[ℝ] TangentSpace I a} {L' : G ≃L[ℝ] TangentSpace I b} (hL : ∀ v, L v = L' v)
    (v : G) :
    (hJ.isNondegenerate.symplecticFormAt a).unitarization (J.almostComplexStructureAt a)
        (L : G →ₗ[ℝ] TangentSpace I a) v =
      (hJ.isNondegenerate.symplecticFormAt b).unitarization (J.almostComplexStructureAt b)
        (L' : G →ₗ[ℝ] TangentSpace I b) v := by
  subst hab
  obtain rfl : L = L' := ContinuousLinearEquiv.ext (funext hL)
  rfl

omit [FiniteDimensional ℝ E] in
/-- **The unitarization of a complex frame.** Let `σ` be a smooth two-form on `M` with a
compatible smooth almost complex structure `J`, and `G` a complex inner product space of half the
real dimension of `M`. Along a continuous map `f : Y → M`, every frame `φ₀` of the complex vector
bundle `(TM, J)`, continuous into the tangent bundle and complex linear, is normalized fibrewise
to real-linear isomorphisms `φ y : G ≃ T_(f y) M`, continuous into the tangent bundle, which are
complex linear and carry the Hermitian inner product of `G` to the one of `(σ, J)`: the metric
`σ(·, J ·)` restricts to `Re ⟪·, ·⟫` and `σ` to the standard symplectic form `Im ⟪·, ·⟫`. Each
`φ y` only depends on the point `f y` and on `φ₀ y`: wherever `f` and `φ₀` take the same values,
so does `φ`. -/
theorem Compatible.exists_continuous_unitary_frame_of_frame (hJ : σ.Compatible J)
    (hf : Continuous f) {φ₀ : ∀ y, G ≃L[ℝ] TangentSpace I (f y)}
    (hφ₀ : Continuous fun q : Y × G ↦ (⟨f q.1, φ₀ q.1 q.2⟩ : TangentBundle I M))
    (hφ₀J : ∀ y v, φ₀ y (Complex.I • v) = J (f y) (φ₀ y v)) :
    ∃ φ : ∀ y, G ≃L[ℝ] TangentSpace I (f y),
      Continuous (fun q : Y × G ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ y v, φ y (Complex.I • v) = J (f y) (φ y v)) ∧
      (∀ y v w, σ.eval₂ (f y) (φ y v) (J (f y) (φ y w)) = (inner ℂ v w).re) ∧
      (∀ y v w, σ.eval₂ (f y) (φ y v) (φ y w) = (inner ℂ v w).im) ∧
      ∀ y y', f y = f y' → (∀ v, φ₀ y v = φ₀ y' v) → ∀ v, φ y v = φ y' v := by
  have hφ₀J' (y : Y) (v : G) : (φ₀ y : G →ₗ[ℝ] TangentSpace I (f y)) (Complex.I • v) =
      J.almostComplexStructureAt (f y) (φ₀ y v) := by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact hφ₀J y v
  -- Normalize `φ₀ y` by the transport `T y` of the metric `k y` it pulls back to `G`.
  have hJ' (y : Y) := hJ.compatibleAt (f y)
  let k : Y → G →L[ℝ] G →L[ℝ] ℝ := fun y ↦
    (hJ.isNondegenerate.symplecticFormAt (f y)).frameMetric (J.almostComplexStructureAt (f y))
      (φ₀ y : G →ₗ[ℝ] TangentSpace I (f y))
  have hk (y : Y) := (hJ' y).isStrictlyPositive_frameMetric (φ₀ y).injective
  -- The metrics `k y`, hence their transports, depend continuously on `y`.
  have hkc : Continuous k := by
    refine continuous_clm_apply.2 fun v ↦ continuous_clm_apply.2 fun w ↦ ?_
    have hσ : IsSmoothForm I 0 σ.val := σ.isSmoothForm.of_le (by simp)
    refine (hσ.continuous_apply (v := fun y ↦ ![φ₀ y v, φ₀ y (Complex.I • w)]) hf fun j ↦ ?_).congr
      fun y ↦ ?_
    · fin_cases j
      exacts [hφ₀.comp (Continuous.prodMk_left v), hφ₀.comp (Continuous.prodMk_left _)]
    · simp [k, hφ₀J, SmoothBundleForm.eval₂_apply]
  have hTc : Continuous fun y ↦ (k y).metricChangeTransport :=
    ContinuousLinearMap.continuousOn_metricChangeTransport.comp_continuous hkc hk
  -- Each normalized frame is the unitarization of `φ₀ y`.
  have hφ (y : Y) (v : G) : ((k y).metricChangeEquiv (hk y)).trans (φ₀ y) v =
      (hJ.isNondegenerate.symplecticFormAt (f y)).unitarization (J.almostComplexStructureAt (f y))
        (φ₀ y : G →ₗ[ℝ] TangentSpace I (f y)) v := by
    simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.metricChangeEquiv_apply,
      SymplecticForm.unitarization_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, k]
  refine ⟨fun y ↦ ((k y).metricChangeEquiv (hk y)).trans (φ₀ y), ?_, fun y v ↦ ?_,
    fun y v w ↦ ?_, fun y v w ↦ ?_, fun y y' hy hφy v ↦ ?_⟩
  · exact (hφ₀.comp (continuous_fst.prodMk ((hTc.comp continuous_fst).clm_apply
      continuous_snd))).congr fun q ↦ by
        simp only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
          ContinuousLinearMap.metricChangeEquiv_apply]
  · rw [hφ, hφ, (hJ' y).unitarization_I_smul (φ₀ y).injective (hφ₀J' y),
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  · rw [hφ, hφ, ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
      ← IsNondegenerate.symplecticFormAt_apply hJ.isNondegenerate]
    exact (hJ' y).apply_unitarization_apply_unitarization (φ₀ y).injective v w
  · rw [hφ, hφ, ← IsNondegenerate.symplecticFormAt_apply hJ.isNondegenerate]
    exact (hJ' y).apply_unitarization_unitarization (φ₀ y).injective (hφ₀J' y) v w
  · rw [hφ, hφ]
    exact unitarization_apply_congr hJ hy hφy v

/-- **Unitary trivializations along maps from contractible spaces.** Let `σ` be a smooth two-form
on `M` with a compatible smooth almost complex structure `J`, and `G` a complex inner product space
of half the real dimension of `M`. Along a continuous map `f` from a contractible paracompact R₁
space, there are real-linear isomorphisms `φ y : G ≃ T_(f y) M`, continuous into the tangent bundle,
which are complex linear and carry the Hermitian inner product of `G` to the one of `(σ, J)`: the
metric `σ(·, J ·)` restricts to `Re ⟪·, ·⟫` and `σ` to the standard symplectic form `Im ⟪·, ·⟫`. -/
theorem Compatible.exists_continuous_unitary_frame [Fact (finrank ℝ E = 2 * finrank ℂ G)]
    [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y] (hJ : σ.Compatible J)
    (hf : Continuous f) :
    ∃ φ : ∀ y, G ≃L[ℝ] TangentSpace I (f y),
      Continuous (fun q : Y × G ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ y v, φ y (Complex.I • v) = J (f y) (φ y v)) ∧
      (∀ y v w, σ.eval₂ (f y) (φ y v) (J (f y) (φ y w)) = (inner ℂ v w).re) ∧
      ∀ y v w, σ.eval₂ (f y) (φ y v) (φ y w) = (inner ℂ v w).im := by
  obtain ⟨φ₀, hφ₀, hφ₀J⟩ := (J.toContMDiff 0).exists_continuous_frame (G := G) hf
  obtain ⟨φ, hφ, hφJ, hφg, hφσ, -⟩ := hJ.exists_continuous_unitary_frame_of_frame hf hφ₀
    fun y v ↦ (hφ₀J y v).trans (J.toContMDiff_apply 0 (f y) _)
  exact ⟨φ, hφ, hφJ, hφg, hφσ⟩

/-- **Periodic unitary frames along loops.** Let `σ` be a smooth two-form on `M` with a compatible
smooth almost complex structure `J`, and `G` a complex inner product space of half the real
dimension of `M`. Along every continuous loop `f : [0, 1] → M`, `f 0 = f 1`, there is a unitary
frame of the tangent bundle, as in
`TauCeti.SmoothTwoForm.Compatible.exists_continuous_unitary_frame`, that takes the same value at
the two ends of the loop. It is the unitarization of a frame of the complex vector bundle `(TM, J)`
along the loop, corrected at its end by a path of complex automorphisms of `G` that closes it
up. -/
theorem Compatible.exists_continuous_unitary_frame_loop [Fact (finrank ℝ E = 2 * finrank ℂ G)]
    (hJ : σ.Compatible J) {f : unitInterval → M} (hf : Continuous f) (hf₀₁ : f 0 = f 1) :
    ∃ φ : ∀ t, G ≃L[ℝ] TangentSpace I (f t),
      Continuous (fun q : unitInterval × G ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ t v, φ t (Complex.I • v) = J (f t) (φ t v)) ∧
      (∀ t v w, σ.eval₂ (f t) (φ t v) (J (f t) (φ t w)) = (inner ℂ v w).re) ∧
      (∀ t v w, σ.eval₂ (f t) (φ t v) (φ t w) = (inner ℂ v w).im) ∧
      ∀ v, φ 0 v = φ 1 v := by
  obtain ⟨φc, hφc, hφcJ⟩ := (J.toContMDiff 0).exists_continuous_frame (G := G) hf
  replace hφcJ (t : unitInterval) (v : G) : φc t (Complex.I • v) = J (f t) (φc t v) :=
    (hφcJ t v).trans (J.toContMDiff_apply 0 (f t) _)
  -- The frame at the end of the loop, read over its start: the tangent spaces are both the model
  -- space, so this is the same family of maps.
  let ψ₁ : G ≃L[ℝ] TangentSpace I (f 0) := φc 1
  have hψ₁J (v : G) : ψ₁ (Complex.I • v) = J (f 0) (ψ₁ v) :=
    (hφcJ 1 v).trans (J.apply_congr hf₀₁.symm _)
  -- The defect `D = φc(1)⁻¹ φc(0)` is a complex automorphism, joined to the identity by a path `P`.
  let D : G ≃L[ℂ] G := ((φc 0).trans ψ₁.symm).complexOfMapISmul
    (SmoothAlmostComplexStructure.trans_symm_I_smul (hφcJ 0) hψ₁J)
  obtain ⟨P, hPc, hP₀, hP₁⟩ := ContinuousLinearEquiv.exists_continuous_path_refl D
  -- The frame `φc ∘ P` closes up along the loop.
  let φp : ∀ t, G ≃L[ℝ] TangentSpace I (f t) := fun t ↦ ((P t).restrictScalars ℝ).trans (φc t)
  have hPc' : Continuous fun t ↦ ((P t : G →L[ℂ] G).restrictScalars ℝ : G →L[ℝ] G) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ G G ℝ ℝ).continuous.comp hPc
  have hφp : Continuous fun q : unitInterval × G ↦ (⟨f q.1, φp q.1 q.2⟩ : TangentBundle I M) :=
    hφc.comp (continuous_fst.prodMk ((hPc'.comp continuous_fst).clm_apply continuous_snd))
  have hφpJ (t : unitInterval) (v : G) : φp t (Complex.I • v) = J (f t) (φp t v) := by
    simp only [φp, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.restrictScalars_apply,
      map_smul, hφcJ]
  have hφp₀₁ (v : G) : φp 0 v = φp 1 v := by
    simp only [φp, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.restrictScalars_apply,
      hP₀, hP₁, ContinuousLinearEquiv.refl_apply, D,
      ContinuousLinearEquiv.complexOfMapISmul_apply]
    exact (ψ₁.apply_symm_apply _).symm
  obtain ⟨φ, hφ, hφJ, hφg, hφσ, hφ₀₁⟩ := hJ.exists_continuous_unitary_frame_of_frame hf hφp hφpJ
  exact ⟨φ, hφ, hφJ, hφg, hφσ, hφ₀₁ 0 1 hf₀₁ hφp₀₁⟩

end TauCeti.SmoothTwoForm
