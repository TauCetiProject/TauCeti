/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Constancy.CoordPlane
public import TauCeti.Analysis.Distribution.Rectifiable.Integral
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Integral constancy in a coordinate plane

For an injection `I : Fin k ↪ Fin n` and a point `x ∈ ℝⁿ`, the current of the coordinate plane
`TauCeti.coordPlaneCurrent I x U` integrates the coefficient `ω_y(e_{I 0}, …, e_{I (k-1)})` over
the plane `P = x + span (e_{I j})`. Since `TauCeti.coordPlaneMap I x` is an isometry, the
Euclidean Hausdorff measure `μHE[k]` restricted to `P` is the image of Lebesgue measure on `ℝᵏ`, so
the plane current is the frame current of `P` with multiplicity one and the constant frame
`e_I = (e_{I 0}, …, e_{I (k-1)})` (`TauCeti.coordPlaneCurrent_eq_frameCurrent`).

The constancy theorem for currents in a plane
(`TauCeti.existsUnique_eq_smul_coordPlaneCurrent_of_comp_extDerivCLM_eq_zero`) says that a current
`T` of locally finite mass on `U`, supported in `P`, with `∂T = 0` in `U`, is `c • [[P ∩ U]]` for
a unique real `c`, when the part of the plane in `U` is connected. If `T` is moreover
integer-rectifiable, in particular locally integral, then `c` is an integer
(`Distribution.IsIntegerRectifiable.exists_eq_zsmul_coordPlaneCurrent`).

Write `T = ∫ θ ξ dμHE[k]` with integer multiplicity `θ` and orientation `ξ = τ₁ ∧ ⋯ ∧ τₖ` for
orthonormal frames `τ`. The `k`-vector field `D = θ ξ − c 1_P e_I` integrates to zero against
every test field of `k`-vectors, so by the fundamental lemma for vector fields
`TauCeti.ae_eq_zero_of_forall_integral_inner_eq_zero`, which holds for every measure, `D = 0` for
`μHE[k]`-almost every point of `U`. The plane meets `U` in a set of
positive `μHE[k]` measure, so at some point `y ∈ P ∩ U` we have `θ(y) ξ(y) = c e_I`, and taking
norms gives `|c| = |θ(y)|`.

## Main declarations

* `TauCeti.coordPlaneCurrent_apply_eq_setIntegral`: the plane current integrates the coefficient
  of a form over the plane against `μHE[k]`.
* `TauCeti.coordPlaneCurrent_eq_frameCurrent`: the plane current is the frame current of the plane
  with multiplicity one.
* `Distribution.IsIntegerRectifiable.exists_eq_zsmul_coordPlaneCurrent`,
  `Distribution.IsLocallyIntegral.exists_eq_zsmul_coordPlaneCurrent`: integral constancy in a
  coordinate plane.

## References

* H. Federer, *Geometric Measure Theory*, 4.1.31.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory exteriorPower
open scoped Distributions ENNReal RealInnerProductSpace

namespace TauCeti

variable {k n : ℕ}

/-- The current of a coordinate plane integrates the coefficient of a test form on
`e_{I 0}, …, e_{I (k-1)}` over the plane, against the Euclidean Hausdorff measure `μHE[k]`. -/
theorem coordPlaneCurrent_apply_eq_setIntegral (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ω : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) :
    coordPlaneCurrent I x U ω =
      ∫ y in range (coordPlaneMap I x), ω y (fun j ↦ EuclideanSpace.single (I j) 1) ∂μHE[k] := by
  rw [coordPlaneCurrent_apply, ← (isometry_coordPlaneMap I x).map_euclideanHausdorffMeasure,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    (isometry_coordPlaneMap I x).isClosedEmbedding.measurableEmbedding.integral_map]

/-- The restriction of `μHE[k]` to a coordinate `k`-plane is locally finite. -/
instance isLocallyFiniteMeasure_euclideanHausdorffMeasure_restrict_range_coordPlaneMap
    (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    IsLocallyFiniteMeasure ((μHE[k] : Measure (EuclideanSpace ℝ (Fin n))).restrict
      (range (coordPlaneMap I x))) := by
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap
    (volume : Measure (EuclideanSpace ℝ (Fin k)))
    (isometry_coordPlaneMap I x).isClosedEmbedding.isProperMap
  rw [← (isometry_coordPlaneMap I x).map_euclideanHausdorffMeasure,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  infer_instance

/-- The indicator function of a coordinate `k`-plane is locally integrable for `μHE[k]`. -/
theorem locallyIntegrable_indicator_range_coordPlaneMap (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    LocallyIntegrable ((range (coordPlaneMap I x)).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ))
      μHE[k] := by
  have hP := (isometry_coordPlaneMap I x).isClosedEmbedding.isClosed_range.measurableSet
  intro y
  obtain ⟨t, ht, hi⟩ := (locallyIntegrable_const (1 : ℝ) :
    LocallyIntegrable _ ((μHE[k] : Measure (EuclideanSpace ℝ (Fin n))).restrict
      (range (coordPlaneMap I x)))) y
  refine ⟨t, ht, ?_⟩
  rw [IntegrableOn, integrable_indicator_iff hP, IntegrableOn, Measure.restrict_comm hP]
  exact hi

/-- The current of a coordinate plane is the frame current of the plane with multiplicity one and
the constant frame `e_{I 0}, …, e_{I (k-1)}`. -/
theorem coordPlaneCurrent_eq_frameCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    coordPlaneCurrent I x U = Distribution.frameCurrent ((range (coordPlaneMap I x)).indicator 1)
      fun _ j ↦ EuclideanSpace.single (I j) 1 := by
  ext ω
  rw [coordPlaneCurrent_apply_eq_setIntegral, Distribution.frameCurrent_apply
    (τ := fun _ j ↦ EuclideanSpace.single (I j) 1)
    ((locallyIntegrable_indicator_range_coordPlaneMap I x).locallyIntegrableOn _) measurable_const
    fun _ _ ↦ EuclideanSpace.orthonormal_single.comp _ I.injective, ← integral_indicator
    (isometry_coordPlaneMap I x).isClosedEmbedding.isClosed_range.measurableSet]
  congr 1
  funext y
  by_cases hy : y ∈ range (coordPlaneMap I x) <;> simp [hy]

/-- A property that holds `μHE[k]`-almost everywhere on an open set `U` holds at some point of a
coordinate `k`-plane meeting `U`, since the plane meets `U` in a set of positive measure. -/
private theorem exists_mem_range_coordPlaneMap_of_ae_restrict {I : Fin k ↪ Fin n}
    {x : EuclideanSpace ℝ (Fin n)} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (hU : (coordPlaneMap I x ⁻¹' U).Nonempty) {p : EuclideanSpace ℝ (Fin n) → Prop}
    (h : ∀ᵐ y ∂(μHE[k] : Measure (EuclideanSpace ℝ (Fin n))).restrict U, p y) :
    ∃ y ∈ range (coordPlaneMap I x), p y := by
  have : (ae ((μHE[k] : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((U : Set (EuclideanSpace ℝ (Fin n))) ∩ range (coordPlaneMap I x)))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero,
      ← (isometry_coordPlaneMap I x).euclideanHausdorffMeasure_preimage,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ((U.isOpen.preimage (coordPlaneMap I x).continuous).measure_pos volume hU).ne'
  have hae : ∀ᵐ y ∂(μHE[k] : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((U : Set (EuclideanSpace ℝ (Fin n))) ∩ range (coordPlaneMap I x)),
      y ∈ range (coordPlaneMap I x) ∧ p y := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left h,
      ae_restrict_mem (U.isOpen.measurableSet.inter
        (isometry_coordPlaneMap I x).isClosedEmbedding.isClosed_range.measurableSet)]
      with y hy hyP
    exact ⟨hyP.2, hy⟩
  exact hae.exists

end TauCeti

namespace Distribution

open TauCeti

variable {k n : ℕ} {I : Fin (k + 1) ↪ Fin n} {x : EuclideanSpace ℝ (Fin n)}
  {U : Opens (EuclideanSpace ℝ (Fin n))}

/-- The test `k`-form `ω_y = ⟪φ y, ·⟫` of a test field `φ` of `k`-vectors. -/
private def vectorForm (φ : 𝓓(U, ⋀[ℝ]^(k + 1) (EuclideanSpace ℝ (Fin n)))) :
    𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
  postcompCLM (LinearMap.toContinuousLinearMap
    (alternatingFormEquiv (EuclideanSpace ℝ (Fin n)) (k + 1)).toLinearMap) φ

private theorem vectorForm_apply (φ : 𝓓(U, ⋀[ℝ]^(k + 1) (EuclideanSpace ℝ (Fin n))))
    (y : EuclideanSpace ℝ (Fin n)) (v : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) :
    vectorForm φ y v = ⟪φ y, ιMulti ℝ (k + 1) v⟫ := by
  simp [vectorForm, postcompCLM_apply]

/-- If `m (v₀ ∧ ⋯ ∧ vₖ) = c (e₀ ∧ ⋯ ∧ eₖ)` for an integer `m`, an orthonormal family `e`, and a
family `v` that is orthonormal unless `m = 0`, then taking norms gives `|c| = |m|`, so `c` is an
integer. -/
private theorem exists_int_eq_of_intCast_smul_ιMulti_eq_smul {m : ℤ}
    {v e : Fin (k + 1) → EuclideanSpace ℝ (Fin n)} (hv : m ≠ 0 → Orthonormal ℝ v)
    (he : Orthonormal ℝ e) {c : ℝ} (h : (m : ℝ) • ιMulti ℝ (k + 1) v = c • ιMulti ℝ (k + 1) e) :
    ∃ m : ℤ, c = m := by
  have hn := congrArg norm h
  rw [norm_smul, norm_smul, he.norm_ιMulti, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at hn
  by_cases hm : m = 0
  · exact ⟨0, by simpa [hm, eq_comm] using hn⟩
  · rw [(hv hm).norm_ιMulti, mul_one] at hn
    rcases abs_eq_abs.1 hn with h' | h'
    · exact ⟨m, h'.symm⟩
    · exact ⟨-m, by push_cast; linarith⟩

/-- If the frame current of an integer multiplicity is a real multiple `c` of the current of a
coordinate plane meeting `U`, then `c` is an integer. -/
private theorem exists_int_eq_of_frameCurrent_eq_smul_coordPlaneCurrent
    (hU : (coordPlaneMap I x ⁻¹' U).Nonempty) {θ : EuclideanSpace ℝ (Fin n) → ℤ}
    {τ : EuclideanSpace ℝ (Fin n) → Fin (k + 1) → EuclideanSpace ℝ (Fin n)} (hτ : Measurable τ)
    (hθ : LocallyIntegrableOn (fun y ↦ (θ y : ℝ)) U μHE[k + 1])
    (hτo : ∀ y, θ y ≠ 0 → Orthonormal ℝ (τ y)) {c : ℝ}
    (h : (frameCurrent (fun y ↦ (θ y : ℝ)) τ :
        𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      c • coordPlaneCurrent I x U) :
    ∃ m : ℤ, c = m := by
  set P := range (coordPlaneMap I x)
  set e : Fin (k + 1) → EuclideanSpace ℝ (Fin n) := fun j ↦ EuclideanSpace.single (I j) 1
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp _ I.injective
  have hτo' : ∀ y, (θ y : ℝ) ≠ 0 → Orthonormal ℝ (τ y) := fun y hy ↦ hτo y (by exact_mod_cast hy)
  have hP : LocallyIntegrableOn (P.indicator 1) U μHE[k + 1] :=
    (locallyIntegrable_indicator_range_coordPlaneMap I x).locallyIntegrableOn _
  -- The `k`-vector field `D = θ ξ - c 1_P e_I`.
  set D : EuclideanSpace ℝ (Fin n) → ⋀[ℝ]^(k + 1) (EuclideanSpace ℝ (Fin n)) := fun y ↦
    frameDensity (fun y ↦ (θ y : ℝ)) τ y - c • frameDensity (P.indicator 1) (fun _ ↦ e) y
  have hD : LocallyIntegrableOn D U μHE[k + 1] :=
    (locallyIntegrableOn_frameDensity hθ hτ hτo').sub
      ((locallyIntegrableOn_frameDensity hP measurable_const fun _ _ ↦ he).smul c)
  -- `D` integrates to zero against every test field of `k`-vectors.
  have hzero (φ : 𝓓(U, ⋀[ℝ]^(k + 1) (EuclideanSpace ℝ (Fin n)))) :
      ∫ y, ⟪φ y, D y⟫ ∂μHE[k + 1] = 0 := by
    have h1 := DFunLike.congr_fun h (vectorForm φ)
    rw [smul_apply, coordPlaneCurrent_eq_frameCurrent, smul_eq_mul,
      frameCurrent_apply hθ hτ hτo', frameCurrent_apply hP measurable_const fun _ _ ↦ he] at h1
    calc ∫ y, ⟪φ y, D y⟫ ∂μHE[k + 1]
        = ∫ y, ((θ y : ℝ) * vectorForm φ y (τ y) -
            c * (P.indicator 1 y * vectorForm φ y e)) ∂μHE[k + 1] := by
          congr 1
          funext y
          simp only [D, frameDensity_apply, vectorForm_apply, inner_sub_right,
            real_inner_smul_right (F := ⋀[ℝ]^(k + 1) (EuclideanSpace ℝ (Fin n)))]
      _ = 0 := by
          rw [integral_sub (integrable_frameCurrent_integrand hθ hτ hτo' _)
            ((integrable_frameCurrent_integrand hP measurable_const (fun _ _ ↦ he) _).const_mul c),
            integral_const_mul, h1, sub_self]
  -- Hence `D = 0` almost everywhere on `U`.
  have hDU : ∀ᵐ y ∂(μHE[k + 1] : Measure (EuclideanSpace ℝ (Fin n))).restrict U, D y = 0 := by
    rw [ae_restrict_iff_subtype U.isOpen.measurableSet]
    refine TauCeti.ae_eq_zero_of_forall_integral_inner_eq_zero
      ((locallyIntegrable_comap U.isOpen.measurableSet).2 hD) fun φ ↦ ?_
    refine (integral_subtype_comap U.isOpen.measurableSet fun y ↦ ⟪φ y, D y⟫).trans
      ((setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_).trans (hzero φ))
    rw [image_eq_zero_of_notMem_tsupport fun hmem ↦ hy (φ.tsupport_subset hmem), inner_zero_left]
  obtain ⟨y, hyP, hy⟩ := exists_mem_range_coordPlaneMap_of_ae_restrict hU hDU
  -- At such a point `θ(y) ξ(y) = c e_I`.
  refine exists_int_eq_of_intCast_smul_ιMulti_eq_smul (hτo y) he ?_
  simpa [D, sub_eq_zero, frameDensity_apply, indicator_of_mem (show y ∈ P from hyP)] using hy

/-- **Integral constancy in a coordinate plane.** An integer-rectifiable `(k + 1)`-current `T` on
`U`, supported in `U` in a coordinate plane whose part in `U` is connected, with `∂T = 0` in `U`,
is an integer multiple of the current of the plane. -/
theorem IsIntegerRectifiable.exists_eq_zsmul_coordPlaneCurrent
    (hU : IsConnected (coordPlaneMap I x ⁻¹' U))
    {T : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : IsIntegerRectifiable T)
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (hb : T ∘L extDerivCLM = 0) :
    ∃ m : ℤ, T = m • coordPlaneCurrent I x U := by
  obtain ⟨c, hc, -⟩ := existsUnique_eq_smul_coordPlaneCurrent_of_comp_extDerivCLM_eq_zero hU
    hT.hasLocallyFiniteMass hTI hb
  obtain ⟨θ, τ, -, hτ, -, hθ, hτo, -, rfl⟩ := isIntegerRectifiable_iff.1 hT
  obtain ⟨m, rfl⟩ :=
    exists_int_eq_of_frameCurrent_eq_smul_coordPlaneCurrent hU.nonempty hτ hθ hτo hc
  exact ⟨m, hc.trans (Int.cast_smul_eq_zsmul ℝ m (coordPlaneCurrent I x U))⟩

/-- **Integral constancy for locally integral currents in a coordinate plane.** A locally
integral `(k + 1)`-current `T` on `U`, supported in `U` in a coordinate plane whose part in `U` is
connected, with `∂T = 0` in `U`, is an integer multiple of the current of the plane. -/
theorem IsLocallyIntegral.exists_eq_zsmul_coordPlaneCurrent
    (hU : IsConnected (coordPlaneMap I x ⁻¹' U))
    {T : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : IsLocallyIntegral T)
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (hb : T ∘L extDerivCLM = 0) :
    ∃ m : ℤ, T = m • coordPlaneCurrent I x U :=
  hT.isIntegerRectifiable.exists_eq_zsmul_coordPlaneCurrent hU hTI hb

end Distribution
