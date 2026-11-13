/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import TauCeti.Analysis.Distribution.Mass.Normal
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.Order.Fin.Tuple
import TauCeti.Analysis.Calculus.DifferentialForm.Box
import TauCeti.Data.Fin.Basic
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The oriented current of a coordinate box

For `a b : ℝᵖ` the coordinate box `[a, b] = ∏ᵢ [aᵢ, bᵢ]`, oriented by the standard basis
`e₀, …, e_{p-1}` of `ℝᵖ = EuclideanSpace ℝ (Fin p)`, defines the `p`-current

`[[a, b]] ω = ∫_{[a, b]} ω(x)(e₀, …, e_{p-1}) dx`

on test `p`-forms on any open set `Ω ⊆ ℝᵖ` (`TauCeti.boxCurrent`). The box is read in Euclidean
space through `toLp 2`, so that forms carry the Euclidean comass norm; it need not lie in `Ω`,
since test forms on `Ω` vanish off `Ω`. The current is supported in the box, and it is zero when
`a ≤ b` fails, since the box is then empty. Translates and dilates of the unit cube `[0, 1]ᵖ` are
boxes, so these are the oriented cubes of cubical grids.

For `i : Fin (p + 1)` and `t : ℝ`, the affine map `TauCeti.boxFaceMap i t : ℝᵖ → ℝᵖ⁺¹` inserts `t`
as the `i`-th coordinate. It is an injective affine map, hence a closed embedding, so the
pushforward of currents along it is defined by pulling test forms back
(`TestFunction.pullbackCLM`). It maps the box `[a ∘ i.succAbove, b ∘ i.succAbove]` onto the face
`xᵢ = t` of `[a, b]` when `t` is `aᵢ` or `bᵢ`. Stokes' theorem on the box
(`TauCeti.integral_extDeriv_toLp_Icc`) is then the **boundary formula** of the cubical boundary
operator: for `a ≤ b` in `ℝᵖ⁺¹`,

`∂ [[a, b]] = ∑ᵢ (-1)ⁱ ((Fᵢ^{bᵢ})_# [[a ∘ i.succAbove, b ∘ i.succAbove]] -`
`  (Fᵢ^{aᵢ})_# [[a ∘ i.succAbove, b ∘ i.succAbove]])`,

where `∂ T = T ∘ d` and `Fᵢ^t = boxFaceMap i t`. The mass satisfies `M([[a, b]]) ≤ vol([a, b])`,
so `[[a, b]]` is a normal current. In dimension zero `[[a, b]]` is the Dirac current at the point.

## Main declarations

* `TauCeti.boxFaceMap i t`: the affine map inserting `t` as the `i`-th coordinate.
* `TauCeti.boxCurrent a b Ω`: the oriented current `[[a, b]]` on test `p`-forms on `Ω`.
* `TauCeti.boxCurrent_apply`: `[[a, b]] ω = ∫_{[a, b]} ω(x)(e₀, …, e_{p-1}) dx`.
* `TauCeti.boxCurrent_eq_zero_of_not_le`: `[[a, b]] = 0` unless `a ≤ b`.
* `TauCeti.dsupport_boxCurrent_subset`: the support of `[[a, b]]` lies in the box.
* `TauCeti.boxCurrent_extDerivCLM`, `TauCeti.boxCurrent_comp_extDerivCLM`: the boundary formula.
* `TauCeti.mass_boxCurrent_le`: `M([[a, b]]) ≤ vol([a, b])`.
* `TauCeti.isNormal_boxCurrent`: `[[a, b]]` is a normal current.

The construction `boxCurrent` and its evaluation, support, restriction, mass and normality proofs
are adapted from `simplexCurrent`, `simplexCurrent_apply`, `dsupport_simplexCurrent_subset`,
`simplexCurrent_monoCLM`, `mass_simplexCurrent_le` and `isNormal_simplexCurrent` in
`TauCeti.Analysis.Distribution.TestFunction.SimplexCurrent`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (Cartesian products of currents and oriented
  intervals) and §4.2 (deformation of currents onto cubical grids).
* M. Spivak, *Calculus on Manifolds*, Chapter 4 (the boundary of the standard cube).
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction Distribution WithLp
open scoped Distributions ENNReal

namespace TauCeti

variable {p : ℕ} {n : ℕ∞}

section FaceMap

/-- The affine map `ℝᵖ → ℝᵖ⁺¹` inserting `t` as the `i`-th coordinate,
`y ↦ (y₀, …, y_{i-1}, t, yᵢ, …, y_{p-1})` (`TauCeti.boxFaceMap_apply`). For `t = aᵢ` or `t = bᵢ`
it maps the box `[a ∘ i.succAbove, b ∘ i.succAbove]` onto a face of the box `[a, b]`. -/
noncomputable def boxFaceMap (i : Fin (p + 1)) (t : ℝ) :
    EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (p + 1)) :=
  ContinuousLinearMap.toContinuousAffineMap
      (LinearIsometry.piLpExtendByZero 2 ℝ ℝ i.succAboveEmb).toContinuousLinearMap +
    ContinuousAffineMap.const ℝ _ (EuclideanSpace.single i t)

/-- `boxFaceMap i t` inserts `t` as the `i`-th coordinate. -/
@[simp]
theorem boxFaceMap_apply (i : Fin (p + 1)) (t : ℝ) (y : EuclideanSpace ℝ (Fin p)) :
    boxFaceMap i t y = toLp 2 (i.insertNth t (ofLp y)) := by
  ext j
  refine i.succAboveCases ?_ (fun k ↦ ?_) j
  · simp [boxFaceMap]
  · simp [boxFaceMap, Fin.succAbove_right_injective.extend_apply]

/-- The linear part of a face map inserts a zero coordinate. -/
@[simp]
theorem contLinear_boxFaceMap_apply (i : Fin (p + 1)) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin p)) :
    (boxFaceMap i t).contLinear y = toLp 2 (i.insertNth 0 (ofLp y)) := by
  ext j
  refine i.succAboveCases ?_ (fun k ↦ ?_) j
  · simp [boxFaceMap]
  · simp [boxFaceMap, Fin.succAbove_right_injective.extend_apply]

/-- The underlying affine map's linear part inserts a zero coordinate. -/
@[simp]
theorem linear_boxFaceMap_apply (i : Fin (p + 1)) (t : ℝ) (y : EuclideanSpace ℝ (Fin p)) :
    (boxFaceMap i t).linear y = toLp 2 (i.insertNth 0 (ofLp y)) := by
  rw [← ContinuousAffineMap.coe_contLinear, contLinear_boxFaceMap_apply]

/-- The linear part of `boxFaceMap i t` sends a vector on the `k`-th axis to the corresponding
vector on the `i.succAbove k`-th axis. -/
theorem contLinear_boxFaceMap_single (i : Fin (p + 1)) (t : ℝ) (k : Fin p) (r : ℝ) :
    (boxFaceMap i t).contLinear (EuclideanSpace.single k r) =
      EuclideanSpace.single (i.succAbove k) r := by
  simp [boxFaceMap]

/-- Inserting a coordinate preserves distances. -/
theorem isometry_boxFaceMap (i : Fin (p + 1)) (t : ℝ) : Isometry (boxFaceMap i t) := by
  have h : ⇑(boxFaceMap i t) =
      (· + EuclideanSpace.single i t) ∘ LinearIsometry.piLpExtendByZero 2 ℝ ℝ i.succAboveEmb := by
    ext1 y
    simp [boxFaceMap]
  rw [h]
  exact (isometry_add_right _).comp (LinearIsometry.piLpExtendByZero 2 ℝ ℝ i.succAboveEmb).isometry

/-- The linear part of a face map has operator norm at most one, including in dimension zero. -/
theorem norm_contLinear_boxFaceMap_le_one (i : Fin (p + 1)) (t : ℝ) :
    ‖(boxFaceMap i t).contLinear‖ ≤ 1 := by
  simpa [boxFaceMap] using
    (LinearIsometry.piLpExtendByZero 2 ℝ ℝ i.succAboveEmb).norm_toContinuousLinearMap_le

/-- Inserting a coordinate is injective. -/
theorem boxFaceMap_injective (i : Fin (p + 1)) (t : ℝ) : Function.Injective (boxFaceMap i t) :=
  (isometry_boxFaceMap i t).injective

/-- A face map is a closed embedding. -/
theorem isClosedEmbedding_boxFaceMap (i : Fin (p + 1)) (t : ℝ) :
    Topology.IsClosedEmbedding (boxFaceMap i t) :=
  ContinuousAffineMap.isClosedEmbedding_of_injective (boxFaceMap_injective i t)

/-- Inserting a coordinate between its endpoints maps the lower-dimensional box into the box. -/
theorem mapsTo_boxFaceMap (i : Fin (p + 1)) {a b : Fin (p + 1) → ℝ} {t : ℝ}
    (ht : t ∈ Icc (a i) (b i)) :
    MapsTo (boxFaceMap i t) (ofLp ⁻¹' Icc (a ∘ i.succAbove) (b ∘ i.succAbove))
      (ofLp ⁻¹' Icc a b) := by
  intro y hy
  rw [mem_preimage, boxFaceMap_apply, ofLp_toLp, Fin.insertNth_mem_Icc]
  exact ⟨ht, hy⟩

/-- Inserting two fixed coordinates commutes after adjusting their indices. -/
theorem boxFaceMap_comp_boxFaceMap (i : Fin (p + 2)) (j : Fin (p + 1)) (t u : ℝ) :
    (boxFaceMap i t).comp (boxFaceMap j u) =
      (boxFaceMap (i.succAbove j) u).comp (boxFaceMap (j.predAbove i) t) := by
  ext1 y
  simp only [ContinuousAffineMap.comp_apply, boxFaceMap_apply]
  rw [Fin.insertNth_insertNth]

/-- Preimages of compact sets under `boxFaceMap i t` are compact, so it is proper from all of
`ℝᵖ` and pulls test forms back to test forms. -/
theorem isCompact_inter_preimage_boxFaceMap (i : Fin (p + 1)) (t : ℝ)
    {K : Set (EuclideanSpace ℝ (Fin (p + 1)))} (hK : IsCompact K) :
    IsCompact (((⊤ : Opens (EuclideanSpace ℝ (Fin p))) : Set (EuclideanSpace ℝ (Fin p))) ∩
      boxFaceMap i t ⁻¹' K) := by
  simpa using (isClosedEmbedding_boxFaceMap i t).isCompact_preimage hK

end FaceMap

/-- The **oriented current of the coordinate box** `[[a, b]]`: the continuous linear functional
`ω ↦ ∫_{[a, b]} ω(x)(e₀, …, e_{p-1}) dx` on test `p`-forms on an open set `Ω ⊆ ℝᵖ`, where `eᵢ` is
the standard basis and the box `Icc a b` is read in Euclidean space through `toLp 2`
(`TauCeti.boxCurrent_apply`). -/
noncomputable def boxCurrent (a b : Fin p → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  integralAgainstBilinCLM
    (ContinuousLinearMap.mul ℝ ℝ ∘L
      ContinuousAlternatingMap.apply ℝ _ ℝ fun i ↦ EuclideanSpace.single i 1)
    (volume.restrict (ofLp ⁻¹' Icc a b)) fun _ ↦ (1 : ℝ)

/-- The current `[[a, b]]` integrates the coefficient of a test `p`-form on the standard basis
over the box. -/
theorem boxCurrent_apply (a b : Fin p → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin p)))
    (ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ)) :
    boxCurrent a b Ω ω = ∫ x in Icc a b, ω (toLp 2 x) fun i ↦ EuclideanSpace.single i 1 := by
  rw [boxCurrent,
    integralAgainstBilinCLM_eq_integral ((locallyIntegrable_const 1).locallyIntegrableOn _)]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousAlternatingMap.apply_apply, ContinuousLinearMap.mul_apply', mul_one]
  have he : MeasurableEmbedding (@ofLp 2 (Fin p → ℝ)) := by
    rw [← MeasurableEquiv.coe_toLp_symm]
    exact (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm.measurableEmbedding
  rw [← (PiLp.volume_preserving_ofLp (Fin p)).setIntegral_preimage_emb he]

/-- The box `[a, b]` is empty unless `a ≤ b`, and then `[[a, b]] = 0`. -/
@[simp]
theorem boxCurrent_eq_zero_of_not_le {a b : Fin p → ℝ} (h : ¬a ≤ b)
    (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    (boxCurrent a b Ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  ext ω
  simp [boxCurrent_apply, Icc_eq_empty h]

/-- A coordinate box with a nonpositive side length defines the zero current. -/
theorem boxCurrent_eq_zero_of_le {a b : Fin p → ℝ} (i : Fin p) (hi : b i ≤ a i)
    (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    (boxCurrent a b Ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  have hvol : volume (Icc a b) = 0 := by
    rw [Real.volume_Icc_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hi))
  ext ω
  rw [boxCurrent_apply, setIntegral_measure_zero _ hvol]
  rfl

/-- A box with identical endpoints in positive dimension defines the zero current. -/
@[simp]
theorem boxCurrent_self (a : Fin (p + 1) → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin (p + 1)))) :
    (boxCurrent a a Ω :
      𝓓^{n}(Ω, EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin (p + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 :=
  boxCurrent_eq_zero_of_le 0 le_rfl Ω

/-- **Dimension zero**: `[[a, b]]` is the Dirac current at the point of `ℝ⁰`. -/
@[simp]
theorem boxCurrent_apply_finZero (a b : Fin 0 → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin 0)))
    (ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin 0) [⋀^Fin 0]→L[ℝ] ℝ)) :
    boxCurrent a b Ω ω = ω 0 ![] := by
  have hs : Icc a b = univ := eq_univ_of_forall fun x ↦ by simp [Subsingleton.elim a x,
    Subsingleton.elim b x]
  rw [boxCurrent_apply, hs, Measure.restrict_univ, Measure.volume_pi_eq_dirac 0, integral_dirac]
  simp only [Subsingleton.elim (_ : Fin 0 → EuclideanSpace ℝ (Fin 0)) ![]]
  exact congrArg (fun x ↦ ω x ![]) (Subsingleton.elim _ _)

/-- The support of `[[a, b]]` lies in the box `[a, b]`. -/
theorem dsupport_boxCurrent_subset (a b : Fin p → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    dsupport (boxCurrent a b Ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) → ℝ) ⊆
      ofLp ⁻¹' Icc a b := by
  refine sInter_subset_of_mem ⟨fun ω hω ↦ ?_, isClosed_Icc.preimage (PiLp.continuous_ofLp _ _)⟩
  rw [boxCurrent_apply]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  simp [image_eq_zero_of_notMem_tsupport fun h ↦ hω h hx]

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback along a face map evaluates the form on its linear part. -/
theorem pullbackCLM_boxFaceMap_apply (i : Fin (p + 1)) (t : ℝ) {k : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (p + 1)))}
    {hc : ContDiffOn ℝ (⊤ : ℕ∞) (boxFaceMap i t) (⊤ : Opens (EuclideanSpace ℝ (Fin p)))}
    {hp : ∀ K, IsCompact K → K ⊆ Ω →
      IsCompact (((⊤ : Opens (EuclideanSpace ℝ (Fin p))) : Set _) ∩ boxFaceMap i t ⁻¹' K)}
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin k]→L[ℝ] F))
    (y : EuclideanSpace ℝ (Fin p)) :
    pullbackCLM (boxFaceMap i t) hc hp ω y =
      (ω (boxFaceMap i t y)).compContinuousLinearMap (boxFaceMap i t).contLinear := by
  rw [pullbackCLM_apply_of_mem _ (by simp), ContinuousAffineMap.fderiv]

/-- A test form pulled back along `boxFaceMap i t` is, on the standard basis of `ℝᵖ`, the form
evaluated on the standard basis of `ℝᵖ⁺¹` without `eᵢ`. -/
theorem pullbackCLM_boxFaceMap_apply_single (i : Fin (p + 1)) (t : ℝ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (p + 1)))}
    {hc : ContDiffOn ℝ (⊤ : ℕ∞) (boxFaceMap i t) (⊤ : Opens (EuclideanSpace ℝ (Fin p)))}
    {hp : ∀ K, IsCompact K → K ⊆ Ω →
      IsCompact (((⊤ : Opens (EuclideanSpace ℝ (Fin p))) : Set _) ∩ boxFaceMap i t ⁻¹' K)}
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F))
    (y : EuclideanSpace ℝ (Fin p)) :
    pullbackCLM (boxFaceMap i t) hc hp ω y (fun k ↦ EuclideanSpace.single k 1) =
      ω (boxFaceMap i t y) (i.removeNth fun j ↦ EuclideanSpace.single j 1) := by
  rw [pullbackCLM_boxFaceMap_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  exact contLinear_boxFaceMap_single i t k 1

/-- Pushforward along a face map does not increase the mass of a current. -/
theorem mass_comp_pullbackCLM_boxFaceMap_le (i : Fin (p + 1)) (t : ℝ) {k : ℕ}
    {V : Type*} [NormedAddCommGroup V]
    {Ω : Opens (EuclideanSpace ℝ (Fin (p + 1)))} {Ω' : Opens (EuclideanSpace ℝ (Fin p))}
    {hc : ContDiffOn ℝ (⊤ : ℕ∞) (boxFaceMap i t) Ω'}
    {hp : ∀ K, IsCompact K → K ⊆ Ω → IsCompact ((Ω' : Set _) ∩ boxFaceMap i t ⁻¹' K)}
    (T : 𝓓(Ω', EuclideanSpace ℝ (Fin p) [⋀^Fin k]→L[ℝ] F) → V) :
    mass (T ∘ pullbackCLM (boxFaceMap i t) hc hp) ≤ mass T := by
  refine mass_le_iff.2 fun ω hω ↦ enorm_le_mass (f := T) fun x ↦ ?_
  refine (norm_pullbackCLM_apply_le ω x).trans ?_
  rw [ContinuousAffineMap.fderiv]
  simpa using mul_le_mul (hω _)
    (pow_le_one₀ (norm_nonneg _) (norm_contLinear_boxFaceMap_le_one i t)) (by positivity)
    zero_le_one

end Pullback

/-- **The boundary of the box on a test form**: for `a ≤ b`, `[[a, b]] (d ω)` is the alternating
sum over `i` of `[[a', b']] ((Fᵢ^{bᵢ})^* ω) - [[a', b']] ((Fᵢ^{aᵢ})^* ω)`, where
`a' = a ∘ i.succAbove`, `b' = b ∘ i.succAbove` and `Fᵢ^t = boxFaceMap i t`. This is Stokes' theorem
on the box for test forms. -/
theorem boxCurrent_extDerivCLM {a b : Fin (p + 1) → ℝ} (hab : a ≤ b)
    (Ω : Opens (EuclideanSpace ℝ (Fin (p + 1))))
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] ℝ)) :
    boxCurrent a b Ω (extDerivCLM ω) =
      ∑ i : Fin (p + 1), (-1 : ℝ) ^ (i : ℕ) •
        (boxCurrent (a ∘ i.succAbove) (b ∘ i.succAbove) ⊤
            (pullbackCLM (boxFaceMap i (b i)) (boxFaceMap i (b i)).contDiff.contDiffOn
              (fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap i (b i) hK) ω) -
          boxCurrent (a ∘ i.succAbove) (b ∘ i.succAbove) ⊤
            (pullbackCLM (boxFaceMap i (a i)) (boxFaceMap i (a i)).contDiff.contDiffOn
              (fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap i (a i) hK) ω)) := by
  have hω : ContDiff ℝ 1 (ω : EuclideanSpace ℝ (Fin (p + 1)) → _) := ω.contDiff.of_le (by simp)
  have hdω : Continuous fun x : Fin (p + 1) → ℝ ↦
      extDerivCLM ω (toLp 2 x) fun i ↦ EuclideanSpace.single i 1 :=
    ((extDerivCLM ω).continuous.comp (PiLp.continuous_toLp _ _)).eval_const _
  rw [boxCurrent_apply]
  simp only [extDerivCLM_apply] at hdω ⊢
  rw [integral_extDeriv_toLp_Icc hab
    (hω.continuous.comp (PiLp.continuous_toLp _ _)).continuousOn
    (fun x _ ↦ hω.differentiable one_ne_zero _) hdω.integrableOn_Icc, boxBoundarySum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [boxCurrent_apply, pullbackCLM_boxFaceMap_apply_single, boxFaceMap_apply, smul_sub,
    integral_smul]

/-- **The boundary of the box**: for `a ≤ b`,
`∂ [[a, b]] = ∑ᵢ (-1)ⁱ ((Fᵢ^{bᵢ})_# [[a', b']] - (Fᵢ^{aᵢ})_# [[a', b']])`, where `∂ T = T ∘ d`,
`a' = a ∘ i.succAbove`, `b' = b ∘ i.succAbove`, and `(Fᵢ^t)_# T = T ∘ (Fᵢ^t)^*` is the pushforward
along the face map `Fᵢ^t = boxFaceMap i t`. -/
theorem boxCurrent_comp_extDerivCLM {a b : Fin (p + 1) → ℝ} (hab : a ≤ b)
    (Ω : Opens (EuclideanSpace ℝ (Fin (p + 1)))) :
    boxCurrent a b Ω ∘L extDerivCLM =
      ∑ i : Fin (p + 1), (-1 : ℝ) ^ (i : ℕ) •
        (boxCurrent (a ∘ i.succAbove) (b ∘ i.succAbove) ⊤ ∘L
            pullbackCLM (boxFaceMap i (b i)) (boxFaceMap i (b i)).contDiff.contDiffOn
              (fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap i (b i) hK) -
          boxCurrent (a ∘ i.succAbove) (b ∘ i.succAbove) ⊤ ∘L
            pullbackCLM (boxFaceMap i (a i)) (boxFaceMap i (a i)).contDiff.contDiffOn
              (fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap i (a i) hK)) := by
  ext ω
  simp [boxCurrent_extDerivCLM hab]

/-- `[[a, b]]` is compatible with restriction: on a test form extended by zero from a smaller open
set `Ω'`, the current `[[a, b]]` on `Ω` is the current `[[a, b]]` on `Ω'`. -/
@[simp]
theorem boxCurrent_monoCLM (a b : Fin p → ℝ) {Ω Ω' : Opens (EuclideanSpace ℝ (Fin p))}
    (h : Ω' ≤ Ω) (ω : 𝓓^{n}(Ω', EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ)) :
    boxCurrent a b Ω (monoCLM ℝ ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ)) =
      boxCurrent a b Ω' ω := by
  simp [boxCurrent_apply, monoCLM_apply, h]

/-- **The mass of the box**: `M([[a, b]]) ≤ vol([a, b])`. -/
theorem mass_boxCurrent_le (a b : Fin p → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    mass (boxCurrent a b Ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) → ℝ) ≤
      volume (Icc a b) := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  rw [boxCurrent_apply]
  calc ‖∫ x in Icc a b, ω (toLp 2 x) fun i ↦ EuclideanSpace.single i 1‖ₑ
      ≤ ∫⁻ x in Icc a b, ‖ω (toLp 2 x) fun i ↦ EuclideanSpace.single i 1‖ₑ :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ _ in Icc a b, 1 := lintegral_mono fun x ↦ by
        rw [← ofReal_norm, ENNReal.ofReal_le_one]
        exact ((ω (toLp 2 x)).le_opNorm _).trans (by simpa using hω (toLp 2 x))
    _ = volume (Icc a b) := by simp

/-- **The box is a normal current**: `[[a, b]]` and its boundary have finite mass. -/
theorem isNormal_boxCurrent (a b : Fin p → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    IsNormal (boxCurrent a b Ω :
      𝓓(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  have hT (p : ℕ) (a b : Fin p → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
      mass (boxCurrent a b Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top isCompact_Icc.measure_ne_top (mass_boxCurrent_le a b Ω)
  induction p with
  | zero => exact isNormal_finZero_iff.2 (hT 0 a b Ω)
  | succ p ih =>
    refine isNormal_succ_iff.2 ⟨hT _ a b Ω, ?_⟩
    by_cases hab : a ≤ b
    swap
    · simp [boxCurrent_eq_zero_of_not_le hab]
    -- The boundary is a finite combination of pushforwards of boxes along affine maps.
    have hF (i : Fin (p + 1)) (t : ℝ) :
        IsNormal (boxCurrent (a ∘ i.succAbove) (b ∘ i.succAbove) ⊤ ∘L
          pullbackCLM (boxFaceMap i t) (boxFaceMap i t).contDiff.contDiffOn
            (fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap i t hK) :
          𝓓(Ω, EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
      (ih _ _ ⊤).comp_pullbackCLM (L := 1) fun x _ ↦ by
        rw [ContinuousAffineMap.fderiv]
        exact norm_contLinear_boxFaceMap_le_one i t
    rw [boxCurrent_comp_extDerivCLM hab]
    exact IsNormal.mass_ne_top (mem_normalCurrentSubmodule.1
      ((normalCurrentSubmodule ℝ ℝ Ω p).sum_mem fun i _ ↦ mem_normalCurrentSubmodule.2
        (((hF i (b i)).sub (hF i (a i))).smul _)))

end TauCeti
