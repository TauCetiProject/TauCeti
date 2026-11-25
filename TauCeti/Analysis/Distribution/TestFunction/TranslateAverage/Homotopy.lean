/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.TranslateAverage.Basic
public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Means of translates of test forms and their homotopy operator

Let `ν` be a finite measure on a finite-dimensional real normed space `E`, concentrated on the
closed ball of radius `r` about `0`, and let `U`, `Ω` be open sets of `E` with
`U + closedBall 0 r ⊆ Ω`. The **mean of the translates** of a test function `φ` on `U` against `ν`
is the test function

`M φ = x ↦ ∫ φ (x + v) dν(v)`

on `Ω` (`TestFunction.translationMeanCLM`). For `ν` with a smooth density `ρ` this is the
convolution of `φ` with the reflection of `ρ`, and for a normalized bump on the whole space it is
the mollification `TestFunction.mollifyCLM`; for `ν` the Dirac mass at `h` it is the translate
`x ↦ φ (x + h)`. The mean commutes with the exterior derivative of test forms.

The **averaged homotopy operator** sends a test `(k + 1)`-form `ω` on `U` to the test `k`-form

`K ω = x ↦ ∫ ω(x + t v)(v, ·) d(ν × dt)(v, t)`

on `Ω`, the integral being over `E × [0, 1]` (`TestFunction.translationHomotopyCLM`): the average
over `v` of the homotopy operators `ω ↦ x ↦ ∫₀¹ ω(x + t v)(v, ·) dt` of the straight-line
homotopies `(x, t) ↦ x + t v` from the identity to the translation by `v`. It satisfies the
homotopy identity

`K (d ω) + d (K ω) = M ω - ν(E) ω`,

with `K (d f) = M f - ν(E) f` in degree zero. Pointwise this is the constant-coefficient Cartan
formula `d ι_v + ι_v d = ∂_v` integrated along the segments `t ↦ x + t v`, then averaged against
`ν`. Since `‖K ω‖ ≤ r ν(E) sup ‖ω‖`, the identity says that `M` differs from `ν(E)` times the
identity by a boundary plus a term of size at most `r`. Composing with a current gives the
**homotopy formula** for the averaged current `T ∘ M`:

`∂ (T ∘ K) + (∂ T) ∘ K = T ∘ M - ν(E) T`,

where `∂ T = T ∘ d`, together with the mass bounds `M(T ∘ M) ≤ ν(E) M(T)` and
`M(T ∘ K) ≤ r ν(E) M(T)`. These are the ingredients of the flat approximation of normal currents
by their regularizations.

## Main declarations

* `TestFunction.translationMeanCLM`: the mean of translates, with values
  `TestFunction.translationMeanCLM_apply`, support `TestFunction.tsupport_translationMeanCLM_subset`
  and sup bound `TestFunction.norm_translationMeanCLM_apply_le`.
* `TestFunction.extDerivCLM_translationMeanCLM`: the mean commutes with the exterior derivative.
* `TestFunction.translationHomotopyCLM`: the averaged homotopy operator, with values
  `TestFunction.translationHomotopyCLM_apply`, support
  `TestFunction.tsupport_translationHomotopyCLM_subset` and sup bound
  `TestFunction.norm_translationHomotopyCLM_apply_le`.
* `TestFunction.translationHomotopyCLM_extDerivCLM_add_extDerivCLM_translationHomotopyCLM`,
  `TestFunction.translationHomotopyCLM_extDerivCLM_finZero`: the homotopy identity.
* `ContinuousLinearMap.comp_translationMeanCLM_comp_extDerivCLM`: `∂ (T ∘ M) = (∂ T) ∘ M`.
* `ContinuousLinearMap.comp_translationHomotopyCLM_comp_extDerivCLM`,
  `ContinuousLinearMap.comp_translationHomotopyCLM_comp_extDerivCLM_finZero`: the homotopy
  formula for currents.
* `Distribution.mass_comp_translationMeanCLM_le`,
  `Distribution.mass_comp_translationHomotopyCLM_le`: the mass bounds.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.2 and §4.1.18 (regularization of currents by
  convolution, and the homotopy relating a current to its regularizations).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter ContinuousAlternatingMap TauCeti
open scoped Pointwise Distributions

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ν : Measure E} [IsFiniteMeasure ν] {r : ℝ} {U Ω : Opens E} {k : ℕ}

section Mean

/-- The **mean of the translates** of test functions against a finite measure `ν` concentrated
on `closedBall 0 r`: the continuous linear map sending a test function `φ` on `U` to the test
function `x ↦ ∫ φ (x + v) dν(v)` on `Ω`, where `U + closedBall 0 r ⊆ Ω`. -/
def translationMeanCLM (ν : Measure E) [IsFiniteMeasure ν]
    (hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r)
    (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)) : 𝓓(U, F) →L[ℝ] 𝓓(Ω, F) :=
  translationAverageCLM (A := fun _ ↦ ContinuousLinearMap.id ℝ F) (s := id)
    aestronglyMeasurable_const (ae_of_all _ fun _ ↦ ContinuousLinearMap.norm_id_le)
    aestronglyMeasurable_id hν hUΩ

variable {hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r}
  {hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)}

/-- The mean of the translates of a test function is `x ↦ ∫ φ (x + v) dν(v)`. -/
@[simp]
theorem translationMeanCLM_apply (φ : 𝓓(U, F)) (x : E) :
    translationMeanCLM ν hν hUΩ φ x = ∫ v, φ (x + v) ∂ν := by
  simp [translationMeanCLM]

/-- The mean of the translates of a test function is the translation average with the identity
operators and the identity displacements. -/
theorem coe_translationMeanCLM (φ : 𝓓(U, F)) :
    ⇑(translationMeanCLM ν hν hUΩ φ) =
      translationAverage ν (fun _ ↦ ContinuousLinearMap.id ℝ F) id φ :=
  coe_translationAverageCLM ..

/-- The mean of the translates of a test function is supported in `tsupport φ + closedBall 0 r`. -/
theorem tsupport_translationMeanCLM_subset (φ : 𝓓(U, F)) :
    tsupport (translationMeanCLM ν hν hUΩ φ) ⊆ tsupport φ + closedBall (0 : E) r :=
  tsupport_translationAverageCLM_subset ..

/-- A bound `C` on the values of `φ` bounds the mean of its translates by `C ν(E)`. -/
theorem norm_translationMeanCLM_apply_le (φ : 𝓓(U, F)) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) (x : E) :
    ‖translationMeanCLM ν hν hUΩ φ x‖ ≤ C * ν.real univ := by
  rw [coe_translationMeanCLM]
  simpa using norm_translationAverage_le (s := id)
    (ae_of_all _ fun _ ↦ ContinuousLinearMap.norm_id_le) hC x

variable [CompleteSpace F]

/-- **The mean of translates commutes with the exterior derivative**: `d (M ω) = M (d ω)`. -/
theorem extDerivCLM_translationMeanCLM (ω : 𝓓(U, E [⋀^Fin k]→L[ℝ] F)) :
    extDerivCLM (translationMeanCLM ν hν hUΩ ω) = translationMeanCLM ν hν hUΩ (extDerivCLM ω) := by
  ext x : 1
  unfold translationMeanCLM
  have h := (alternatizeUncurryFinCLM ℝ E F).integral_comp_comm
    (integrable_comp_fderiv_comp_add (A := fun _ ↦ ContinuousLinearMap.id ℝ (E [⋀^Fin k]→L[ℝ] F))
      (ν := ν) aestronglyMeasurable_const (ae_of_all _ fun _ ↦ ContinuousLinearMap.norm_id_le)
      aestronglyMeasurable_id ω x)
  rw [alternatizeUncurryFinCLM_apply] at h
  rw [extDerivCLM_apply, extDeriv, (hasFDerivAt_translationAverageCLM hUΩ ω x).fderiv, ← h,
    translationAverageCLM_apply]
  simp [extDeriv]

end Mean

section Homotopy

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasure ν] in
/-- The interior products with the vectors `v` of the support of `ν` are bounded by `r`. -/
private theorem ae_norm_curryLeftFlipL_le (hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r) :
    ∀ᵐ p ∂(ν.prod (volume.restrict (Icc (0 : ℝ) 1))),
      ‖curryLeftFlipL (𝕜 := ℝ) (E := E) (F := F) (n := k) p.1‖ ≤ r :=
  (Measure.quasiMeasurePreserving_fst.ae hν).mono fun p hp ↦
    (norm_curryLeftFlipL_apply_le p.1).trans (by simpa using hp)

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasure ν] in
/-- For `t ∈ [0, 1]` and `v` in the support of `ν`, the displacement `t v` lies in
`closedBall 0 r`. -/
private theorem ae_smul_mem_closedBall (hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r) :
    ∀ᵐ p ∂(ν.prod (volume.restrict (Icc (0 : ℝ) 1))), p.2 • p.1 ∈ closedBall (0 : E) r := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)] with p hv ht
  rw [mem_closedBall_zero_iff] at hv ⊢
  rw [norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hv

omit [IsFiniteMeasure ν] in
/-- The interior products with the first coordinate form a measurable family of operators. -/
private theorem aestronglyMeasurable_curryLeftFlipL :
    AEStronglyMeasurable (fun p : E × ℝ ↦
      curryLeftFlipL (𝕜 := ℝ) (E := E) (F := F) (n := k) p.1)
      (ν.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
  (ContinuousLinearMap.continuous _).comp_aestronglyMeasurable measurable_fst.aestronglyMeasurable

/-- The **averaged homotopy operator** on test forms: the continuous linear map sending a test
`(k + 1)`-form `ω` on `U` to the test `k`-form `x ↦ ∫ ω(x + t v)(v, ·) d(ν × dt)(v, t)` on `Ω`, the
integral being over `E × [0, 1]`, for a finite measure `ν` concentrated on `closedBall 0 r` and
`U + closedBall 0 r ⊆ Ω`. It is the average against `ν` of the homotopy operators
`ω ↦ x ↦ ∫₀¹ ω(x + t v)(v, ·) dt` of the straight-line homotopies from the identity to the
translations by `v`. -/
def translationHomotopyCLM (ν : Measure E) [IsFiniteMeasure ν]
    (hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r)
    (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)) :
    𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  translationAverageCLM aestronglyMeasurable_curryLeftFlipL (ae_norm_curryLeftFlipL_le hν)
    (continuous_snd.smul continuous_fst).aestronglyMeasurable (ae_smul_mem_closedBall hν) hUΩ

variable {hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r}
  {hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)}

/-- The averaged homotopy operator is `x ↦ ∫ ω(x + t v)(v, ·) d(ν × dt)(v, t)` over
`E × [0, 1]`. -/
@[simp]
theorem translationHomotopyCLM_apply (ω : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    translationHomotopyCLM ν hν hUΩ ω x =
      ∫ p, (ω (x + p.2 • p.1)).curryLeft p.1 ∂(ν.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  simp [translationHomotopyCLM]

/-- The averaged homotopy of a test form is supported in `tsupport ω + closedBall 0 r`. -/
theorem tsupport_translationHomotopyCLM_subset (ω : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (translationHomotopyCLM ν hν hUΩ ω) ⊆ tsupport ω + closedBall (0 : E) r :=
  tsupport_translationAverageCLM_subset ..

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [IsFiniteMeasure ν] in
/-- The product of `ν` with the Lebesgue measure on `[0, 1]` has the total mass of `ν`. -/
private theorem measureReal_prod_Icc_univ :
    (ν.prod (volume.restrict (Icc (0 : ℝ) 1))).real univ = ν.real univ := by
  simp [Measure.real, ← univ_prod_univ, Measure.prod_prod]

/-- **The sup bound for the averaged homotopy**: a bound `C` on the values of a test form `ω`
bounds `K ω` by `r C ν(E)`. -/
theorem norm_translationHomotopyCLM_apply_le {ω : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F)} {C : ℝ}
    (hω : ∀ y, ‖ω y‖ ≤ C) (x : E) :
    ‖translationHomotopyCLM ν hν hUΩ ω x‖ ≤ r * C * ν.real univ := by
  rw [translationHomotopyCLM_apply]
  simpa [translationAverage_apply, measureReal_prod_Icc_univ] using
    norm_translationAverage_le (s := fun p : E × ℝ ↦ p.2 • p.1)
      (ae_norm_curryLeftFlipL_le (F := F) (k := k) hν) hω x

/-- **Averaged fundamental theorem of calculus**: integrating the derivatives `Dφ (x + t v) v`
over `t ∈ [0, 1]` and against `ν` gives `∫ φ (x + v) dν(v) - ν(E) φ x`. -/
private theorem integral_fderiv_apply_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r) (φ : 𝓓(U, G)) (x : E) :
    ∫ p, fderiv ℝ φ (x + p.2 • p.1) p.1 ∂(ν.prod (volume.restrict (Icc (0 : ℝ) 1))) =
      ∫ v, φ (x + v) ∂ν - ν.real univ • φ x := by
  have hφ' : Continuous (fderiv ℝ φ) := φ.contDiff.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hφ'.bounded_above_of_compact_support (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨D, hD⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  -- The integrand is continuous, and bounded by `C r` on the support of the product measure.
  have hint : Integrable (fun p : E × ℝ ↦ fderiv ℝ φ (x + p.2 • p.1) p.1)
      (ν.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    refine Integrable.of_bound (C := C * r) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν] with p hp
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hC _) (mem_closedBall_zero_iff.1 hp) (norm_nonneg _)
        ((norm_nonneg _).trans (hC 0)))
  -- Along each segment, the fundamental theorem of calculus.
  have hftc (v : E) : ∫ t in Icc (0 : ℝ) 1, fderiv ℝ φ (x + t • v) v = φ (x + v) - φ x := by
    have hcont : Continuous fun t : ℝ ↦ fderiv ℝ φ (x + t • v) v := by fun_prop
    have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ ↦ φ (x + t • v)) (fderiv ℝ φ (x + t • v) v) t := by
      have h := ((φ.contDiff.differentiable (by simp)) (x + t • v)).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const v).const_add x)
      simpa [Function.comp_def] using h
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
        (hcont.intervalIntegrable _ _)]
    simp
  rw [integral_prod _ hint]
  simp_rw [hftc]
  rw [integral_sub (Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) D
      (ae_of_all _ fun _ ↦ hD _)) (integrable_const _), integral_const]

/-- The derivative of the averaged homotopy operator, under the integral sign. -/
private theorem hasFDerivAt_translationHomotopyCLM (ω : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F))
    (x : E) :
    HasFDerivAt (translationHomotopyCLM ν hν hUΩ ω)
      (∫ p, (curryLeftFlipL (𝕜 := ℝ) (E := E) (F := F) (n := k)
        p.1).comp (fderiv ℝ ω (x + p.2 • p.1)) ∂(ν.prod (volume.restrict (Icc (0 : ℝ) 1)))) x :=
  hasFDerivAt_translationAverageCLM hUΩ ω x

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `ν(E)` times the extension of `φ` to `Ω` is `ν(E) φ` pointwise. If `U ⊄ Ω`, the extension is
zero, but then `closedBall 0 r` is empty and `ν = 0`. -/
private theorem measureReal_univ_smul_monoCLM_apply {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r)
    (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)) (φ : 𝓓(U, G)) (x : E) :
    (ν.real univ • (monoCLM ℝ φ : 𝓓(Ω, G))) x = ν.real univ • φ x := by
  rcases eq_zero_or_neZero ν with rfl | _
  · simp
  · obtain ⟨v, hv⟩ := hν.exists
    have hr : 0 ≤ r := (norm_nonneg v).trans (mem_closedBall_zero_iff.1 hv)
    have hUΩ' : U ≤ Ω := fun y hy ↦ hUΩ ⟨y, hy, 0, mem_closedBall_self hr, add_zero y⟩
    simp [monoCLM_apply, hUΩ']

variable [CompleteSpace F]

/-- **The homotopy identity for the mean of translates**: `K (d ω) + d (K ω) = M ω - ν(E) ω` for
test `(k + 1)`-forms `ω`, where `M` is the mean of translates against `ν` and `K` the averaged
homotopy operator. -/
theorem translationHomotopyCLM_extDerivCLM_add_extDerivCLM_translationHomotopyCLM
    (ω : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    translationHomotopyCLM ν hν hUΩ (extDerivCLM ω) +
        extDerivCLM (translationHomotopyCLM ν hν hUΩ ω) =
      translationMeanCLM ν hν hUΩ ω - ν.real univ • monoCLM ℝ ω := by
  ext x : 1
  have hs : AEStronglyMeasurable (fun p : E × ℝ ↦ p.2 • p.1)
      (ν.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    (continuous_snd.smul continuous_fst).aestronglyMeasurable
  obtain ⟨C, hC⟩ := (extDerivCLM ω).continuous.bounded_above_of_compact_support
    (extDerivCLM ω).hasCompactSupport
  have hint := integrable_comp_fderiv_comp_add
    (aestronglyMeasurable_curryLeftFlipL (ν := ν) (F := F) (k := k))
    (ae_norm_curryLeftFlipL_le hν) hs ω x
  -- Differentiate `K ω` under the integral, and move the alternatization inside.
  have hcomm := (alternatizeUncurryFinCLM ℝ E F).integral_comp_comm hint
  rw [alternatizeUncurryFinCLM_apply] at hcomm
  have hint' : Integrable (fun p : E × ℝ ↦ (extDerivCLM ω (x + p.2 • p.1)).curryLeft p.1)
      (ν.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    simpa using integrable_translationAverage_integrand
      (aestronglyMeasurable_curryLeftFlipL (ν := ν) (F := F) (k := k + 1))
      (ae_norm_curryLeftFlipL_le hν) hs (extDerivCLM ω).continuous hC x
  rw [_root_.add_apply, extDerivCLM_apply, extDeriv,
    (hasFDerivAt_translationHomotopyCLM ω x).fderiv,
    ← hcomm, translationHomotopyCLM_apply, ← integral_add hint'
      ((alternatizeUncurryFinCLM ℝ E F).integrable_comp hint),
    _root_.sub_apply, translationMeanCLM_apply, measureReal_univ_smul_monoCLM_apply hν hUΩ,
    ← integral_fderiv_apply_eq hν ω x]
  -- Pointwise, this is the constant-coefficient Cartan formula `ι_v d + d ι_v = ∂_v`.
  refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
  simp only [extDerivCLM_apply, extDeriv, alternatizeUncurryFinCLM_apply]
  exact (add_comm _ _).trans
    (alternatizeUncurryFin_curryLeft_comp_add_curryLeft (fderiv ℝ ω (x + p.2 • p.1)) p.1)

/-- **The homotopy identity in degree zero**: `K (d f) = M f - ν(E) f` for test `0`-forms `f`. -/
theorem translationHomotopyCLM_extDerivCLM_finZero (ω : 𝓓(U, E [⋀^Fin 0]→L[ℝ] F)) :
    translationHomotopyCLM ν hν hUΩ (extDerivCLM ω) =
      translationMeanCLM ν hν hUΩ ω - ν.real univ • monoCLM ℝ ω := by
  ext x : 1
  rw [translationHomotopyCLM_apply, _root_.sub_apply, translationMeanCLM_apply,
    measureReal_univ_smul_monoCLM_apply hν hUΩ, ← integral_fderiv_apply_eq hν ω x]
  refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
  ext w
  simp [Subsingleton.elim w ![], extDeriv_apply_fin_one]

end Homotopy

end TestFunction

namespace ContinuousLinearMap

open TestFunction

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul ℝ G] {ν : Measure E} [IsFiniteMeasure ν] {r : ℝ} {U Ω : Opens E} {k : ℕ}
  {hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r}
  {hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)}

omit [IsTopologicalAddGroup G] [ContinuousConstSMul ℝ G] in
/-- **The boundary of the mean of translates of a current** is the mean of translates of its
boundary: `∂ (T ∘ M) = (∂ T) ∘ M`. -/
theorem comp_translationMeanCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L translationMeanCLM ν hν hUΩ) ∘L extDerivCLM =
      (T ∘L extDerivCLM) ∘L translationMeanCLM ν hν hUΩ := by
  ext ω
  simp [extDerivCLM_translationMeanCLM]

/-- **The homotopy formula for the mean of translates of a current**: for a `(k + 1)`-current `T`
on `Ω`, with `M` the mean of translates against `ν` and `K` the averaged homotopy operator,
`∂ (T ∘ K) + (∂ T) ∘ K = T ∘ M - ν(E) T` as currents on `U`, where `∂ S = S ∘ d`. -/
theorem comp_translationHomotopyCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L translationHomotopyCLM ν hν hUΩ) ∘L extDerivCLM +
        (T ∘L extDerivCLM) ∘L translationHomotopyCLM ν hν hUΩ =
      T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ) := by
  ext ω
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    _root_.sub_apply, _root_.smul_apply]
  rw [← map_add, translationHomotopyCLM_extDerivCLM_add_extDerivCLM_translationHomotopyCLM,
    map_sub, map_smul]

/-- **The homotopy formula for the mean of translates in degree zero**: for a `0`-current `T` on
`Ω`, `∂ (T ∘ K) = T ∘ M - ν(E) T` as `0`-currents on `U`. -/
theorem comp_translationHomotopyCLM_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L translationHomotopyCLM ν hν hUΩ) ∘L extDerivCLM =
      T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ) := by
  ext ω
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
    _root_.smul_apply]
  rw [translationHomotopyCLM_extDerivCLM_finZero, map_sub, map_smul]

end ContinuousLinearMap

namespace Distribution

open TestFunction
open scoped ENNReal BoundedContinuousFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ν : Measure E} [IsFiniteMeasure ν] {r : ℝ}
  {U Ω : Opens E} {k : ℕ} {hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r}
  {hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)}

/-- **The mass of the mean of translates of a current**: `M(T ∘ M) ≤ ν(E) M(T)`. -/
theorem mass_comp_translationMeanCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, F) V]
    [LinearMapClass 𝓕 ℝ 𝓓(Ω, F) V] (T : 𝓕) :
    mass (T ∘ translationMeanCLM (F := F) ν hν hUΩ) ≤ ν univ * mass T := by
  refine (mass_comp_le_of_norm_apply_le T measureReal_nonneg fun φ hφ x ↦ ?_).trans_eq
    (by rw [ofReal_measureReal (measure_ne_top ν univ)])
  simpa using norm_translationMeanCLM_apply_le (hν := hν) (hUΩ := hUΩ) φ hφ x

/-- **The mass of the averaged homotopy of a current**: `M(T ∘ K) ≤ r ν(E) M(T)`, for the averaged
homotopy operator `K` of a measure `ν` concentrated on `closedBall 0 r`. -/
theorem mass_comp_translationHomotopyCLM_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) :
    mass (T ∘ translationHomotopyCLM (F := F) (k := k) ν hν hUΩ) ≤
      ENNReal.ofReal r * ν univ * mass T := by
  have hK (ω : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F)) (hω : ∀ y, ‖ω y‖ ≤ 1) (x : E) :
      ‖translationHomotopyCLM (F := F) (k := k) ν hν hUΩ ω x‖ ≤ r * ν.real univ := by
    simpa using norm_translationHomotopyCLM_apply_le (hν := hν) (hUΩ := hUΩ) hω x
  refine (mass_comp_le_of_norm_apply_le T ((norm_nonneg _).trans (hK 0 (by simp) 0)) hK).trans_eq
    ?_
  rw [ENNReal.ofReal_mul' measureReal_nonneg, ofReal_measureReal (measure_ne_top ν univ)]

end Distribution
