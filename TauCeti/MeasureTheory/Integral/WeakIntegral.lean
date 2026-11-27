/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Function.Lp.ScalarEvaluation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weak set integrals: the Dunford and weak-star integrals

Let `f : S → X` be a function into a normed space over `𝕜 = ℝ` or `ℂ`, and let a Banach space `Y`
of tests act on `X` through `ι : Y →L[𝕜] StrongDual 𝕜 X`. If every scalar test `s ↦ ι y (f s)` is
integrable, then for every set `A` the formula `y ↦ ∫ s in A, ι y (f s) ∂μ` defines a continuous
linear functional on `Y`, the weak set integral `TauCeti.weakSetIntegral f ι hf A`. It is the
adjoint of the bounded scalar-evaluation operator `T_f = TauCeti.scalarEvalLp f ι : Y → L¹(μ)`
applied to the set-integral functional on `L¹(μ)`, so it is bounded by `‖T_f‖`
(`TauCeti.norm_weakSetIntegral_le`). No measurability of `f` is assumed, and the functional need
not be represented by a vector of `X`; the Pettis integral is the case where it is.

Two choices of tests are singled out.

* For `Y = X*` and `ι` the identity, the hypothesis is that `f` is weakly integrable
  (`TauCeti.WeaklyIntegrable`), and the weak set integral is the *Dunford* set integral
  `TauCeti.dunfordSetIntegral f hf A ∈ X**`.
* For a dual-valued `f : S → X*` and `ι` the canonical embedding of a Banach space `X` into its
  bidual, the tests are the evaluations at points of `X`, and the weak set integral is the
  *weak-star* set integral `TauCeti.weakStarSetIntegral f hf A ∈ X*`. It is the restriction of the
  Dunford set integral to `X` (`TauCeti.dunfordSetIntegral_comp_inclusionInDoubleDual`).

The file develops the general weak set integral: uniqueness through scalar tests, linearity in
`f`, invariance under almost-everywhere equality, finite and countable additivity in the set,
restriction of the measure, change of the tests along a bounded linear map, functoriality along a
bounded linear map `T : X → W` through the restricted adjoint, its value at an indicator vector, and
agreement with the Bochner set integral for Bochner-integrable `f`.

## References

* N. Dunford, J. T. Schwartz, *Linear Operators, Part I*, Interscience, 1958, §III.3.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, §1.2.c and Examples 1.2.33–1.2.34.
-/

public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {𝕜 X W S : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {mS : MeasurableSpace S} {μ : Measure S}

section WeakSetIntegral

variable {Y Z V : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]

/-- The weak set integral of `f` over `A` with respect to the tests `ι : Y →L[𝕜] StrongDual 𝕜 X`:
the continuous linear functional `y ↦ ∫ s in A, ι y (f s) ∂μ` on the Banach space `Y`, for a
function `f` all of whose scalar tests are integrable. It is the adjoint of the scalar-evaluation
operator `TauCeti.scalarEvalLp f ι : Y → L¹(μ)` applied to the set-integral functional on `L¹(μ)`
(`TauCeti.weakSetIntegral_eq_comp_scalarEvalLp`). -/
def weakSetIntegral (f : S → X) (ι : Y →L[𝕜] StrongDual 𝕜 X)
    (hf : ∀ y, Integrable (fun s ↦ ι y (f s)) μ) (A : Set S) : StrongDual 𝕜 Y :=
  ((L1.integralCLM' 𝕜).comp (LpToLpRestrictCLM S 𝕜 𝕜 μ 1 A)).comp
    (scalarEvalLp f ι fun y ↦ memLp_one_iff_integrable.2 (hf y))

variable {f g : S → X} {ι : Y →L[𝕜] StrongDual 𝕜 X}
  {hf : ∀ y, Integrable (fun s ↦ ι y (f s)) μ} {hg : ∀ y, Integrable (fun s ↦ ι y (g s)) μ}
  {A B : Set S}

/-- The weak set integral is the adjoint of the scalar-evaluation operator `T_f : Y → L¹(μ)`
applied to the set-integral functional `φ ↦ ∫ s in A, φ s ∂μ` on `L¹(μ)`. -/
theorem weakSetIntegral_eq_comp_scalarEvalLp :
    weakSetIntegral f ι hf A =
      ((L1.integralCLM' 𝕜).comp (LpToLpRestrictCLM S 𝕜 𝕜 μ 1 A)).comp
        (scalarEvalLp f ι fun y ↦ memLp_one_iff_integrable.2 (hf y)) := (rfl)

/-- The value of the weak set integral at `y` is the set integral of the `L¹` class
`scalarEvalLp f ι y`. -/
theorem weakSetIntegral_apply_eq_setIntegral_scalarEvalLp (y : Y) :
    weakSetIntegral f ι hf A y =
      ∫ s in A, scalarEvalLp f ι (fun y ↦ memLp_one_iff_integrable.2 (hf y)) y s ∂μ := by
  rw [weakSetIntegral_eq_comp_scalarEvalLp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 A _)

/-- The value of the weak set integral at a test `y` is the set integral of the scalar test
`s ↦ ι y (f s)`. -/
@[simp]
theorem weakSetIntegral_apply (y : Y) :
    weakSetIntegral f ι hf A y = ∫ s in A, ι y (f s) ∂μ := by
  rw [weakSetIntegral_apply_eq_setIntegral_scalarEvalLp]
  exact integral_congr_ae (ae_restrict_of_ae (coeFn_scalarEvalLp y))

/-- **Uniqueness.** The weak set integral is the only functional on `Y` whose value at every test
`y` is the set integral of `s ↦ ι y (f s)`. -/
theorem eq_weakSetIntegral_iff {φ : StrongDual 𝕜 Y} :
    φ = weakSetIntegral f ι hf A ↔ ∀ y, φ y = ∫ s in A, ι y (f s) ∂μ := by
  simp [ContinuousLinearMap.ext_iff]

/-- The weak set integral is bounded by the norm of the scalar-evaluation operator
`T_f : Y → L¹(μ)`. -/
theorem norm_weakSetIntegral_le :
    ‖weakSetIntegral f ι hf A‖ ≤
      ‖scalarEvalLp f ι fun y ↦ memLp_one_iff_integrable.2 (hf y)‖ := by
  set T := scalarEvalLp f ι fun y ↦ memLp_one_iff_integrable.2 (hf y)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
  calc ‖weakSetIntegral f ι hf A y‖ = ‖∫ s in A, T y s ∂μ‖ := by
        rw [weakSetIntegral_apply_eq_setIntegral_scalarEvalLp]
    _ ≤ ∫ s in A, ‖T y s‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ s, ‖T y s‖ ∂μ :=
        setIntegral_le_integral (L1.integrable_coeFn _).norm (.of_forall fun _ ↦ norm_nonneg _)
    _ = ‖T y‖ := (L1.norm_eq_integral_norm _).symm
    _ ≤ ‖T‖ * ‖y‖ := T.le_opNorm y

/-- The weak set integral only depends on the scalar tests up to almost-everywhere equality. -/
theorem weakSetIntegral_congr (hfg : ∀ y, (fun s ↦ ι y (f s)) =ᵐ[μ] fun s ↦ ι y (g s)) :
    weakSetIntegral f ι hf A = weakSetIntegral g ι hg A := by
  ext y
  simpa using integral_congr_ae (ae_restrict_of_ae (hfg y))

/-- The weak set integral is invariant under almost-everywhere equality of functions. -/
theorem weakSetIntegral_congr_ae (hfg : f =ᵐ[μ] g) :
    weakSetIntegral f ι hf A = weakSetIntegral g ι hg A :=
  weakSetIntegral_congr fun _ ↦ hfg.mono fun s hs ↦ by simp only [hs]

/-- The weak set integral only depends on the set up to a null set. -/
theorem weakSetIntegral_congr_set (hAB : A =ᵐ[μ] B) :
    weakSetIntegral f ι hf A = weakSetIntegral f ι hf B := by
  ext y
  simpa using setIntegral_congr_set hAB

/-- The weak set integral of the zero function vanishes. -/
@[simp]
theorem weakSetIntegral_zero (h0 : ∀ y, Integrable (fun s ↦ ι y ((0 : S → X) s)) μ) :
    weakSetIntegral 0 ι h0 A = 0 := by
  ext y
  simp

/-- The weak set integral is additive in the function. -/
theorem weakSetIntegral_add (hfg : ∀ y, Integrable (fun s ↦ ι y ((f + g) s)) μ) :
    weakSetIntegral (f + g) ι hfg A = weakSetIntegral f ι hf A + weakSetIntegral g ι hg A := by
  ext y
  simp [integral_add (hf y).integrableOn (hg y).integrableOn]

/-- The weak set integral is homogeneous in the function. -/
theorem weakSetIntegral_smul (c : 𝕜) (hcf : ∀ y, Integrable (fun s ↦ ι y ((c • f) s)) μ) :
    weakSetIntegral (c • f) ι hcf A = c • weakSetIntegral f ι hf A := by
  ext y
  simp [integral_const_mul]

/-- The weak set integral is additive over disjoint sets. -/
theorem weakSetIntegral_union (hAB : Disjoint A B) (hB : MeasurableSet B) :
    weakSetIntegral f ι hf (A ∪ B) = weakSetIntegral f ι hf A + weakSetIntegral f ι hf B := by
  ext y
  simp [setIntegral_union hAB hB (hf y).integrableOn (hf y).integrableOn]

/-- **Weak-star countable additivity.** At every test `y`, the weak set integral over a countable
union of pairwise disjoint measurable sets is the sum of the weak set integrals over the pieces. -/
theorem hasSum_weakSetIntegral_iUnion {J : Type*} [Countable J] {A : J → Set S}
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A)) (y : Y) :
    HasSum (fun i ↦ weakSetIntegral f ι hf (A i) y) (weakSetIntegral f ι hf (⋃ i, A i) y) := by
  simpa using hasSum_integral_iUnion hA hd (hf y).integrableOn

/-- Restricting the measure to a measurable set `B` restricts the weak set integrals to subsets
of `B`. -/
theorem weakSetIntegral_restrict (hB : MeasurableSet B) :
    weakSetIntegral (μ := μ.restrict B) f ι (fun y ↦ (hf y).restrict) A =
      weakSetIntegral f ι hf (A ∩ B) := by
  ext y
  simp [Measure.restrict_restrict' hB]

/-- Changing the tests along a bounded linear map `κ : Z → Y` composes the weak set integral with
`κ`. For `κ` the inclusion of a closed subspace this is restriction of the functional. -/
theorem weakSetIntegral_comp (κ : Z →L[𝕜] Y) :
    weakSetIntegral (μ := μ) f (ι.comp κ) (fun z ↦ by simpa using hf (κ z)) A =
      (weakSetIntegral f ι hf A).comp κ := by
  ext z
  simp

/-- **Functoriality.** Let `T : X → W` be bounded, let `V` act on `W` through `ι'`, and let
`κ : V → Y` be a bounded linear map with `ι (κ v) = ι' v ∘ T`, so that `κ` is the adjoint of `T`
restricted to the tests. Then the weak set integral of `T ∘ f` is that of `f` composed with `κ`. -/
theorem weakSetIntegral_comp_left (T : X →L[𝕜] W) (ι' : V →L[𝕜] StrongDual 𝕜 W)
    (κ : V →L[𝕜] Y) (hκ : ∀ v, ι (κ v) = (ι' v).comp T)
    (hTf : ∀ v, Integrable (fun s ↦ ι' v ((T ∘ f) s)) μ) :
    weakSetIntegral (T ∘ f) ι' hTf A = (weakSetIntegral f ι hf A).comp κ := by
  ext v
  simp [hκ]

/-- The weak set integral of the indicator vector `𝟙_B x` of a measurable set `B` takes the value
`μ(A ∩ B) ι y (x)` at the test `y`. -/
theorem weakSetIntegral_indicator_const_apply (hB : MeasurableSet B) (x : X)
    (hf : ∀ y, Integrable (fun s ↦ ι y (B.indicator (fun _ ↦ x) s)) μ) (y : Y) :
    weakSetIntegral (B.indicator fun _ ↦ x) ι hf A y = μ.real (A ∩ B) * ι y x := by
  have h : (fun s ↦ ι y (B.indicator (fun _ ↦ x) s)) = B.indicator fun _ ↦ ι y x := by
    ext s
    by_cases hs : s ∈ B <;> simp [hs]
  rw [weakSetIntegral_apply, h, integral_indicator_const _ hB, measureReal_restrict_apply hB,
    inter_comm, RCLike.real_smul_eq_coe_mul]

/-- For a Bochner-integrable function, the weak set integral at the test `y` is the value of `ι y`
at the Bochner set integral. -/
theorem weakSetIntegral_apply_of_integrable [NormedSpace ℝ X] [CompleteSpace X]
    (hfi : Integrable f μ) (y : Y) :
    weakSetIntegral f ι hf A y = ι y (∫ s in A, f s ∂μ) := by
  rw [weakSetIntegral_apply, (ι y).integral_comp_comm hfi.integrableOn]

end WeakSetIntegral

section Dunford

variable (𝕜) in
/-- A function `f : S → X` is weakly integrable if `s ↦ x' (f s)` is integrable for every
continuous linear functional `x'` on `X`. No measurability of `f` itself is required. -/
def WeaklyIntegrable (f : S → X) (μ : Measure S) : Prop :=
  ∀ x' : StrongDual 𝕜 X, Integrable (fun s ↦ x' (f s)) μ

variable {f g : S → X}

/-- Weak integrability unfolds to integrability of every scalar test. -/
theorem weaklyIntegrable_iff :
    WeaklyIntegrable 𝕜 f μ ↔ ∀ x' : StrongDual 𝕜 X, Integrable (fun s ↦ x' (f s)) μ :=
  Iff.rfl

/-- Every scalar test of a weakly integrable function is integrable. -/
theorem WeaklyIntegrable.integrable_apply (hf : WeaklyIntegrable 𝕜 f μ) (x' : StrongDual 𝕜 X) :
    Integrable (fun s ↦ x' (f s)) μ :=
  hf x'

/-- A Bochner-integrable function is weakly integrable. -/
theorem _root_.MeasureTheory.Integrable.weaklyIntegrable (hf : Integrable f μ) :
    WeaklyIntegrable 𝕜 f μ :=
  fun x' ↦ x'.integrable_comp hf

/-- The zero function is weakly integrable. -/
@[simp]
theorem weaklyIntegrable_zero : WeaklyIntegrable 𝕜 (0 : S → X) μ :=
  integrable_zero S X μ |>.weaklyIntegrable

/-- Weak integrability is invariant under almost-everywhere equality. -/
theorem WeaklyIntegrable.congr (hf : WeaklyIntegrable 𝕜 f μ) (hfg : f =ᵐ[μ] g) :
    WeaklyIntegrable 𝕜 g μ :=
  fun x' ↦ (hf x').congr (hfg.mono fun s hs ↦ by simp only [hs])

/-- A sum of weakly integrable functions is weakly integrable. -/
theorem WeaklyIntegrable.add (hf : WeaklyIntegrable 𝕜 f μ) (hg : WeaklyIntegrable 𝕜 g μ) :
    WeaklyIntegrable 𝕜 (f + g) μ :=
  fun x' ↦ by
    simp only [Pi.add_apply, map_add]
    exact (hf x').add (hg x')

/-- A scalar multiple of a weakly integrable function is weakly integrable. -/
theorem WeaklyIntegrable.const_smul (hf : WeaklyIntegrable 𝕜 f μ) (c : 𝕜) :
    WeaklyIntegrable 𝕜 (c • f) μ :=
  fun x' ↦ by simpa using (hf x').const_mul c

/-- A weakly integrable function is weakly integrable for every restriction of the measure. -/
theorem WeaklyIntegrable.restrict (hf : WeaklyIntegrable 𝕜 f μ) (A : Set S) :
    WeaklyIntegrable 𝕜 f (μ.restrict A) :=
  fun x' ↦ (hf x').restrict

/-- The image of a weakly integrable function under a bounded linear map is weakly integrable. -/
theorem _root_.ContinuousLinearMap.weaklyIntegrable_comp (T : X →L[𝕜] W)
    (hf : WeaklyIntegrable 𝕜 f μ) : WeaklyIntegrable 𝕜 (fun s ↦ T (f s)) μ :=
  fun w' ↦ by simpa using hf (w'.comp T)

/-- The Dunford set integral of a weakly integrable function `f` over `A`: the functional
`x' ↦ ∫ s in A, x' (f s) ∂μ` in the bidual of `X`. It is the weak set integral for the full dual as
space of tests. -/
def dunfordSetIntegral (f : S → X) (hf : WeaklyIntegrable 𝕜 f μ) (A : Set S) :
    StrongDual 𝕜 (StrongDual 𝕜 X) :=
  weakSetIntegral (μ := μ) f (ContinuousLinearMap.id 𝕜 _)
    (fun x' ↦ by simpa using hf.integrable_apply x') A

/-- The Dunford set integral is the weak set integral for the full dual as space of tests; this
transfers the general weak set integral API to it. -/
theorem dunfordSetIntegral_eq_weakSetIntegral (hf : WeaklyIntegrable 𝕜 f μ) (A : Set S) :
    dunfordSetIntegral f hf A =
      weakSetIntegral (μ := μ) f (ContinuousLinearMap.id 𝕜 _)
        (fun x' ↦ by simpa using hf.integrable_apply x') A := (rfl)

/-- The value of the Dunford set integral at `x'` is the set integral of `s ↦ x' (f s)`. -/
@[simp]
theorem dunfordSetIntegral_apply (hf : WeaklyIntegrable 𝕜 f μ) (A : Set S)
    (x' : StrongDual 𝕜 X) : dunfordSetIntegral f hf A x' = ∫ s in A, x' (f s) ∂μ := by
  simp [dunfordSetIntegral_eq_weakSetIntegral]

/-- The Dunford set integral of a Bochner-integrable function is the image of its Bochner set
integral in the bidual. -/
theorem dunfordSetIntegral_of_integrable [NormedSpace ℝ X] [CompleteSpace X]
    (hf : WeaklyIntegrable 𝕜 f μ) (hfi : Integrable f μ) (A : Set S) :
    dunfordSetIntegral f hf A = NormedSpace.inclusionInDoubleDual 𝕜 X (∫ s in A, f s ∂μ) := by
  ext x'
  rw [dunfordSetIntegral_eq_weakSetIntegral, weakSetIntegral_apply_of_integrable hfi]
  simp

end Dunford

section WeakStar

variable [CompleteSpace X]

/-- The weak-star set integral of a dual-valued function `f : S → X*` over `A`, for a Banach space
`X`, when `s ↦ f s x` is integrable for every `x : X`: the functional `x ↦ ∫ s in A, f s x ∂μ`.
It is the weak set integral whose tests are the evaluations at points of `X`. -/
def weakStarSetIntegral (f : S → StrongDual 𝕜 X) (hf : ∀ x, Integrable (fun s ↦ f s x) μ)
    (A : Set S) : StrongDual 𝕜 X :=
  weakSetIntegral (μ := μ) f (NormedSpace.inclusionInDoubleDual 𝕜 X)
    (fun x ↦ by simpa using hf x) A

variable {f : S → StrongDual 𝕜 X}

/-- The weak-star set integral is the weak set integral whose tests are the evaluations at points
of `X`; this transfers the general weak set integral API to it. -/
theorem weakStarSetIntegral_eq_weakSetIntegral (hf : ∀ x, Integrable (fun s ↦ f s x) μ)
    (A : Set S) :
    weakStarSetIntegral f hf A =
      weakSetIntegral (μ := μ) f (NormedSpace.inclusionInDoubleDual 𝕜 X)
        (fun x ↦ by simpa using hf x) A := (rfl)

/-- The value of the weak-star set integral at `x` is the set integral of `s ↦ f s x`. -/
@[simp]
theorem weakStarSetIntegral_apply (hf : ∀ x, Integrable (fun s ↦ f s x) μ) (A : Set S) (x : X) :
    weakStarSetIntegral f hf A x = ∫ s in A, f s x ∂μ := by
  simp [weakStarSetIntegral_eq_weakSetIntegral]

/-- The weak-star set integral is the restriction to `X ⊆ X**` of the Dunford set integral of a
weakly integrable dual-valued function. -/
theorem dunfordSetIntegral_comp_inclusionInDoubleDual (hf : WeaklyIntegrable 𝕜 f μ) (A : Set S) :
    (dunfordSetIntegral f hf A).comp (NormedSpace.inclusionInDoubleDual 𝕜 X) =
      weakStarSetIntegral (μ := μ) f
        (fun x ↦ by
          simpa using hf.integrable_apply (NormedSpace.inclusionInDoubleDual 𝕜 X x)) A := by
  ext x
  simp

/-- The weak-star set integral of a Bochner-integrable dual-valued function is its Bochner set
integral. -/
theorem weakStarSetIntegral_of_integrable (hf : ∀ x, Integrable (fun s ↦ f s x) μ)
    (hfi : Integrable f μ) (A : Set S) : weakStarSetIntegral f hf A = ∫ s in A, f s ∂μ := by
  ext x
  rw [weakStarSetIntegral_apply, ContinuousLinearMap.integral_apply hfi.integrableOn]

end WeakStar

end TauCeti
