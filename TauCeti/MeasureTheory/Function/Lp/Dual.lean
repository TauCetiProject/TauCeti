/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Duality
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Function.Lp.UniformConvex
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
import TauCeti.MeasureTheory.Function.Holder
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Function.Lp.Exponent
import TauCeti.MeasureTheory.Function.LpSeminorm.AbsolutelyContinuous

/-!
# Representation of continuous functionals on `Lᵖ`

On a σ-finite measure space, the integral pairing identifies the continuous dual of `Lᵠ`
with `Lᵖ` for conjugate exponents `1 ≤ q < ∞`, including the endpoint `L¹(μ)⋆ = L^∞(μ)`. The
isometric embedding is supplied by `MeasureTheory.Lp.toDual`.

The same holds, again for `1 ≤ q < ∞`, for functions with values in a Hilbert space `H`, where
`Lᵖ(μ; H⋆)` represents the continuous dual of `Lᵠ(μ; H)` by `g ↦ (f ↦ ∫ g x (f x) dμ)`, with
`H⋆ = StrongDual 𝕜 H` (`MeasureTheory.Lp.strongDualEquiv`). The pairing is bilinear, with no
complex conjugation. It is a linear isometry `MeasureTheory.Lp.toStrongDual` for all Hölder
conjugate exponents, `q = ∞` included: its norm is computed by testing against the pointwise Riesz
representative of `g`. For `1 < q < ∞`, surjectivity follows from reflexivity of `Lᵠ(μ; H)`, which
is uniformly convex: a functional annihilating the closed range is evaluation at an `Lᵠ(μ; H)`
function, which must vanish because it pairs to zero with every Riesz dual of a test function.
The scalar case is `H = 𝕜`: a density `G` with values in `𝕜⋆` gives the scalar density
`x ↦ G x 1`.

At the endpoint `q = 1`, for a finite measure, the density of `φ ∈ L¹(μ; H)⋆` is found in
`L²(μ; H)`. As `L²(μ; H)` maps continuously into `L¹(μ; H)` (`MeasureTheory.Lp.ofExponentLEL`), `φ`
restricts to a continuous linear functional on `L²(μ; H)`. The Riesz representation theorem writes
it as `f ↦ ∫ ⟪u, f⟫` for some `u ∈ L²(μ; H)`. Testing against bounded functions of finite-measure
support bounds `‖u‖_∞` by `‖φ‖`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`), and density
of simple functions in `L¹(μ; H)` gives `φ f = ∫ ⟪u, f⟫` for every `f ∈ L¹(μ; H)`. A σ-finite
measure `μ` has a positive weight `w` with `∫ w dμ < ∞`
(`MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite`), and `ν = w μ` is a finite measure with
the same null sets as `μ`. Multiplication by `w` maps `L¹(ν; H)` linearly and isometrically onto
`L¹(μ; H)` (`MeasureTheory.withDensitySMulLIE`), so `φ` pulls back to a functional on `L¹(ν; H)`,
whose density `g ∈ L^∞(ν; H⋆) = L^∞(μ; H⋆)` represents `φ`:
`φ (w u) = ∫ g u dν = ∫ g (w u) dμ`. Some hypothesis on `μ` is needed: for the measure on a point
that gives it infinite mass, `L¹(μ) = 0` while `L^∞(μ) = 𝕜`.

This representation passes distributional test-function bounds to actual `Lᵖ` weak derivatives.

For a real inner product space `E` with a finite orthonormal basis `b`, the dual of the product
`(Lᵠ)ᶥ` is represented by `Lᵖ(α; E)`: a functional `Λ` is `g ↦ ∑ᵢ ∫ ⟪H, bᵢ⟫ gᵢ` for a field
`H ∈ Lᵖ` with `‖H‖_{Lᵖ} ≤ |ι| ‖Λ‖` (`MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`).

## Main declarations

* `MeasureTheory.Lp.toStrongDual`: the integral pairing as a linear isometry
  `Lᵖ(μ; H⋆) → (Lᵠ(μ; H))⋆` for a Hilbert space `H` and any Hölder conjugate exponents.
* `MeasureTheory.Lp.strongDualEquiv`: the isometric isomorphism `Lᵖ(μ; H⋆) ≃ (Lᵠ(μ; H))⋆` for a
  Hilbert space `H` and `1 ≤ q < ∞`.
* `MeasureTheory.Lp.toDual_surjective`: for `1 ≤ q < ∞`, every continuous linear functional on
  `Lᵠ(μ)` is integration against some `g ∈ Lᵖ(μ)`.
* `MeasureTheory.Lp.dualEquiv`: the isometric isomorphism `Lᵖ(μ) ≃ (Lᵠ(μ))⋆` for `1 ≤ q < ∞`.
* `MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`: the representation of functionals on
  `(Lᵠ)ᶥ` by `Lᵖ(α; E)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.14 (the dual of `L¹`).
* G. B. Folland, *Real Analysis*, second edition, Theorems 6.15 and 6.16.
* J. Diestel, J. J. Uhl, *Vector Measures*, Mathematical Surveys 15, AMS, 1977, Chapter IV, §1
  (the dual of the Lebesgue–Bochner space `Lᵠ(μ; X)` is `Lᵖ(μ; X⋆)` when `X⋆` has the
  Radon–Nikodým property, for instance when `X` is reflexive).
-/

public section

open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}

variable [SigmaFinite μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-! ### Functionals on `Lᵠ` with values in a Hilbert space -/

section StrongDual

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [SigmaFinite μ] in
/-- The pairing of `g ∈ Lᵖ(μ; H⋆)` with `f ∈ Lᵠ(μ; H)` is the integral of the inner product of
the pointwise Riesz representative of `g` with `f`. -/
private theorem lpPairing_id_eq_integral_inner (g : Lp (StrongDual 𝕜 H) p μ) (f : Lp H q μ) :
    (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q g f =
      ∫ x, ⟪(InnerProductSpace.toDual 𝕜 H).symm (g x), f x⟫_𝕜 ∂μ := by
  simp [ContinuousLinearMap.lpPairing_eq_integral]

/-- **Norming by the Riesz representative.** The norm of `g ∈ Lᵖ(μ; H⋆)` is at most the norm of
the functional `f ↦ ∫ g x (f x) dμ` on `Lᵠ(μ; H)`: the pointwise Riesz representative of `g` is
normed by bounded test functions of finite-measure support. -/
private theorem eLpNorm_le_enorm_lpPairing (g : Lp (StrongDual 𝕜 H) p μ) :
    eLpNorm g p μ ≤ ‖(ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q g‖ₑ := by
  set Λ := (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q g
  set h : α → H := fun x ↦ (InnerProductSpace.toDual 𝕜 H).symm (g x)
  have hh : AEStronglyMeasurable h μ :=
    (InnerProductSpace.toDual 𝕜 H).symm.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable g)
  rw [eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable g) hh (ae_of_all _ fun x ↦ by simp [h])]
  refine hh.eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := 𝕜) (q' := q)
    fun f s hs hfs hf ↦ ?_
  -- A bounded function of finite-measure support is an element of `Lᵠ`.
  have hfq : MemLp f q μ := hf.mono_exponent_of_measure_support_ne_top hfs hs le_top
  have hpair : ∫ x, ⟪h x, f x⟫_𝕜 ∂μ = Λ (hfq.toLp f) := by
    rw [lpPairing_id_eq_integral_inner]
    exact integral_congr_ae (hfq.coeFn_toLp.mono fun x hx ↦ by simp only [h, hx])
  rw [hpair, ← eNorm_toLp hfq]
  exact Λ.le_opENorm _

/-- An element `f ∈ Lᵠ(μ; H)` paired to zero with every `g ∈ Lᵖ(μ; H⋆)` is zero: it is normed by
the Riesz duals of bounded test functions of finite-measure support. -/
private theorem eq_zero_of_forall_lpPairing_eq_zero (f : Lp H q μ)
    (hf : ∀ g : Lp (StrongDual 𝕜 H) p μ,
      (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q g f = 0) :
    f = 0 := by
  have hle : eLpNorm f q μ ≤ 0 := by
    refine (Lp.aestronglyMeasurable f).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := 𝕜)
      (q' := p) fun g s hs hgs hg ↦ ?_
    have hgp : MemLp g p μ := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
    set G : α → StrongDual 𝕜 H := fun x ↦ InnerProductSpace.toDual 𝕜 H (g x)
    have hGp : MemLp G p μ :=
      (InnerProductSpace.toDualMap 𝕜 H).toContinuousLinearMap.comp_memLp' hgp
    -- The pairing of `f` with `g` is the conjugate of the pairing of `G` with `f`, which is zero.
    have hpair : ∫ x, ⟪f x, g x⟫_𝕜 ∂μ = conj
        ((ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q (hGp.toLp G) f) := by
      rw [lpPairing_id_eq_integral_inner, ← integral_conj]
      refine integral_congr_ae (hGp.coeFn_toLp.mono fun x hx ↦ ?_)
      simp [hx, G]
    simp [hpair, hf]
  rw [← norm_eq_zero, Lp.norm_def, nonpos_iff_eq_zero.1 hle, ENNReal.toReal_zero]

variable (𝕜 μ p q) in
/-- The integral pairing `g ↦ (f ↦ ∫ g x (f x) dμ)` as a linear isometry from `Lᵖ(μ; H⋆)` to the
continuous dual of `Lᵠ(μ; H)`, for every pair of Hölder conjugate exponents, including `q = ∞`.
It is onto for `q ≠ ∞` (`MeasureTheory.Lp.strongDualEquiv`). -/
noncomputable def toStrongDual :
    Lp (StrongDual 𝕜 H) p μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp H q μ) where
  toLinearMap := (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q
  norm_map' g := by
    set B := ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)
    rw [ContinuousLinearMap.coe_coe]
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f ↦ ?_) ?_
    · exact (B.norm_lpPairing_apply_apply_le g f).trans
        (by gcongr; exact mul_le_of_le_one_left (norm_nonneg _) ContinuousLinearMap.norm_id_le)
    · rw [← toReal_eNorm g, ← toReal_eNorm (B.lpPairing μ p q g), Lp.eNorm_def]
      exact ENNReal.toReal_mono eNorm_ne_top (eLpNorm_le_enorm_lpPairing g)

/-- Evaluation of the integral pairing between `Lᵖ(μ; H⋆)` and `Lᵠ(μ; H)`. -/
@[simp]
theorem toStrongDual_apply (g : Lp (StrongDual 𝕜 H) p μ) (f : Lp H q μ) :
    toStrongDual 𝕜 μ p q g f = ∫ x, g x (f x) ∂μ := by
  rw [toStrongDual, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.id_apply]

/-- For a finite measure `ν`, every continuous linear functional `φ` on `L¹(ν; H)` is integration
against an essentially bounded `H⋆`-valued function: the pointwise dual of the Riesz
representative of `φ` restricted to `L²(ν; H)`. -/
private theorem exists_toStrongDual_eq_of_isFiniteMeasure {ν : Measure α} [IsFiniteMeasure ν]
    (φ : StrongDual 𝕜 (Lp H 1 ν)) :
    ∃ g : Lp (StrongDual 𝕜 H) ∞ ν, toStrongDual 𝕜 ν ∞ 1 g = φ := by
  -- The Riesz representative `u` of `φ` restricted to `L²(ν; H)` represents `φ` on `L²(ν; H)`.
  set ι : Lp H 2 ν →L[𝕜] Lp H 1 ν := Lp.ofExponentLEL 𝕜 H one_le_two
  set u : Lp H 2 ν := (InnerProductSpace.toDual 𝕜 (Lp H 2 ν)).symm (φ.comp ι)
  have hφ : ∀ (f : Lp H 1 ν) (f' : Lp H 2 ν), (f : α → H) =ᵐ[ν] f' →
      φ f = ∫ x, ⟪u x, f x⟫_𝕜 ∂ν := fun f f' hf => by
    have hfι : f = ι f' := Lp.ext (by simpa only [ι, Lp.coeFn_ofExponentLEL] using hf)
    calc φ f = ⟪u, f'⟫_𝕜 := by
          rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, hfι]
      _ = ∫ x, ⟪u x, f x⟫_𝕜 ∂ν := by
          rw [L2.inner_def]
          exact integral_congr_ae (hf.mono fun x hx => by simp only [hx])
  -- Testing against bounded functions of finite-measure support bounds `‖u‖_∞` by `‖φ‖`.
  have hbound : eLpNorm u ∞ ν ≤ ‖φ‖ₑ :=
    (Lp.aestronglyMeasurable u).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := 𝕜) (q' := 1)
      fun g s hs hgs hg => by
        have hg₁ : MemLp g 1 ν := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
        have hg₂ : MemLp g 2 ν := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
        have hpair : ∫ x, ⟪u x, g x⟫_𝕜 ∂ν = φ (hg₁.toLp g) := by
          rw [hφ _ (hg₂.toLp g) (hg₁.coeFn_toLp.trans hg₂.coeFn_toLp.symm)]
          exact integral_congr_ae (hg₁.coeFn_toLp.mono fun x hx => by simp only [hx])
        rw [hpair, ← eNorm_toLp hg₁]
        exact φ.le_opENorm _
  have hu_top : MemLp u ∞ ν := memLp_iff.2 (hbound.trans_lt eNorm_lt_top)
  set G : α → StrongDual 𝕜 H := fun x ↦ InnerProductSpace.toDual 𝕜 H (u x)
  have hG : MemLp G ∞ ν :=
    (InnerProductSpace.toDualMap 𝕜 H).toContinuousLinearMap.comp_memLp' hu_top
  refine ⟨hG.toLp G, ContinuousLinearMap.ext fun f => ?_⟩
  -- Both functionals are continuous, and they agree on indicator functions.
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hs hμs =>
    rw [Lp.simpleFunc.coe_indicatorConst, toStrongDual_apply,
      hφ _ (indicatorConstLp 2 hs hμs.ne c)
        (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)]
    exact integral_congr_ae (by filter_upwards [hG.coeFn_toLp] with x hx; simp [hx, G])
  | add _ _ _ hf hg => rw [map_add, map_add, hf, hg]
  | isClosed => exact isClosed_eq (ContinuousLinearMap.continuous _) φ.continuous

/-- **The dual of `L¹(μ; H)`.** On a σ-finite measure space, every continuous linear functional on
`L¹(μ; H)` is integration against an essentially bounded `H⋆`-valued function. -/
private theorem exists_toStrongDual_eq (φ : StrongDual 𝕜 (Lp H 1 μ)) :
    ∃ g : Lp (StrongDual 𝕜 H) ∞ μ, toStrongDual 𝕜 μ ∞ 1 g = φ := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  -- A positive weight `w` with finite integral makes `ν = w μ` a finite measure with the null sets
  -- of `μ`.
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  have hw0' : ∀ᵐ x ∂μ, w x ≠ 0 := .of_forall fun x ↦ (hw0 x).ne'
  set ν := μ.withDensity fun x ↦ (w x : ℝ≥0∞)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hwi.trans ENNReal.one_lt_top).ne
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hwm.coe_nnreal_ennreal.aemeasurable
    (hw0'.mono fun x hx ↦ ENNReal.coe_ne_zero.2 hx)
  -- Multiplication by `w` is a linear isometric equivalence `T` from `L¹(ν; H)` onto `L¹(μ; H)`,
  -- and the functional `φ ∘ T` on `L¹(ν; H)` has a density `g ∈ L^∞(ν; H⋆)`.
  set T : Lp H 1 ν ≃ₗᵢ[𝕜] Lp H 1 μ := withDensitySMulLIE 𝕜 hwm hw0'
  obtain ⟨g, hg⟩ := exists_toStrongDual_eq_of_isFiniteMeasure (φ.comp (T : Lp H 1 ν →L[𝕜] _))
  have hgμ : MemLp g ∞ μ := (Lp.memLp g).mono_ac_top hμν
  refine ⟨hgμ.toLp g, ContinuousLinearMap.ext fun f ↦ ?_⟩
  -- Write `f = T u`; then `φ f = ∫ g u dν = ∫ g (w u) dμ`.
  obtain ⟨u, rfl⟩ := T.surjective f
  calc toStrongDual 𝕜 μ ∞ 1 (hgμ.toLp g) (T u)
      = ∫ x, (w x : ℝ) • g x (u x) ∂μ := by
        rw [toStrongDual_apply]
        refine integral_congr_ae ?_
        have hTu := coeFn_withDensitySMulLI hwm u
        rw [← coe_withDensitySMulLIE 𝕜 hwm hw0'] at hTu
        filter_upwards [hgμ.coeFn_toLp, hTu] with x h₁ h₂
        rw [h₁, h₂, NNReal.smul_def, map_real_smul (g x) (g x).continuous]
    _ = ∫ x, g x (u x) ∂ν := (integral_withDensity_eq_integral_smul hwm _).symm
    _ = toStrongDual 𝕜 ν ∞ 1 g u := (toStrongDual_apply g u).symm
    _ = φ (T u) := by
        rw [hg, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv]

private theorem toStrongDual_surjective (hq_top : q ≠ ∞) :
    Function.Surjective (toStrongDual 𝕜 μ p q (H := H)) := by
  rcases (Fact.out : 1 ≤ q).eq_or_lt with rfl | hq
  · obtain rfl : p = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).2 rfl
    exact exists_toStrongDual_eq
  -- `Lᵠ(μ; H)` is reflexive, since `H` is uniformly convex.
  have : UniformConvexSpace H := by
    let := InnerProductSpace.rclikeToReal 𝕜 H
    infer_instance
  refine LinearIsometry.surjective_of_surjective_inclusionInDoubleDual _
    (surjective_inclusionInDoubleDual (𝕜 := 𝕜) (μ := μ) hq hq_top)
    fun f hf ↦ eq_zero_of_forall_lpPairing_eq_zero (𝕜 := 𝕜) (p := p) f fun g ↦ hf g

variable (𝕜 μ p q) in
/-- **Duality of Lebesgue–Bochner spaces with values in a Hilbert space.** On a σ-finite measure
space, for Hölder conjugate exponents with `1 ≤ q < ∞` and a Hilbert space `H`, the integral
pairing `g ↦ (f ↦ ∫ g x (f x) dμ)` identifies `Lᵖ(μ; H⋆)`, `H⋆ = StrongDual 𝕜 H`, linearly and
isometrically with the continuous dual of `Lᵠ(μ; H)`. -/
noncomputable def strongDualEquiv (hq_top : q ≠ ∞) :
    Lp (StrongDual 𝕜 H) p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp H q μ) :=
  LinearIsometryEquiv.ofSurjective _ (toStrongDual_surjective hq_top)

/-- The integral representation equivalence for `Lᵠ(μ; H)` is the integral pairing
`MeasureTheory.Lp.toStrongDual`. -/
@[simp]
theorem coe_strongDualEquiv (hq_top : q ≠ ∞) :
    ⇑(strongDualEquiv 𝕜 μ p q hq_top) = toStrongDual 𝕜 μ p q (H := H) :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- Evaluation of the integral representation of functionals on `Lᵠ(μ; H)`. -/
theorem strongDualEquiv_apply (hq_top : q ≠ ∞) (g : Lp (StrongDual 𝕜 H) p μ) (f : Lp H q μ) :
    strongDualEquiv 𝕜 μ p q hq_top g f = ∫ x, g x (f x) ∂μ := by
  rw [coe_strongDualEquiv, toStrongDual_apply]

/-- The representing density of a functional on `Lᵠ(μ; H)` integrates to its value on every
`f ∈ Lᵠ(μ; H)`. -/
@[simp]
theorem integral_strongDualEquiv_symm_apply (hq_top : q ≠ ∞) (Λ : StrongDual 𝕜 (Lp H q μ))
    (f : Lp H q μ) :
    ∫ x, (strongDualEquiv 𝕜 μ p q hq_top).symm Λ x (f x) ∂μ = Λ f := by
  rw [← strongDualEquiv_apply hq_top, LinearIsometryEquiv.apply_symm_apply]

end StrongDual

/-! ### Scalar functionals on `Lᵠ` -/

/-- **Riesz representation of `(Lᵠ)⋆`.** On a σ-finite measure space, every continuous scalar
functional on `Lᵠ` is integration against an `Lᵖ` function, for Hölder conjugate exponents with
`1 ≤ q < ∞`. -/
theorem toDual_surjective (hq_top : q ≠ ∞) : Function.Surjective (toDual 𝕜 μ p q) := by
  -- This is the case `H = 𝕜`: a density `G` with values in `𝕜⋆` gives the scalar density
  -- `x ↦ G x 1`.
  intro φ
  obtain ⟨G, rfl⟩ := toStrongDual_surjective (H := 𝕜) (p := p) hq_top φ
  refine ⟨(ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compLp G, ContinuousLinearMap.ext fun f ↦ ?_⟩
  rw [toDual_apply, toStrongDual_apply]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).coeFn_compLp' G] with x hx
  -- A scalar functional is multiplication by its value at `1`.
  conv_rhs => rw [← (G x).toSpanSingleton_apply_map_one, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hx, ContinuousLinearMap.apply_apply, smul_eq_mul, mul_comm]

variable (𝕜 μ p q) in
/-- The norm-preserving integral representation of the continuous dual of `Lᵠ` by `Lᵖ`, for
Hölder conjugate exponents with `1 ≤ q < ∞`. -/
noncomputable def dualEquiv (hq_top : q ≠ ∞) : Lp 𝕜 p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q μ) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 μ p q) (toDual_surjective hq_top)

/-- The integral representation equivalence is the integral pairing `MeasureTheory.Lp.toDual`. -/
@[simp]
theorem coe_dualEquiv (hq_top : q ≠ ∞) : ⇑(dualEquiv 𝕜 μ p q hq_top) = toDual 𝕜 μ p q :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- Evaluation of the integral representation equivalence. -/
theorem dualEquiv_apply (hq_top : q ≠ ∞) (g : Lp 𝕜 p μ) (f : Lp 𝕜 q μ) :
    dualEquiv 𝕜 μ p q hq_top g f = ∫ x, g x * f x ∂μ := by
  rw [coe_dualEquiv, toDual_apply]

/-- The representing density of a functional integrates to its value on every `Lᵠ` function. -/
@[simp]
theorem integral_dualEquiv_symm_mul (hq_top : q ≠ ∞) (Λ : StrongDual 𝕜 (Lp 𝕜 q μ))
    (f : Lp 𝕜 q μ) : ∫ x, (dualEquiv 𝕜 μ p q hq_top).symm Λ x * f x ∂μ = Λ f := by
  rw [← dualEquiv_apply hq_top, LinearIsometryEquiv.apply_symm_apply]

/-- **Representation of functionals on `(Lᵠ)ᶥ`.** Let `b` be a finite orthonormal basis of a real
inner product space `E`. A continuous functional `Λ` on `(Lᵠ)ᶥ` is `g ↦ ∑ᵢ ∫ ⟪H, bᵢ⟫ gᵢ` for a
field `H ∈ Lᵖ(α; E)` with `‖H‖_{Lᵖ} ≤ |ι| ‖Λ‖`. -/
theorem exists_memLp_forall_dual_pi_apply_eq {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hq_top : q ≠ ∞) (b : OrthonormalBasis ι ℝ E)
    (Λ : StrongDual ℝ (ι → Lp ℝ q μ)) :
    ∃ H : α → E, MemLp H p μ ∧ eLpNorm H p μ ≤ Fintype.card ι * ENNReal.ofReal ‖Λ‖ ∧
      ∀ g, Λ g = ∑ i, ∫ x, ⟪H x, b i⟫_ℝ * g i x ∂μ := by
  classical
  let Λc : ι → StrongDual ℝ (Lp ℝ q μ) := fun i =>
    Λ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => Lp ℝ q μ) i)
  let Hc : ι → Lp ℝ p μ := fun i => (dualEquiv ℝ μ p q hq_top).symm (Λc i)
  have hHc (i : ι) : ‖Hc i‖ ≤ ‖Λ‖ := by
    simp only [Hc, LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    calc ‖Λc i g‖ ≤ ‖Λ‖ * ‖Pi.single (M := fun _ : ι => Lp ℝ q μ) i g‖ := Λ.le_opNorm _
      _ = ‖Λ‖ * ‖g‖ := by rw [Pi.norm_single]
  have hHi (i : ι) : MemLp (fun x => (Hc i : α → ℝ) x • b i) p μ :=
    (Lp.memLp (Hc i)).smul (memLp_top_const (b i))
  have hsum : (fun x => ∑ i, (Hc i : α → ℝ) x • b i) = ∑ i, fun x => (Hc i : α → ℝ) x • b i :=
    (Finset.sum_fn _ _).symm
  have hinner (x : α) (i : ι) : ⟪∑ j, (Hc j : α → ℝ) x • b j, b i⟫_ℝ = Hc i x := by
    simp [sum_inner, real_inner_smul_left, b.inner_eq_ite]
  refine ⟨fun x => ∑ i, (Hc i : α → ℝ) x • b i, ?_, ?_, fun g => ?_⟩
  · rw [hsum]
    exact memLp_finsetSum' Finset.univ fun i _ => hHi i
  · calc eLpNorm (fun x => ∑ i, (Hc i : α → ℝ) x • b i) p μ
        ≤ ∑ i, eLpNorm (fun x => (Hc i : α → ℝ) x • b i) p μ := by
          rw [hsum]
          exact eLpNorm_sum_le Fact.out
      _ ≤ ∑ _i : ι, ENNReal.ofReal ‖Λ‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [eLpNorm_congr_norm_ae (hHi i).aestronglyMeasurable (Lp.aestronglyMeasurable (Hc i))
            (ae_of_all _ fun x => by rw [norm_smul, b.orthonormal.1 i, mul_one]), ← Lp.eNorm_def,
            ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hHc i)
      _ = Fintype.card ι * ENNReal.ofReal ‖Λ‖ := by simp
  · conv_lhs => rw [← Finset.univ_sum_single g]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hinner]
    exact (integral_dualEquiv_symm_mul (p := p) hq_top (Λc i) (g i)).symm

end MeasureTheory.Lp
