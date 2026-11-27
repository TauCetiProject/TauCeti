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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Lp.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.Lp.Exponent

/-!
# Representation of continuous functionals on `Lᵖ`

On a σ-finite measure space, the integral pairing identifies the continuous dual of `Lᵠ`
with `Lᵖ` for conjugate exponents `1 ≤ q < ∞`, including the endpoint `L¹(μ)⋆ = L^∞(μ)`. The
isometric embedding is supplied by `MeasureTheory.Lp.toDual`. For `1 < q`, surjectivity follows
from reflexivity of `Lᵠ`: a functional annihilating the closed range is evaluation at an `Lᵠ`
function, which must vanish by the injectivity of the reversed integral pairing.

For `q = 1` and a finite measure, the density of `φ ∈ L¹(μ)⋆` is found in `L²(μ)`. As `L²(μ)` maps
continuously into `L¹(μ)` (`MeasureTheory.Lp.ofExponentLEL`), `φ` restricts to a continuous linear
functional on `L²(μ)`. The Riesz representation theorem writes it as `f ↦ ∫ h f` for some
`h ∈ L²(μ)`. Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le`), and density
of simple functions in `L¹(μ)` gives `φ f = ∫ h f` for every `f ∈ L¹(μ)`. A σ-finite measure `μ`
has a positive weight `w` with `∫ w dμ < ∞`
(`MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite`), and `ν = w μ` is a finite measure with
the same null sets as `μ`. Multiplication by `w` maps `L¹(ν)` isometrically onto `L¹(μ)`
(`MeasureTheory.withDensitySMulLI`), so `φ` pulls back to a functional on `L¹(ν)`, whose density
`g ∈ L^∞(ν) = L^∞(μ)` represents `φ`: `φ (w u) = ∫ g u dν = ∫ g (w u) dμ`. Some hypothesis on `μ`
is needed: for the measure on a point that gives it infinite mass, `L¹(μ) = 0` while
`L^∞(μ) = 𝕜`.

This representation passes distributional test-function bounds to actual `Lᵖ` weak derivatives.

The same holds for functions with values in a Hilbert space `H`, where `Lᵖ(μ; H⋆)` represents the
continuous dual of `Lᵠ(μ; H)` by `g ↦ (f ↦ ∫ g x (f x) dμ)`, with `H⋆ = StrongDual 𝕜 H`
(`MeasureTheory.Lp.strongDualEquiv`). The pairing is bilinear, with no complex conjugation. Its
norm is computed by testing against the pointwise Riesz representative of `g`, and surjectivity
again follows from reflexivity of `Lᵠ(μ; H)`, which is uniformly convex.

For a real inner product space `E` with a finite orthonormal basis `b`, the dual of the product
`(Lᵠ)ᶥ` is represented by `Lᵖ(α; E)`: a functional `Λ` is `g ↦ ∑ᵢ ∫ ⟪H, bᵢ⟫ gᵢ` for a field
`H ∈ Lᵖ` with `‖H‖_{Lᵖ} ≤ |ι| ‖Λ‖` (`MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`).

## Main declarations

* `MeasureTheory.Lp.toDual_surjective`: for `1 ≤ q < ∞`, every continuous linear functional on
  `Lᵠ(μ)` is integration against some `g ∈ Lᵖ(μ)`.
* `MeasureTheory.Lp.dualEquiv`: the isometric isomorphism `Lᵖ(μ) ≃ (Lᵠ(μ))⋆` for `1 ≤ q < ∞`.
* `MeasureTheory.Lp.strongDualEquiv`: the isometric isomorphism `Lᵖ(μ; H⋆) ≃ (Lᵠ(μ; H))⋆` for a
  Hilbert space `H`.
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

/-! ### The dual of `L¹` -/

section L1

open scoped NNReal ComplexConjugate

/-- For a finite measure, every continuous linear functional on `L¹(μ)` is integration against
an essentially bounded function. -/
private theorem exists_toDual_eq_of_isFiniteMeasure [IsFiniteMeasure μ]
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, toDual 𝕜 μ ∞ 1 g = φ := by
  -- The Riesz representation `h` of `φ` restricted to `L²(μ)` represents `φ` on `L²(μ)`.
  set ι : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ := Lp.ofExponentLEL 𝕜 𝕜 one_le_two
  set u : Lp 𝕜 2 μ := (InnerProductSpace.toDual 𝕜 (Lp 𝕜 2 μ)).symm (φ.comp ι)
  set h : α → 𝕜 := fun x => conj (u x)
  have hφ : ∀ (f : Lp 𝕜 1 μ) (f' : Lp 𝕜 2 μ), (f : α → 𝕜) =ᵐ[μ] f' →
      φ f = ∫ x, h x * f x ∂μ := fun f f' hf => by
    have hfι : f = ι f' := Lp.ext (by simpa only [ι, Lp.coeFn_ofExponentLEL] using hf)
    calc φ f = inner 𝕜 u f' := by
          rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, hfι]
      _ = ∫ x, h x * f x ∂μ := by
          rw [L2.inner_def]
          refine integral_congr_ae (hf.mono fun x hx => ?_)
          simp [h, hx, mul_comm]
  -- Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`.
  have hint : Integrable h μ := (Lp.memLp u).star.integrable one_le_two
  have hbound : eLpNorm h ∞ μ ≤ ‖φ‖ₑ :=
    hint.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le fun σ hσ =>
      have hσ₂ := σ.memLp_of_isFiniteMeasure 2 μ
      enorm_integral_mul_le_of_apply_eq φ hσ
        (hφ _ (hσ₂.toLp σ) (hσ.coeFn_toLp.trans hσ₂.coeFn_toLp.symm))
  have hh : MemLp h ∞ μ := memLp_iff.2 (hbound.trans_lt eNorm_lt_top)
  refine ⟨hh.toLp h, ContinuousLinearMap.ext fun f => ?_⟩
  -- Both functionals are continuous, and they agree on indicator functions.
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hs hμs =>
    rw [toDual_apply, Lp.simpleFunc.coe_indicatorConst,
      hφ _ (indicatorConstLp 2 hs hμs.ne c)
        (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)]
    exact integral_congr_ae (by filter_upwards [hh.coeFn_toLp] with x hx; rw [hx])
  | add _ _ _ hf hg => rw [map_add, map_add, hf, hg]
  | isClosed => exact isClosed_eq (ContinuousLinearMap.continuous _) φ.continuous

/-- Multiplication by a weight `w`, from `L¹(w μ)` to `L¹(μ)`, commutes with scalars of `𝕜`. -/
private theorem withDensitySMulLI_smul {w : α → ℝ≥0} (hw : Measurable w) (c : 𝕜)
    (u : Lp 𝕜 1 (μ.withDensity fun x ↦ (w x : ℝ≥0∞))) :
    withDensitySMulLI μ hw (c • u) = c • withDensitySMulLI μ hw u := by
  ext1
  filter_upwards [(ae_withDensity_iff hw.coe_nnreal_ennreal).1 (Lp.coeFn_smul c u),
    (memL1_smul_of_L1_withDensity hw (c • u)).coeFn_toLp,
    Lp.coeFn_smul c (withDensitySMulLI μ hw u),
    (memL1_smul_of_L1_withDensity hw u).coeFn_toLp] with x h₁ h₂ h₃ h₄
  rw [withDensitySMulLI_apply, h₂, h₃, Pi.smul_apply, withDensitySMulLI_apply, h₄]
  rcases eq_or_ne (w x) 0 with hx | hx
  · simp [hx]
  · rw [h₁ (ENNReal.coe_ne_zero.2 hx), Pi.smul_apply, smul_comm]

/-- Multiplication by a positive weight `w` maps `L¹(w μ)` onto `L¹(μ)`. -/
private theorem withDensitySMulLI_surjective {w : α → ℝ≥0} (hw : Measurable w)
    (hw0 : ∀ x, w x ≠ 0) : Function.Surjective (withDensitySMulLI μ (E := 𝕜) hw) := by
  intro f
  have hμν : μ ≪ μ.withDensity fun x ↦ (w x : ℝ≥0∞) := withDensity_absolutelyContinuous'
    hw.coe_nnreal_ennreal.aemeasurable (.of_forall fun x ↦ ENNReal.coe_ne_zero.2 (hw0 x))
  have hcancel (x : α) (y : 𝕜) : w x • (w x : ℝ)⁻¹ • y = y := by
    rw [NNReal.smul_def, smul_inv_smul₀ (NNReal.coe_ne_zero.2 (hw0 x))]
  have hu : MemLp (fun x ↦ (w x : ℝ)⁻¹ • f x) 1 (μ.withDensity fun x ↦ (w x : ℝ≥0∞)) :=
    memLp_one_iff_integrable.2 <| (integrable_withDensity_iff_integrable_smul hw).2 <|
      (memLp_one_iff_integrable.1 (Lp.memLp f)).congr (.of_forall fun x ↦ (hcancel x _).symm)
  refine ⟨hu.toLp _, Lp.ext ?_⟩
  filter_upwards [(memL1_smul_of_L1_withDensity hw (hu.toLp _)).coeFn_toLp,
    hμν.ae_le hu.coeFn_toLp] with x h₁ h₂
  rw [withDensitySMulLI_apply, h₁, h₂, hcancel]

/-- **The dual of `L¹`.** On a σ-finite measure space, every continuous linear functional on
`L¹(μ)` is integration against an essentially bounded function. -/
private theorem exists_toDual_eq [SigmaFinite μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, toDual 𝕜 μ ∞ 1 g = φ := by
  -- A positive weight `w` with finite integral makes `ν = w μ` a finite measure with the null sets
  -- of `μ`.
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set ν := μ.withDensity fun x ↦ (w x : ℝ≥0∞)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hwi.trans ENNReal.one_lt_top).ne
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hwm.coe_nnreal_ennreal.aemeasurable
    (.of_forall fun x ↦ ENNReal.coe_ne_zero.2 (hw0 x).ne')
  -- Multiplication by `w` is a continuous `𝕜`-linear map `T` from `L¹(ν)` onto `L¹(μ)`, and
  -- the functional `φ ∘ T` on `L¹(ν)` has a density `g ∈ L^∞(ν)`.
  set T : Lp 𝕜 1 ν →L[𝕜] Lp 𝕜 1 μ :=
    { toFun := withDensitySMulLI μ hwm
      map_add' := map_add _
      map_smul' := withDensitySMulLI_smul hwm
      cont := (withDensitySMulLI μ hwm).continuous }
  obtain ⟨g, hg⟩ := exists_toDual_eq_of_isFiniteMeasure (φ.comp T)
  have hgμ : MemLp g ∞ μ := (Lp.memLp g).mono_ac_top hμν
  refine ⟨hgμ.toLp g, ContinuousLinearMap.ext fun f ↦ ?_⟩
  -- Write `f = T u`; then `φ f = ∫ g u dν = ∫ g (w u) dμ`.
  obtain ⟨u, rfl⟩ := withDensitySMulLI_surjective hwm (fun x ↦ (hw0 x).ne') f
  calc toDual 𝕜 μ ∞ 1 (hgμ.toLp g) (withDensitySMulLI μ hwm u)
      = ∫ x, (w x : ℝ) • (g x * u x) ∂μ := by
        rw [toDual_apply]
        refine integral_congr_ae ?_
        filter_upwards [hgμ.coeFn_toLp, (memL1_smul_of_L1_withDensity hwm u).coeFn_toLp]
          with x h₁ h₂
        rw [h₁, withDensitySMulLI_apply, h₂, mul_smul_comm, NNReal.smul_def]
    _ = ∫ x, g x * u x ∂ν := (integral_withDensity_eq_integral_smul hwm _).symm
    _ = φ (withDensitySMulLI μ hwm u) := by rw [← toDual_apply, hg]; rfl

end L1

variable [SigmaFinite μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- **Riesz representation of `(Lᵠ)⋆`.** On a σ-finite measure space, every continuous scalar
functional on `Lᵠ` is integration against an `Lᵖ` function, for Hölder conjugate exponents with
`1 ≤ q < ∞`. -/
theorem toDual_surjective (hq_top : q ≠ ∞) : Function.Surjective (toDual 𝕜 μ p q) := by
  rcases (Fact.out : 1 ≤ q).eq_or_lt with rfl | hq
  · obtain rfl : p = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).2 rfl
    exact exists_toDual_eq
  exact LinearIsometry.surjective_of_surjective_inclusionInDoubleDual _
    (surjective_inclusionInDoubleDual (E := 𝕜) hq hq_top) fun f hf ↦
    (toDual 𝕜 μ q p).injective <| ContinuousLinearMap.ext fun g ↦ by
      rw [map_zero, zero_apply, toDual_apply]
      simpa only [toDual_apply, mul_comm] using hf g

variable (𝕜 μ p q) in
/-- The norm-preserving integral representation of the continuous dual of `Lᵠ` by `Lᵖ`, for
Hölder conjugate exponents with `1 ≤ q < ∞`. -/
noncomputable def dualEquiv (hq_top : q ≠ ∞) : Lp 𝕜 p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q μ) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 μ p q) (toDual_surjective hq_top)

/-- Evaluation of the integral representation equivalence. -/
theorem dualEquiv_apply (hq_top : q ≠ ∞) (g : Lp 𝕜 p μ) (f : Lp 𝕜 q μ) :
    dualEquiv 𝕜 μ p q hq_top g f = ∫ x, g x * f x ∂μ :=
  toDual_apply g f

@[simp]
theorem coe_dualEquiv (hq_top : q ≠ ∞) : ⇑(dualEquiv 𝕜 μ p q hq_top) = toDual 𝕜 μ p q := by
  funext g
  ext f
  exact (dualEquiv_apply hq_top g f).trans (toDual_apply g f).symm

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

/-! ### Functionals on `Lᵠ` with values in a Hilbert space -/

section StrongDual

open scoped InnerProductSpace ComplexConjugate

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
    have hGp : MemLp G p μ := hgp.congr_norm
      ((InnerProductSpace.toDual 𝕜 H).continuous.comp_aestronglyMeasurable hgp.aestronglyMeasurable)
      (ae_of_all _ fun x ↦ by simp [G])
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
continuous dual of `Lᵠ(μ; H)`. -/
private noncomputable def toStrongDual :
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

private theorem toStrongDual_apply (g : Lp (StrongDual 𝕜 H) p μ) (f : Lp H q μ) :
    toStrongDual 𝕜 μ p q g f = (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 H)).lpPairing μ p q g f :=
  rfl

private theorem toStrongDual_surjective (hq : 1 < q) (hq_top : q ≠ ∞) :
    Function.Surjective (toStrongDual 𝕜 μ p q (H := H)) := by
  -- `Lᵠ(μ; H)` is reflexive, since `H` is uniformly convex.
  have : UniformConvexSpace H := by
    let := InnerProductSpace.rclikeToReal 𝕜 H
    infer_instance
  refine LinearIsometry.surjective_of_surjective_inclusionInDoubleDual _
    (surjective_inclusionInDoubleDual (𝕜 := 𝕜) (μ := μ) hq hq_top)
    fun f hf ↦ eq_zero_of_forall_lpPairing_eq_zero (𝕜 := 𝕜) (p := p) f fun g ↦ ?_
  rw [← toStrongDual_apply]
  exact hf g

variable (𝕜 μ p q) in
/-- **Duality of Lebesgue–Bochner spaces with values in a Hilbert space.** On a σ-finite measure
space, for Hölder conjugate exponents `1 < p, q < ∞` and a Hilbert space `H`, the integral pairing
`g ↦ (f ↦ ∫ g x (f x) dμ)` identifies `Lᵖ(μ; H⋆)`, `H⋆ = StrongDual 𝕜 H`, linearly and
isometrically with the continuous dual of `Lᵠ(μ; H)`. -/
noncomputable def strongDualEquiv (hq : 1 < q) (hq_top : q ≠ ∞) :
    Lp (StrongDual 𝕜 H) p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp H q μ) :=
  LinearIsometryEquiv.ofSurjective _ (toStrongDual_surjective hq hq_top)

/-- Evaluation of the integral representation of functionals on `Lᵠ(μ; H)`. -/
@[simp]
theorem strongDualEquiv_apply (hq : 1 < q) (hq_top : q ≠ ∞) (g : Lp (StrongDual 𝕜 H) p μ)
    (f : Lp H q μ) :
    strongDualEquiv 𝕜 μ p q hq hq_top g f = ∫ x, g x (f x) ∂μ := by
  rw [strongDualEquiv, LinearIsometryEquiv.coe_ofSurjective, toStrongDual_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.id_apply]

/-- The representing density of a functional on `Lᵠ(μ; H)` integrates to its value on every
`f ∈ Lᵠ(μ; H)`. -/
@[simp]
theorem integral_strongDualEquiv_symm_apply (hq : 1 < q) (hq_top : q ≠ ∞)
    (Λ : StrongDual 𝕜 (Lp H q μ)) (f : Lp H q μ) :
    ∫ x, (strongDualEquiv 𝕜 μ p q hq hq_top).symm Λ x (f x) ∂μ = Λ f := by
  rw [← strongDualEquiv_apply hq hq_top, LinearIsometryEquiv.apply_symm_apply]

end StrongDual

end MeasureTheory.Lp
