/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.LpSection.Basic
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Multiplication of `Lᵖ` sections by essentially bounded functions

Let `E → B` be a vector bundle over `𝕜 = ℝ` or `ℂ` whose fibres carry norms varying continuously
over the total space, and let `μ` be a measure on the base. An essentially bounded scalar function
`φ ∈ L^∞(μ)` multiplies a section `f ∈ Lᵖ(E, μ)` pointwise, `(φ • f) x = φ x • f x`
(`TauCeti.LpSection.coeFn_lpSMul`), and

`‖φ • f‖_{Lᵖ} ≤ ‖φ‖_{L^∞} ‖f‖_{Lᵖ}`

(`TauCeti.LpSection.norm_lpSMul_le`). This is the action of Mathlib's `L^∞(μ)` on the `Lᵖ` spaces
of `MeasureTheory.Lp` (in `Mathlib.MeasureTheory.Function.Holder`) carried over to sections of a
vector bundle. It makes `Lᵖ(E, μ)` a module over the ring `L^∞(μ)`, and gives a continuous
bilinear map `TauCeti.LpSection.lpSMulL` whose value at `φ` is the multiplication operator `M_φ`
of norm at most `‖φ‖_{L^∞}`.

On `L²` sections of a bundle with fibre inner products, `⟪φ • f, g⟫ = ⟪f, star φ • g⟫`, so the
adjoint of `M_φ` is `M_{star φ}` (`TauCeti.LpSection.adjoint_lpSMulL`), where `star φ` is the
complex conjugate function. For finitely many `χ i ∈ L^∞(μ)` with
`∑ i, |χ i x|² = 1` almost everywhere, for instance the cutoffs of a square partition of unity
`∑ i, χ i ² = 1`, a section is recovered from its localizations,

`∑ i, star (χ i) • (χ i • f) = f` (`TauCeti.LpSection.sum_star_lpSMul_lpSMul`),

and its `L²` norm splits as `‖f‖² = ∑ i, ‖χ i • f‖²`
(`TauCeti.LpSection.sum_norm_lpSMul_sq`). For the indicator functions `1_U` and `1_{Uᶜ}` of a
measurable set and of its complement this is `‖f‖² = ‖1_U • f‖² + ‖1_{Uᶜ} • f‖²`.

For the trivial bundle with fibre `ℂ`-Hilbert space and `p = 2` these are the multiplication
operators `MeasureTheory.Lp.multiplicationOperator` on `MeasureTheory.Lp`.

## Main declarations

* `TauCeti.AEStronglyMeasurableSection.smul` (in `LpSection/Measurable.lean`): the product of a
  measurable scalar function and a measurable section is measurable.
* The `Module (Lp 𝕜 ∞ μ) (LpSection 𝕜 F E p μ)` instance, with `TauCeti.LpSection.coeFn_lpSMul`,
  and the `IsScalarTower` and `SMulCommClass` instances relating it to the action of `𝕜`.
* `TauCeti.LpSection.norm_lpSMul_le`: `‖φ • f‖ ≤ ‖φ‖ ‖f‖`.
* The `IsBoundedSMul` instance, and `TauCeti.LpSection.lpSMulL`: multiplication as a continuous
  bilinear map, Mathlib's `ContinuousLinearMap.lsmul` for this action, with the composition laws
  `TauCeti.LpSection.lpSMulL_mul` and `TauCeti.LpSection.lpSMulL_one`.
* `TauCeti.LpSection.inner_lpSMul_left`, `inner_lpSMul_right` and `adjoint_lpSMulL`:
  `M_φ† = M_{star φ}`.
* `TauCeti.LpSection.sum_star_lpSMul_lpSMul` and `TauCeti.LpSection.sum_norm_lpSMul_sq`:
  reconstruction and the norm identity for families with `∑ i, |χ i|² = 1`.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §VIII.3
  (multiplication operators).
-/

public section

noncomputable section

open Bundle MeasureTheory Filter
open scoped ENNReal InnerProductSpace

variable {𝕜 B F : Type*} [RCLike 𝕜] [TopologicalSpace B] [MeasurableSpace B]
  [OpensMeasurableSpace B] [SecondCountableTopology B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] {p : ℝ≥0∞} {μ : Measure B}

namespace TauCeti

namespace LpSection

section Normed

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]

variable (φ ψ : Lp 𝕜 ∞ μ) (f g : LpSection 𝕜 F E p μ)

omit [TopologicalSpace B] [OpensMeasurableSpace B] [SecondCountableTopology B] in
/-- The pointwise product of an essentially bounded function and a section with `p`-integrable
fibre norm has `p`-integrable fibre norm. -/
theorem memLp_norm_lpSMul {s : ∀ x, E x} (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    MemLp (fun x ↦ ‖φ x • s x‖) p μ :=
  (hsp.const_mul ‖φ‖).of_le
    (((Lp.aestronglyMeasurable φ).norm.mul hsp.aestronglyMeasurable).congr
      (.of_forall fun x ↦ (norm_smul _ _).symm))
    ((Lp.ae_norm_le_norm_top φ).mono fun x hx ↦ by
      rw [norm_norm, norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- **Multiplication by essentially bounded functions.** An `L^∞` function `φ` multiplies an `Lᵖ`
section `f` pointwise: `(φ • f) x = φ x • f x` almost everywhere
(`TauCeti.LpSection.coeFn_lpSMul`). -/
instance : SMul (Lp 𝕜 ∞ μ) (LpSection 𝕜 F E p μ) where
  smul φ f := mk (fun x ↦ φ x • f x)
    (f.aestronglyMeasurableSection.smul (Lp.aestronglyMeasurable φ))
    (memLp_norm_lpSMul φ f.memLp_norm)

@[simp]
theorem mk_lpSMul {s : ∀ x, E x} (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    φ • mk s hs hsp =
      mk (fun x ↦ φ x • s x) (hs.smul (Lp.aestronglyMeasurable φ)) (memLp_norm_lpSMul φ hsp) :=
  mk_eq_mk_iff.2 ((coeFn_mk hs hsp).mono fun x hx ↦ by rw [hx])

theorem coeFn_lpSMul : ∀ᵐ x ∂μ, (φ • f) x = φ x • f x :=
  coeFn_mk _ _

/-- `‖φ • f‖_{Lᵖ} ≤ ‖φ‖_{L^∞} ‖f‖_{Lᵖ}`. -/
theorem norm_lpSMul_le : ‖φ • f‖ ≤ ‖φ‖ * ‖f‖ := by
  have hle : eLpNorm (fun x ↦ ‖(φ • f) x‖) p μ ≤
      ENNReal.ofReal ‖φ‖ * eLpNorm (fun x ↦ ‖f x‖) p μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (aestronglyMeasurable_norm _) ?_ p
    filter_upwards [coeFn_lpSMul φ f, Lp.ae_norm_le_norm_top φ] with x hx hφ
    rw [hx, norm_norm, norm_norm, norm_smul]
    exact mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
  rw [norm_def, norm_def f, ← ENNReal.toReal_ofReal (norm_nonneg φ), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    f.memLp_norm.eLpNorm_ne_top) hle

/-- `L^∞(μ)` acts on `Lᵖ` sections as a module, by pointwise multiplication. -/
instance : Module (Lp 𝕜 ∞ μ) (LpSection 𝕜 F E p μ) where
  one_smul f := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul 1 f, Lp.coeFn_one (E := 𝕜) (μ := μ)] with x h₁ h₂
    rw [h₁, h₂, Pi.one_apply, one_smul]
  mul_smul φ ψ f := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul (φ * ψ) f, Lp.coeFn_mul φ ψ, coeFn_lpSMul φ (ψ • f),
      coeFn_lpSMul ψ f] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, Pi.mul_apply, mul_smul]
  smul_zero φ := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul φ (0 : LpSection 𝕜 F E p μ),
      coeFn_zero (𝕜 := 𝕜) (F := F) (E := E) (p := p) (μ := μ)] with x h₁ h₂
    rw [h₁, h₂, smul_zero]
  smul_add φ f g := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul φ (f + g), coeFn_add f g, coeFn_add (φ • f) (φ • g),
      coeFn_lpSMul φ f, coeFn_lpSMul φ g] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, h₃, h₄, h₅, smul_add]
  add_smul φ ψ f := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul (φ + ψ) f, Lp.coeFn_add φ ψ, coeFn_add (φ • f) (ψ • f),
      coeFn_lpSMul φ f, coeFn_lpSMul ψ f] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, h₃, h₄, h₅, Pi.add_apply, add_smul]
  zero_smul f := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul (0 : Lp 𝕜 ∞ μ) f, Lp.coeFn_zero 𝕜 ∞ μ,
      coeFn_zero (𝕜 := 𝕜) (F := F) (E := E) (p := p) (μ := μ)] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃, Pi.zero_apply, zero_smul]

instance : IsScalarTower 𝕜 (Lp 𝕜 ∞ μ) (LpSection 𝕜 F E p μ) where
  smul_assoc c φ f := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul (c • φ) f, Lp.coeFn_smul c φ, coeFn_smul (φ • f) c,
      coeFn_lpSMul φ f] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, Pi.smul_apply, smul_eq_mul, mul_smul]

instance : SMulCommClass 𝕜 (Lp 𝕜 ∞ μ) (LpSection 𝕜 F E p μ) where
  smul_comm c φ f := by
    refine ext _ _ ?_
    filter_upwards [coeFn_lpSMul φ (c • f), coeFn_smul f c, coeFn_smul (φ • f) c,
      coeFn_lpSMul φ f] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, smul_comm]

/-- The `L^∞` action on `Lᵖ` sections is bounded: `‖φ • f‖ ≤ ‖φ‖ ‖f‖`. -/
instance [Fact (1 ≤ p)] : IsBoundedSMul (Lp 𝕜 ∞ μ) (LpSection 𝕜 F E p μ) :=
  .of_norm_smul_le norm_lpSMul_le

variable (𝕜 F E p μ) in
/-- Multiplication of `Lᵖ` sections by essentially bounded functions, as a continuous bilinear map
`L^∞(μ) → Lᵖ(E, μ) → Lᵖ(E, μ)`: Mathlib's `ContinuousLinearMap.lsmul` for the module structure
above. Its value at `φ` is the multiplication operator `M_φ`, of norm at most `‖φ‖_{L^∞}`
(`ContinuousLinearMap.opNorm_lsmul_apply_le`), and it has norm at most `1`
(`ContinuousLinearMap.opNorm_lsmul_le`). -/
abbrev lpSMulL [Fact (1 ≤ p)] :
    Lp 𝕜 ∞ μ →L[𝕜] LpSection 𝕜 F E p μ →L[𝕜] LpSection 𝕜 F E p μ :=
  ContinuousLinearMap.lsmul 𝕜 (Lp 𝕜 ∞ μ)

/-- **Composition of multiplication operators**: `M_{φ ψ} = M_φ ∘ M_ψ`. -/
@[simp]
theorem lpSMulL_mul [Fact (1 ≤ p)] :
    lpSMulL 𝕜 F E p μ (φ * ψ) = lpSMulL 𝕜 F E p μ φ ∘L lpSMulL 𝕜 F E p μ ψ :=
  ContinuousLinearMap.ext fun f ↦ mul_smul φ ψ f

/-- Multiplication by the constant function `1` is the identity: `M_1 = id`. -/
@[simp]
theorem lpSMulL_one [Fact (1 ≤ p)] :
    lpSMulL 𝕜 F E p μ 1 = ContinuousLinearMap.id 𝕜 (LpSection 𝕜 F E p μ) :=
  ContinuousLinearMap.ext fun f ↦ one_smul (Lp 𝕜 ∞ μ) f

end Normed

section Inner

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E] (φ : Lp 𝕜 ∞ μ) (f g : LpSection 𝕜 F E 2 μ)

/-- `⟪φ • f, g⟫ = ⟪f, star φ • g⟫` for `L²` sections. -/
theorem inner_lpSMul_left : ⟪φ • f, g⟫_𝕜 = ⟪f, star φ • g⟫_𝕜 := by
  rw [inner_def, inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpSMul φ f, coeFn_lpSMul (star φ) g, Lp.coeFn_star φ] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, Pi.star_apply, inner_smul_left, inner_smul_right, RCLike.star_def]

/-- `⟪f, φ • g⟫ = ⟪star φ • f, g⟫` for `L²` sections. -/
theorem inner_lpSMul_right : ⟪f, φ • g⟫_𝕜 = ⟪star φ • f, g⟫_𝕜 := by
  rw [inner_lpSMul_left, star_star]

/-- **The adjoint of a multiplication operator** on `L²` sections is multiplication by the complex
conjugate function: `M_φ† = M_{star φ}`. -/
theorem adjoint_lpSMulL [CompleteSpace (LpSection 𝕜 F E 2 μ)] :
    ContinuousLinearMap.adjoint (lpSMulL 𝕜 F E 2 μ φ) = lpSMulL 𝕜 F E 2 μ (star φ) :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ by
    rw [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.lsmul_apply, inner_lpSMul_left,
      star_star]).symm

/-- A multiplication operator by a real-valued function, `star φ = φ`, is self-adjoint. -/
theorem isSelfAdjoint_lpSMulL [CompleteSpace (LpSection 𝕜 F E 2 μ)] (hφ : star φ = φ) :
    IsSelfAdjoint (lpSMulL 𝕜 F E 2 μ φ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', adjoint_lpSMulL, hφ]

end Inner

section SquarePartition

variable {ι : Type*} (s : Finset ι) (χ : ι → Lp 𝕜 ∞ μ)

/-- **Reconstruction from localizations.** If `∑ i ∈ s, |χ i x|² = 1` for almost every `x`, then
every `Lᵖ` section is the sum `∑ i ∈ s, star (χ i) • (χ i • f)` of its localizations by the
`χ i`, put back with the conjugate functions. -/
theorem sum_star_lpSMul_lpSMul [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
    (hχ : ∀ᵐ x ∂μ, ∑ i ∈ s, ‖χ i x‖ ^ 2 = 1) (f : LpSection 𝕜 F E p μ) :
    ∑ i ∈ s, star (χ i) • χ i • f = f := by
  refine ext _ _ ?_
  have hc : ∀ᵐ x ∂μ, ∀ i ∈ s, (star (χ i) • χ i • f) x = (star (χ i x) * χ i x) • f x := by
    refine (eventually_all_finset s).2 fun i _ ↦ ?_
    filter_upwards [coeFn_lpSMul (star (χ i)) (χ i • f), coeFn_lpSMul (χ i) f,
      Lp.coeFn_star (χ i)] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃, Pi.star_apply, mul_smul]
  filter_upwards [coeFn_sum s fun i ↦ star (χ i) • χ i • f, hc, hχ] with x h₁ h₂ h₃
  rw [h₁, Finset.sum_congr rfl h₂, ← Finset.sum_smul]
  have : ∑ i ∈ s, star (χ i x) * χ i x = ((∑ i ∈ s, ‖χ i x‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ by rw [RCLike.star_def, RCLike.conj_mul]
  rw [this, h₃, RCLike.ofReal_one, one_smul]

/-- **The `L²` norm of a section splits over a square partition.** If `∑ i ∈ s, |χ i x|² = 1` for
almost every `x`, then `‖f‖² = ∑ i ∈ s, ‖χ i • f‖²` for every `L²` section `f`. -/
theorem sum_norm_lpSMul_sq [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
    (hχ : ∀ᵐ x ∂μ, ∑ i ∈ s, ‖χ i x‖ ^ 2 = 1) (f : LpSection 𝕜 F E 2 μ) :
    ∑ i ∈ s, ‖χ i • f‖ ^ 2 = ‖f‖ ^ 2 := by
  simp_rw [norm_sq_eq_integral]
  rw [← integral_finsetSum _ fun i _ ↦ MemLp.integrable_sq (memLp_norm (χ i • f))]
  refine integral_congr_ae ?_
  have hc : ∀ᵐ x ∂μ, ∀ i ∈ s, (χ i • f) x = χ i x • f x :=
    (eventually_all_finset s).2 fun i _ ↦ coeFn_lpSMul (χ i) f
  filter_upwards [hc, hχ] with x h₁ h₂
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [h₁ i hi, norm_smul, mul_pow], ← Finset.sum_mul, h₂,
    one_mul]

end SquarePartition

end LpSection

end TauCeti
