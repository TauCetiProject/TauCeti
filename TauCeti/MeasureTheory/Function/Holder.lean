/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.MeasureTheory.Function.Lp.One
import Mathlib.Analysis.InnerProductSpace.Continuous
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Hölder estimates for pointwise pairings

Consequences of Mathlib's Hölder estimates for the pairings used in duality and weak
integration-by-parts arguments:

* `MeasureTheory.MemLp.integrable_apply`: evaluating an `L^p` function with values in continuous
  linear maps `V →L[𝕜] W` on a `V`-valued `L^q` function, for Hölder conjugate exponents, gives
  an integrable function. This supplies the integrability needed to split integrals in weak
  integration-by-parts formulas. It specializes Mathlib's bilinear Hölder estimate
  `ContinuousLinearMap.memLp_of_bilin` to evaluation.
* `MeasureTheory.MemLp.integrable_bilinear_apply`: more generally, an essentially bounded field of
  continuous bilinear maps applied to an `L^p` function and an `L^q` function is integrable.
* `MeasureTheory.MemLp.integrable_inner_of_holderConjugate`: Hölder's inequality makes the
  pointwise inner product `⟪h, g⟫` of `h ∈ L^q` and `g ∈ L^{q'}` integrable.
* `ContinuousLinearMap.lpPairing_mul_eq_integral`: the Hölder pairing
  `ContinuousLinearMap.lpPairing` of the multiplication of a complete normed algebra is the
  integral of the product.
* `ContinuousLinearMap.integrableOn_of_bilin_of_continuousOn_of_ae_mem`: a continuous bilinear
  pairing of a function integrable on a set `s` with a function continuous on a compact set `K` of
  full measure for `μ.restrict s` is integrable on `s`.
* `ContinuousLinearMap.integrable_of_bilin_of_continuousOn`: a continuous bilinear pairing of a
  function integrable on a compact set `K` and vanishing almost everywhere off `K` with a function
  continuous on `K` is integrable.
* `ContinuousLinearMap.norm_lpPairing_apply_apply_le`: Hölder's inequality
  `‖B.lpPairing μ p q g f‖ ≤ ‖B‖ * ‖g‖ * ‖f‖` for the integral pairing of a bilinear map `B`.
* `ContinuousLinearMap.norm_lpPairing_le`: the Hölder pairing induced by a continuous bilinear map
  `B` has norm at most `‖B‖`.
* `TauCeti.enorm_integral_smul_le`: Hölder's inequality `‖∫ a • f‖ ≤ ‖a‖_p ‖f‖_q` for the
  Bochner integral of a pointwise scalar multiple, for any boundedly acting scalars.
* `TauCeti.eNorm_integral_smul_sub_integral_smul_le`: against an integrable weight, the integrals
  of two products `a • b` and `f • g` of `L^∞` functions differ by at most
  `‖b‖_∞ ∫ |ψ| ‖a - f‖ + ‖f‖_∞ ∫ |ψ| ‖b - g‖`.
* `TauCeti.lintegral_enorm_mul_enorm_mul_enorm_le` and
  `MeasureTheory.MemLp.integrable_norm_mul_norm_mul_norm`: Hölder's inequality in three factors,
  `∫ |w| |g| |f| ≤ ‖w‖_p ‖g‖_r ‖f‖_q` for `1/p + 1/q = 1/s` and `1/r + 1/s = 1`, and the resulting
  integrability.
* `MeasureTheory.Lp.sum_smul` and `MeasureTheory.Lp.smul_sum`: the heterogeneous scalar
  multiplication `Lᵖ × L^q → Lʳ` distributes over finite sums in each factor.
* `MeasureTheory.MemLp.toLp_smul_toLp`: the product of the classes of `f` and `g` is the class of
  `f • g`; `MeasureTheory.Lp.one_smul`: the constant one of `L^∞` acts trivially.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α 𝕜 : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜] {μ : Measure α}
  {p q : ℝ≥0∞} [p.HolderConjugate q]

section Evaluation

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
  [NormedSpace 𝕜 W] {f : α → V →L[𝕜] W} {g : α → V}

/-- Evaluating an `L^p` function with values in continuous linear maps on an `L^q` function is
integrable when the exponents are Hölder conjugate. This covers dual pairings, where
`W = 𝕜`. -/
theorem integrable_apply (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ f x (g x)) μ :=
  memLp_one_iff_integrable.1
    ((ContinuousLinearMap.id 𝕜 (V →L[𝕜] W)).memLp_of_bilin 1 hf hg)

end Evaluation

section Bilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {B : α → E →L[𝕜] F →L[𝕜] G}
  {f : α → E} {g : α → F}

/-- Applying an essentially bounded field of continuous bilinear maps to an `L^p` function and
an `L^q` function gives an integrable function when the exponents are Hölder conjugate. -/
theorem integrable_bilinear_apply (hB : MemLp B ⊤ μ) (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ B x (f x) (g x)) μ := by
  -- The Hölder exponents are pinned explicitly, and the application goes through `exact`:
  -- elaborating it against the expected type in term mode unfolds `MemLp` and loops.
  have hBf : MemLp (fun x ↦ B x (f x)) p μ := by
    exact (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).memLp_of_bilin (𝕜 := 𝕜)
      (p := ⊤) (q := p) (f := B) (g := f) p hB hf
  -- The partial application `x ↦ B x (f x)` is an `L^p` field of linear maps `F →L[𝕜] G`.
  exact hBf.integrable_apply hg

end Bilinear

end MeasureTheory.MemLp

namespace MeasureTheory

open scoped InnerProductSpace

variable {α 𝕜 H : Type*} [MeasurableSpace α] [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] {μ : Measure α}

/-- Hölder's inequality makes the pairing `x ↦ ⟪h x, g x⟫` integrable for `h ∈ L^q` and
`g ∈ L^{q'}`. For `q = q' = 2` this is `MeasureTheory.MemLp.integrable_inner`. -/
theorem MemLp.integrable_inner_of_holderConjugate {q q' : ℝ≥0∞} [q.HolderConjugate q']
    {h g : α → H} (hh : MemLp h q μ) (hg : MemLp g q' μ) :
    Integrable (fun x => ⟪h x, g x⟫_𝕜) μ :=
  memLp_one_iff_integrable.1 <| hh.of_bilin (fun a b => ⟪a, b⟫_𝕜) 1 hg continuous_inner
    (ae_of_all _ fun x => by simpa [← NNReal.coe_le_coe] using norm_inner_le_norm (h x) (g x))

/-- Hölder's inequality in three factors makes `‖w‖ ‖g‖ ‖f‖` integrable for `w ∈ Lᵖ`, `g ∈ Lʳ`
and `f ∈ L^q` with `1/p + 1/q = 1/s` and `1/r + 1/s = 1`. -/
theorem MemLp.integrable_norm_mul_norm_mul_norm {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] {p q r s : ℝ≥0∞} [p.HolderTriple q s]
    [r.HolderTriple s 1] {w : α → E} {g : α → F} {f : α → G} (hw : MemLp w p μ)
    (hg : MemLp g r μ) (hf : MemLp f q μ) :
    Integrable (fun x ↦ ‖w x‖ * (‖g x‖ * ‖f x‖)) μ :=
  (memLp_one_iff_integrable.1 (hg.norm.mul (hw.norm.mul hf.norm (r := s)))).congr
    (ae_of_all _ fun x ↦ by simp only [Pi.mul_apply]; ring)

end MeasureTheory

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R] [NormedSpace ℝ R] [SMulCommClass ℝ 𝕜 R]
  [CompleteSpace R] {mα : MeasurableSpace α} {μ : Measure α} {q q' : ℝ≥0∞} [Fact (1 ≤ q)]
  [Fact (1 ≤ q')] [q.HolderConjugate q']

/-- The Hölder pairing of the multiplication `ContinuousLinearMap.mul 𝕜 R` is the integral of the
product. -/
theorem lpPairing_mul_eq_integral (g : Lp R q μ) (f : Lp R q' μ) :
    (mul 𝕜 R).lpPairing μ q q' g f = ∫ x, g x * f x ∂μ := by
  simp [lpPairing_eq_integral]

end ContinuousLinearMap

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 E F G : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] {μ : Measure α}

/-- A continuous bilinear pairing of a function integrable on a set `s` with a function continuous
on a compact set `K` of full measure for `μ.restrict s` (that is, `∀ᵐ x ∂μ.restrict s, x ∈ K`) is
integrable on `s`. Neither `s` nor `K` needs to be measurable. -/
theorem integrableOn_of_bilin_of_continuousOn_of_ae_mem (B : E →L[𝕜] F →L[𝕜] G) {f : α → E}
    {g : α → F} {s K : Set α} (hf : IntegrableOn f s μ) (hg : ContinuousOn g K)
    (hK : IsCompact K) (hsK : ∀ᵐ x ∂μ.restrict s, x ∈ K) :
    IntegrableOn (fun x ↦ B (f x) (g x)) s μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  -- `K` need not be measurable, so measure `g` on a measurable `T ⊆ K` of full measure.
  obtain ⟨T, hTae, hTm, hTK⟩ := hsK.exists_measurable_mem
  have hgT : AEStronglyMeasurable g ((μ.restrict s).restrict T) :=
    (hg.aestronglyMeasurable_of_subset_isCompact hK hTm hTK).mono_measure
      (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
  rw [Measure.restrict_eq_self_of_ae_mem hTae] at hgT
  exact B.integrable_of_bilin_of_bdd_right C hf hgT (hsK.mono fun x hx ↦ hC x hx)

/-- A continuous bilinear pairing of a function integrable on a compact set `K` and vanishing
almost everywhere off `K` with a function continuous on `K` is integrable. The domain need not be
Hausdorff, and `K` need not be measurable. -/
theorem integrable_of_bilin_of_continuousOn (B : E →L[𝕜] F →L[𝕜] G) {f : α → E} {K : Set α}
    (hf : IntegrableOn f K μ) (hK : IsCompact K) (hfK : ∀ᵐ x ∂μ, x ∉ K → f x = 0) {g : α → F}
    (hg : ContinuousOn g K) : Integrable (fun x => B (f x) (g x)) μ := by
  have hfi := hf.integrable_of_ae_notMem_eq_zero hfK
  -- `K` need not be measurable, so integrate over the support of `f` instead: it is
  -- null-measurable, and almost all of it lies in `K`.
  refine (B.integrableOn_of_bilin_of_continuousOn_of_ae_mem (s := Function.support f)
    hfi.integrableOn hg hK ?_).integrable_of_forall_notMem_eq_zero fun x hx ↦ ?_
  · filter_upwards [ae_restrict_mem₀ hfi.aestronglyMeasurable.nullMeasurableSet_support,
      ae_restrict_of_ae hfK] with x hx hxK
    exact by_contra fun h ↦ Function.mem_support.mp hx (hxK h)
  · simp [Function.notMem_support.mp hx]

end ContinuousLinearMap

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G] {mα : MeasurableSpace α}
  {μ : Measure α} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- **Hölder's inequality** for the integral pairing `lpPairing` of a bilinear map `B`. -/
theorem norm_lpPairing_apply_apply_le (B : E →L[𝕜] F →L[𝕜] G) (g : Lp E p μ) (f : Lp F q μ) :
    ‖B.lpPairing μ p q g f‖ ≤ ‖B‖ * ‖g‖ * ‖f‖ := by
  have h : B.lpPairing μ p q g f = L1.integral (B.holder 1 g f) := by
    simp [lpPairing, L1.integral_eq' 𝕜]
  rw [h]
  exact (L1.norm_integral_le _).trans (B.norm_holder_apply_apply_le _ _)

/-- **Hölder's inequality for the pairing** `∫ B (f x) (g x) dx` of `Lᵖ` and `L^q`: the Hölder
pairing induced by a continuous bilinear map `B` has norm at most `‖B‖`. -/
theorem norm_lpPairing_le (B : E →L[𝕜] F →L[𝕜] G) : ‖B.lpPairing μ p q‖ ≤ ‖B‖ :=
  opNorm_le_bound₂ _ (norm_nonneg B) B.norm_lpPairing_apply_apply_le

end ContinuousLinearMap

namespace MeasureTheory.Lp

variable {α ι 𝕜 E : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p q r : ℝ≥0∞}
  [p.HolderTriple q r] [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The heterogeneous scalar multiplication of `Lp` functions distributes over finite sums in the
scalar factor. -/
protected theorem sum_smul (s : Finset ι) (f : ι → Lp 𝕜 p μ) (g : Lp E q μ) :
    (∑ i ∈ s, f i) • g = ∑ i ∈ s, (f i • g : Lp E r μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Lp.smul_add, ih]

/-- The heterogeneous scalar multiplication of `Lp` functions distributes over finite sums in the
vector factor. -/
protected theorem smul_sum (s : Finset ι) (f : Lp 𝕜 p μ) (g : ι → Lp E q μ) :
    f • (∑ i ∈ s, g i) = ∑ i ∈ s, (f • g i : Lp E r μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Lp.add_smul, ih]

/-- The heterogeneous product of the `Lp` classes of `f` and `g` is the class of the pointwise
product `f • g`. -/
theorem _root_.MeasureTheory.MemLp.toLp_smul_toLp {f : α → 𝕜} {g : α → E} (hf : MemLp f p μ)
    (hg : MemLp g q μ) : (hf.toLp f • hg.toLp g : Lp E r μ) = (hf.smul hg).toLp (f • g) :=
  MemLp.toLp_congr _ _ <| by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h₁ h₂
    rw [Pi.smul_apply', h₁, h₂, Pi.smul_apply']

omit [p.HolderTriple q r] in
/-- The constant one of `L^∞` acts trivially on every `L^q` function. -/
@[simp]
protected theorem one_smul (g : Lp E q μ) : ((1 : Lp 𝕜 ∞ μ) • g : Lp E q μ) = g := by
  conv_lhs => rw [one_def, ← Lp.toLp_coeFn g (Lp.memLp g), MemLp.toLp_smul_toLp]
  conv_rhs => rw [← Lp.toLp_coeFn g (Lp.memLp g)]
  exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ by simp)

end MeasureTheory.Lp

namespace TauCeti

open MeasureTheory

/-- **Hölder's inequality** for the Bochner integral of a pointwise scalar multiple:
`‖∫ a • f‖ ≤ ‖a‖_p ‖f‖_q` for Hölder conjugate exponents `p` and `q`. The scalars only need to
act boundedly, as a normed field does on a normed space and a normed ring does on itself. -/
theorem enorm_integral_smul_le {α 𝕜 F : Type*} [MeasurableSpace α]
    [NormedAddGroup 𝕜] [NormedAddCommGroup F] [SMulZeroClass 𝕜 F] [IsBoundedSMul 𝕜 F]
    [NormedSpace ℝ F] {μ : Measure α} {p q : ℝ≥0∞} [p.HolderConjugate q] {a : α → 𝕜}
    {f : α → F} :
    ‖∫ x, a x • f x ∂μ‖ₑ ≤ eLpNorm a p μ * eLpNorm f q μ := by
  calc ‖∫ x, a x • f x ∂μ‖ₑ ≤ eLpNorm (fun x => a x • f x) 1 μ :=
      (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ ≤ eLpNorm a p μ * eLpNorm f q μ := by
      simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (· • ·) 1
        continuous_smul.comp_aestronglyMeasurable₂
        (.of_forall fun _ => by simpa using eNorm_smul_le) zero_lt_one

/-- Against an integrable weight `ψ`, the products `a • b` and `f • g` of bounded functions differ
by at most `‖b‖_∞ ∫ |ψ| ‖a - f‖ + ‖f‖_∞ ∫ |ψ| ‖b - g‖`, from
`a • b - f • g = (a - f) • b + f • (b - g)`. -/
theorem eNorm_integral_smul_sub_integral_smul_le {α 𝕜 F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
    [NormedSpace ℝ F] {ψ : α → 𝕜} (hψ : Integrable ψ μ) (a f : Lp 𝕜 ∞ μ) (b g : Lp F ∞ μ) :
    ‖(∫ x, ψ x • (a • b : Lp F ∞ μ) x ∂μ) - ∫ x, ψ x • (f • g : Lp F ∞ μ) x ∂μ‖ₑ ≤
      ‖b‖ₑ * (∫⁻ x, ‖ψ x‖ₑ * ‖a x - f x‖ₑ ∂μ) + ‖f‖ₑ * ∫⁻ x, ‖ψ x‖ₑ * ‖b x - g x‖ₑ ∂μ := by
  have hint : ∀ u : Lp F ∞ μ, Integrable (fun x ↦ ψ x • u x) μ :=
    fun u ↦ hψ.smul_of_top_left (Lp.memLp u)
  have hm : AEMeasurable (fun x ↦ ‖ψ x‖ₑ * ‖a x - f x‖ₑ) μ :=
    hψ.aestronglyMeasurable.eNorm.mul
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).eNorm
  rw [← integral_sub (hint _) (hint _), ← lintegral_const_mul' _ _ eNorm_ne_top,
    ← lintegral_const_mul' _ _ eNorm_ne_top, ← lintegral_add_left' (hm.const_mul _)]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) a b, Lp.coeFn_lpSMul (r := ∞) f g,
    Lp.ae_norm_le_norm_top b, Lp.ae_norm_le_norm_top f] with x hab hfg hb hf
  rw [← smul_sub, hab, hfg, Pi.smul_apply', Pi.smul_apply']
  have hsplit : a x • b x - f x • g x = (a x - f x) • b x + f x • (b x - g x) := by
    rw [sub_smul, smul_sub]
    abel
  have hb' : ‖b x‖ₑ ≤ ‖b‖ₑ := eNorm_le_iff_norm_le.2 hb
  have hf' : ‖f x‖ₑ ≤ ‖f‖ₑ := eNorm_le_iff_norm_le.2 hf
  calc ‖ψ x • (a x • b x - f x • g x)‖ₑ
      ≤ ‖ψ x‖ₑ * (‖a x - f x‖ₑ * ‖b‖ₑ + ‖f‖ₑ * ‖b x - g x‖ₑ) := by
        refine eNorm_smul_le.trans ?_
        rw [hsplit]
        gcongr
        refine (eNorm_add_le _ _).trans ?_
        gcongr
        · exact eNorm_smul_le.trans (by gcongr)
        · exact eNorm_smul_le.trans (by gcongr)
    _ = ‖b‖ₑ * (‖ψ x‖ₑ * ‖a x - f x‖ₑ) + ‖f‖ₑ * (‖ψ x‖ₑ * ‖b x - g x‖ₑ) := by ring

/-- **Hölder's inequality in three factors**: `∫ |w| |g| |f| ≤ ‖w‖_p ‖g‖_r ‖f‖_q` for
`1/p + 1/q = 1/s` and `1/r + 1/s = 1`, by Hölder's inequality applied twice. -/
theorem lintegral_enorm_mul_enorm_mul_enorm_le {α E F G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {p q r s : ℝ≥0∞} [p.HolderTriple q s] [r.HolderTriple s 1] {w : α → E} {g : α → F}
    {f : α → G} (hw : AEStronglyMeasurable w μ) (hg : AEStronglyMeasurable g μ)
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖w x‖ₑ * (‖g x‖ₑ * ‖f x‖ₑ) ∂μ ≤
      eLpNorm w p μ * (eLpNorm g r μ * eLpNorm f q μ) := by
  have h₁ := eLpNorm_smul_le_mul_eLpNorm (p := r) (q := s) (r := 1) hg.norm
    (hw.norm.smul hf.norm) (μ := μ)
  have h₂ := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := s) hw.norm hf.norm (μ := μ)
  rw [eLpNorm_norm _ hg] at h₁
  rw [eLpNorm_norm _ hw, eLpNorm_norm _ hf] at h₂
  calc ∫⁻ x, ‖w x‖ₑ * (‖g x‖ₑ * ‖f x‖ₑ) ∂μ
      = eLpNorm ((fun x ↦ ‖g x‖) • ((fun x ↦ ‖w x‖) • fun x ↦ ‖f x‖)) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm (hg.norm.smul (hw.norm.smul hf.norm))]
        refine lintegral_congr fun x ↦ ?_
        simp only [Pi.smul_apply', Pi.mul_apply, smul_eq_mul, eNorm_mul, eNorm_norm]
        ring
    _ ≤ eLpNorm g r μ * eLpNorm ((fun x ↦ ‖w x‖) • fun x ↦ ‖f x‖) s μ := h₁
    _ ≤ eLpNorm w p μ * (eLpNorm g r μ * eLpNorm f q μ) := by
        rw [mul_left_comm]
        gcongr

end TauCeti
