/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.ExtremalRpow
import TauCeti.Analysis.Normed.Module.RCLike.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.SpanningSets
import TauCeti.MeasureTheory.Function.Holder

/-!
# Norming `Lᵖ` functions by test functions

For Hölder conjugate exponents `1 / q + 1 / q' = 1`, the `L^q` norm of a function `h` is the
supremum of the pairings `|∫ h g|` over simple functions `g` of `L^{q'}` norm at most one. This
file proves the half of that duality which is used to bound a norm: if
`‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple `g ∈ L^{q'}`, then `‖h‖_q ≤ C`.

For `q < ∞` this holds for every `h ∈ L^q`, on any measure space. The test function is the
extremal one `conj g * |g| ^ (q - 2)` of a simple approximation `g` of `h`; the scalar statement
is the case `H = 𝕜` of the inner product version below, applied to `conj h`. For `q = ∞` it
needs the measure to be σ-finite (on a measure with an atom of infinite measure every integrable
`g` vanishes on the atom), and it reduces to the case `q = 1` on a set of finite positive measure
where `‖h‖` is close to its essential supremum.

Testing against simple functions only, rather than against all of `L^{q'}`, is what makes the
statement usable when the pairings can only be computed on simple functions, as in the
Riesz–Thorin theorem. Together with Hölder's inequality, the duality bound shows that the
integral pairing `g ↦ (f ↦ ∫ g f dμ)` is a linear isometry from `L^q(μ)` to the continuous dual
of `L^q'(μ)` on a σ-finite measure space.

For functions with values in an inner product space, paired by `∫ ⟪h, g⟫`, the file proves the
duality bound for `q < ∞` against integrable simple test functions, as needed for the complex
interpolation spaces of the Lebesgue couple, where the pairings can only be computed on those:
first for `h ∈ L^q`, then, on a σ-finite measure space, for an arbitrary `h`, by applying the
first version to the truncations of `h` to the sets where it is bounded inside a spanning set.
As a corollary, the same bound holds against bounded test functions that vanish off a set of
finite measure, again without assuming `h ∈ L^q` in advance. This is the form needed to prove
that an operator defined on `L²` maps `L² ∩ Lᵖ` into `L^q` by duality.

The integral Hölder bounds apply to arbitrary functions, using the convention that `eLpNorm`
is `∞` outside the almost everywhere strongly measurable functions.

## Main declarations

* `TauCeti.enorm_integral_mul_le`: Hölder's inequality `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for an integral.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`: the duality bound
  for `q < ∞`.
* `MeasureTheory.AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le`: the duality
  bound for `q = ∞` on a σ-finite measure space, without assuming `h ∈ L^∞` in advance.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le`: the duality bound for every
  `1 ≤ q ≤ ∞` on a σ-finite measure space.
* `MeasureTheory.Lp.enorm_integral_mul_le_of_apply_eq`: a continuous linear functional on
  `L^q'` that is integration against `h` satisfies the hypothesis of these duality bounds.
* `MeasureTheory.Lp.toDual`: on a σ-finite measure space, the integral pairing is a linear
  isometry `L^q(μ) → L^q'(μ)*`.
* `MeasureTheory.Lp.toDual_indicatorConstLp`: the value of the pairing at an indicator function.
* `MeasureTheory.Lp.exists_norm_le_one_integral_mul_eq`,
  `MeasureTheory.Lp.exists_ae_sum_norm_sq_le_one_sum_integral_mul_eq`: exact norming of elements
  and finite `ℓ²(L¹)` families in `L¹(μ)` by `L∞(μ)` test functions on any measure space.
* `TauCeti.enorm_integral_inner_le`: Hölder's inequality `‖∫ ⟪u, v⟫‖ ≤ ‖u‖_p ‖v‖_q`.
* `TauCeti.enorm_integral_inner_comm`: `‖∫ ⟪u, v⟫‖ = ‖∫ ⟪v, u⟫‖`.
* `TauCeti.tendsto_integral_inner_of_tendsto_eLpNorm_sub`: if `Gᵢ → F` in `Lᵖ` then
  `∫ ⟪Gᵢ, g⟫ → ∫ ⟪F, g⟫` for every `g ∈ L^q`.
* `MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`: the duality
  bound for `q < ∞` for inner product space valued functions, against bounded test functions of
  finite-measure support, without assuming `h ∈ L^q`.
* `MeasureTheory.MemLp.innerLpCLM`: integration against `G ∈ L^q`, `f ↦ ∫ ⟪G, f⟫`, as a
  continuous linear functional on `L^{q'}` of norm at most `‖G‖_q`.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_inner_le_of_ne_top`,
  `MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_simpleFunc_le`:
  the duality bound for `q < ∞` for inner product space valued functions, against integrable
  simple test functions, for `h ∈ L^q` and, on a σ-finite measure space, without assuming
  `h ∈ L^q`.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.14.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

namespace TauCeti

variable {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- **Hölder's inequality** for the integral of a product: `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for Hölder
conjugate exponents `p` and `q`. -/
theorem enorm_integral_mul_le {𝕜 : Type*} [NonUnitalNormedRing 𝕜] [NormedSpace ℝ 𝕜]
    {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → 𝕜} :
    ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  simpa only [smul_eq_mul] using enorm_integral_smul_le (μ := μ) (p := p) (a := u) (f := v)

/-- **Hölder's inequality** for the integral of an inner product: `‖∫ ⟪u, v⟫‖ ≤ ‖u‖_p ‖v‖_q` for
Hölder conjugate exponents `p` and `q`. -/
theorem enorm_integral_inner_le {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → H} :
    ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  calc ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm (fun x => ⟪u x, v x⟫_𝕜) 1 μ :=
        (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ ≤ eLpNorm u p μ * eLpNorm v q μ := by
        simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (fun a b => ⟪a, b⟫_𝕜) 1
          continuous_inner (ae_of_all _ fun x => by simpa using norm_inner_le_norm (u x) (v x))
          zero_lt_one

/-- Swapping the arguments of the pairing `∫ ⟪u, v⟫` conjugates it, so its norm is unchanged. -/
theorem enorm_integral_inner_comm {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (u v : α → H) :
    ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ = ‖∫ x, ⟪v x, u x⟫_𝕜 ∂μ‖ₑ := by
  rw [← RCLike.eNorm_conj, ← integral_conj]
  simp_rw [inner_conj_symm]

open Filter Topology in
/-- **Continuity of the pairing `∫ ⟪u, v⟫` in `Lᵖ`.** If `Gᵢ → F` in `Lᵖ`, then
`∫ ⟪Gᵢ, g⟫ → ∫ ⟪F, g⟫` for every `g ∈ L^q`, `q` the Hölder conjugate exponent. -/
theorem tendsto_integral_inner_of_tendsto_eLpNorm_sub {𝕜 H β : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {p q : ℝ≥0∞} [p.HolderConjugate q]
    {l : Filter β} {F g : α → H} {G : β → α → H} (hF : MemLp F p μ) (hG : ∀ i, MemLp (G i) p μ)
    (hg : MemLp g q μ) (hGF : Tendsto (fun i => eLpNorm (F - G i) p μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, ⟪G i x, g x⟫_𝕜 ∂μ) l (𝓝 (∫ x, ⟪F x, g x⟫_𝕜 ∂μ)) := by
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.mul_const hGF (Or.inr hg.eLpNorm_ne_top))
    (fun _ => zero_le) fun i => ?_
  rw [eDist_eq_eNorm_sub, ← integral_sub ((hG i).integrable_inner_of_holderConjugate hg)
    (hF.integrable_inner_of_holderConjugate hg), eLpNorm_sub_comm]
  simp_rw [← inner_sub_left]
  exact enorm_integral_inner_le (u := G i - F)

end TauCeti

namespace MeasureTheory

variable {α 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

open TauCeti


namespace MemLp

variable (𝕜) in
/-- Integration against a fixed `G ∈ L^q`, `f ↦ ∫ ⟪G, f⟫`, as a continuous linear functional on
the conjugate space `L^{q'}`: Mathlib's pairing `ContinuousLinearMap.lpPairing` of `L^{q'}` with
the field `x ↦ ⟪G x, ·⟫` of functionals. Its norm is at most `‖G‖_q`
(`MemLp.norm_innerLpCLM_le`). -/
noncomputable def innerLpCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {q q' : ℝ≥0∞} [Fact (1 ≤ q')] [hqq : q.HolderConjugate q'] {G : α → H} (hG : MemLp G q μ) :
    Lp H q' μ →L[𝕜] 𝕜 :=
  haveI : Fact (1 ≤ q) := ⟨hqq.one_le⟩
  (ContinuousLinearMap.id 𝕜 (H →L[𝕜] 𝕜)).lpPairing μ q q'
    ((hG.of_le ((innerSL 𝕜).continuous.comp_aestronglyMeasurable hG.aestronglyMeasurable)
      (ae_of_all _ fun x => (innerSL_apply_norm 𝕜 (G x)).le)).toLp _)

/-- The pairing functional of `G` sends `f` to `∫ ⟪G, f⟫`. -/
@[simp]
theorem innerLpCLM_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {q q' : ℝ≥0∞} [Fact (1 ≤ q')] [q.HolderConjugate q'] {G : α → H} (hG : MemLp G q μ)
    (f : Lp H q' μ) : hG.innerLpCLM 𝕜 f = ∫ x, ⟪G x, f x⟫_𝕜 ∂μ := by
  rw [innerLpCLM, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (f := fun x => innerSL 𝕜 (G x)) (p := q) (μ := μ) _] with x hx
  rw [ContinuousLinearMap.id_apply, hx, innerSL_apply_apply]

/-- **Hölder's inequality** for the pairing functional: `‖f ↦ ∫ ⟪G, f⟫‖ ≤ ‖G‖_q`. -/
theorem norm_innerLpCLM_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {q q' : ℝ≥0∞} [Fact (1 ≤ q')] [q.HolderConjugate q'] {G : α → H} (hG : MemLp G q μ) :
    ‖hG.innerLpCLM 𝕜 (q' := q')‖ ≤ (eLpNorm G q μ).toReal := by
  refine ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg fun f => ?_
  rw [innerLpCLM_apply, Lp.norm_def, ← ENNReal.toReal_mul, ← toReal_eNorm]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hG.eLpNorm_ne_top (Lp.eLpNorm_ne_top f))
    (TauCeti.enorm_integral_inner_le (p := q) (q := q'))

end MemLp

/-- The extremal test function of a simple function `φ ∈ L^q`, `q < ∞`: the integrable simple
function `g = |φ| ^ (q - 2) φ`, with `⟪φ, g⟫ = |φ| ^ q` and `‖g‖_{q'} ≤ ‖φ‖_q ^ (q - 1)`. -/
private theorem exists_simpleFunc_inner_eq_rpow {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q'] (hq : q ≠ ∞)
    {φ : SimpleFunc α H} (hφ : MemLp φ q μ) :
    ∃ g : SimpleFunc α H, Integrable g μ ∧ MemLp g q' μ ∧
      eLpNorm g q' μ ≤ eLpNorm φ q μ ^ (q.toReal - 1) ∧
      ∀ x, ⟪φ x, g x⟫_𝕜 = ((‖φ x‖ ^ q.toReal : ℝ) : 𝕜) := by
  have hr1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hqq.one_le
  set g : SimpleFunc α H := φ.map fun c => ((‖c‖ ^ (q.toReal - 2) : ℝ) : 𝕜) • c
  have hgX : eLpNorm g q' μ ≤ eLpNorm φ q μ ^ (q.toReal - 1) :=
    eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq g.aestronglyMeasurable (ae_of_all _ fun x => by
      simpa [g] using norm_ofReal_rpow_sub_two_smul_le (𝕜 := 𝕜) q.toReal (φ x))
  -- The extremal function vanishes where `φ` does, so it has finite-measure support.
  refine ⟨g, SimpleFunc.FinMeasSupp.integrable ?_, memLp_iff.2 (hgX.trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) hφ.eLpNorm_lt_top.ne)), hgX, fun x => ?_⟩
  · exact ((SimpleFunc.memLp_iff_finMeasSupp hqq.ne_zero hq).1 hφ).map (by simp)
  · simpa [g] using inner_ofReal_rpow_sub_two_smul (𝕜 := 𝕜) (by linarith : q.toReal ≠ 0) (φ x)

/-- **Norming by simple functions, inner product version, `q < ∞`.** Let `q < ∞` and `q'` be
Hölder conjugate. If `h ∈ L^q` with values in an inner product space satisfies
`‖∫ ⟪h, g⟫‖ ≤ C ‖g‖_{q'}` for every integrable simple function `g`, then `‖h‖_q ≤ C`. -/
theorem MemLp.eLpNorm_le_of_forall_enorm_integral_inner_le_of_ne_top {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q']
    {h : α → H} (hh : MemLp h q μ) (hq : q ≠ ∞) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α H, Integrable g μ →
      ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by simp [hε.ne']
  -- Approximate `h` by a simple function `φ` and test against the extremal function of `φ`.
  obtain ⟨φ, hφ, hφmem⟩ := hh.exists_simpleFunc_eLpNorm_sub_lt hq hε2
  obtain ⟨g, hgint, hgmem, hgX, hφg⟩ := exists_simpleFunc_inner_eq_rpow (𝕜 := 𝕜) (q' := q') hq hφmem
  set X := eLpNorm φ q μ
  have hX : X ≠ ∞ := hφmem.eLpNorm_lt_top.ne
  -- The pairing of `φ` with its extremal function is `‖φ‖_q ^ q`.
  have hXr : X ^ q.toReal ≤ ‖∫ x, ⟪φ x, g x⟫_𝕜 ∂μ‖ₑ := by
    simp_rw [hφg]
    exact (hφmem.eLpNorm_rpow_toReal_eq_enorm_integral (𝕜 := 𝕜) hqq.ne_zero hq).le
  -- Replacing `φ` by `h` costs at most `‖h - φ‖_q ‖g‖_{q'}`.
  have hsplit : ‖∫ x, ⟪φ x, g x⟫_𝕜 ∂μ‖ₑ ≤ (C + ε / 2) * X ^ (q.toReal - 1) := by
    have heq : ∫ x, ⟪φ x, g x⟫_𝕜 ∂μ =
        ∫ x, ⟪h x, g x⟫_𝕜 ∂μ - ∫ x, ⟪h x - φ x, g x⟫_𝕜 ∂μ := by
      rw [← integral_sub (hh.integrable_inner_of_holderConjugate hgmem)
        ((hh.sub hφmem).integrable_inner_of_holderConjugate hgmem)]
      congr 1 with x
      rw [inner_sub_left, sub_sub_cancel]
    calc ‖∫ x, ⟪φ x, g x⟫_𝕜 ∂μ‖ₑ
        ≤ ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ + ‖∫ x, ⟪h x - φ x, g x⟫_𝕜 ∂μ‖ₑ := by
          rw [heq]
          exact eNorm_sub_le
      _ ≤ C * eLpNorm g q' μ + eLpNorm (h - ⇑φ) q μ * eLpNorm g q' μ :=
          add_le_add (hC g hgint) (TauCeti.enorm_integral_inner_le (u := h - ⇑φ))
      _ ≤ (C + ε / 2) * X ^ (q.toReal - 1) := by
          rw [← add_mul]
          gcongr
  -- Hence `‖φ‖_q ≤ C + ε / 2`, and `‖h‖_q ≤ ‖φ‖_q + ε / 2`.
  have hXle : X ≤ C + ε / 2 := ENNReal.le_of_rpow_le_mul_rpow_sub_one hX (hXr.trans hsplit)
  calc eLpNorm h q μ = eLpNorm ((h - ⇑φ) + ⇑φ) q μ := by simp
    _ ≤ eLpNorm (h - ⇑φ) q μ + X := eLpNorm_add_le hqq.one_le
    _ ≤ ε / 2 + (C + ε / 2) := by gcongr
    _ = C + ε := by rw [add_comm, add_assoc, ENNReal.add_halves]

/-- **Norming by simple functions, inner product version.** On a σ-finite measure space, let
`q < ∞` and `q'` be Hölder conjugate. If an almost everywhere strongly measurable `h` with values
in an inner product space satisfies `‖∫ ⟪h, g⟫‖ ≤ C ‖g‖_{q'}` for every integrable simple function
`g`, then `‖h‖_q ≤ C`.

Unlike `MemLp.eLpNorm_le_of_forall_enorm_integral_inner_le_of_ne_top`, `h` is not assumed to lie
in `L^q`: the bound is first proved for the truncations of `h` to the sets where it is bounded
inside a spanning set of the measure, which lie in `L^q`. -/
theorem AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_simpleFunc_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [SigmaFinite μ] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] (hq : q ≠ ∞) {h : α → H} (hh : AEStronglyMeasurable h μ)
    {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α H, Integrable g μ →
      ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  set h' := hh.mk h
  have hh' : StronglyMeasurable h' := hh.stronglyMeasurable_mk
  rw [eLpNorm_congr_ae hh.ae_eq_mk]
  refine Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop)
    (f := fun N => (spanningSets μ N ∩ {x | ‖h' x‖ ≤ N}).indicator h')
    (Filter.Eventually.of_forall fun N => ?_)
    (fun N => (hh'.indicator (measurableSet_spanningSets_inter_norm_le hh' N)).aestronglyMeasurable)
    hh'.aestronglyMeasurable
    (ae_of_all _ fun x => tendsto_indicator_spanningSets_inter_norm_le h' x)
  -- The truncation `1_S h` lies in `L^q`; testing it against `g` tests `h` against `1_S g`.
  set S := spanningSets μ N ∩ {x | ‖h' x‖ ≤ N}
  have hS : MeasurableSet S := measurableSet_spanningSets_inter_norm_le hh' N
  have hmem : MemLp (S.indicator h') q μ := by
    refine memLp_of_norm_le_of_measure_support_ne_top (hh'.indicator hS).aestronglyMeasurable
      (c := N) (ae_of_all _ fun x => ?_) (measure_spanningSets_lt_top μ N).ne
      (fun x hx => Set.indicator_of_notMem (fun h => hx (Set.mem_of_mem_inter_left h)) _) q
    by_cases hx : x ∈ S
    · simpa [Set.indicator_of_mem hx] using hx.2
    · simp [Set.indicator_of_notMem hx]
  refine hmem.eLpNorm_le_of_forall_enorm_integral_inner_le_of_ne_top (𝕜 := 𝕜) (q' := q') hq
    fun g hg => ?_
  calc ‖∫ x, ⟪S.indicator h' x, g x⟫_𝕜 ∂μ‖ₑ = ‖∫ x, ⟪h x, g.restrict S x⟫_𝕜 ∂μ‖ₑ := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hh.ae_eq_mk] with x hx
        rw [g.restrict_apply hS]
        by_cases hxS : x ∈ S <;> simp [hxS, hx, h']
    _ ≤ C * eLpNorm (g.restrict S) q' μ :=
        hC _ (by rw [g.coe_restrict hS]; exact hg.indicator hS)
    _ ≤ C * eLpNorm g q' μ := by
        rw [g.coe_restrict hS]
        gcongr
        exact eLpNorm_indicator_le _ hS.nullMeasurableSet


/-- **Norming by bounded functions of finite-measure support.** On a σ-finite measure space, let
`q < ∞` and `q'` be Hölder conjugate. If an almost everywhere strongly measurable `h` with values
in an inner product space satisfies `‖∫ ⟪h, g⟫‖ ≤ C ‖g‖_{q'}` for every bounded `g` vanishing off a
set of finite measure, then `‖h‖_q ≤ C`.

Unlike `MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`, `h` is not assumed to lie in
`L^q`: when `C < ∞`, membership in `L^q` follows from the conclusion. The test functions lie in
every `Lˢ`, so the hypothesis only involves pairings that are defined, for instance, for every
`h ∈ L²`. -/
theorem AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [SigmaFinite μ] {q q' : ℝ≥0∞}
    [q.HolderConjugate q'] (hq : q ≠ ∞) {h : α → H} (hh : AEStronglyMeasurable h μ)
    {C : ℝ≥0∞}
    (hC : ∀ (g : α → H) (s : Set α), μ s ≠ ∞ → (∀ x, x ∉ s → g x = 0) → MemLp g ∞ μ →
      ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C :=
  hh.eLpNorm_le_of_forall_enorm_integral_inner_simpleFunc_le hq fun g hg =>
    hC g (Function.support g)
      (SimpleFunc.finMeasSupp_iff_support.1 (SimpleFunc.integrable_iff_finMeasSupp.1 hg)).ne
      (fun _ => Function.notMem_support.1) (g.memLp_top μ)


/-- **Norming by simple functions, `q < ∞`.** Let `q < ∞` and `q'` be Hölder conjugate. If
`h ∈ L^q` satisfies `‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple function `g ∈ L^{q'}`, then
`‖h‖_q ≤ C`. -/
theorem MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top {q q' : ℝ≥0∞}
    [q.HolderConjugate q'] {h : α → 𝕜} (hh : MemLp h q μ) (hq : q ≠ ∞) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g q' μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  -- This is the inner product version for `H = 𝕜`, applied to `conj h`.
  rw [← eLpNorm_star]
  refine hh.star.eLpNorm_le_of_forall_enorm_integral_inner_le_of_ne_top (𝕜 := 𝕜) (q' := q') hq
    fun g hg => ?_
  simpa [RCLike.inner_apply', mul_comm] using
    hC g (SimpleFunc.memLp_of_finite_measure_preimage _ (SimpleFunc.integrable_iff.1 hg))

/-- **Norming by simple functions, `q = ∞`.** On a σ-finite measure space, let `h` be almost
everywhere strongly measurable. If `h` satisfies
`‖∫ h g‖ ≤ C ‖g‖₁` for every simple function `g ∈ L¹`, then `‖h‖_∞ ≤ C`. In particular `h ∈ L^∞`
as soon as `C < ∞`. -/
theorem AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le [SigmaFinite μ]
    {h : α → 𝕜} (hmeas : AEStronglyMeasurable h μ)
    {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g 1 μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g 1 μ) :
    eLpNorm h ∞ μ ≤ C := by
  by_contra! hlt
  obtain ⟨t, hCt, htN⟩ := exists_between hlt
  set h' := hmeas.mk h
  have hhh' : h =ᵐ[μ] h' := hmeas.ae_eq_mk
  -- The set `{t < ‖h‖}` has positive measure, so by σ-finiteness it contains a set of finite
  -- positive measure; we first cut it down to a set on which `h` is bounded.
  have hE : MeasurableSet {x | t < ‖h' x‖ₑ} :=
    measurableSet_lt measurable_const hmeas.stronglyMeasurable_mk.measurable.eNorm
  have hG (N : ℕ) : MeasurableSet {x | ‖h' x‖ₑ ≤ N} :=
    measurableSet_le hmeas.stronglyMeasurable_mk.measurable.eNorm measurable_const
  have hpos : 0 < μ {x | t < ‖h' x‖ₑ} := by
    refine pos_iff_ne_zero.2 fun hnull => htN.not_ge ?_
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hhh', measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hx'
    rw [hx]
    simpa using hx'
  -- some bounded slice `{t < ‖h' x‖ₑ} ∩ {‖h' x‖ₑ ≤ N}` has positive measure
  have hcover : {x | t < ‖h' x‖ₑ} ⊆ ⋃ N : ℕ, {x | t < ‖h' x‖ₑ} ∩ {x | ‖h' x‖ₑ ≤ N} := fun x hx ↦ by
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (eNorm_ne_top (x := h' x))
    exact Set.mem_iUnion.2 ⟨N, hx, hN.le⟩
  obtain ⟨N, hNpos⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (hpos.trans_le (measure_mono hcover)).ne'
  obtain ⟨F, hFm, hFE, hFpos, hFtop⟩ :=
    Measure.exists_subset_measure_lt_top (hE.inter (hG N)) hNpos
  -- The case `q = 1`, applied to `1_F h`, bounds `∫_F ‖h‖` by `C μ(F)`.
  have hk : MemLp (F.indicator h) 1 μ := by
    rw [memLp_indicator_iff_restrict hFm.nullMeasurableSet, memLp_one_iff_integrable]
    refine Measure.integrableOn_of_bounded (M := N) hFtop.ne hmeas ?_
    filter_upwards [ae_restrict_of_ae hhh', ae_restrict_mem hFm] with x hx hxF
    have h2 : ‖h' x‖ₑ ≤ (N : ℝ≥0∞) := (hFE hxF).2
    rw [hx]
    simpa [← ofReal_norm] using h2
  have hkC : eLpNorm (F.indicator h) 1 μ ≤ C * μ F := by
    refine hk.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top (q' := ∞) ENNReal.one_ne_top
      fun g _ => ?_
    have hgF : eLpNorm (g.restrict F) 1 μ ≤ μ F * eLpNorm g ∞ μ := by
      rw [SimpleFunc.coe_restrict _ hFm,
        eLpNorm_indicator_eq_eLpNorm_restrict hFm.nullMeasurableSet]
      calc eLpNorm g 1 (μ.restrict F)
          ≤ eLpNorm g ∞ (μ.restrict F) * μ.restrict F Set.univ ^ (1 / (1 : ℝ≥0∞).toReal -
              1 / (∞ : ℝ≥0∞).toReal) :=
            eLpNorm_le_eLpNorm_mul_rpow_measure_univ le_top g.aestronglyMeasurable
        _ ≤ eLpNorm g ∞ μ * μ F := by
            simp only [ENNReal.toReal_one, ENNReal.toReal_top, div_zero, sub_zero, div_one,
              ENNReal.rpow_one, Measure.restrict_apply_univ]
            gcongr
            exact Measure.restrict_le_self
        _ = μ F * eLpNorm g ∞ μ := mul_comm _ _
    have hgmem : MemLp (g.restrict F) 1 μ :=
      memLp_iff.2 (hgF.trans_lt (ENNReal.mul_lt_top hFtop (g.memLp_top μ).eLpNorm_lt_top))
    calc ‖∫ x, F.indicator h x * g x ∂μ‖ₑ = ‖∫ x, h x * g.restrict F x ∂μ‖ₑ := by
          congr 2 with x
          rw [SimpleFunc.restrict_apply _ hFm]
          by_cases hx : x ∈ F <;> simp [hx]
      _ ≤ C * eLpNorm (g.restrict F) 1 μ := hC _ hgmem
      _ ≤ C * (μ F * eLpNorm g ∞ μ) := by gcongr
      _ = C * μ F * eLpNorm g ∞ μ := (mul_assoc _ _ _).symm
  -- On the other hand `‖h‖ > t` on `F`, so `t μ(F) ≤ C μ(F)`, contradicting `C < t`.
  have hlow : t * μ F ≤ eLpNorm (F.indicator h) 1 μ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hFm.nullMeasurableSet,
      eLpNorm_one_eq_lintegral_eNorm hmeas.restrict, ← setLIntegral_const]
    refine setLIntegral_mono_ae hmeas.eNorm.restrict ?_
    filter_upwards [hhh'] with x hx hxF
    rw [hx]
    exact (hFE hxF).1.le
  exact ((ENNReal.mul_le_mul_iff_left hFpos.ne' hFtop.ne).1 (hlow.trans hkC)).not_gt hCt

/-- **Norming by simple functions.** On a σ-finite measure space, let `q` and `q'` be Hölder
conjugate. If `h ∈ L^q` satisfies `‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple function
`g ∈ L^{q'}`, then `‖h‖_q ≤ C`. -/
theorem MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le [SigmaFinite μ] {q q' : ℝ≥0∞}
    [q.HolderConjugate q'] {h : α → 𝕜} (hh : MemLp h q μ) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g q' μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q').1 rfl
    exact hh.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le hC
  · exact hh.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top hq hC

/-- If a continuous linear functional `Λ` on `L^q'(μ)` is integration against `h` at the class of
`σ`, then `‖∫ h σ‖ ≤ ‖Λ‖ ‖σ‖_q'`. This is the hypothesis of the norming lemmas above. -/
theorem Lp.enorm_integral_mul_le_of_apply_eq {q' : ℝ≥0∞} [Fact (1 ≤ q')]
    (Λ : StrongDual 𝕜 (Lp 𝕜 q' μ)) {h σ : α → 𝕜} (hσ : MemLp σ q' μ)
    (hΛ : Λ (hσ.toLp σ) = ∫ x, h x * hσ.toLp σ x ∂μ) :
    ‖∫ x, h x * σ x ∂μ‖ₑ ≤ ‖Λ‖ₑ * eLpNorm σ q' μ :=
  calc ‖∫ x, h x * σ x ∂μ‖ₑ = ‖Λ (hσ.toLp σ)‖ₑ := by
        rw [hΛ]
        congr 1
        exact integral_congr_ae (by filter_upwards [hσ.coeFn_toLp] with x hx; rw [hx])
    _ ≤ ‖Λ‖ₑ * ‖hσ.toLp σ‖ₑ := Λ.le_opENorm _
    _ = ‖Λ‖ₑ * eLpNorm σ q' μ := by rw [Lp.eNorm_def, eLpNorm_congr_ae hσ.coeFn_toLp]

end MeasureTheory

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}

section toDual

variable {q q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q.HolderConjugate q']

variable (𝕜 μ q q') in
/-- On a σ-finite measure space, for Hölder conjugate exponents `q` and `q'`, the integral pairing
`g ↦ (f ↦ ∫ g f dμ)` is a linear isometry from `L^q(μ)` to the continuous dual of `L^q'(μ)`:
integration against `g` is a continuous linear functional on `L^q'(μ)` of norm `‖g‖_q`. -/
noncomputable def toDual [SigmaFinite μ] : Lp 𝕜 q μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q' μ) where
  toLinearMap := ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q q' :
    Lp 𝕜 q μ →ₗ[𝕜] StrongDual 𝕜 (Lp 𝕜 q' μ))
  norm_map' g := by
    set Λ := (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q q' g
    -- Both norms are the real parts of the extended norms, so it suffices to compare those.
    rw [ContinuousLinearMap.coe_coe, ← toReal_eNorm, ← toReal_eNorm]
    congr 1
    -- Hölder's inequality gives `‖Λ‖ ≤ ‖g‖_q`; testing `Λ` on simple functions gives the converse.
    refine le_antisymm (Λ.opENorm_le_bound fun f => ?_) ?_
    · rw [ContinuousLinearMap.lpPairing_mul_eq_integral, Lp.eNorm_def, Lp.eNorm_def]
      exact TauCeti.enorm_integral_mul_le
    · rw [Lp.eNorm_def]
      exact (Lp.memLp g).eLpNorm_le_of_forall_enorm_integral_mul_le fun σ hσ =>
        enorm_integral_mul_le_of_apply_eq Λ hσ
          (ContinuousLinearMap.lpPairing_mul_eq_integral g _)

@[simp]
theorem toDual_apply [SigmaFinite μ] (g : Lp 𝕜 q μ) (f : Lp 𝕜 q' μ) :
    toDual 𝕜 μ q q' g f = ∫ x, g x * f x ∂μ := by
  rw [toDual, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.lpPairing_mul_eq_integral]

/-- Pairing `g ∈ L^q(μ)` with the indicator function of a set `s` of finite measure, scaled by
`c`, gives `c` times the integral of `g` over `s`. -/
-- High priority, so that `simp` uses this lemma before unfolding the pairing by `toDual_apply`.
@[simp high]
theorem toDual_indicatorConstLp [SigmaFinite μ] (g : Lp 𝕜 q μ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜) :
    toDual 𝕜 μ q q' g (indicatorConstLp q' hs hμs c) = (∫ x in s, g x ∂μ) * c := by
  rw [toDual_apply, ← integral_mul_const, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := q') (hs := hs) (hμs := hμs) (c := c)] with x hx
  by_cases hxs : x ∈ s <;> simp [hx, hxs]

end toDual

section NormingByLinfty

/-- Every `v : Lp 𝕜 1 μ` on any measure space is normed by some `u : Lp 𝕜 ∞ μ` of norm at most `1`:
`∫ x, v x * u x ∂μ = ‖v‖`. -/
theorem exists_norm_le_one_integral_mul_eq (v : Lp 𝕜 1 μ) :
    ∃ u : Lp 𝕜 ∞ μ, ‖u‖ ≤ 1 ∧ ∫ x, v x * u x ∂μ = ((‖v‖ : ℝ) : 𝕜) := by
  have hv_ae := (Lp.aestronglyMeasurable v).ae_eq_mk
  have hv_sm := (Lp.aestronglyMeasurable v).stronglyMeasurable_mk
  set v' : α → 𝕜 := (Lp.aestronglyMeasurable v).mk v
  set u₀ : α → 𝕜 := fun x ↦ ((‖v' x‖⁻¹ : ℝ) : 𝕜) * star (v' x)
  have hu₀_sm : StronglyMeasurable u₀ :=
    (RCLike.continuous_ofReal.comp_stronglyMeasurable
      hv_sm.norm.measurable.inv.stronglyMeasurable).mul
      (continuous_star.comp_stronglyMeasurable hv_sm)
  have hu₀_le (x : α) : ‖u₀ x‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)), norm_star]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  have hu_mem : MemLp u₀ ∞ μ :=
    memLp_top_of_bound hu₀_sm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hu₀_le)
  refine ⟨hu_mem.toLp u₀, Lp.norm_le_of_ae_bound_top zero_le_one ?_, ?_⟩
  · filter_upwards [hu_mem.coeFn_toLp] with x hx
    rw [hx]
    exact hu₀_le x
  · have hvu : (fun x ↦ v x * (hu_mem.toLp u₀) x) =ᵐ[μ] fun x ↦ ((‖v x‖ : ℝ) : 𝕜) := by
      filter_upwards [hv_ae, hu_mem.coeFn_toLp] with x hvx hux
      rw [hvx, hux]
      dsimp only [u₀]
      rcases eq_or_ne (v' x) 0 with h0 | h0
      · simp [h0]
      · have hn0 : ‖v' x‖ ≠ 0 := norm_ne_zero_iff.2 h0
        calc
          v' x * (((‖v' x‖⁻¹ : ℝ) : 𝕜) * star (v' x)) =
              ((‖v' x‖⁻¹ : ℝ) : 𝕜) * (v' x * starRingEnd 𝕜 (v' x)) := by
            rw [starRingEnd_apply]
            ring
          _ = ((‖v' x‖⁻¹ : ℝ) : 𝕜) * ((‖v' x‖ ^ 2 : ℝ) : 𝕜) := by
            rw [RCLike.mul_conj, RCLike.ofReal_pow]
          _ = ((‖v' x‖ : ℝ) : 𝕜) := by
            push_cast
            field_simp [RCLike.ofReal_ne_zero.2 hn0]
    rw [integral_congr_ae hvu, integral_ofReal, L1.norm_eq_integral_norm]

/-- Every finite family `y : ι → Lp 𝕜 1 μ` on any measure space is normed in `ℓ²(L¹)` by a family
`g : ι → Lp 𝕜 ∞ μ` with `∑ i, ‖g i x‖ ^ 2 ≤ 1` almost everywhere:
`∑ i, ∫ x, y i x * g i x ∂μ = ‖WithLp.toLp 2 y‖`. -/
theorem exists_ae_sum_norm_sq_le_one_sum_integral_mul_eq {ι : Type*} [Fintype ι]
    (y : ι → Lp 𝕜 1 μ) :
    ∃ g : ι → Lp 𝕜 ∞ μ, (∀ᵐ x ∂μ, ∑ i, ‖g i x‖ ^ 2 ≤ 1) ∧
      ∑ i, ∫ x, y i x * g i x ∂μ = ((‖WithLp.toLp 2 y‖ : ℝ) : 𝕜) := by
  set N : ℝ := ‖WithLp.toLp 2 y‖
  rcases (norm_nonneg (WithLp.toLp 2 y)).eq_or_lt with hN0 | hN
  · refine ⟨0, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero 𝕜 ∞ μ] with x hx
      simp only [Pi.zero_apply]
      rw [hx]
      simp
    · simp only [Pi.zero_apply, ← ContinuousLinearMap.lpPairing_mul_eq_integral (𝕜 := 𝕜),
        map_zero, Finset.sum_const_zero, N, ← hN0]
  · choose u hu_norm hu_int using fun i ↦ exists_norm_le_one_integral_mul_eq (y i)
    have hu_le (i : ι) : ∀ᵐ x ∂μ, ‖u i x‖ ≤ 1 :=
      (Lp.ae_norm_le_norm_top (u i)).mono fun _ hx ↦ hx.trans (hu_norm i)
    set g : ι → Lp 𝕜 ∞ μ := fun i ↦ ((‖y i‖ / N : ℝ) : 𝕜) • u i
    have hN_sq : N ^ 2 = ∑ i, ‖y i‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 (fun _ : ι ↦ Lp 𝕜 1 μ) (WithLp.toLp 2 y)
    refine ⟨g, ?_, ?_⟩
    · filter_upwards [Filter.eventually_all.mpr fun i ↦
          Lp.coeFn_smul (((‖y i‖ / N : ℝ) : 𝕜)) (u i),
        Filter.eventually_all.mpr hu_le] with x hsmul hle
      calc
        ∑ i, ‖g i x‖ ^ 2 ≤ ∑ i, (‖y i‖ / N) ^ 2 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hgi : ‖g i x‖ ≤ ‖y i‖ / N := by
            rw [hsmul i, Pi.smul_apply, norm_smul, RCLike.norm_ofReal,
              abs_of_nonneg (div_nonneg (norm_nonneg _) hN.le)]
            exact mul_le_of_le_one_right (div_nonneg (norm_nonneg _) hN.le) (hle i)
          exact sq_le_sq'
            ((neg_nonpos.2 (div_nonneg (norm_nonneg _) hN.le)).trans (norm_nonneg _)) hgi
        _ = (∑ i, ‖y i‖ ^ 2) / N ^ 2 := by
          simp_rw [div_pow]
          rw [← Finset.sum_div]
        _ = 1 := by rw [← hN_sq, div_self (pow_ne_zero 2 hN.ne')]
    · have hterm (i : ι) :
          ∫ x, y i x * g i x ∂μ = ((‖y i‖ ^ 2 / N : ℝ) : 𝕜) := by
        rw [← ContinuousLinearMap.lpPairing_mul_eq_integral (𝕜 := 𝕜), map_smul,
          ContinuousLinearMap.lpPairing_mul_eq_integral (𝕜 := 𝕜), hu_int i, smul_eq_mul,
          ← RCLike.ofReal_mul]
        congr 1
        ring
      simp_rw [hterm]
      rw [← RCLike.ofReal_sum, ← Finset.sum_div, ← hN_sq]
      congr 1
      field_simp [hN.ne']

end NormingByLinfty

end MeasureTheory.Lp
