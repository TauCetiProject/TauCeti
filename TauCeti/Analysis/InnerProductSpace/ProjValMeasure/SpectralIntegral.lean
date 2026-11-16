/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Null
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Unbounded spectral integrals against a projection-valued measure

For a normalized projection-valued measure `P : ProjValMeasure X H` on an arbitrary measurable
space `X` acting on a complex Hilbert space `H`, and any function `f : X → ℂ`, this file defines
the unbounded spectral integral `P.spectralIntegral f : H →ₗ.[ℂ] H` on the maximal second-moment
domain

`dom (P.spectralIntegral f) = {x : H | MemLp f 2 (P.diag x)}`.

For `x` in the domain, the Cauchy–Schwarz inequality for the variation of the polarized complex
measure `μ_(y,x) = P.polarizedComplexMeasure y x` shows that `f` is integrable against `μ_(y,x)`
and that `y ↦ star (∫ᵛ t, f t ∂[mul ℝ ℂ; μ_(y,x)])` is a bounded `ℂ`-linear functional on `H`.
By the Riesz representation theorem, there is a unique vector `P.spectralIntegral f x : H` with
matrix elements

`⟪y, P.spectralIntegral f x⟫_ℂ = ∫ᵛ t, f t ∂[mul ℝ ℂ; μ_(y,x)]`.

Omitting a measurability parameter from the definition gives unconditional rewriting and cleaner
transport, while keeping the exact hypotheses visible in every theorem:

* closedness (`isClosed_spectralIntegral`), the norm-square identity
  `‖P.spectralIntegral f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)` (`norm_sq_spectralIntegral_apply`),
  almost-everywhere invariance (`spectralIntegral_congr_ae`), formal adjointness of
  `P.spectralIntegral (star f)` (`isFormalAdjoint_spectralIntegral_star`), and intertwining with
  bounded Borel integrals (`spectralIntegral_integral_apply`) hold for every `f : X → ℂ`;
* density of the domain is equivalent to `∀ x : H, AEStronglyMeasurable f (P.diag x)`
  (`dense_spectralIntegral_domain_iff`), which in turn is equivalent to the adjoint identity
  `(P.spectralIntegral f)† = P.spectralIntegral (star f)` (`adjoint_spectralIntegral_iff`);
* for a measurable symbol `f`, the spectral cutoffs `P({‖f‖ ≤ n})` act as bounded Borel integrals
  and their ranges span a graph core (`hasCore_spectralIntegral`).

## Main definitions

* `TauCeti.ProjValMeasure.spectralIntegral`: the unbounded spectral integral `f[P] : H →ₗ.[ℂ] H`.

## Main results

* `TauCeti.ProjValMeasure.mem_spectralIntegral_domain_iff_memLp`,
  `TauCeti.ProjValMeasure.mem_spectralIntegral_domain_iff`: domain characterization.
* `TauCeti.ProjValMeasure.inner_spectralIntegral_apply`,
  `TauCeti.ProjValMeasure.eq_spectralIntegral_of_inner`: matrix-element characterization and
  uniqueness.
* `TauCeti.ProjValMeasure.spectralIntegral_congr_ae`,
  `TauCeti.ProjValMeasure.spectralIntegral_eq_spectralIntegral_iff`: `P`-almost-everywhere
  invariance and faithfulness.
* `TauCeti.ProjValMeasure.spectralIntegral_eq_toPMap`: agreement with the bounded Borel integral
  `P.integral`.
* `TauCeti.ProjValMeasure.spectralIntegral_integral_apply`,
  `TauCeti.ProjValMeasure.spectralIntegral_proj_apply`: intertwining with bounded Borel operators
  and spectral projections.
* `TauCeti.ProjValMeasure.norm_sq_spectralIntegral_apply`: the vector norm-square identity.
* `TauCeti.ProjValMeasure.isClosed_spectralIntegral`: closedness of the unbounded spectral
  integral.
* `TauCeti.ProjValMeasure.dense_spectralIntegral_domain_iff`,
  `TauCeti.ProjValMeasure.hasCore_spectralIntegral`: density and spectral-cutoff graph core.
* `TauCeti.ProjValMeasure.adjoint_spectralIntegral`,
  `TauCeti.ProjValMeasure.adjoint_spectralIntegral_iff`,
  `TauCeti.ProjValMeasure.norm_adjoint_spectralIntegral_apply`,
  `TauCeti.ProjValMeasure.isSelfAdjoint_spectralIntegral_iff`: adjoint, normality, and
  self-adjointness.
* `TauCeti.ProjValMeasure.existsUnique_spectralIntegral`: existence and uniqueness of the
  unbounded spectral integral with its domain, matrix elements, density, closedness, norm-square
  identity, and adjoint characterization.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  AMS, 2009, Section 3.1, equations (3.23) and (3.25)–(3.29), Theorem 3.2.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Chapters 4 and 5.
-/

public section

noncomputable section

open MeasureTheory Filter Topology LinearPMap
open scoped InnerProductSpace ENNReal

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Construction via Riesz representation -/

/-- The continuous `ℂ`-linear functional `y ↦ star (∫ᵛ f dμ_(y,x))` whose Riesz representative is
`P.spectralIntegral f x`. -/
private def spectralIntegralDual (P : ProjValMeasure X H) (f : X → ℂ) {x : H}
    (hx : MemLp f 2 (P.diag x)) : StrongDual ℂ H :=
  LinearMap.mkContinuous
    { toFun y := star (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
      map_add' y₁ y₂ := by
        rw [P.polarizedComplexMeasure_add_left,
          VectorMeasure.integral_add_vectorMeasure
            (P.integrable_polarizedComplexMeasure_of_memLp y₁ hx)
            (P.integrable_polarizedComplexMeasure_of_memLp y₂ hx),
          star_add]
      map_smul' c y := by
        rw [P.polarizedComplexMeasure_smul_left, VectorMeasure.integral_smul_vectorMeasure_mul,
          star_mul', star_star, RingHom.id_apply, smul_eq_mul] }
    (Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag x)))
    (fun y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_star]
      rw [mul_comm]
      exact P.norm_integral_polarizedComplexMeasure_le y hx)

private theorem spectralIntegralDual_apply (P : ProjValMeasure X H) (f : X → ℂ) {x : H}
    (hx : MemLp f 2 (P.diag x)) (y : H) :
    P.spectralIntegralDual f hx y =
      star (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :=
  rfl

private theorem inner_symm_spectralIntegralDual (P : ProjValMeasure X H) (f : X → ℂ) {x : H}
    (hx : MemLp f 2 (P.diag x)) (y : H) :
    ⟪y, (InnerProductSpace.toDual ℂ H).symm (P.spectralIntegralDual f hx)⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  rw [← inner_conj_symm, ← InnerProductSpace.toDual_apply_apply,
    LinearIsometryEquiv.apply_symm_apply, spectralIntegralDual_apply,
    RCLike.star_def, starRingEnd_self_apply]

/-- The **unbounded spectral integral** of `f : X → ℂ` against a normalized projection-valued
measure `P`, as a partial linear map `H →ₗ.[ℂ] H`. Its domain is the second-moment subspace
`{x | MemLp f 2 (P.diag x)}` and its matrix elements are `⟪y, P.spectralIntegral f x⟫ =
∫ᵛ t, f t ∂[mul ℝ ℂ; P.polarizedComplexMeasure y x]`. -/
def spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) : H →ₗ.[ℂ] H where
  domain :=
    { carrier := {x : H | MemLp f 2 (P.diag x)}
      zero_mem' := by simp [P.diag_zero]
      add_mem' {x y} hx hy := by
        refine MemLp.mono_measure (P.diag_add_le x y) ?_
        have hx' : MemLp f 2 ((2 : ℝ≥0∞) • P.diag x) := hx.smul_measure ENNReal.ofNat_ne_top
        have hy' : MemLp f 2 ((2 : ℝ≥0∞) • P.diag y) := hy.smul_measure ENNReal.ofNat_ne_top
        exact memLp_iff.2 ((eLpNorm_add_measure_le f one_le_two).trans_lt
          (ENNReal.add_lt_top.2 ⟨hx'.eLpNorm_lt_top, hy'.eLpNorm_lt_top⟩))
      smul_mem' c x hx := by
        rw [Set.mem_ofPred_eq, P.diag_smul]
        exact hx.smul_measure (ENNReal.pow_ne_top eNorm_ne_top) }
  toFun :=
    { toFun x := (InnerProductSpace.toDual ℂ H).symm (P.spectralIntegralDual f x.2)
      map_add' x y := by
        apply ext_inner_left ℂ
        intro z
        rw [inner_add_right, P.inner_symm_spectralIntegralDual,
          P.inner_symm_spectralIntegralDual, P.inner_symm_spectralIntegralDual,
          Submodule.coe_add, P.polarizedComplexMeasure_add_right,
          VectorMeasure.integral_add_vectorMeasure
            (P.integrable_polarizedComplexMeasure_of_memLp z x.2)
            (P.integrable_polarizedComplexMeasure_of_memLp z y.2)]
      map_smul' c x := by
        apply ext_inner_left ℂ
        intro z
        rw [RingHom.id_apply, inner_smul_right, P.inner_symm_spectralIntegralDual,
          P.inner_symm_spectralIntegralDual, SetLike.val_smul,
          P.polarizedComplexMeasure_smul_right, VectorMeasure.integral_smul_vectorMeasure_mul] }

/-! ## Domain, matrix elements, and uniqueness -/

/-- A vector `x` lies in the domain of `P.spectralIntegral f` iff `f ∈ L²(P.diag x)`. -/
@[simp]
theorem mem_spectralIntegral_domain_iff_memLp (P : ProjValMeasure X H) (f : X → ℂ) (x : H) :
    x ∈ (P.spectralIntegral f).domain ↔ MemLp f 2 (P.diag x) :=
  Iff.rfl

/-- For a symbol `f` that is a.e. strongly measurable for `P.diag x`, `x` lies in the domain of
`P.spectralIntegral f` iff its second spectral moment `∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x)` is finite. -/
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) {f : X → ℂ} {x : H}
    (hf : AEStronglyMeasurable f (P.diag x)) :
    x ∈ (P.spectralIntegral f).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ := by
  rw [mem_spectralIntegral_domain_iff_memLp, memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- **Matrix-element characterization** of the unbounded spectral integral: for every `x` in its
domain and every `y : H`, `⟪y, P.spectralIntegral f x⟫` is the integral of `f` against the
polarized complex measure `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (x : (P.spectralIntegral f).domain) (y : H) :
    ⟪y, P.spectralIntegral f x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] :=
  P.inner_symm_spectralIntegralDual f x.2 y

/-- A vector `w` equals `P.spectralIntegral f x` iff its inner products with all `y : H` match
the polarized integrals of `f`. -/
theorem spectralIntegral_apply_eq_of_inner (P : ProjValMeasure X H) (f : X → ℂ)
    (x : (P.spectralIntegral f).domain) {w : H}
    (h : ∀ y : H, ⟪y, w⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :
    P.spectralIntegral f x = w := by
  apply ext_inner_left ℂ
  intro y
  rw [P.inner_spectralIntegral_apply f x y, h y]

/-- **Uniqueness from domain and matrix elements**: any partial linear map with the same domain
and polarized matrix elements as `P.spectralIntegral f` equals `P.spectralIntegral f`. -/
theorem eq_spectralIntegral_of_inner (P : ProjValMeasure X H) (f : X → ℂ) {T : H →ₗ.[ℂ] H}
    (hdom : T.domain = (P.spectralIntegral f).domain)
    (hinner : ∀ (x : T.domain) (y : H),
      ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :
    T = P.spectralIntegral f := by
  refine LinearPMap.ext hdom fun x hx hxy => ?_
  apply ext_inner_left ℂ
  intro z
  rw [hinner ⟨x, hx⟩ z, P.inner_spectralIntegral_apply f ⟨x, hxy⟩ z]

/-- Symbols equal `P`-almost everywhere define the same unbounded spectral integral. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ} (h : f =ᶠ[P.ae] g) :
    P.spectralIntegral f = P.spectralIntegral g := by
  have hdom : (P.spectralIntegral f).domain = (P.spectralIntegral g).domain := by
    ext x
    exact memLp_congr_ae (P.ae_diag_of_ae x h)
  refine P.eq_spectralIntegral_of_inner g hdom fun x y => ?_
  rw [P.inner_spectralIntegral_apply]
  exact VectorMeasure.integral_congr_ae
    ((P.polarizedComplexMeasure_variation_absolutelyContinuous_right y x)
      (P.ae_diag_of_ae x h))

/-! ## Bounded symbols, intertwining, and spectral cutoffs -/

/-- If `f` agrees `P.diag x`-almost everywhere with a bounded Borel symbol `g`, then `x` lies in
the domain of `P.spectralIntegral f`. -/
theorem mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction (P : ProjValMeasure X H)
    {f : X → ℂ} {g : BoundedBorelFunction X} {x : H} (h : f =ᵐ[P.diag x] g) :
    x ∈ (P.spectralIntegral f).domain :=
  (MemLp.of_bound g.measurable.aestronglyMeasurable ‖g‖
    (Eventually.of_forall g.norm_coe_le_norm)).ae_eq h.symm

/-- If `f` agrees `P.diag x`-almost everywhere with a bounded Borel symbol `g`, then
`P.spectralIntegral f` acts on `x` as the bounded operator `P.integral g`. -/
theorem spectralIntegral_apply_of_ae_eq_boundedBorelFunction (P : ProjValMeasure X H)
    {f : X → ℂ} {g : BoundedBorelFunction X} {x : H} (h : f =ᵐ[P.diag x] g) :
    P.spectralIntegral f ⟨x, P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction h⟩ =
      P.integral g x := by
  refine P.spectralIntegral_apply_eq_of_inner f _ fun y => ?_
  rw [← P.integral_polarizedComplexMeasure_eq_inner_integral g y x]
  exact (VectorMeasure.integral_congr_ae
    ((P.polarizedComplexMeasure_variation_absolutelyContinuous_right y x) h)).symm

/-- For a bounded Borel symbol `f`, the unbounded spectral integral `P.spectralIntegral f`
recovers the bounded operator `P.integral f` on the whole space `⊤`. -/
theorem spectralIntegral_eq_toPMap (P : ProjValMeasure X H) (f : BoundedBorelFunction X) :
    P.spectralIntegral f = (P.integral f).toLinearMap.toPMap ⊤ := by
  refine (P.eq_spectralIntegral_of_inner f ?_ fun x y => ?_).symm
  · ext x
    simp [P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction (g := f) EventuallyEq.rfl]
  · exact (P.integral_polarizedComplexMeasure_eq_inner_integral f y x).symm

/-- The domain of the spectral integral of a bounded Borel symbol is the whole space `⊤`. -/
@[simp]
theorem spectralIntegral_boundedBorelFunction_domain (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) : (P.spectralIntegral f).domain = ⊤ := by
  rw [P.spectralIntegral_eq_toPMap f]
  rfl

/-- Every bounded Borel operator `P.integral g` leaves the domain of `P.spectralIntegral f`
invariant. -/
theorem integral_apply_mem_spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ)
    (g : BoundedBorelFunction X) {x : H} (hx : x ∈ (P.spectralIntegral f).domain) :
    P.integral g x ∈ (P.spectralIntegral f).domain := by
  rw [mem_spectralIntegral_domain_iff_memLp, P.diag_integral]
  have hle : (P.diag x).withDensity (fun t => ‖g t‖ₑ ^ 2) ≤ (‖g‖ₑ ^ 2) • P.diag x := by
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun t => by
      dsimp only
      exact pow_le_pow_left' (by
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (g.norm_coe_le_norm t)) 2)
  exact (hx.smul_measure (ENNReal.pow_ne_top eNorm_ne_top)).mono_measure hle

/-- **Intertwining with bounded Borel operators**: `P.spectralIntegral f` commutes with
`P.integral g` on its domain. -/
theorem spectralIntegral_integral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (g : BoundedBorelFunction X) (x : (P.spectralIntegral f).domain) :
    P.spectralIntegral f ⟨P.integral g x, P.integral_apply_mem_spectralIntegral_domain f g x.2⟩ =
      P.integral g (P.spectralIntegral f x) := by
  apply ext_inner_left ℂ
  intro y
  have hpol : P.polarizedComplexMeasure y (P.integral g x) =
      P.polarizedComplexMeasure (P.integral (star g) y) x := by
    rw [P.polarizedComplexMeasure_integral_right, P.polarizedComplexMeasure_integral_left]
    simp
  rw [P.inner_spectralIntegral_apply, hpol, ← P.inner_spectralIntegral_apply,
    map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- Every spectral projection `P.proj B hB` leaves the domain of `P.spectralIntegral f`
invariant. -/
theorem proj_apply_mem_spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ) (B : Set X)
    (hB : MeasurableSet B) {x : H} (hx : x ∈ (P.spectralIntegral f).domain) :
    P.proj B hB x ∈ (P.spectralIntegral f).domain := by
  simpa only [P.integral_indicator hB] using
    P.integral_apply_mem_spectralIntegral_domain f (BoundedBorelFunction.indicator B hB 1) hx

/-- Every spectral projection `P.proj B hB` commutes with `P.spectralIntegral f` on its domain. -/
theorem spectralIntegral_proj_apply (P : ProjValMeasure X H) (f : X → ℂ) (B : Set X)
    (hB : MeasurableSet B) (x : (P.spectralIntegral f).domain) :
    P.spectralIntegral f ⟨P.proj B hB x, P.proj_apply_mem_spectralIntegral_domain f B hB x.2⟩ =
      P.proj B hB (P.spectralIntegral f x) := by
  have hind := P.spectralIntegral_integral_apply f (BoundedBorelFunction.indicator B hB 1) x
  simpa only [P.integral_indicator hB] using hind

/-- The bounded Borel truncation `f · 1_{‖f‖ ≤ R}` of a measurable symbol `f`. -/
private def cutoffSymbol (f : X → ℂ) (hf : Measurable f) (R : ℝ) : BoundedBorelFunction X :=
  BoundedBorelFunction.ofFunction ({t | ‖f t‖ ≤ R}.indicator f)
    (hf.indicator (measurableSet_le hf.norm measurable_const))
    ⟨max R 0, le_max_right R 0, fun t => by
      by_cases ht : t ∈ {t | ‖f t‖ ≤ R}
      · rw [Set.indicator_of_mem ht]
        exact le_max_of_le_left (Set.mem_ofPred_eq.mp ht)
      · rw [Set.indicator_of_notMem ht, norm_zero]
        exact le_max_right R 0⟩

private theorem cutoffSymbol_apply (f : X → ℂ) (hf : Measurable f) (R : ℝ) (t : X) :
    cutoffSymbol f hf R t = ({t | ‖f t‖ ≤ R}.indicator f) t :=
  BoundedBorelFunction.ofFunction_apply ..

/-- Applying `P.proj {‖g‖ ≤ R}` to `P.spectralIntegral f x` produces
`P.integral (cutoffSymbol g R) x` whenever `f =ᵐ[P.diag x] g`. -/
private theorem proj_cutoff_spectralIntegral_eq_integral (P : ProjValMeasure X H) {f g : X → ℂ}
    (hg : Measurable g) (R : ℝ) (x : (P.spectralIntegral f).domain) (hfg : f =ᵐ[P.diag x] g) :
    P.proj {t | ‖g t‖ ≤ R} (measurableSet_le hg.norm measurable_const) (P.spectralIntegral f x) =
      P.integral (cutoffSymbol g hg R) x := by
  have hB : MeasurableSet {t | ‖g t‖ ≤ R} := measurableSet_le hg.norm measurable_const
  have hae : f =ᵐ[P.diag (P.proj {t | ‖g t‖ ≤ R} hB x)] cutoffSymbol g hg R := by
    rw [P.diag_proj]
    filter_upwards [ae_restrict_of_ae hfg, ae_restrict_mem hB] with t htf htB
    rw [htf, cutoffSymbol_apply, Set.indicator_of_mem htB]
  rw [← P.spectralIntegral_proj_apply f {t | ‖g t‖ ≤ R} hB x,
    P.spectralIntegral_apply_of_ae_eq_boundedBorelFunction hae, ← P.integral_indicator hB,
    ← mul_apply_eq_comp, ← map_mul]
  congr 2
  ext t
  by_cases ht : t ∈ {t | ‖g t‖ ≤ R} <;>
    simp [ht, cutoffSymbol_apply, BoundedBorelFunction.indicator_apply]

/-- Strong convergence `P({‖g‖ ≤ n}) v → v` for any measurable `g : X → ℂ`. -/
private theorem tendsto_proj_cutoff (P : ProjValMeasure X H) {g : X → ℂ} (hg : Measurable g)
    (v : H) :
    Tendsto (fun n : ℕ => P.proj {t | ‖g t‖ ≤ (n : ℝ)}
      (measurableSet_le hg.norm measurable_const) v) atTop (𝓝 v) := by
  have hE (n : ℕ) : MeasurableSet {t | ‖g t‖ ≤ (n : ℝ)} :=
    measurableSet_le hg.norm measurable_const
  have hmono : Monotone fun n : ℕ => {t | ‖g t‖ ≤ (n : ℝ)} :=
    fun _ _ hmn _ ht => Set.mem_ofPred_eq.mpr ((Set.mem_ofPred_eq.mp ht).trans (Nat.cast_le.2 hmn))
  have hunion : ⋃ n : ℕ, {t | ‖g t‖ ≤ (n : ℝ)} = Set.univ :=
    Set.eq_univ_iff_forall.2 fun t =>
      let ⟨n, hn⟩ := exists_nat_ge ‖g t‖
      Set.mem_iUnion.2 ⟨n, Set.mem_ofPred_eq.mpr hn⟩
  have h := P.tendsto_proj_iUnion_of_monotone hE hmono v
  simpa [P.proj_congr hunion (MeasurableSet.iUnion hE) MeasurableSet.univ, P.proj_univ] using h

/-- On any spectral cutoff set `{‖f‖ ≤ R}` of a measurable symbol `f`, every projected vector
`P({‖f‖ ≤ R}) x` lies in the domain of `P.spectralIntegral f`. -/
theorem proj_cutoff_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (R : ℝ) (x : H) :
    P.proj {t | ‖f t‖ ≤ R} (measurableSet_le hf.norm measurable_const) x ∈
      (P.spectralIntegral f).domain := by
  have hB : MeasurableSet {t | ‖f t‖ ≤ R} := measurableSet_le hf.norm measurable_const
  refine P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction (g := cutoffSymbol f hf R) ?_
  rw [P.diag_proj]
  filter_upwards [ae_restrict_mem hB] with t ht
  rw [cutoffSymbol_apply, Set.indicator_of_mem ht]

/-- On a spectral cutoff `{‖f‖ ≤ R}` of a measurable symbol `f`, `P.spectralIntegral f` agrees
with the bounded integral of any bounded Borel symbol equal `P.diag x`-almost everywhere to
`f · 1_{‖f‖ ≤ R}`. -/
theorem spectralIntegral_proj_cutoff_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (R : ℝ) (x : H) {g : BoundedBorelFunction X}
    (hg : (g : X → ℂ) =ᵐ[P.diag x] ({t | ‖f t‖ ≤ R}.indicator f)) :
    P.spectralIntegral f
        ⟨P.proj {t | ‖f t‖ ≤ R} (measurableSet_le hf.norm measurable_const) x,
          P.proj_cutoff_mem_spectralIntegral_domain hf R x⟩ =
      P.integral g x := by
  have hB : MeasurableSet {t | ‖f t‖ ≤ R} := measurableSet_le hf.norm measurable_const
  have hae : f =ᵐ[P.diag (P.proj {t | ‖f t‖ ≤ R} hB x)] g := by
    rw [P.diag_proj]
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem hB] with t htg htB
    rw [htg, Set.indicator_of_mem htB]
  rw [P.spectralIntegral_apply_of_ae_eq_boundedBorelFunction hae, ← P.integral_indicator hB,
    ← mul_apply_eq_comp, ← map_mul, ← sub_eq_zero, ← _root_.sub_apply, ← _root_.map_sub,
    P.integral_apply_eq_zero_iff]
  filter_upwards [hg] with t htg
  by_cases ht : t ∈ {t | ‖f t‖ ≤ R}
  · simp [ht, BoundedBorelFunction.indicator_apply]
  · simp [ht, htg, BoundedBorelFunction.indicator_apply]

/-! ## Norm-square identity, closedness, and density -/

/-- Monotone convergence for the second moments of the cutoffs `cutoffSymbol g hg n`. -/
private theorem iSup_lintegral_cutoffSymbol_sq {μ : Measure X} {g : X → ℂ} (hg : Measurable g) :
    ⨆ n : ℕ, ∫⁻ t, ‖cutoffSymbol g hg n t‖ₑ ^ 2 ∂μ = ∫⁻ t, ‖g t‖ₑ ^ 2 ∂μ := by
  have hmeas (n : ℕ) : Measurable fun t => ‖cutoffSymbol g hg n t‖ₑ ^ 2 :=
    ((cutoffSymbol g hg n).measurable.eNorm).pow_const 2
  have hmono : Monotone fun (n : ℕ) (t : X) => ‖cutoffSymbol g hg n t‖ₑ ^ 2 := by
    intro m n hmn t
    by_cases hm : t ∈ {t | ‖g t‖ ≤ (m : ℝ)}
    · have hn : t ∈ {t | ‖g t‖ ≤ (n : ℝ)} :=
        Set.mem_ofPred_eq.mpr ((Set.mem_ofPred_eq.mp hm).trans (Nat.cast_le.2 hmn))
      simp [cutoffSymbol_apply, Set.indicator_of_mem hm, Set.indicator_of_mem hn]
    · simp [cutoffSymbol_apply, Set.indicator_of_notMem hm]
  rw [← lintegral_iSup hmeas hmono]
  refine lintegral_congr fun t => le_antisymm (iSup_le fun n => ?_) ?_
  · by_cases hn : t ∈ {t | ‖g t‖ ≤ (n : ℝ)}
    · simp [cutoffSymbol_apply, Set.indicator_of_mem hn]
    · simp [cutoffSymbol_apply, Set.indicator_of_notMem hn]
  · obtain ⟨n, hn⟩ := exists_nat_ge ‖g t‖
    have ht : t ∈ {t | ‖g t‖ ≤ (n : ℝ)} := Set.mem_ofPred_eq.mpr hn
    exact le_iSup_of_le n (by rw [cutoffSymbol_apply, Set.indicator_of_mem ht])

/-- If `f =ᵐ[P.diag x] g` for measurable `g` and the cutoff norms
`‖P.integral (cutoffSymbol g n) x‖` are uniformly bounded, then `x` lies in the domain of
`P.spectralIntegral f`. -/
private theorem mem_spectralIntegral_domain_of_cutoff_bound (P : ProjValMeasure X H) {f g : X → ℂ}
    (hg : Measurable g) {x : H} (hfg : f =ᵐ[P.diag x] g) (C : ℝ)
    (hb : ∀ n : ℕ, ‖P.integral (cutoffSymbol g hg n) x‖ ≤ C) :
    x ∈ (P.spectralIntegral f).domain := by
  rw [P.mem_spectralIntegral_domain_iff (hg.aestronglyMeasurable.congr hfg.symm),
    lintegral_congr_ae (hfg.mono fun t ht => by rw [ht]), ← iSup_lintegral_cutoffSymbol_sq hg]
  refine (iSup_le fun n => ?_).trans_lt (ENNReal.ofReal_lt_top (r := C ^ 2))
  have hint : Integrable (fun t => ‖cutoffSymbol g hg n t‖ ^ 2) (P.diag x) :=
    .of_bound (((cutoffSymbol g hg n).measurable.norm.pow_const 2).aestronglyMeasurable)
      (‖cutoffSymbol g hg n‖ ^ 2) (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((cutoffSymbol g hg n).norm_coe_le_norm t) 2)
  calc ∫⁻ t, ‖cutoffSymbol g hg n t‖ₑ ^ 2 ∂(P.diag x)
      = ENNReal.ofReal (∫ t, ‖cutoffSymbol g hg n t‖ ^ 2 ∂(P.diag x)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
        simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (‖P.integral (cutoffSymbol g hg n) x‖ ^ 2) := by
        rw [P.norm_sq_integral_apply]
    _ ≤ ENNReal.ofReal (C ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb n) 2)

/-- **Norm-square identity** for the unbounded spectral integral: for every `x` in its domain,
`‖P.spectralIntegral f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. No measurability hypothesis on `f`
is needed. -/
theorem norm_sq_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (x : (P.spectralIntegral f).domain) :
    ‖P.spectralIntegral f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  let g : X → ℂ := x.2.aestronglyMeasurable.mk f
  have hg : Measurable g := x.2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[P.diag x] g := x.2.aestronglyMeasurable.ae_eq_mk
  have hlim_lhs : Tendsto (fun n : ℕ =>
      ‖P.proj {t | ‖g t‖ ≤ (n : ℝ)} (measurableSet_le hg.norm measurable_const)
        (P.spectralIntegral f x)‖ ^ 2) atTop (𝓝 (‖P.spectralIntegral f x‖ ^ 2)) :=
    ((P.tendsto_proj_cutoff hg (P.spectralIntegral f x)).norm).pow 2
  have hsq : Integrable (fun t => ‖g t‖ ^ 2) (P.diag x) := by
    simpa using (x.2.ae_eq hfg).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have hlim_rhs : Tendsto (fun n : ℕ => ∫ t, ‖cutoffSymbol g hg n t‖ ^ 2 ∂(P.diag x))
      atTop (𝓝 (∫ t, ‖g t‖ ^ 2 ∂(P.diag x))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖g t‖ ^ 2)
      (fun n => ((cutoffSymbol g hg n).measurable.norm.pow_const 2).aestronglyMeasurable) hsq
      (fun n => Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        by_cases ht : t ∈ {t | ‖g t‖ ≤ (n : ℝ)}
        · rw [cutoffSymbol_apply, Set.indicator_of_mem ht]
        · rw [cutoffSymbol_apply, Set.indicator_of_notMem ht]; simp)
      (Eventually.of_forall fun t => tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖g t‖)
        fun n hn => by
          have ht : t ∈ {t | ‖g t‖ ≤ (n : ℝ)} :=
            Set.mem_ofPred_eq.mpr ((Nat.le_ceil ‖g t‖).trans (Nat.cast_le.2 hn))
          rw [cutoffSymbol_apply, Set.indicator_of_mem ht])
  rw [integral_congr_ae (hfg.mono fun t ht => by rw [ht])]
  exact tendsto_nhds_unique hlim_lhs (hlim_rhs.congr fun n => by
    rw [← P.norm_sq_integral_apply, ← P.proj_cutoff_spectralIntegral_eq_integral hg n x hfg])

/-- Given a convergent sequence `u n → x` along whose diagonal measures `f` is a.e. strongly
measurable, there is a single measurable function `g` agreeing with `f` almost everywhere for
`P.diag x` and for every `P.diag (u n)`. -/
private theorem exists_measurable_ae_eq_of_tendsto (P : ProjValMeasure X H) {f : X → ℂ}
    {u : ℕ → H} {x : H} (hu : ∀ n, AEStronglyMeasurable f (P.diag (u n)))
    (hlim : Tendsto u atTop (𝓝 x)) :
    ∃ g : X → ℂ, Measurable g ∧ f =ᵐ[P.diag x] g ∧ ∀ n, f =ᵐ[P.diag (u n)] g := by
  let g_seq : ℕ → X → ℂ := fun n => (hu n).mk f
  let N : ℕ → Set X := fun n => toMeasurable (P.diag (u n)) {t | f t ≠ g_seq n t}
  have hN_null (n : ℕ) : P.diag (u n) (N n) = 0 := by
    rw [measure_toMeasurable]; exact (hu n).ae_eq_mk
  let D : ℕ → Set X := disjointed fun n => (N n)ᶜ
  have hD_meas (n : ℕ) : MeasurableSet (D n) :=
    MeasurableSet.disjointed (fun k => (measurableSet_toMeasurable _ _).compl) n
  let g : X → ℂ := fun t => ∑' n, (D n).indicator (g_seq n) t
  have hsum_on {n : ℕ} {t : X} (ht : t ∈ D n) :
      HasSum (fun k => (D k).indicator (g_seq k) t) (g_seq n t) := by
    simpa [Set.indicator_of_mem ht] using
      hasSum_single (f := fun k => (D k).indicator (g_seq k) t) n fun k hne =>
        Set.indicator_of_notMem (Set.disjoint_left.1 (disjoint_disjointed _ hne.symm) ht) _
  have hg_seq (k : ℕ) : Measurable (g_seq k) := (hu k).stronglyMeasurable_mk.measurable
  have hg : Measurable g :=
    measurable_of_tendsto_metrizable
      (fun M => Finset.measurable_sum (Finset.range M) fun k _ => (hg_seq k).indicator (hD_meas k))
      (tendsto_pi_nhds.2 fun t => by
        by_cases hex : ∃ n, t ∈ D n
        · obtain ⟨n, hn⟩ := hex
          have hgt : g t = g_seq n t := (hsum_on hn).tsum_eq
          rw [hgt]
          exact (hsum_on hn).tendsto_sum_nat
        · have hz (k : ℕ) : (D k).indicator (g_seq k) t = 0 :=
            Set.indicator_of_notMem (fun h => hex ⟨k, h⟩) (g_seq k)
          simp [g, hz])
  have hfg_on {t : X} (ht : t ∈ ⋃ n, D n) : f t = g t := by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ht
    have hgt : g t = g_seq n t := (hsum_on hn).tsum_eq
    rw [hgt]
    by_contra hne
    exact disjointed_subset (fun k => (N k)ᶜ) n hn (subset_toMeasurable _ _ hne)
  have hZ_meas : MeasurableSet (⋃ n, D n)ᶜ := (MeasurableSet.iUnion hD_meas).compl
  have hZ_null_u (n : ℕ) : P.diag (u n) (⋃ k, D k)ᶜ = 0 :=
    measure_mono_null (by
      rw [iUnion_disjointed]
      exact fun t ht => not_not.1 fun htA => ht (Set.mem_iUnion.2 ⟨n, htA⟩)) (hN_null n)
  have hZ_null_x : P.diag x (⋃ k, D k)ᶜ = 0 := by
    have hproj_u (n : ℕ) : P.proj (⋃ k, D k)ᶜ hZ_meas (u n) = 0 :=
      eNorm_eq_zero.1 <| sq_eq_zero_iff.1 <| by rw [P.enorm_sq_proj_apply, hZ_null_u n]
    have hproj_x : P.proj (⋃ k, D k)ᶜ hZ_meas x = 0 :=
      tendsto_nhds_unique (((P.proj (⋃ k, D k)ᶜ hZ_meas).continuous.tendsto x).comp hlim)
        ((tendsto_const_nhds (x := (0 : H))).congr fun n => (hproj_u n).symm)
    rw [← P.enorm_sq_proj_apply _ hZ_meas x, hproj_x]; simp
  exact ⟨g, hg, Filter.mem_of_superset (MeasureTheory.mem_ae_iff.2 hZ_null_x) (fun _ => hfg_on),
    fun n => Filter.mem_of_superset (MeasureTheory.mem_ae_iff.2 (hZ_null_u n)) (fun _ => hfg_on)⟩

/-- **Closedness of the unbounded spectral integral**: `P.spectralIntegral f` is closed for every
`f : X → ℂ`, with no measurability hypothesis on `f`. -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) :
    (P.spectralIntegral f).IsClosed := by
  rw [LinearPMap.IsClosed, ← isSeqClosed_iff_isClosed]
  intro seq p hseq hlim
  have hdom_seq (n : ℕ) : (seq n).1 ∈ (P.spectralIntegral f).domain :=
    mem_domain_of_mem_graph (hseq n)
  have hval_seq (n : ℕ) : P.spectralIntegral f ⟨(seq n).1, hdom_seq n⟩ = (seq n).2 :=
    ((image_iff _).2 (hseq n)).symm
  obtain ⟨g, hg, hfg_x, hfg_u⟩ := P.exists_measurable_ae_eq_of_tendsto
    (fun n => (hdom_seq n).aestronglyMeasurable) ((continuous_fst.tendsto p).comp hlim)
  let E (k : ℕ) : Set X := {t | ‖g t‖ ≤ (k : ℝ)}
  have hE (k : ℕ) : MeasurableSet (E k) := measurableSet_le hg.norm measurable_const
  have hproj_eq (k : ℕ) : P.proj (E k) (hE k) p.2 = P.integral (cutoffSymbol g hg k) p.1 := by
    have hstep (n : ℕ) :
        P.proj (E k) (hE k) (seq n).2 = P.integral (cutoffSymbol g hg k) (seq n).1 := by
      rw [← hval_seq n]
      exact P.proj_cutoff_spectralIntegral_eq_integral hg k ⟨(seq n).1, hdom_seq n⟩ (hfg_u n)
    have h1 := ((P.proj (E k) (hE k)).continuous.tendsto p.2).comp
      ((continuous_snd.tendsto p).comp hlim)
    have h2 := ((P.integral (cutoffSymbol g hg k)).continuous.tendsto p.1).comp
      ((continuous_fst.tendsto p).comp hlim)
    exact tendsto_nhds_unique h1 (h2.congr fun n => (hstep n).symm)
  have hdom_p : p.1 ∈ (P.spectralIntegral f).domain :=
    P.mem_spectralIntegral_domain_of_cutoff_bound hg hfg_x ‖p.2‖ fun k => by
      rw [← hproj_eq k]
      exact P.norm_proj_apply_le _ _ p.2
  rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
  refine ⟨⟨p.1, hdom_p⟩, rfl, ?_⟩
  refine tendsto_nhds_unique (P.tendsto_proj_cutoff hg (P.spectralIntegral f ⟨p.1, hdom_p⟩))
    ((P.tendsto_proj_cutoff hg p.2).congr fun k => ?_)
  rw [hproj_eq k, P.proj_cutoff_spectralIntegral_eq_integral hg k ⟨p.1, hdom_p⟩ hfg_x]

/-- **Density characterization**: the domain of `P.spectralIntegral f` is dense in `H` iff `f` is
a.e. strongly measurable with respect to every diagonal measure `P.diag x`. -/
theorem dense_spectralIntegral_domain_iff (P : ProjValMeasure X H) (f : X → ℂ) :
    Dense ((P.spectralIntegral f).domain : Set H) ↔
      ∀ x : H, AEStronglyMeasurable f (P.diag x) := by
  constructor
  · intro hd x
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.1 (hd x)
    obtain ⟨g, hg, hfg, _⟩ := P.exists_measurable_ae_eq_of_tendsto
      (fun n => (hu_mem n).aestronglyMeasurable) hu_lim
    exact hg.aestronglyMeasurable.congr hfg.symm
  · intro hf x
    let g : X → ℂ := (hf x).mk f
    have hg : Measurable g := (hf x).stronglyMeasurable_mk.measurable
    have hfg : f =ᵐ[P.diag x] g := (hf x).ae_eq_mk
    refine mem_closure_iff_seq_limit.2
      ⟨fun n => P.proj {t | ‖g t‖ ≤ (n : ℝ)} (measurableSet_le hg.norm measurable_const) x,
        fun n => ?_, P.tendsto_proj_cutoff hg x⟩
    have hB : MeasurableSet {t | ‖g t‖ ≤ (n : ℝ)} := measurableSet_le hg.norm measurable_const
    refine P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction
      (g := cutoffSymbol g hg n) ?_
    rw [P.diag_proj]
    filter_upwards [ae_restrict_of_ae hfg, ae_restrict_mem hB] with t htf htE
    rw [htf, cutoffSymbol_apply, Set.indicator_of_mem htE]

/-- For a measurable symbol `f`, the domain of `P.spectralIntegral f` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    Dense ((P.spectralIntegral f).domain : Set H) :=
  (P.dense_spectralIntegral_domain_iff f).2 fun _ => hf.aestronglyMeasurable

/-- **Truncation graph core**: for a measurable symbol `f`, the span of the spectral cutoff ranges
`⨆ n : ℕ, range (P({‖f‖ ≤ n}))` is a graph core for `P.spectralIntegral f`. -/
theorem hasCore_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f).HasCore
      (⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ (n : ℝ)}
        (measurableSet_le hf.norm measurable_const)).range) := by
  let E : ℕ → Set X := fun n => {t | ‖f t‖ ≤ (n : ℝ)}
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_le hf.norm measurable_const
  set S : Submodule ℂ H := ⨆ n : ℕ, (P.proj (E n) (hE n)).range
  have hS_le : S ≤ (P.spectralIntegral f).domain := by
    refine iSup_le fun n => ?_
    rintro _ ⟨x, rfl⟩
    exact P.proj_cutoff_mem_spectralIntegral_domain hf n x
  refine ((P.isClosed_spectralIntegral f).hasCore_iff_graph_subset_closure hS_le).2 ?_
  rintro ⟨x, y⟩ hxy
  have hx : x ∈ (P.spectralIntegral f).domain := mem_domain_of_mem_graph hxy
  have hy : P.spectralIntegral f ⟨x, hx⟩ = y := ((image_iff _).2 hxy).symm
  refine mem_closure_iff_seq_limit.2
    ⟨fun n => (P.proj (E n) (hE n) x, P.proj (E n) (hE n) y), fun n => ?_,
      (P.tendsto_proj_cutoff hf x).prodMk_nhds (P.tendsto_proj_cutoff hf y)⟩
  have hmemS : P.proj (E n) (hE n) x ∈ S :=
    le_iSup (fun k => (P.proj (E k) (hE k)).range) n ⟨x, rfl⟩
  dsimp only
  rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
  have hdom : P.proj (E n) (hE n) x ∈ ((P.spectralIntegral f).domRestrict S).domain := by
    rw [domRestrict_domain]
    exact ⟨hmemS, hS_le hmemS⟩
  refine ⟨⟨P.proj (E n) (hE n) x, hdom⟩, rfl, ?_⟩
  rw [domRestrict_le.2 (y := ⟨P.proj (E n) (hE n) x,
    P.proj_apply_mem_spectralIntegral_domain f (E n) (hE n) hx⟩) rfl, ← hy]
  exact P.spectralIntegral_proj_apply f (E n) (hE n) ⟨x, hx⟩

/-! ## Adjoint, normality, self-adjointness, and faithfulness -/

/-- The domain of `P.spectralIntegral (star f)` coincides with that of `P.spectralIntegral f`. -/
@[simp]
theorem spectralIntegral_star_domain (P : ProjValMeasure X H) (f : X → ℂ) :
    (P.spectralIntegral (star f)).domain = (P.spectralIntegral f).domain := by
  ext x
  simp only [mem_spectralIntegral_domain_iff_memLp]
  exact ⟨fun hx => by simpa [star_star] using hx.star, fun hx => hx.star⟩

/-- `P.spectralIntegral (star f)` is a formal adjoint of `P.spectralIntegral f` for every
`f : X → ℂ`. -/
theorem isFormalAdjoint_spectralIntegral_star (P : ProjValMeasure X H) (f : X → ℂ) :
    (P.spectralIntegral (star f)).IsFormalAdjoint (P.spectralIntegral f) := by
  intro x y
  rw [← inner_conj_symm, P.inner_spectralIntegral_apply, ← RCLike.star_def,
    ← P.integral_polarizedComplexMeasure_star]
  simpa [star_star] using (P.inner_spectralIntegral_apply f y x).symm

/-- **Adjoint of the unbounded spectral integral**: whenever `P.spectralIntegral f` is densely
defined, its Hilbert adjoint is `P.spectralIntegral (star f)`. -/
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ)
    (hd : Dense ((P.spectralIntegral f).domain : Set H)) :
    (P.spectralIntegral f)† = P.spectralIntegral (star f) := by
  have hle : P.spectralIntegral (star f) ≤ (P.spectralIntegral f)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd
      (by simpa [star_star] using P.isFormalAdjoint_spectralIntegral_star (star f))
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  set w : H := (P.spectralIntegral f)† ⟨y, hy⟩
  have hfy : AEStronglyMeasurable f (P.diag y) := (P.dense_spectralIntegral_domain_iff f).1 hd y
  let g : X → ℂ := hfy.mk f
  have hg : Measurable g := hfy.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[P.diag y] g := hfy.ae_eq_mk
  rw [P.spectralIntegral_star_domain]
  refine P.mem_spectralIntegral_domain_of_cutoff_bound hg hfg ‖w‖ fun n => ?_
  set gn : BoundedBorelFunction X := cutoffSymbol g hg n
  set xn : H := P.integral (star gn) y
  have hae : f =ᵐ[P.diag xn] gn := by
    rw [P.diag_integral, EventuallyEq,
      ae_withDensity_iff ((((star gn).measurable.eNorm).pow_const 2))]
    filter_upwards [hfg] with t htf hne
    have hgn_ne : gn t ≠ 0 := fun h0 => hne (by simp [h0])
    have htE : t ∈ {t | ‖g t‖ ≤ (n : ℝ)} := by
      by_contra hnot
      exact hgn_ne (by rw [cutoffSymbol_apply, Set.indicator_of_notMem hnot])
    rw [htf, cutoffSymbol_apply, Set.indicator_of_mem htE]
  have hxn_dom : xn ∈ (P.spectralIntegral f).domain :=
    P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction hae
  have hinner : ⟪w, xn⟫_ℂ = ((‖xn‖ ^ 2 : ℝ) : ℂ) := by
    have hadj := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ ⟨xn, hxn_dom⟩
    rw [P.spectralIntegral_apply_of_ae_eq_boundedBorelFunction hae] at hadj
    rw [hadj, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have hsq : ‖xn‖ ^ 2 ≤ ‖w‖ * ‖xn‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) w xn
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at this
  have hnorm_eq : ‖P.integral gn y‖ = ‖xn‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [P.norm_sq_integral_apply, P.norm_sq_integral_apply]
    simp only [BoundedBorelFunction.star_apply, norm_star]
  rw [hnorm_eq]
  by_cases h0 : ‖xn‖ = 0
  · rw [h0]; exact norm_nonneg w
  · exact le_of_mul_le_mul_right (by simpa [sq] using hsq)
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

/-- The adjoint identity `(P.spectralIntegral f)† = P.spectralIntegral (star f)` holds if and only
if `P.spectralIntegral f` is densely defined. -/
theorem adjoint_spectralIntegral_iff (P : ProjValMeasure X H) (f : X → ℂ) :
    (P.spectralIntegral f)† = P.spectralIntegral (star f) ↔
      Dense ((P.spectralIntegral f).domain : Set H) := by
  refine ⟨fun h => ?_, P.adjoint_spectralIntegral f⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
  have horth : ∀ x : (P.spectralIntegral f).domain, ⟪y, P.spectralIntegral f x⟫_ℂ = 0 := by
    intro x
    let g : X → ℂ := x.2.aestronglyMeasurable.mk f
    have hg : Measurable g := x.2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hfg : f =ᵐ[P.diag x] g := x.2.aestronglyMeasurable.ae_eq_mk
    refine tendsto_nhds_unique
      (((continuous_const.inner continuous_id).tendsto _).comp
        (P.tendsto_proj_cutoff hg (P.spectralIntegral f x)))
      (tendsto_const_nhds.congr fun n => ?_)
    have hmem : P.proj {t | ‖g t‖ ≤ (n : ℝ)} (measurableSet_le hg.norm measurable_const)
        (P.spectralIntegral f x) ∈ (P.spectralIntegral f).domain := by
      rw [P.proj_cutoff_spectralIntegral_eq_integral hg n x hfg]
      exact P.integral_apply_mem_spectralIntegral_domain f _ x.2
    exact (Submodule.inner_left_of_mem_orthogonal hmem hy).symm
  have hy_adj : y ∈ ((P.spectralIntegral f)†).domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨0, fun x => by simp [horth x]⟩
  rw [h, P.spectralIntegral_star_domain] at hy_adj
  exact inner_self_eq_zero.1 (Submodule.inner_left_of_mem_orthogonal hy_adj hy)

/-- For a densely defined `P.spectralIntegral f`, its adjoint has the same domain. -/
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ)
    (hd : Dense ((P.spectralIntegral f).domain : Set H)) :
    ((P.spectralIntegral f)†).domain = (P.spectralIntegral f).domain := by
  rw [P.adjoint_spectralIntegral f hd, P.spectralIntegral_star_domain]

/-- **Normality of the unbounded spectral integral**: for a densely defined `P.spectralIntegral f`,
`‖(P.spectralIntegral f)† x‖ = ‖P.spectralIntegral f x‖` for every `x` in the domain. -/
theorem norm_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (hd : Dense ((P.spectralIntegral f).domain : Set H)) (x : (P.spectralIntegral f).domain) :
    ‖(P.spectralIntegral f)†
        ⟨(x : H), by rw [P.adjoint_spectralIntegral_domain f hd]; exact x.2⟩‖ =
      ‖P.spectralIntegral f x‖ := by
  have heq : (P.spectralIntegral f)†
      ⟨(x : H), by rw [P.adjoint_spectralIntegral_domain f hd]; exact x.2⟩ =
      P.spectralIntegral (star f)
        ⟨(x : H), by rw [P.spectralIntegral_star_domain]; exact x.2⟩ :=
    (LinearPMap.dExt_iff.1 (P.adjoint_spectralIntegral f hd)).2 rfl
  rw [heq]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [P.norm_sq_spectralIntegral_apply, P.norm_sq_spectralIntegral_apply]
  simp only [Pi.star_apply, norm_star]

/-- On the common cutoff `{‖f'‖ ≤ n} ∩ {‖g'‖ ≤ n}`, equality of `P.spectralIntegral f` and
`P.spectralIntegral g` forces `f' = g'` `P.diag x`-almost everywhere. -/
private theorem ae_eq_on_common_cutoff (P : ProjValMeasure X H) {f g f' g' : X → ℂ}
    (h : P.spectralIntegral f = P.spectralIntegral g) (hf' : Measurable f') (hg' : Measurable g')
    {x : H} (hff' : f =ᵐ[P.diag x] f') (hgg' : g =ᵐ[P.diag x] g') (n : ℕ) :
    ∀ᵐ t ∂(P.diag x), ‖f' t‖ ≤ (n : ℝ) → ‖g' t‖ ≤ (n : ℝ) → f' t = g' t := by
  let E : Set X := {t | ‖f' t‖ ≤ (n : ℝ)} ∩ {t | ‖g' t‖ ≤ (n : ℝ)}
  have hE : MeasurableSet E :=
    (measurableSet_le hf'.norm measurable_const).inter (measurableSet_le hg'.norm measurable_const)
  let mk (u : X → ℂ) (hu : Measurable u) (hle : ∀ t ∈ E, ‖u t‖ ≤ (n : ℝ)) :
      BoundedBorelFunction X :=
    BoundedBorelFunction.ofFunction (E.indicator u) (hu.indicator hE)
      ⟨n, Nat.cast_nonneg n, fun t => by
        by_cases ht : t ∈ E
        · rw [Set.indicator_of_mem ht]; exact hle t ht
        · rw [Set.indicator_of_notMem ht, norm_zero]; exact Nat.cast_nonneg n⟩
  let fn := mk f' hf' fun _ ht => Set.mem_ofPred_eq.mp ht.1
  let gn := mk g' hg' fun _ ht => Set.mem_ofPred_eq.mp ht.2
  have hae (u u' : X → ℂ) (hu : Measurable u') (hle : ∀ t ∈ E, ‖u' t‖ ≤ (n : ℝ))
      (huu' : u =ᵐ[P.diag x] u') : u =ᵐ[P.diag (P.proj E hE x)] mk u' hu hle := by
    rw [P.diag_proj]
    filter_upwards [ae_restrict_of_ae huu', ae_restrict_mem hE] with t htu htE
    simp [mk, htu, Set.indicator_of_mem htE]
  have hae_f := hae f f' hf' (fun _ ht => Set.mem_ofPred_eq.mp ht.1) hff'
  have hae_g := hae g g' hg' (fun _ ht => Set.mem_ofPred_eq.mp ht.2) hgg'
  have hmul (u : BoundedBorelFunction X) (hu : ∀ t ∉ E, u t = 0) :
      P.integral u (P.proj E hE x) = P.integral u x := by
    rw [← P.integral_indicator hE, ← mul_apply_eq_comp, ← map_mul]
    congr 2; ext t; by_cases ht : t ∈ E <;> simp [ht, hu, BoundedBorelFunction.indicator_apply]
  have hact : P.integral (fn - gn) x = 0 := by
    have heq_op :
        P.spectralIntegral f ⟨P.proj E hE x,
          P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction hae_f⟩ =
        P.spectralIntegral g ⟨P.proj E hE x,
          P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction hae_g⟩ :=
      (LinearPMap.dExt_iff.1 h).2 rfl
    rw [P.spectralIntegral_apply_of_ae_eq_boundedBorelFunction hae_f,
      P.spectralIntegral_apply_of_ae_eq_boundedBorelFunction hae_g,
      hmul fn (fun t ht => by simp [fn, mk, Set.indicator_of_notMem ht]),
      hmul gn (fun t ht => by simp [gn, mk, Set.indicator_of_notMem ht])] at heq_op
    rw [_root_.map_sub, _root_.sub_apply, sub_eq_zero]
    exact heq_op
  filter_upwards [(P.integral_apply_eq_zero_iff (fn - gn) x).1 hact] with t ht hfn hgn
  have htE : t ∈ E := ⟨Set.mem_ofPred_eq.mpr hfn, Set.mem_ofPred_eq.mpr hgn⟩
  have hsub : fn t - gn t = 0 := by simpa using ht
  simpa [fn, gn, mk, Set.indicator_of_mem htE, sub_eq_zero] using hsub

/-- **Faithfulness**: when `P.spectralIntegral f` is densely defined, `P.spectralIntegral f =
P.spectralIntegral g` iff `f = g` `P`-almost everywhere. -/
theorem spectralIntegral_eq_spectralIntegral_iff (P : ProjValMeasure X H) {f g : X → ℂ}
    (hd : Dense ((P.spectralIntegral f).domain : Set H)) :
    P.spectralIntegral f = P.spectralIntegral g ↔ f =ᶠ[P.ae] g := by
  refine ⟨fun h => ?_, P.spectralIntegral_congr_ae⟩
  rw [EventuallyEq, P.eventually_ae_iff]
  intro x
  have hfx : AEStronglyMeasurable f (P.diag x) := (P.dense_spectralIntegral_domain_iff f).1 hd x
  have hgx : AEStronglyMeasurable g (P.diag x) :=
    (P.dense_spectralIntegral_domain_iff g).1 (h ▸ hd) x
  have hcut := P.ae_eq_on_common_cutoff h hfx.stronglyMeasurable_mk.measurable
    hgx.stronglyMeasurable_mk.measurable hfx.ae_eq_mk hgx.ae_eq_mk
  filter_upwards [hfx.ae_eq_mk, hgx.ae_eq_mk, ae_all_iff.2 hcut] with t htf htg hall
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ‖hfx.mk f t‖
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ‖hgx.mk g t‖
  rw [htf, htg]
  exact hall (max n₁ n₂) (hn₁.trans (Nat.cast_le.2 (le_max_left _ _)))
    (hn₂.trans (Nat.cast_le.2 (le_max_right _ _)))

/-- **Self-adjointness characterization**: `P.spectralIntegral f` is self-adjoint iff it is
densely defined and `f` is real `P`-almost everywhere. -/
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) (f : X → ℂ) :
    IsSelfAdjoint (P.spectralIntegral f) ↔
      Dense ((P.spectralIntegral f).domain : Set H) ∧ ∀ᶠ t in P.ae, star (f t) = f t := by
  constructor
  · intro hA
    have hd : Dense ((P.spectralIntegral f).domain : Set H) := hA.dense_domain
    have hadj : P.spectralIntegral (star f) = P.spectralIntegral f := by
      rw [← P.adjoint_spectralIntegral f hd]
      exact LinearPMap.isSelfAdjoint_def.1 hA
    have hd' : Dense ((P.spectralIntegral (star f)).domain : Set H) := by
      rwa [P.spectralIntegral_star_domain]
    exact ⟨hd, (P.spectralIntegral_eq_spectralIntegral_iff hd').1 hadj⟩
  · rintro ⟨hd, hreal⟩
    rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral f hd]
    exact P.spectralIntegral_congr_ae hreal

/-- The spectral integral of a real-valued function that is a.e. strongly measurable for every
diagonal measure is self-adjoint. -/
theorem isSelfAdjoint_spectralIntegral_ofReal (P : ProjValMeasure X H) {f : X → ℝ}
    (hf : ∀ x : H, AEStronglyMeasurable f (P.diag x)) :
    IsSelfAdjoint (P.spectralIntegral fun t => (f t : ℂ)) :=
  (P.isSelfAdjoint_spectralIntegral_iff _).2
    ⟨(P.dense_spectralIntegral_domain_iff _).2 fun x =>
        Complex.continuous_ofReal.comp_aestronglyMeasurable (hf x),
      Eventually.of_forall fun t => Complex.conj_ofReal (f t)⟩

/-! ## Existence and uniqueness of the unbounded spectral integral -/

/-- **Existence and uniqueness of the unbounded spectral integral.** For any normalized
projection-valued measure `P` on an arbitrary measurable space `X` and any `f : X → ℂ` that is
a.e. strongly measurable for every diagonal measure `P.diag x` (in particular, any measurable
`f`), there is a unique partial linear map `T : H →ₗ.[ℂ] H` whose domain is the second-moment
subspace `{x | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` and whose matrix elements are the integrals of
`f` against the polarized measures `P.polarizedComplexMeasure y x`. It is densely defined and
closed, its norm square is the second spectral moment, and its Hilbert adjoint has the same domain
and the polarized matrix elements of `star f`. -/
theorem existsUnique_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : ∀ x : H, AEStronglyMeasurable f (P.diag x)) :
    ∃! T : H →ₗ.[ℂ] H,
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ =
          ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (∀ x : T.domain, ‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) ∧
      T.adjoint.domain = T.domain ∧
      (∀ (x : T.adjoint.domain) (y : H),
        ⟪y, T.adjoint x⟫_ℂ =
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  have hd : Dense ((P.spectralIntegral f).domain : Set H) :=
    (P.dense_spectralIntegral_domain_iff f).2 hf
  refine ⟨P.spectralIntegral f, ⟨fun x => P.mem_spectralIntegral_domain_iff (hf x),
    P.inner_spectralIntegral_apply f, hd, P.isClosed_spectralIntegral f,
    P.norm_sq_spectralIntegral_apply f, P.adjoint_spectralIntegral_domain f hd, fun x y => ?_⟩,
    fun T hT => ?_⟩
  · have hadj : (P.spectralIntegral f)† = P.spectralIntegral (star f) :=
      P.adjoint_spectralIntegral f hd
    have hx' : (x : H) ∈ (P.spectralIntegral (star f)).domain := hadj ▸ x.2
    have heq : (P.spectralIntegral f)† x = P.spectralIntegral (star f) ⟨(x : H), hx'⟩ :=
      (LinearPMap.dExt_iff.1 hadj).2 rfl
    rw [heq, P.inner_spectralIntegral_apply]
    rfl
  · refine P.eq_spectralIntegral_of_inner f ?_ hT.2.1
    ext x
    rw [hT.1 x, P.mem_spectralIntegral_domain_iff (hf x)]

end ProjValMeasure
end TauCeti
