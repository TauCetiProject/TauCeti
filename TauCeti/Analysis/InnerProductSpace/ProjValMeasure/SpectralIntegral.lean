/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement
public import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.VectorMeasure.Integral

/-!
# Unbounded spectral integration against a projection-valued measure

Let `P` be a normalized projection-valued measure on an arbitrary measurable space `X` acting on a
complex Hilbert space `H`, with finite diagonal scalar measures `P.diag x` and polarized complex
measures `P.polarizedComplexMeasure y x`. For an arbitrary measurable symbol `f : X → ℂ`, this file
constructs the unbounded spectral integral `P.spectralIntegral f hf : H →ₗ.[ℂ] H` on its maximal
second-moment domain

`{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`

as the strong limit of the bounded Borel integrals `P.integral` of the level-set truncations
`BoundedBorelFunction.truncate f hf M` as `M → ∞` (`tendsto_integral_truncate_spectralIntegral`). No
topological or countability assumption is placed on `X`, and no separability assumption is placed
on `H`.

## Main declarations

* `ProjValMeasure.spectralIntegral`: the unbounded partial linear operator `∫ f dP` of a measurable
  symbol `f : X → ℂ`, with domain `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`
  (`mem_spectralIntegral_domain_iff`, `spectralIntegral_star_domain`,
  `mem_spectralIntegral_domain_iff_memLp`, and
  `mem_spectralIntegral_domain_iff_integrable_norm_sq`).
* `ProjValMeasure.dense_spectralIntegral_domain`,
  `ProjValMeasure.spectralIntegral_hasCore_iSup_range_proj`, and
  `ProjValMeasure.spectralIntegral_hasCore_iSup_range_proj_norm_le`: the domain of
  `P.spectralIntegral f hf` is dense in `H`, and the supremum of the ranges of any family of
  spectral projections converging strongly to the identity along a nontrivial (`NeBot`) filter and
  mapping into the domain (in particular `⨆ n : ℕ, LinearMap.range (P.proj {‖f‖ ≤ n} _)`)
  is a graph core for `P.spectralIntegral f hf`.
* `ProjValMeasure.norm_sq_spectralIntegral_apply` and `ProjValMeasure.diag_spectralIntegral`: the
  second-moment norm identity `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)` and
  the diagonal measure density `P.diag (P.spectralIntegral f hf x) = (P.diag x).withDensity _`.
* `ProjValMeasure.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain` and
  `ProjValMeasure.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain_left`: when
  either vector belongs to the domain, `f` is integrable against `P.polarizedComplexMeasure y x`.
* `ProjValMeasure.inner_spectralIntegral_apply`,
  `ProjValMeasure.inner_spectralIntegral_apply_left`,
  `ProjValMeasure.spectralIntegral_apply_eq_of_inner`,
  `ProjValMeasure.polarizedComplexMeasure_spectralIntegral_right`,
  `ProjValMeasure.polarizedComplexMeasure_spectralIntegral_left`, and
  `ProjValMeasure.eq_spectralIntegral_of_domain_of_inner`: matrix-element and weighted-measure
  formulas for `P.spectralIntegral f hf`, and uniqueness from the domain and matrix elements.
* `ProjValMeasure.mem_spectralIntegral_domain_congr_ae`,
  `ProjValMeasure.spectralIntegral_apply_congr_ae`,
  `ProjValMeasure.spectralIntegral_coe_boundedBorelFunction`,
  `ProjValMeasure.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction`,
  `ProjValMeasure.spectralIntegral_apply_of_ae_eq_boundedBorelFunction`,
  `ProjValMeasure.integral_apply_mem_spectralIntegral_domain`,
  `ProjValMeasure.spectralIntegral_integral_apply`,
  `ProjValMeasure.spectralIntegral_proj_apply`,
  `ProjValMeasure.proj_mem_spectralIntegral_domain_of_bound`,
  `ProjValMeasure.spectralIntegral_proj_eq_integral_indicator_of_ae_eq`, and
  `ProjValMeasure.spectralIntegral_proj_norm_le_eq_integral_truncate`: vectorwise a.e. congruence,
  compatibility and intertwining with the bounded Borel integral `P.integral`, spectral
  projections `P.proj`, and level-set truncations.
* `ProjValMeasure.spectralIntegral_eq_zero_iff`,
  `ProjValMeasure.spectralIntegral_eq_spectralIntegral_iff`, and
  `ProjValMeasure.spectralIntegral_map`: `P`-almost-everywhere characterizations of vanishing and
  equality, and change of variables along measurable maps.
* `ProjValMeasure.adjoint_spectralIntegral`, `ProjValMeasure.isClosed_spectralIntegral`,
  `ProjValMeasure.norm_adjoint_spectralIntegral_apply`,
  `ProjValMeasure.isSelfAdjoint_spectralIntegral_iff`,
  `ProjValMeasure.isSelfAdjoint_spectralIntegral_iff_proj_im_ne_zero_eq_zero`, and
  `ProjValMeasure.isSelfAdjoint_spectralIntegral_ofReal`: the Hilbert adjoint
  is the spectral integral of `star f` (with the same domain), every spectral integral is closed and
  normal, and it is self-adjoint if and only if `star f =ᶠ[P.ae] f` (equivalently, the projection
  of `{t | (f t).im ≠ 0}` vanishes).
* `ProjValMeasure.existsUnique_spectralIntegral`: existence and uniqueness of the closed densely
  defined partial operator with the second-moment domain and polarized-measure matrix elements,
  together with its norm-square and adjoint laws.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  American Mathematical Society, 2009, Section 3.1, Theorem 3.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 13.24.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer, 2012, Section 4.3.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Construction of the unbounded spectral integral -/

/-- The maximal second-moment submodule `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`. -/
private def spectralIntegralDomain (P : ProjValMeasure X H) (f : X → ℂ) : Submodule ℂ H where
  carrier := {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}
  zero_mem' := by simp [P.diag_zero]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    refine (lintegral_mono' (P.diag_add_le x y) le_rfl).trans_lt ?_
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
      smul_eq_mul]
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hx, ENNReal.mul_lt_top ENNReal.ofNat_lt_top hy⟩
  smul_mem' c {x} hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [P.diag_smul, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) hx

/-- On the second-moment domain, the bounded integrals of the real-threshold level-set truncations
form a Cauchy filter in `H`. -/
private theorem cauchy_map_integral_truncate (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : spectralIntegralDomain P f) :
    Cauchy (Filter.map (fun M : ℝ =>
      P.integral (BoundedBorelFunction.truncate f hf M) x) atTop) := by
  have hmem : MemLp f 2 (P.diag x) :=
    hf.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.2 x.property
  have hmem_tr (M : ℝ) : MemLp (BoundedBorelFunction.truncate f hf M) 2 (P.diag x) :=
    MemLp.of_bound (BoundedBorelFunction.truncate f hf M).measurable.aestronglyMeasurable
      ‖BoundedBorelFunction.truncate f hf M‖
      (Eventually.of_forall (BoundedBorelFunction.norm_coe_le_norm _))
  have hlim_eLp : Tendsto (fun M : ℝ => eLpNorm (⇑(BoundedBorelFunction.truncate f hf M) - f) 2
      (P.diag x)) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by simp)
      (Eventually.of_forall fun M =>
        (BoundedBorelFunction.truncate f hf M).measurable.aestronglyMeasurable)
      hmem
      (Eventually.of_forall fun M => Eventually.of_forall fun t => by
        by_cases ht : ‖f t‖ ≤ M <;> simp [ht])
      (Eventually.of_forall fun t => BoundedBorelFunction.tendsto_truncate_apply hf t)
  have hlp_cauchy : Cauchy (Filter.map (fun M : ℝ =>
      (hmem_tr M).toLp (BoundedBorelFunction.truncate f hf M)) atTop) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun M : ℝ => ⇑(BoundedBorelFunction.truncate f hf M))
      hmem_tr f hmem).2 hlim_eLp).cauchy_map
  have hedist (M₁ M₂ : ℝ) :
      edist (P.integral (BoundedBorelFunction.truncate f hf M₁) x)
        (P.integral (BoundedBorelFunction.truncate f hf M₂) x) =
      edist ((hmem_tr M₁).toLp (BoundedBorelFunction.truncate f hf M₁))
        ((hmem_tr M₂).toLp (BoundedBorelFunction.truncate f hf M₂)) := by
    rw [eDist_eq_eNorm_sub, ← sub_apply, ← map_sub, P.enorm_integral_apply_eq_eLpNorm,
      FunLike.coe_sub, Lp.edist_toLp_toLp]
  rw [cauchy_map_iff, uniformity_basis_edist.tendsto_right_iff] at hlp_cauchy ⊢
  simpa only [Set.mem_ofPred_eq, hedist] using hlp_cauchy

private def spectralIntegralAux (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : spectralIntegralDomain P f) : H :=
  limUnder (atTop : Filter ℝ) fun M : ℝ => P.integral (BoundedBorelFunction.truncate f hf M) x

/-- The **unbounded spectral integral** `P.spectralIntegral f hf` of a measurable symbol
`f : X → ℂ` against a projection-valued measure `P`, as a partial linear operator `H →ₗ.[ℂ] H`.
Its domain is the maximal second-moment subspace `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`
(`mem_spectralIntegral_domain_iff`), and its matrix elements are the integrals of `f` against the
polarized complex measures (`inner_spectralIntegral_apply`). -/
def spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) : H →ₗ.[ℂ] H where
  domain := spectralIntegralDomain P f
  toFun :=
    { toFun := spectralIntegralAux P f hf
      map_add' := fun x y => by
        have hlim (z : spectralIntegralDomain P f) :
            Tendsto (fun M : ℝ => P.integral (BoundedBorelFunction.truncate f hf M) z) atTop
              (𝓝 (spectralIntegralAux P f hf z)) :=
          tendsto_nhds_limUnder (CompleteSpace.complete (cauchy_map_integral_truncate P hf z))
        refine tendsto_nhds_unique (hlim (x + y)) ?_
        exact ((hlim x).add (hlim y)).congr fun M =>
          (map_add (P.integral (BoundedBorelFunction.truncate f hf M)) (x : H) (y : H)).symm
      map_smul' := fun c x => by
        have hlim (z : spectralIntegralDomain P f) :
            Tendsto (fun M : ℝ => P.integral (BoundedBorelFunction.truncate f hf M) z) atTop
              (𝓝 (spectralIntegralAux P f hf z)) :=
          tendsto_nhds_limUnder (CompleteSpace.complete (cauchy_map_integral_truncate P hf z))
        simpa only [RingHom.id_apply] using
          tendsto_nhds_unique (hlim (c • x))
            (((hlim x).const_smul c).congr fun M =>
              (map_smul (P.integral (BoundedBorelFunction.truncate f hf M)) c (x : H)).symm) }

/-- On the domain of `P.spectralIntegral f hf`, the bounded integrals of the level-set truncations
`BoundedBorelFunction.truncate f hf M` converge to `P.spectralIntegral f hf x` as `M → ∞`. -/
theorem tendsto_integral_truncate_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun M : ℝ => P.integral (BoundedBorelFunction.truncate f hf M) x) atTop
      (𝓝 (P.spectralIntegral f hf x)) :=
  tendsto_nhds_limUnder (CompleteSpace.complete (cauchy_map_integral_truncate P hf x))

/-! ## Domain, spectral cutoffs, and density -/

/-- A vector `x : H` belongs to the domain of `P.spectralIntegral f hf` if and only if `f` has
finite second moment against the diagonal measure `P.diag x`. -/
@[simp]
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  Iff.rfl

/-- Conjugating the symbol preserves the domain of the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_star_domain (P : ProjValMeasure X H) {f : X → ℂ}
    {hsf : Measurable (star f)} :
    (P.spectralIntegral (star f) hsf).domain =
      (P.spectralIntegral f (star_star f ▸ continuous_star.measurable.comp hsf)).domain := by
  ext x
  simp [P.mem_spectralIntegral_domain_iff, ← ofReal_norm]

/-- A vector `x : H` belongs to the domain of `P.spectralIntegral f hf` if and only if `f` belongs
to `L²(P.diag x)` (`MemLp f 2 (P.diag x)`). -/
theorem mem_spectralIntegral_domain_iff_memLp (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ MemLp f 2 (P.diag x) :=
  (P.mem_spectralIntegral_domain_iff hf x).trans
    hf.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.symm

/-- A vector `x : H` belongs to the domain of `P.spectralIntegral f hf` if and only if
`t ↦ ‖f t‖ ^ 2` is Bochner integrable against `P.diag x`. -/
theorem mem_spectralIntegral_domain_iff_integrable_norm_sq (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
  (P.mem_spectralIntegral_domain_iff_memLp hf x).trans
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable)

/-- Every bounded Borel operator `P.integral g` leaves the domain of `P.spectralIntegral f hf`
invariant. -/
theorem integral_apply_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (g : BoundedBorelFunction X) {x : H}
    (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.integral g x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff_memLp hf, P.diag_integral]
  have hle : (P.diag x).withDensity (fun t => ‖g t‖ₑ ^ 2) ≤ (‖g‖ₑ ^ 2) • P.diag x := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun t => pow_le_pow_left'
      (eNorm_le_iff_norm_le.2 (g.norm_coe_le_norm t)) 2)
  exact (((P.mem_spectralIntegral_domain_iff_memLp hf x).1 hx).smul_measure
    (ENNReal.pow_lt_top eNorm_lt_top).ne).mono_measure hle

/-- Every spectral projection `P.proj B hB` leaves the domain of `P.spectralIntegral f hf`
invariant. -/
theorem proj_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (B : Set X) (hB : MeasurableSet B) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  simpa only [P.integral_indicator hB] using
    P.integral_apply_mem_spectralIntegral_domain hf (BoundedBorelFunction.indicator B hB 1) hx

/-- If `f` is bounded in norm by `M` `P.diag x`-almost everywhere on a measurable set `B`, then
`P.proj B hB x` belongs to the domain of `P.spectralIntegral f hf`. -/
theorem proj_mem_spectralIntegral_domain_of_bound (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {x : H} {M : ℝ}
    (hM : ∀ᵐ t ∂P.diag x, t ∈ B → ‖f t‖ ≤ M) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff_memLp hf, P.diag_proj B hB x]
  exact MemLp.of_bound hf.aestronglyMeasurable M ((ae_restrict_iff' hB).2 hM)

/-- If `f` agrees on a measurable set `B` with a bounded Borel symbol `g`, then `P.proj B hB` maps
every vector of `H` into the domain of `P.spectralIntegral f hf`. -/
theorem proj_mem_spectralIntegral_domain_of_eqOn (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {g : BoundedBorelFunction X}
    (hfg : Set.EqOn f g B) (x : H) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain :=
  P.proj_mem_spectralIntegral_domain_of_bound hf hB
    (Eventually.of_forall fun t ht => (hfg ht).symm ▸ g.norm_coe_le_norm t)

/-- The spectral projection of any bounded-symbol window `{t | ‖f t‖ ≤ M}` maps all of `H` into
the domain of `P.spectralIntegral f hf`. -/
theorem proj_norm_le_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (M : ℝ) (x : H) :
    P.proj {t | ‖f t‖ ≤ M} (measurableSet_le hf.norm measurable_const) x ∈
      (P.spectralIntegral f hf).domain :=
  P.proj_mem_spectralIntegral_domain_of_bound hf (measurableSet_le hf.norm measurable_const)
    (Eventually.of_forall fun _ ht => ht)

/-- The second-moment domain of `P.spectralIntegral f hf` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    Dense ((P.spectralIntegral f hf).domain : Set H) := fun x =>
  mem_closure_of_tendsto (P.tendsto_proj_norm_le_apply hf x)
    (Eventually.of_forall fun M : ℝ => P.proj_norm_le_mem_spectralIntegral_domain hf M x)

/-! ## Norm-square identity, diagonal and polarized densities, and matrix elements -/

/-- **Second-moment norm identity** for the unbounded spectral integral: for `x` in the domain of
`P.spectralIntegral f hf`, `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. -/
theorem norm_sq_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf x).1 x.property
  have hcont : Continuous fun v : H => ‖v‖ ^ 2 := continuous_norm.pow 2
  refine tendsto_nhds_unique
    ((hcont.tendsto _).comp (P.tendsto_integral_truncate_spectralIntegral hf x)) ?_
  have hdom : Tendsto
      (fun M : ℝ => ∫ t, ‖BoundedBorelFunction.truncate f hf M t‖ ^ 2 ∂(P.diag x)) atTop
      (𝓝 (∫ t, ‖f t‖ ^ 2 ∂(P.diag x))) :=
    tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
      (Eventually.of_forall fun M =>
        ((BoundedBorelFunction.truncate f hf M).measurable.norm.pow_const
          2).aestronglyMeasurable)
      (Eventually.of_forall fun M => ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (BoundedBorelFunction.norm_truncate_apply_le f hf M t) 2)
      hint
      (ae_of_all _ fun t => ((BoundedBorelFunction.tendsto_truncate_apply hf t).norm).pow 2)
  exact hdom.congr fun M =>
    (P.norm_sq_integral_apply (BoundedBorelFunction.truncate f hf M) x).symm

/-- For `x` in the domain of `P.spectralIntegral f hf`, `P.spectralIntegral f hf x = 0` if and
only if `f = 0` almost everywhere for `P.diag x`. -/
theorem spectralIntegral_apply_eq_zero_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf x = 0 ↔ f =ᵐ[P.diag x] 0 := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf x).1 x.property
  rw [← norm_eq_zero, ← pow_eq_zero_iff (n := 2) two_ne_zero, P.norm_sq_spectralIntegral_apply hf,
    integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint]
  simp [EventuallyEq]

/-- For `x` in the domain of `P.spectralIntegral f hf` and every `y : H`, the symbol `f` is
integrable against the polarized complex measure `P.polarizedComplexMeasure y x`. -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain
    (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    (P.polarizedComplexMeasure y x).Integrable f :=
  P.integrable_polarizedComplexMeasure_of_memLp
    ((P.mem_spectralIntegral_domain_iff_memLp hf x).1 hx) y

/-- For `y` in the domain of `P.spectralIntegral f hf` and every `x : H`, the symbol `f` is
integrable against the polarized complex measure `P.polarizedComplexMeasure y x`. -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain_left
    (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {y : H} (hy : y ∈ (P.spectralIntegral f hf).domain) (x : H) :
    (P.polarizedComplexMeasure y x).Integrable f :=
  P.integrable_polarizedComplexMeasure_of_memLp_left
    ((P.mem_spectralIntegral_domain_iff_memLp hf y).1 hy) x

/-- **Matrix elements of the unbounded spectral integral.** For `x` in the domain of
`P.spectralIntegral f hf` and any `y : H`, `⟪y, P.spectralIntegral f hf x⟫_ℂ` is the scalar
integral of `f` against `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    ⟪y, P.spectralIntegral f hf x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hint := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x.property y
  have hcont : Continuous fun v : H => ⟪y, v⟫_ℂ := continuous_const.inner continuous_id
  refine tendsto_nhds_unique
    ((hcont.tendsto _).comp (P.tendsto_integral_truncate_spectralIntegral hf x)) ?_
  have hdom : Tendsto
      (fun M : ℝ => ∫ᵛ t, BoundedBorelFunction.truncate f hf M t
        ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
      atTop (𝓝 (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
      (Eventually.of_forall fun M =>
        (BoundedBorelFunction.truncate f hf M).measurable.aestronglyMeasurable)
      (Eventually.of_forall fun M =>
        ae_of_all _ (BoundedBorelFunction.norm_truncate_apply_le f hf M))
      hint.norm
      (ae_of_all _ fun t => BoundedBorelFunction.tendsto_truncate_apply hf t)
  exact hdom.congr fun M =>
    P.integral_polarizedComplexMeasure_eq_inner_integral
      (BoundedBorelFunction.truncate f hf M) y x

/-- Characterization of `P.spectralIntegral f hf x` by its matrix elements against all `y : H`. -/
theorem spectralIntegral_apply_eq_of_inner (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) {w : H}
    (h : ∀ y : H, ⟪y, w⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :
    P.spectralIntegral f hf x = w := by
  apply ext_inner_left ℂ
  intro y
  rw [P.inner_spectralIntegral_apply hf x y, h y]

/-- **Left-slot matrix elements of the unbounded spectral integral.** For `y` in the domain of
`P.spectralIntegral f hf` and any `x : H`, `⟪P.spectralIntegral f hf y, x⟫_ℂ` is the scalar
integral of `star (f t)` against `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral_apply_left (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (y : (P.spectralIntegral f hf).domain) (x : H) :
    ⟪P.spectralIntegral f hf y, x⟫_ℂ =
      ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  rw [← inner_conj_symm, P.inner_spectralIntegral_apply hf y x,
    ← P.integral_polarizedComplexMeasure_star f x y]
  simp only [RCLike.star_def]

/-- **Intertwining with bounded Borel operators**: `P.spectralIntegral f hf` commutes with
`P.integral g` on its domain. -/
theorem spectralIntegral_integral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (g : BoundedBorelFunction X) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf
        ⟨P.integral g x, P.integral_apply_mem_spectralIntegral_domain hf g x.property⟩ =
      P.integral g (P.spectralIntegral f hf x) := by
  apply ext_inner_left ℂ
  intro y
  have hpol : P.polarizedComplexMeasure y (P.integral g x) =
      P.polarizedComplexMeasure (P.integral (star g) y) x := by
    rw [P.polarizedComplexMeasure_integral_right, P.polarizedComplexMeasure_integral_left]
    simp
  rw [P.inner_spectralIntegral_apply, hpol, ← P.inner_spectralIntegral_apply,
    P.inner_integral_star_left]

/-- Every spectral projection `P.proj B hB` commutes with `P.spectralIntegral f hf` on its
domain. -/
theorem spectralIntegral_proj_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (B : Set X) (hB : MeasurableSet B) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf B hB x.property⟩ =
      P.proj B hB (P.spectralIntegral f hf x) := by
  simpa only [P.integral_indicator hB] using
    P.spectralIntegral_integral_apply hf (BoundedBorelFunction.indicator B hB 1) x

/-- The diagonal scalar measure of `P.spectralIntegral f hf x` is `P.diag x` weighted by
`t ↦ ‖f t‖ₑ ^ 2`. -/
@[simp]
theorem diag_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    P.diag (P.spectralIntegral f hf x) = (P.diag x).withDensity fun t => ‖f t‖ₑ ^ 2 := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf x).1 x.property
  ext B hB
  let xB : (P.spectralIntegral f hf).domain :=
    ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf B hB x.property⟩
  calc
    P.diag (P.spectralIntegral f hf x) B
        = ‖P.proj B hB (P.spectralIntegral f hf x)‖ₑ ^ 2 :=
      (P.enorm_sq_proj_apply B hB _).symm
    _ = ENNReal.ofReal (‖P.spectralIntegral f hf xB‖ ^ 2) := by
      rw [← P.spectralIntegral_proj_apply hf B hB x,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∫ t in B, ‖f t‖ ^ 2 ∂(P.diag x)) := by
      rw [P.norm_sq_spectralIntegral_apply hf xB, P.diag_proj B hB x]
    _ = ∫⁻ t in B, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
      simpa only [ENNReal.rpow_two] using
        MeasureTheory.ofReal_setIntegral_norm_sq_eq hint.integrableOn
    _ = ((P.diag x).withDensity fun t => ‖f t‖ₑ ^ 2) B := (withDensity_apply _ hB).symm

/-- Applying `P.spectralIntegral f hf` in the linear argument weights the polarized complex measure
by `f`. -/
theorem polarizedComplexMeasure_spectralIntegral_right (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : H) (x : (P.spectralIntegral f hf).domain) :
    P.polarizedComplexMeasure y (P.spectralIntegral f hf x) =
      (P.polarizedComplexMeasure y x).withDensity f (ContinuousLinearMap.mul ℝ ℂ) := by
  ext B hB
  rw [P.polarizedComplexMeasure_apply _ _ _ hB, ← P.spectralIntegral_proj_apply hf B hB x,
    P.inner_spectralIntegral_apply hf _ y, P.polarizedComplexMeasure_proj_right B hB y x,
    ← VectorMeasure.withDensity_apply
      (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x.property y)]

/-- Applying `P.spectralIntegral f hf` in the conjugate-linear argument weights the polarized
complex measure by `star f`. -/
theorem polarizedComplexMeasure_spectralIntegral_left (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : (P.spectralIntegral f hf).domain) (x : H) :
    P.polarizedComplexMeasure (P.spectralIntegral f hf y) x =
      (P.polarizedComplexMeasure y x).withDensity (star f) (ContinuousLinearMap.mul ℝ ℂ) := by
  have hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have hy' : (y : H) ∈ (P.spectralIntegral (star f) hsf).domain := by
    rw [P.spectralIntegral_star_domain]
    exact y.property
  ext B hB
  rw [P.polarizedComplexMeasure_apply _ _ _ hB, P.inner_spectralIntegral_apply_left hf y _,
    P.polarizedComplexMeasure_proj_right B hB y x,
    VectorMeasure.withDensity_apply
      (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain_left hsf hy' x)]
  simp only [Pi.star_apply]

/-- A partial linear operator whose domain is the second-moment subspace of `f` and whose matrix
elements are the integrals of `f` against `P.polarizedComplexMeasure` equals
`P.spectralIntegral f hf`. -/
theorem eq_spectralIntegral_of_domain_of_inner (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {T : H →ₗ.[ℂ] H}
    (hdom : ∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞)
    (hinner : ∀ (x : T.domain) (y : H),
      ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :
    T = P.spectralIntegral f hf :=
  LinearPMap.ext (Submodule.ext hdom) fun x hx₁ hx₂ =>
    (P.spectralIntegral_apply_eq_of_inner hf ⟨x, hx₂⟩ (hinner ⟨x, hx₁⟩)).symm

/-! ## Bounded calculus comparison, algebraic properties, `P.ae`-invariance, and reindexing -/

/-- If two measurable symbols agree `P.diag x`-almost everywhere, then `x` belongs to the domain of
`P.spectralIntegral f hf` if and only if it belongs to the domain of `P.spectralIntegral g hg`. -/
theorem mem_spectralIntegral_domain_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) {x : H} (h : f =ᵐ[P.diag x] g) :
    x ∈ (P.spectralIntegral f hf).domain ↔ x ∈ (P.spectralIntegral g hg).domain := by
  rw [P.mem_spectralIntegral_domain_iff_memLp hf, P.mem_spectralIntegral_domain_iff_memLp hg]
  exact memLp_congr_ae h

/-- If two measurable symbols agree `P.diag x`-almost everywhere and `x` lies in the domain of
`P.spectralIntegral f hf`, then `x` also lies in the domain of `P.spectralIntegral g hg` and the
two spectral integrals agree at `x`. -/
theorem spectralIntegral_apply_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) {x : H} (h : f =ᵐ[P.diag x] g)
    (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨x, hx⟩ =
      P.spectralIntegral g hg ⟨x, (P.mem_spectralIntegral_domain_congr_ae hf hg h).1 hx⟩ := by
  refine P.spectralIntegral_apply_eq_of_inner hf ⟨x, hx⟩ fun y => ?_
  rw [P.inner_spectralIntegral_apply hg
    ⟨x, (P.mem_spectralIntegral_domain_congr_ae hf hg h).1 hx⟩ y]
  exact VectorMeasure.integral_congr_ae
    ((P.variation_polarizedComplexMeasure_absolutelyContinuous_diag y x) h.symm)

/-- For a bounded Borel symbol `g`, the unbounded spectral integral `P.spectralIntegral g _` is
everywhere defined and coincides with the bounded Borel integral `P.integral g`. -/
@[simp]
theorem spectralIntegral_coe_boundedBorelFunction (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) :
    P.spectralIntegral g g.measurable = (P.integral g).toPMap ⊤ := by
  symm
  refine P.eq_spectralIntegral_of_domain_of_inner g.measurable (fun x => ?_) (fun x y => ?_)
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff,
      ← P.mem_spectralIntegral_domain_iff g.measurable, P.mem_spectralIntegral_domain_iff_memLp]
    exact MemLp.of_bound g.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  · have hx : ((P.integral g).toPMap ⊤) x = (P.integral g : H →ₗ[ℂ] H) x :=
      LinearMap.toPMap_apply (P.integral g : H →ₗ[ℂ] H) ⊤ x
    rw [hx, ContinuousLinearMap.coe_coe]
    exact (P.integral_polarizedComplexMeasure_eq_inner_integral g y x).symm

/-- If `f` agrees `P.diag x`-almost everywhere with a bounded Borel symbol `g`, then `x` lies in
the domain of `P.spectralIntegral f hf`. -/
theorem mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) {g : BoundedBorelFunction X} {x : H}
    (h : f =ᵐ[P.diag x] g) :
    x ∈ (P.spectralIntegral f hf).domain :=
  (P.mem_spectralIntegral_domain_congr_ae hf g.measurable h).2
    (by rw [P.spectralIntegral_coe_boundedBorelFunction g]; simp)

/-- If `f` agrees `P.diag x`-almost everywhere with a bounded Borel symbol `g`, then
`P.spectralIntegral f hf` acts on `x` as the bounded operator `P.integral g`. -/
theorem spectralIntegral_apply_of_ae_eq_boundedBorelFunction (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) {g : BoundedBorelFunction X} {x : H}
    (h : f =ᵐ[P.diag x] g) :
    P.spectralIntegral f hf
        ⟨x, P.mem_spectralIntegral_domain_of_ae_eq_boundedBorelFunction hf h⟩ =
      P.integral g x := by
  refine (P.spectralIntegral_apply_congr_ae hf g.measurable h _).trans ?_
  rw [LinearPMap.congr_fun (P.spectralIntegral_coe_boundedBorelFunction g) _ (by simp)]
  simp

/-- If `f` agrees with a bounded Borel symbol `g` `P.diag x`-almost everywhere on a measurable set
`B`, then `P.spectralIntegral f hf` acts on `P.proj B hB x` as the bounded Borel integral of
`BoundedBorelFunction.indicator B hB g` applied to `x`. -/
theorem spectralIntegral_proj_eq_integral_indicator_of_ae_eq (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {g : BoundedBorelFunction X} {x : H}
    (hfg : ∀ᵐ t ∂P.diag x, t ∈ B → f t = g t) :
    P.spectralIntegral f hf ⟨P.proj B hB x,
        P.proj_mem_spectralIntegral_domain_of_bound hf hB
          (hfg.mono fun t ht htB => (ht htB).symm ▸ g.norm_coe_le_norm t)⟩ =
      P.integral (BoundedBorelFunction.indicator B hB g) x := by
  have hfg' : f =ᵐ[P.diag (P.proj B hB x)] g := by
    rw [P.diag_proj B hB x]
    exact (ae_restrict_iff' hB).2 hfg
  exact (P.spectralIntegral_apply_of_ae_eq_boundedBorelFunction hf hfg').trans
    (P.integral_proj_apply g hB x)

/-- If `f` agrees on a measurable set `B` with a bounded Borel symbol `g`, then
`P.spectralIntegral f hf` acts on `P.proj B hB x` as the bounded Borel integral of
`BoundedBorelFunction.indicator B hB g` applied to `x`. -/
theorem spectralIntegral_proj_eq_integral_indicator_of_eqOn (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {g : BoundedBorelFunction X}
    (hfg : Set.EqOn f g B) (x : H) :
    P.spectralIntegral f hf
        ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain_of_eqOn hf hB hfg x⟩ =
      P.integral (BoundedBorelFunction.indicator B hB g) x :=
  P.spectralIntegral_proj_eq_integral_indicator_of_ae_eq hf hB (Eventually.of_forall hfg)

/-- On the spectral cutoff `P.proj {t | ‖f t‖ ≤ M} _ x`, `P.spectralIntegral f hf` evaluates to the
bounded Borel integral `P.integral (BoundedBorelFunction.truncate f hf M) x`. -/
theorem spectralIntegral_proj_norm_le_eq_integral_truncate (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (M : ℝ) (x : H) :
    P.spectralIntegral f hf ⟨P.proj {t | ‖f t‖ ≤ M}
        (measurableSet_le hf.norm measurable_const) x,
        P.proj_norm_le_mem_spectralIntegral_domain hf M x⟩ =
      P.integral (BoundedBorelFunction.truncate f hf M) x := by
  simpa only [BoundedBorelFunction.indicator_norm_le_truncate] using
    P.spectralIntegral_proj_eq_integral_indicator_of_eqOn hf (B := {t | ‖f t‖ ≤ M})
      (measurableSet_le hf.norm measurable_const)
      (g := BoundedBorelFunction.truncate f hf M)
      (fun _ ht => by simp [Set.indicator_of_mem ht]) x

/-- For `x` in the domain of `P.spectralIntegral f hf`, the values of `P.spectralIntegral f hf` on
the spectral cutoffs `P.proj {t | ‖f t‖ ≤ M} _ x` converge to `P.spectralIntegral f hf x` as
`M → ∞`. -/
theorem tendsto_spectralIntegral_proj_norm_le_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun M : ℝ => P.spectralIntegral f hf ⟨P.proj {t | ‖f t‖ ≤ M}
        (measurableSet_le hf.norm measurable_const) x,
        P.proj_norm_le_mem_spectralIntegral_domain hf M x⟩)
      atTop (𝓝 (P.spectralIntegral f hf x)) := by
  simpa only [spectralIntegral_proj_norm_le_eq_integral_truncate] using
    P.tendsto_integral_truncate_spectralIntegral hf x

/-- The unbounded spectral integral of `0` is the everywhere-defined zero partial operator. -/
@[simp]
theorem spectralIntegral_zero (P : ProjValMeasure X H) :
    P.spectralIntegral 0 measurable_const = 0 := by
  have h := P.spectralIntegral_coe_boundedBorelFunction 0
  simp only [FunLike.coe_zero, map_zero] at h
  refine h.trans (LinearPMap.ext (by simp) ?_)
  simp

/-- The unbounded spectral integral of `1` is the everywhere-defined identity operator. -/
@[simp]
theorem spectralIntegral_one (P : ProjValMeasure X H) :
    P.spectralIntegral 1 measurable_const = (ContinuousLinearMap.id ℂ H).toPMap ⊤ := by
  simpa only [FunLike.coe_one, map_one, ContinuousLinearMap.one_def] using
    P.spectralIntegral_coe_boundedBorelFunction 1

/-- The unbounded spectral integral of the indicator of a measurable set `B` is the everywhere
defined projection `P.proj B hB`. -/
theorem spectralIntegral_indicator_one (P : ProjValMeasure X H) {B : Set X}
    (hB : MeasurableSet B) :
    P.spectralIntegral (B.indicator 1) (measurable_const.indicator hB) =
      (P.proj B hB).toPMap ⊤ := by
  simpa only [BoundedBorelFunction.coe_indicator, FunLike.coe_one,
    P.integral_indicator hB] using
    P.spectralIntegral_coe_boundedBorelFunction (BoundedBorelFunction.indicator B hB 1)

/-- Scaling the symbol by a nonzero scalar `c : ℂ` scales the unbounded spectral integral by `c`,
preserving the domain. -/
theorem spectralIntegral_smul (P : ProjValMeasure X H) {c : ℂ} (hc : c ≠ 0) {f : X → ℂ}
    (hf : Measurable f) :
    P.spectralIntegral (c • f) (hf.const_smul c) = c • P.spectralIntegral f hf := by
  symm
  refine P.eq_spectralIntegral_of_domain_of_inner (hf.const_smul c) (fun x => ?_) (fun x y => ?_)
  · simp only [LinearPMap.smul_domain, ← P.mem_spectralIntegral_domain_iff (hf.const_smul c),
      P.mem_spectralIntegral_domain_iff_memLp]
    exact ⟨fun hx => hx.const_smul c, fun hx => by
      simpa only [inv_smul_smul₀ hc] using hx.const_smul c⁻¹⟩
  · simp only [LinearPMap.smul_apply, inner_smul_right, Pi.smul_apply, smul_eq_mul,
      VectorMeasure.integral_const_mul]
    rw [P.inner_spectralIntegral_apply hf x y]

/-- Negating the symbol negates the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_neg (P : ProjValMeasure X H) {f : X → ℂ} {hnf : Measurable (-f)} :
    P.spectralIntegral (-f) hnf = -P.spectralIntegral f (neg_neg f ▸ hnf.neg) := by
  have hf : Measurable f := neg_neg f ▸ hnf.neg
  have hsmul := P.spectralIntegral_smul (c := (-1 : ℂ)) (by norm_num) hf
  rw [LinearPMap.neg_smul, one_smul] at hsmul
  refine Eq.trans ?_ hsmul
  congr 1
  exact (neg_one_smul ℂ f).symm

/-- The spectral integral of `f + g` extends the operator sum
`P.spectralIntegral f hf + P.spectralIntegral g hg` on the intersection of their domains. -/
theorem add_le_spectralIntegral_add (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) :
    P.spectralIntegral f hf + P.spectralIntegral g hg ≤
      P.spectralIntegral (f + g) (hf.add hg) := by
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · exact (P.mem_spectralIntegral_domain_iff_memLp (hf.add hg) x).2
      (((P.mem_spectralIntegral_domain_iff_memLp hf x).1 hx.1).add
        ((P.mem_spectralIntegral_domain_iff_memLp hg x).1 hx.2))
  · refine ext_inner_left ℂ fun z => ?_
    have hxf : (x : H) ∈ (P.spectralIntegral f hf).domain := x.property.1
    have hxg : (x : H) ∈ (P.spectralIntegral g hg).domain := x.property.2
    have hintf := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hxf z
    have hintg := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hg hxg z
    rw [LinearPMap.add_apply, inner_add_right, P.inner_spectralIntegral_apply hf ⟨x, hxf⟩ z,
      P.inner_spectralIntegral_apply hg ⟨x, hxg⟩ z,
      P.inner_spectralIntegral_apply (hf.add hg) y z, ← hxy]
    exact (VectorMeasure.integral_fun_add hintf hintg).symm

/-- The spectral integral of `f - g` extends the operator difference
`P.spectralIntegral f hf - P.spectralIntegral g hg` on the intersection of their domains. -/
theorem sub_le_spectralIntegral_sub (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) :
    P.spectralIntegral f hf - P.spectralIntegral g hg ≤
      P.spectralIntegral (f - g) (hf.sub hg) := by
  simpa only [sub_eq_add_neg, P.spectralIntegral_neg] using
    P.add_le_spectralIntegral_add hf hg.neg

/-- Measurable symbols that agree `P`-almost everywhere have equal unbounded spectral integrals. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : f =ᶠ[P.ae] g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg :=
  LinearPMap.ext
    (Submodule.ext fun x => P.mem_spectralIntegral_domain_congr_ae hf hg (P.ae_diag_of_ae x h))
    fun x hx₁ _ => P.spectralIntegral_apply_congr_ae hf hg (P.ae_diag_of_ae x h) hx₁

/-- Two measurable symbols have the same unbounded spectral integral against `P` if and only if
they agree `P`-almost everywhere. -/
theorem spectralIntegral_eq_spectralIntegral_iff (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg ↔ f =ᶠ[P.ae] g := by
  refine ⟨fun heq => ?_, P.spectralIntegral_congr_ae hf hg⟩
  have hae_n (n : ℕ) :
      ({t | ‖f t‖ ≤ (n : ℝ)} ∩ {t | ‖g t‖ ≤ (n : ℝ)}).indicator f =ᶠ[P.ae]
        ({t | ‖f t‖ ≤ (n : ℝ)} ∩ {t | ‖g t‖ ≤ (n : ℝ)}).indicator g := by
    let B : Set X := {t | ‖f t‖ ≤ (n : ℝ)} ∩ {t | ‖g t‖ ≤ (n : ℝ)}
    have hB : MeasurableSet B :=
      (measurableSet_le hf.norm measurable_const).inter (measurableSet_le hg.norm measurable_const)
    have hint : P.integral (BoundedBorelFunction.indicator B hB
        (BoundedBorelFunction.truncate f hf n)) =
        P.integral (BoundedBorelFunction.indicator B hB
          (BoundedBorelFunction.truncate g hg n)) := by
      ext x
      have hfx : Set.EqOn f (BoundedBorelFunction.truncate f hf n) B := fun _ ht => by simp [ht.1]
      have hgx : Set.EqOn g (BoundedBorelFunction.truncate g hg n) B := fun _ ht => by simp [ht.2]
      rw [← P.spectralIntegral_proj_eq_integral_indicator_of_eqOn hf hB hfx x,
        ← P.spectralIntegral_proj_eq_integral_indicator_of_eqOn hg hB hgx x]
      exact LinearPMap.congr_fun heq _ _
    have hiff := (P.integral_eq_integral_iff
      (BoundedBorelFunction.indicator B hB (BoundedBorelFunction.truncate f hf n))
      (BoundedBorelFunction.indicator B hB (BoundedBorelFunction.truncate g hg n))).1 hint
    refine hiff.mono fun t ht => ?_
    by_cases htB : t ∈ B
    · simpa [htB, htB.1, htB.2] using ht
    · rw [Set.indicator_of_notMem htB, Set.indicator_of_notMem htB]
  rw [EventuallyEq, P.eventually_ae_iff]
  intro ξ
  have hall : ∀ᵐ t ∂(P.diag ξ), ∀ n : ℕ,
      ({s | ‖f s‖ ≤ (n : ℝ)} ∩ {s | ‖g s‖ ≤ (n : ℝ)}).indicator f t =
        ({s | ‖f s‖ ≤ (n : ℝ)} ∩ {s | ‖g s‖ ≤ (n : ℝ)}).indicator g t :=
    ae_all_iff.2 fun n => P.ae_diag_of_ae ξ (hae_n n)
  filter_upwards [hall] with t ht
  obtain ⟨N, hN⟩ := exists_nat_ge (max ‖f t‖ ‖g t‖)
  have htB : t ∈ {s | ‖f s‖ ≤ (N : ℝ)} ∩ {s | ‖g s‖ ≤ (N : ℝ)} :=
    ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
  simpa [Set.indicator_of_mem htB] using ht N

/-- The unbounded spectral integral `P.spectralIntegral f hf` is the zero partial operator if and
only if `f` vanishes `P`-almost everywhere. -/
@[simp]
theorem spectralIntegral_eq_zero_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral f hf = 0 ↔ f =ᶠ[P.ae] 0 := by
  simpa using P.spectralIntegral_eq_spectralIntegral_iff hf (g := 0) measurable_zero

/-- **Change of variables** for the unbounded spectral integral: integrating `f` against
`P.map κ hκ` equals integrating `f ∘ κ` against `P`, with equality of domains and actions. -/
@[simp]
theorem spectralIntegral_map {Y : Type*} [MeasurableSpace Y] (P : ProjValMeasure X H)
    (κ : X → Y) (hκ : Measurable κ) {f : Y → ℂ} (hf : Measurable f) :
    (P.map κ hκ).spectralIntegral f hf = P.spectralIntegral (f ∘ κ) (hf.comp hκ) := by
  have hdom : ((P.map κ hκ).spectralIntegral f hf).domain =
      (P.spectralIntegral (f ∘ κ) (hf.comp hκ)).domain := by
    ext x
    simp only [mem_spectralIntegral_domain_iff, map_diag]
    rw [lintegral_map (hf.eNorm.pow_const 2) hκ]
    simp only [Function.comp_apply]
  refine LinearPMap.ext hdom fun x hx₁ hx₂ => ?_
  have htr (M : ℝ) : (P.map κ hκ).integral (BoundedBorelFunction.truncate f hf M) x =
      P.integral (BoundedBorelFunction.truncate (f ∘ κ) (hf.comp hκ) M) x := by
    rw [P.integral_map κ hκ, BoundedBorelFunction.compStarAlgHom'_truncate]
  exact tendsto_nhds_unique
    ((P.map κ hκ).tendsto_integral_truncate_spectralIntegral hf ⟨x, hx₁⟩)
    ((P.tendsto_integral_truncate_spectralIntegral (hf.comp hκ) ⟨x, hx₂⟩).congr
      fun M => (htr M).symm)

/-! ## Hilbert adjoint, closedness, normality, self-adjointness, and uniqueness -/

/-- Every vector in the domain of `(P.spectralIntegral f hf).adjoint` belongs to the second-moment
domain of `star f`. -/
private theorem adjoint_domain_le_spectralIntegral_star (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain ≤
      (P.spectralIntegral (star f)
        (continuous_star.measurable.comp hf : Measurable (star f))).domain := by
  intro y hy
  let y' : (P.spectralIntegral f hf).adjoint.domain := ⟨y, hy⟩
  have hdense := P.dense_spectralIntegral_domain hf
  have hproj_eq (n : ℕ) : P.integral (star (BoundedBorelFunction.truncate f hf n)) y =
      P.proj {t | ‖f t‖ ≤ (n : ℝ)} (measurableSet_le hf.norm measurable_const)
        ((P.spectralIntegral f hf).adjoint y') := by
    refine ext_inner_right ℂ fun x => ?_
    let hBn : MeasurableSet {t | ‖f t‖ ≤ (n : ℝ)} := measurableSet_le hf.norm measurable_const
    let xn : (P.spectralIntegral f hf).domain :=
      ⟨P.proj {t | ‖f t‖ ≤ (n : ℝ)} hBn x, P.proj_norm_le_mem_spectralIntegral_domain hf n x⟩
    calc
      ⟪P.integral (star (BoundedBorelFunction.truncate f hf n)) y, x⟫_ℂ
          = ⟪y, P.integral (BoundedBorelFunction.truncate f hf n) x⟫_ℂ :=
        P.inner_integral_star_left _ y x
      _ = ⟪y, P.spectralIntegral f hf xn⟫_ℂ := by
        rw [← P.spectralIntegral_proj_norm_le_eq_integral_truncate hf n x]
      _ = ⟪(P.spectralIntegral f hf).adjoint y', (xn : H)⟫_ℂ :=
        ((LinearPMap.adjoint_isFormalAdjoint hdense) y' xn).symm
      _ = ⟪P.proj {t | ‖f t‖ ≤ (n : ℝ)} hBn ((P.spectralIntegral f hf).adjoint y'), x⟫_ℂ := by
        dsimp only [xn]
        rw [← ContinuousLinearMap.adjoint_inner_left, (P.isSelfAdjoint_proj _ hBn).adjoint_eq]
  rw [P.spectralIntegral_star_domain, P.mem_spectralIntegral_domain_iff hf,
    ← BoundedBorelFunction.iSup_lintegral_enorm_pow_truncate hf 2 (P.diag y)]
  refine (iSup_le (a := ‖(P.spectralIntegral f hf).adjoint y'‖ₑ ^ 2) fun n => ?_).trans_lt
    (ENNReal.pow_lt_top eNorm_lt_top)
  have hdiag : ∫⁻ t, ‖BoundedBorelFunction.truncate f hf n t‖ₑ ^ 2 ∂(P.diag y) =
      ‖P.integral (star (BoundedBorelFunction.truncate f hf n)) y‖ₑ ^ 2 := by
    rw [P.enorm_sq_integral_apply]
    refine lintegral_congr fun t => ?_
    simp only [BoundedBorelFunction.star_apply, ← ofReal_norm, norm_star]
  rw [hdiag, hproj_eq n]
  exact pow_le_pow_left' (eNorm_le_iff_norm_le.2 (P.norm_proj_apply_le _ _ _)) 2

/-- **Hilbert adjoint of the unbounded spectral integral.** The adjoint of `P.spectralIntegral f hf`
is `P.spectralIntegral (star f) _`. -/
@[simp]
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf : Measurable (star f)) := by
  have hfa : (P.spectralIntegral f hf).IsFormalAdjoint
      (P.spectralIntegral (star f) (continuous_star.measurable.comp hf : Measurable (star f))) :=
    fun x y => (P.inner_spectralIntegral_apply_left hf x y).trans
      (P.inner_spectralIntegral_apply (continuous_star.measurable.comp hf) y x).symm
  have hle :
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf : Measurable (star f)) ≤
        (P.spectralIntegral f hf).adjoint :=
    hfa.le_adjoint (P.dense_spectralIntegral_domain hf)
  exact (LinearPMap.eq_of_le_of_domain_eq hle
    (le_antisymm hle.1 (P.adjoint_domain_le_spectralIntegral_star hf))).symm

/-- Matrix elements of `(P.spectralIntegral f hf).adjoint`: for `x` in the adjoint domain and
`y : H`, `⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ` is the integral of `star (f t)` against
`P.polarizedComplexMeasure y x`. -/
theorem inner_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).adjoint.domain) (y : H) :
    ⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ =
      ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  revert x
  rw [P.adjoint_spectralIntegral hf]
  intro x
  exact P.inner_spectralIntegral_apply (continuous_star.measurable.comp hf) x y

/-- The unbounded spectral integral `P.spectralIntegral f hf` is a closed operator (its graph is
closed in `H × H`). -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).IsClosed := by
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have heq : P.spectralIntegral f hf = (P.spectralIntegral (star f) hsf).adjoint := by
    rw [P.adjoint_spectralIntegral hsf]
    exact P.spectralIntegral_congr_ae hf (continuous_star.measurable.comp hsf : Measurable _)
      (Eventually.of_forall fun t => (star_star (f t)).symm)
  rw [heq]
  exact LinearPMap.adjoint_isClosed (P.dense_spectralIntegral_domain hsf)

/-- Any family of spectral projections `P.proj (B i) (hB i)` converging strongly to the identity
along a `NeBot` filter and mapping into `(P.spectralIntegral f hf).domain` generates a graph core
`⨆ i, LinearMap.range (P.proj (B i) (hB i))` for `P.spectralIntegral f hf`. -/
theorem spectralIntegral_hasCore_iSup_range_proj {ι : Type*} {l : Filter ι} [l.NeBot]
    (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) {B : ι → Set X}
    (hB : ∀ i, MeasurableSet (B i))
    (hmem : ∀ i x, P.proj (B i) (hB i) x ∈ (P.spectralIntegral f hf).domain)
    (htend : ∀ x, Tendsto (fun i => P.proj (B i) (hB i) x) l (𝓝 x)) :
    (P.spectralIntegral f hf).HasCore
      (⨆ i, LinearMap.range (P.proj (B i) (hB i) : H →ₗ[ℂ] H)) := by
  let S : Submodule ℂ H := ⨆ i, LinearMap.range (P.proj (B i) (hB i) : H →ₗ[ℂ] H)
  have hS : S ≤ (P.spectralIntegral f hf).domain := by
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    exact hmem i x
  rw [(P.isClosed_spectralIntegral hf).hasCore_iff_graph_subset_closure hS]
  rintro ⟨x, y⟩ hxy
  have hx : x ∈ (P.spectralIntegral f hf).domain := LinearPMap.mem_domain_of_mem_graph hxy
  have hy : y = P.spectralIntegral f hf ⟨x, hx⟩ := (LinearPMap.image_iff hx).2 hxy
  rw [hy]
  have htend_val :
      Tendsto (fun i => P.spectralIntegral f hf ⟨P.proj (B i) (hB i) x, hmem i x⟩)
        l (𝓝 (P.spectralIntegral f hf ⟨x, hx⟩)) := by
    simpa only [P.spectralIntegral_proj_apply hf _ _ ⟨x, hx⟩] using
      htend (P.spectralIntegral f hf ⟨x, hx⟩)
  refine mem_closure_of_tendsto ((htend x).prodMk_nhds htend_val)
    (Eventually.of_forall fun i => ?_)
  have hmemS : P.proj (B i) (hB i) x ∈ S := Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
  have hmemD : P.proj (B i) (hB i) x ∈ ((P.spectralIntegral f hf).domRestrict S).domain := by
    rw [LinearPMap.domRestrict_domain, Submodule.mem_inf]
    exact ⟨hmemS, hmem i x⟩
  have happly : (P.spectralIntegral f hf).domRestrict S ⟨_, hmemD⟩ =
      P.spectralIntegral f hf ⟨_, hmem i x⟩ :=
    LinearPMap.domRestrict_apply rfl
  rw [← happly]
  exact ((P.spectralIntegral f hf).domRestrict S).mem_graph ⟨_, hmemD⟩

/-- The supremum of the spectral cutoff ranges `LinearMap.range (P.proj {t | ‖f t‖ ≤ n} _)` is a
graph core for `P.spectralIntegral f hf`. -/
theorem spectralIntegral_hasCore_iSup_range_proj_norm_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, LinearMap.range
        (P.proj {t | ‖f t‖ ≤ (n : ℝ)}
          (measurableSet_le hf.norm measurable_const) : H →ₗ[ℂ] H)) :=
  P.spectralIntegral_hasCore_iSup_range_proj (l := (atTop : Filter ℕ)) hf
    (fun _ => measurableSet_le hf.norm measurable_const)
    (fun n x => P.proj_norm_le_mem_spectralIntegral_domain hf n x)
    (fun x => (P.tendsto_proj_norm_le_apply hf x).comp tendsto_natCast_atTop_atTop)

/-- **Normality of the unbounded spectral integral:** on their common domain,
`(P.spectralIntegral f hf).adjoint` and `P.spectralIntegral f hf` have equal norms at every
vector. -/
theorem norm_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    ‖(P.spectralIntegral f hf).adjoint ⟨x, by simp⟩‖ =
      ‖P.spectralIntegral f hf x‖ := by
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) hsf).domain := by
    rw [P.spectralIntegral_star_domain]
    exact x.property
  rw [LinearPMap.congr_fun (P.adjoint_spectralIntegral hf) _ hx',
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    P.norm_sq_spectralIntegral_apply hsf ⟨x, hx'⟩, P.norm_sq_spectralIntegral_apply hf x]
  simp

/-- The unbounded spectral integral `P.spectralIntegral f hf` is self-adjoint if and only if
`star f =ᶠ[P.ae] f`. -/
@[simp]
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔ star f =ᶠ[P.ae] f := by
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral hf,
    P.spectralIntegral_eq_spectralIntegral_iff (f := star f)
      (continuous_star.measurable.comp hf) hf]

/-- The unbounded spectral integral `P.spectralIntegral f hf` is self-adjoint if and only if the
spectral projection of `{t | (f t).im ≠ 0}` vanishes. -/
theorem isSelfAdjoint_spectralIntegral_iff_proj_im_ne_zero_eq_zero (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔
      P.proj {t | (f t).im ≠ 0}
        ((measurableSet_eq_fun (Complex.continuous_im.measurable.comp hf)
          measurable_const).compl) = 0 := by
  rw [P.isSelfAdjoint_spectralIntegral_iff hf, P.proj_eq_zero_iff_compl_mem_ae]
  have hset : ({t | (f t).im ≠ 0}ᶜ : Set X) = {t | star (f t) = f t} := by
    ext t
    simpa [Set.mem_compl_iff] using Complex.conj_eq_iff_im.symm
  simp only [EventuallyEq, Pi.star_apply, Filter.eventually_iff, hset]

/-- The unbounded spectral integral of a real-valued measurable function is self-adjoint. -/
@[simp high]
theorem isSelfAdjoint_spectralIntegral_ofReal (P : ProjValMeasure X H) {f : X → ℝ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral (fun t => (f t : ℂ))
      (Complex.continuous_ofReal.measurable.comp hf)) :=
  (P.isSelfAdjoint_spectralIntegral_iff _).2
    (Eventually.of_forall fun t => Complex.conj_ofReal (f t))

/-- **Existence and uniqueness of the unbounded spectral integral.** For a normalized
projection-valued measure `P` on an arbitrary measurable space `X` and a measurable symbol
`f : X → ℂ`, there is a unique partial linear operator `T : H →ₗ.[ℂ] H` whose domain is the
second-moment subspace `{x | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` and whose matrix elements are the
scalar integrals of `f` against `P.polarizedComplexMeasure`; moreover `T` is densely defined and
closed, satisfies `‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`, and its Hilbert adjoint has the same
domain and the matrix elements of `star f`. -/
theorem existsUnique_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    ∃! T : H →ₗ.[ℂ] H,
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (∀ x : T.domain, ‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) ∧
      T.adjoint.domain = T.domain ∧
      (∀ (x : T.adjoint.domain) (y : H),
        ⟪y, T.adjoint x⟫_ℂ =
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) :=
  ⟨P.spectralIntegral f hf,
    ⟨P.mem_spectralIntegral_domain_iff hf, P.inner_spectralIntegral_apply hf,
      P.dense_spectralIntegral_domain hf, P.isClosed_spectralIntegral hf,
      P.norm_sq_spectralIntegral_apply hf, by simp,
      P.inner_adjoint_spectralIntegral_apply hf⟩,
    fun _ hT => P.eq_spectralIntegral_of_domain_of_inner hf hT.1 hT.2.1⟩

end ProjValMeasure
end TauCeti
