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
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Unbounded spectral integration against a projection-valued measure

Let `P` be a normalized projection-valued measure on an arbitrary measurable space `X` acting on a
complex Hilbert space `H`, with finite diagonal scalar measures `P.diag x` and polarized complex
measures `P.polarizedComplexMeasure y x`. For an arbitrary measurable symbol `f : X → ℂ`, this file
constructs the unbounded spectral integral `P.spectralIntegral f hf : H →ₗ.[ℂ] H` on its maximal
second-moment domain

`{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`

as the strong limit of the bounded Borel integrals `P.integral` of the level-set truncations
`BoundedBorelFunction.truncate f hf n` (`tendsto_integral_truncate_spectralIntegral`). No
topological or countability assumption is placed on `X`, and no separability assumption is placed
on `H`.

## Main declarations

* `ProjValMeasure.spectralIntegral`: the unbounded partial linear operator `∫ f dP` of a measurable
  symbol `f : X → ℂ`, with domain `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`
  (`mem_spectralIntegral_domain_iff`, `mem_spectralIntegral_domain_iff_integrable`, and
  `mem_spectralIntegral_domain_iff_memLp`).
* `ProjValMeasure.dense_spectralIntegral_domain` and
  `ProjValMeasure.spectralIntegral_hasCore_iSup_range_proj_norm_le`: the domain of
  `P.spectralIntegral f hf` is dense in `H`, and the supremum of the spectral cutoff ranges
  `LinearMap.range (P.proj {‖f‖ ≤ n} _)` is a graph core for `P.spectralIntegral f hf`.
* `ProjValMeasure.norm_sq_spectralIntegral_apply` and `ProjValMeasure.diag_spectralIntegral`: the
  second-moment norm identity `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)` and
  the diagonal measure density `P.diag (P.spectralIntegral f hf x) = (P.diag x).withDensity _`.
* `ProjValMeasure.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain`,
  `ProjValMeasure.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain_left`, and
  `ProjValMeasure.integral_norm_variation_polarizedComplexMeasure_le`: when either vector belongs to
  the domain, `f` is integrable against `P.polarizedComplexMeasure y x` with Cauchy–Schwarz
  variation bound.
* `ProjValMeasure.inner_spectralIntegral_apply`,
  `ProjValMeasure.inner_spectralIntegral_apply_left`,
  `ProjValMeasure.polarizedComplexMeasure_spectralIntegral_right`,
  `ProjValMeasure.polarizedComplexMeasure_spectralIntegral_left`, and
  `ProjValMeasure.eq_spectralIntegral_of_domain_of_inner`: matrix-element and weighted-measure
  formulas for `P.spectralIntegral f hf`, and uniqueness from the domain and matrix elements.
* `ProjValMeasure.spectralIntegral_coe_boundedBorelFunction`,
  `ProjValMeasure.spectralIntegral_proj_apply`,
  `ProjValMeasure.proj_mem_spectralIntegral_domain_of_bound`,
  `ProjValMeasure.spectralIntegral_proj_eq_integral_indicator_of_ae_eq`, and
  `ProjValMeasure.spectralIntegral_proj_norm_le_eq_integral_truncate`: compatibility with the
  bounded Borel integral `P.integral`, spectral projections `P.proj`, and level-set truncations.
* `ProjValMeasure.spectralIntegral_eq_zero_iff`,
  `ProjValMeasure.spectralIntegral_eq_spectralIntegral_iff`, and
  `ProjValMeasure.spectralIntegral_map`: `P`-almost-everywhere characterizations of vanishing and
  equality, and change of variables along measurable maps.
* `ProjValMeasure.adjoint_spectralIntegral`, `ProjValMeasure.isClosed_spectralIntegral`,
  `ProjValMeasure.norm_adjoint_spectralIntegral_apply`,
  `ProjValMeasure.isSelfAdjoint_spectralIntegral_iff`, and
  `ProjValMeasure.isSelfAdjoint_spectralIntegral_iff_proj_im_ne_zero_eq_zero`: the Hilbert adjoint
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

/-- On the second-moment domain, the bounded integrals of the level-set truncations form a Cauchy
sequence in `H`. -/
private theorem cauchySeq_integral_truncate (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : spectralIntegralDomain P f) :
    CauchySeq fun n : ℕ => P.integral (BoundedBorelFunction.truncate f hf n) x := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1
      (hf.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.2 x.2)
  let tail : ℕ → X → ℝ := fun N => {t | (N : ℝ) < ‖f t‖}.indicator fun t => 4 * ‖f t‖ ^ 2
  have htail_meas (N : ℕ) : Measurable (tail N) :=
    (hf.norm.pow_const 2 |>.const_mul 4).indicator (measurableSet_lt measurable_const hf.norm)
  have htail_le (N : ℕ) (t : X) : ‖tail N t‖ ≤ 4 * ‖f t‖ ^ 2 := by
    dsimp only [tail]
    rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)]
    exact Set.indicator_le_self' (fun _ _ => by positivity) t
  have htail_tendsto : Tendsto (fun N => ∫ t, tail N t ∂(P.diag x)) atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence (F := tail) (f := fun _ => 0)
      (fun t => 4 * ‖f t‖ ^ 2)
      (fun N => (htail_meas N).aestronglyMeasurable) (hint.const_mul 4)
      (fun N => ae_of_all _ (htail_le N))
      (ae_of_all _ fun t => by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
        have hnot : t ∉ {s | (n : ℝ) < ‖f s‖} := not_lt.2 (hN.trans (Nat.cast_le.2 hn))
        exact Set.indicator_of_notMem hnot _)
  have hsqrt : Tendsto (fun N => Real.sqrt (∫ t, tail N t ∂(P.diag x))) atTop (𝓝 0) := by
    simpa using htail_tendsto.sqrt
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (tendsto_order.1 hsqrt).2 ε hε |> eventually_atTop.1
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdiff_int : Integrable
      (fun t => ‖(BoundedBorelFunction.truncate f hf m -
        BoundedBorelFunction.truncate f hf n) t‖ ^ 2) (P.diag x) :=
    ((hint.const_mul 4).indicator (measurableSet_lt measurable_const hf.norm)).mono'
      (((BoundedBorelFunction.truncate f hf m -
        BoundedBorelFunction.truncate f hf n).measurable.norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact BoundedBorelFunction.norm_sub_truncate_sq_le hf (Nat.cast_le.2 hm)
          (Nat.cast_le.2 hn) t)
  have hsq : ‖P.integral (BoundedBorelFunction.truncate f hf m) x -
      P.integral (BoundedBorelFunction.truncate f hf n) x‖ ^ 2 ≤ ∫ t, tail N t ∂(P.diag x) := by
    rw [← sub_apply, ← map_sub, P.norm_sq_integral_apply]
    exact integral_mono hdiff_int
      ((hint.const_mul 4).indicator (measurableSet_lt measurable_const hf.norm))
      (BoundedBorelFunction.norm_sub_truncate_sq_le hf (Nat.cast_le.2 hm) (Nat.cast_le.2 hn))
  rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
  exact (Real.sqrt_le_sqrt hsq).trans_lt (hN N le_rfl)

private def spectralIntegralAux (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f)
    (x : spectralIntegralDomain P f) : H :=
  limUnder atTop fun n : ℕ => P.integral (BoundedBorelFunction.truncate f hf n) x

private theorem tendsto_integral_truncate (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : spectralIntegralDomain P f) :
    Tendsto (fun n : ℕ => P.integral (BoundedBorelFunction.truncate f hf n) x) atTop
      (𝓝 (spectralIntegralAux P f hf x)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_integral_truncate P hf x))

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
        have hlim :=
          (tendsto_integral_truncate P hf x).add (tendsto_integral_truncate P hf y)
        refine tendsto_nhds_unique (tendsto_integral_truncate P hf (x + y)) ?_
        exact hlim.congr fun n =>
          (map_add (P.integral (BoundedBorelFunction.truncate f hf n)) (x : H) (y : H)).symm
      map_smul' := fun c x => by
        have hlim := (tendsto_integral_truncate P hf x).const_smul c
        simpa only [RingHom.id_apply] using
          tendsto_nhds_unique (tendsto_integral_truncate P hf (c • x))
            (hlim.congr fun n =>
              (map_smul (P.integral (BoundedBorelFunction.truncate f hf n)) c (x : H)).symm) }

/-- On the domain of `P.spectralIntegral f hf`, the bounded integrals of the natural level-set
truncations `BoundedBorelFunction.truncate f hf n` converge to `P.spectralIntegral f hf x`. -/
theorem tendsto_integral_truncate_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n : ℕ => P.integral (BoundedBorelFunction.truncate f hf n) x) atTop
      (𝓝 (P.spectralIntegral f hf x)) :=
  tendsto_integral_truncate P hf x

/-! ## Domain, spectral cutoffs, and density -/

/-- A vector `x : H` belongs to the domain of `P.spectralIntegral f hf` if and only if `f` has
finite second moment against the diagonal measure `P.diag x`. -/
@[simp]
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  Iff.rfl

/-- A vector `x : H` belongs to the domain of `P.spectralIntegral f hf` if and only if `f` belongs
to `L²(P.diag x)` (`MemLp f 2 (P.diag x)`). -/
theorem mem_spectralIntegral_domain_iff_memLp (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ MemLp f 2 (P.diag x) :=
  (P.mem_spectralIntegral_domain_iff hf x).trans
    hf.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.symm

/-- A vector `x : H` belongs to the domain of `P.spectralIntegral f hf` if and only if
`t ↦ ‖f t‖ ^ 2` is Bochner integrable against `P.diag x`. -/
theorem mem_spectralIntegral_domain_iff_integrable (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
  (P.mem_spectralIntegral_domain_iff_memLp hf x).trans
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable)

/-- Every spectral projection `P.proj B hB` leaves the domain of `P.spectralIntegral f hf`
invariant. -/
theorem proj_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (B : Set X) (hB : MeasurableSet B) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf] at hx ⊢
  rw [P.diag_proj B hB x]
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hx

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
theorem proj_mem_spectralIntegral_domain_of_eq_on (P : ProjValMeasure X H) {f : X → ℂ}
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

/-- The spectral projections `P.proj {t | ‖f t‖ ≤ n}` converge strongly to the identity on `H`. -/
theorem tendsto_proj_norm_le_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : H) :
    Tendsto (fun n : ℕ => P.proj {t | ‖f t‖ ≤ (n : ℝ)}
      (measurableSet_le hf.norm measurable_const) x) atTop (𝓝 x) := by
  let F : ℕ → BoundedBorelFunction X := fun n =>
    BoundedBorelFunction.indicator {t | ‖f t‖ ≤ (n : ℝ)}
      (measurableSet_le hf.norm measurable_const) 1
  have hlim : Tendsto (fun n => P.integral (F n) x) atTop (𝓝 (P.integral 1 x)) :=
    P.tendsto_integral_apply_filter_of_dominated_convergence (M := 1)
      (Eventually.of_forall fun n => Eventually.of_forall fun t => by
        by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} <;> simp [F, ht])
      (Eventually.of_forall fun t => by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
        have ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} := hN.trans (Nat.cast_le.2 hn)
        simp [F, ht])
      x
  simpa only [F, P.integral_indicator, map_one, one_apply_eq_self] using hlim

/-- The second-moment domain of `P.spectralIntegral f hf` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    Dense ((P.spectralIntegral f hf).domain : Set H) := fun x =>
  mem_closure_of_tendsto (P.tendsto_proj_norm_le_apply hf x)
    (Eventually.of_forall fun n => P.proj_norm_le_mem_spectralIntegral_domain hf n x)

/-- Every spectral projection `P.proj B hB` commutes with `P.spectralIntegral f hf` on its
domain. -/
theorem spectralIntegral_proj_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (B : Set X) (hB : MeasurableSet B) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf B hB x.2⟩ =
      P.proj B hB (P.spectralIntegral f hf x) := by
  let xB : (P.spectralIntegral f hf).domain :=
    ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf B hB x.2⟩
  refine tendsto_nhds_unique (P.tendsto_integral_truncate_spectralIntegral hf xB) ?_
  have hcont := ((P.proj B hB).continuous.tendsto _).comp
    (P.tendsto_integral_truncate_spectralIntegral hf x)
  refine hcont.congr fun n => ?_
  simp only [Function.comp_apply, xB]
  rw [P.integral_proj_apply _ hB x, P.proj_integral_apply hB _ x]

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
  let xB : (P.spectralIntegral f hf).domain :=
    ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain_of_bound hf hB
      (hfg.mono fun t ht htB => (ht htB).symm ▸ g.norm_coe_le_norm t)⟩
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g‖
  refine tendsto_nhds_unique (P.tendsto_integral_truncate_spectralIntegral hf xB) ?_
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  simp only [xB]
  rw [P.integral_proj_apply (BoundedBorelFunction.truncate f hf n) hB x, ← sub_eq_zero,
    ← sub_apply, ← map_sub, P.integral_apply_eq_zero_iff]
  refine hfg.mono fun t ht => ?_
  by_cases htB : t ∈ B
  · have hle : t ∈ {x | ‖f x‖ ≤ (n : ℝ)} := by
      rw [Set.mem_ofPred_eq, ht htB]
      exact (g.norm_coe_le_norm t).trans (hN.trans (Nat.cast_le.2 hn))
    simp [htB, Set.indicator_of_mem hle, ht htB]
  · simp [htB]

/-- If `f` agrees on a measurable set `B` with a bounded Borel symbol `g`, then
`P.spectralIntegral f hf` acts on `P.proj B hB x` as the bounded Borel integral of
`BoundedBorelFunction.indicator B hB g` applied to `x`. -/
theorem spectralIntegral_proj_eq_integral_indicator_of_eq_on (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {g : BoundedBorelFunction X}
    (hfg : Set.EqOn f g B) (x : H) :
    P.spectralIntegral f hf
        ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain_of_eq_on hf hB hfg x⟩ =
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
    P.spectralIntegral_proj_eq_integral_indicator_of_eq_on hf (B := {t | ‖f t‖ ≤ M})
      (measurableSet_le hf.norm measurable_const)
      (g := BoundedBorelFunction.truncate f hf M)
      (fun _ ht => by simp [Set.indicator_of_mem ht]) x

/-- For `x` in the domain of `P.spectralIntegral f hf`, the values of `P.spectralIntegral f hf` on
the spectral cutoffs `P.proj {t | ‖f t‖ ≤ n} _ x` converge to `P.spectralIntegral f hf x`. -/
theorem tendsto_spectralIntegral_proj_norm_le_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n : ℕ => P.spectralIntegral f hf ⟨P.proj {t | ‖f t‖ ≤ (n : ℝ)}
        (measurableSet_le hf.norm measurable_const) x,
        P.proj_norm_le_mem_spectralIntegral_domain hf n x⟩)
      atTop (𝓝 (P.spectralIntegral f hf x)) := by
  simpa only [spectralIntegral_proj_norm_le_eq_integral_truncate] using
    P.tendsto_integral_truncate_spectralIntegral hf x

/-! ## Norm-square identity, diagonal and polarized densities, and matrix elements -/

/-- **Second-moment norm identity** for the unbounded spectral integral: for `x` in the domain of
`P.spectralIntegral f hf`, `‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. -/
theorem norm_sq_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable hf x).1 x.2
  have hcont : Continuous fun v : H => ‖v‖ ^ 2 := continuous_norm.pow 2
  refine tendsto_nhds_unique
    ((hcont.tendsto _).comp (P.tendsto_integral_truncate_spectralIntegral hf x)) ?_
  have hdom : Tendsto
      (fun n : ℕ => ∫ t, ‖BoundedBorelFunction.truncate f hf n t‖ ^ 2 ∂(P.diag x)) atTop
      (𝓝 (∫ t, ‖f t‖ ^ 2 ∂(P.diag x))) :=
    tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
      (fun n => ((BoundedBorelFunction.truncate f hf n).measurable.norm.pow_const
        2).aestronglyMeasurable) hint
      (fun n => ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (BoundedBorelFunction.norm_truncate_apply_le f hf n t) 2)
      (ae_of_all _ fun t =>
        (((BoundedBorelFunction.tendsto_truncate_apply hf t).comp
          tendsto_natCast_atTop_atTop).norm).pow 2)
  exact hdom.congr fun n =>
    (P.norm_sq_integral_apply (BoundedBorelFunction.truncate f hf n) x).symm

/-- The diagonal scalar measure of `P.spectralIntegral f hf x` is `P.diag x` weighted by
`t ↦ ‖f t‖ₑ ^ 2`. -/
@[simp]
theorem diag_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    P.diag (P.spectralIntegral f hf x) = (P.diag x).withDensity fun t => ‖f t‖ₑ ^ 2 := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable hf x).1 x.2
  ext B hB
  let xB : (P.spectralIntegral f hf).domain :=
    ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf B hB x.2⟩
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
      rw [ofReal_integral_eq_lintegral_ofReal hint.integrableOn
        (ae_of_all _ fun _ => sq_nonneg _)]
      refine lintegral_congr fun t => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ((P.diag x).withDensity fun t => ‖f t‖ₑ ^ 2) B := (withDensity_apply _ hB).symm

/-- For `x` in the domain of `P.spectralIntegral f hf`, `P.spectralIntegral f hf x = 0` if and
only if `f = 0` almost everywhere for `P.diag x`. -/
theorem spectralIntegral_apply_eq_zero_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf x = 0 ↔ f =ᵐ[P.diag x] 0 := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable hf x).1 x.2
  rw [← norm_eq_zero, ← pow_eq_zero_iff (n := 2) two_ne_zero, P.norm_sq_spectralIntegral_apply hf,
    integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint]
  simp [EventuallyEq]

private theorem lintegral_enorm_polarizedComplexMeasure_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    ∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure y x).variation ≤
      ENNReal.ofReal (‖y‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag x))) := by
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable hf x).1 hx
  have hlhs : ∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure y x).variation =
      ⨆ n : ℕ, ∫⁻ t, ‖BoundedBorelFunction.truncate f hf n t‖ₑ
        ∂(P.polarizedComplexMeasure y x).variation := by
    rw [← lintegral_iSup (fun n => (BoundedBorelFunction.truncate f hf n).measurable.eNorm)
      ((BoundedBorelFunction.enorm_truncate_apply_mono hf).comp Nat.mono_cast)]
    exact lintegral_congr fun t => (BoundedBorelFunction.iSup_enorm_truncate_apply hf t).symm
  rw [hlhs]
  refine iSup_le fun n => (P.lintegral_enorm_variation_polarizedComplexMeasure_le
    (BoundedBorelFunction.truncate f hf n) y x).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg y)
  rw [← Real.sqrt_sq (norm_nonneg (P.integral (BoundedBorelFunction.truncate f hf n) x)),
    P.norm_sq_integral_apply]
  have htr_int : Integrable (fun t => ‖BoundedBorelFunction.truncate f hf n t‖ ^ 2) (P.diag x) :=
    hint.mono'
      (((BoundedBorelFunction.truncate f hf n).measurable.norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (BoundedBorelFunction.norm_truncate_apply_le f hf n t) 2)
  exact Real.sqrt_le_sqrt (integral_mono htr_int hint fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (BoundedBorelFunction.norm_truncate_apply_le f hf n t) 2)

/-- For `x` in the domain of `P.spectralIntegral f hf` and every `y : H`, the symbol `f` is
integrable against the polarized complex measure `P.polarizedComplexMeasure y x`. -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain
    (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    (P.polarizedComplexMeasure y x).Integrable f :=
  ⟨hf.aestronglyMeasurable,
    (P.lintegral_enorm_polarizedComplexMeasure_le hf hx y).trans_lt ENNReal.ofReal_lt_top⟩

/-- For `y` in the domain of `P.spectralIntegral f hf` and every `x : H`, the symbol `f` is
integrable against the polarized complex measure `P.polarizedComplexMeasure y x`. -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain_left
    (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {y : H} (hy : y ∈ (P.spectralIntegral f hf).domain) (x : H) :
    (P.polarizedComplexMeasure y x).Integrable f := by
  rw [VectorMeasure.Integrable, P.variation_polarizedComplexMeasure_comm y x]
  exact P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hy x

/-- **Cauchy–Schwarz variation estimate** for the polarized spectral measure: for `x` in the
domain of `P.spectralIntegral f hf` and any `y : H`,
`∫ t, ‖f t‖ ∂|μ_(y,x)| ≤ ‖y‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag x))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure y x).variation ≤
      ‖y‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) := by
  rw [integral_norm_eq_lintegral_eNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (P.lintegral_enorm_polarizedComplexMeasure_le hf hx y)

/-- **Left-slot Cauchy–Schwarz variation estimate** for the polarized spectral measure: for `y` in
the domain of `P.spectralIntegral f hf` and any `x : H`,
`∫ t, ‖f t‖ ∂|μ_(y,x)| ≤ ‖x‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag y))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le_left (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) {y : H} (hy : y ∈ (P.spectralIntegral f hf).domain) (x : H) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure y x).variation ≤
      ‖x‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag y)) := by
  rw [P.variation_polarizedComplexMeasure_comm y x]
  exact P.integral_norm_variation_polarizedComplexMeasure_le hf hy x

/-- **Matrix elements of the unbounded spectral integral.** For `x` in the domain of
`P.spectralIntegral f hf` and any `y : H`, `⟪y, P.spectralIntegral f hf x⟫_ℂ` is the scalar
integral of `f` against `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    ⟪y, P.spectralIntegral f hf x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hint := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x.2 y
  have hcont : Continuous fun v : H => ⟪y, v⟫_ℂ := continuous_const.inner continuous_id
  refine tendsto_nhds_unique
    ((hcont.tendsto _).comp (P.tendsto_integral_truncate_spectralIntegral hf x)) ?_
  have hdom : Tendsto
      (fun n : ℕ => ∫ᵛ t, BoundedBorelFunction.truncate f hf n t
        ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
      atTop (𝓝 (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
      (fun n => (BoundedBorelFunction.truncate f hf n).measurable.aestronglyMeasurable) hint.norm
      (fun n => ae_of_all _ (BoundedBorelFunction.norm_truncate_apply_le f hf n))
      (ae_of_all _ fun t =>
        (BoundedBorelFunction.tendsto_truncate_apply hf t).comp tendsto_natCast_atTop_atTop)
  exact hdom.congr fun n =>
    P.integral_polarizedComplexMeasure_eq_inner_integral
      (BoundedBorelFunction.truncate f hf n) y x

/-- **Left-slot matrix elements of the unbounded spectral integral.** For `y` in the domain of
`P.spectralIntegral f hf` and any `x : H`, `⟪P.spectralIntegral f hf y, x⟫_ℂ` is the scalar
integral of `star (f t)` against `P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral_apply_left (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (y : (P.spectralIntegral f hf).domain) (x : H) :
    ⟪P.spectralIntegral f hf y, x⟫_ℂ =
      ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have hy' : (y : H) ∈ (P.spectralIntegral (star f) hsf).domain := by
    simpa [P.mem_spectralIntegral_domain_iff, ← ofReal_norm] using y.2
  have hint := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain_left hsf hy' x
  have hcont : Continuous fun u : H => ⟪u, x⟫_ℂ := continuous_id.inner continuous_const
  refine tendsto_nhds_unique
    ((hcont.tendsto _).comp (P.tendsto_integral_truncate_spectralIntegral hf y)) ?_
  have hdom : Tendsto
      (fun n : ℕ => ∫ᵛ t, star (BoundedBorelFunction.truncate f hf n t)
        ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
      atTop (𝓝 (∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖(star f) t‖)
      (fun n => (star (BoundedBorelFunction.truncate f hf n)).measurable.aestronglyMeasurable)
      hint.norm
      (fun n => ae_of_all _ fun t => by
        simpa using BoundedBorelFunction.norm_truncate_apply_le f hf n t)
      (ae_of_all _ fun t => (continuous_star.tendsto (f t)).comp
        ((BoundedBorelFunction.tendsto_truncate_apply hf t).comp tendsto_natCast_atTop_atTop))
  refine hdom.congr fun n => ?_
  simp only [Function.comp_apply, ← BoundedBorelFunction.star_apply]
  rw [P.integral_polarizedComplexMeasure_eq_inner_integral,
    map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

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
      (P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x.2 y)]

/-- Applying `P.spectralIntegral f hf` in the conjugate-linear argument weights the polarized
complex measure by `star f`. -/
theorem polarizedComplexMeasure_spectralIntegral_left (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : (P.spectralIntegral f hf).domain) (x : H) :
    P.polarizedComplexMeasure (P.spectralIntegral f hf y) x =
      (P.polarizedComplexMeasure y x).withDensity (star f) (ContinuousLinearMap.mul ℝ ℂ) := by
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have hy' : (y : H) ∈ (P.spectralIntegral (star f) hsf).domain := by
    simpa [P.mem_spectralIntegral_domain_iff, ← ofReal_norm] using y.2
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
    T = P.spectralIntegral f hf := by
  refine LinearPMap.ext (Submodule.ext hdom) fun x hx₁ hx₂ => ext_inner_left ℂ fun y => ?_
  rw [hinner ⟨x, hx₁⟩ y, ← P.inner_spectralIntegral_apply hf ⟨x, hx₂⟩ y]

/-! ## Bounded calculus comparison, algebraic properties, `P.ae`-invariance, and reindexing -/

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
  · exact (P.integral_polarizedComplexMeasure_eq_inner_integral g y x).symm

/-- The unbounded spectral integral of `0` is the everywhere-defined zero partial operator. -/
@[simp]
theorem spectralIntegral_zero (P : ProjValMeasure X H) :
    P.spectralIntegral 0 measurable_const = 0 := by
  have h := P.spectralIntegral_coe_boundedBorelFunction 0
  simp only [BoundedBorelFunction.coe_zero, map_zero] at h
  refine h.trans (LinearPMap.ext (by simp) ?_)
  simp

/-- The unbounded spectral integral of `1` is the everywhere-defined identity operator. -/
@[simp]
theorem spectralIntegral_one (P : ProjValMeasure X H) :
    P.spectralIntegral 1 measurable_const = (ContinuousLinearMap.id ℂ H).toPMap ⊤ := by
  simpa only [BoundedBorelFunction.coe_one, map_one, ContinuousLinearMap.one_def] using
    P.spectralIntegral_coe_boundedBorelFunction 1

/-- The unbounded spectral integral of the indicator of a measurable set `B` is the everywhere
defined projection `P.proj B hB`. -/
theorem spectralIntegral_indicator_one (P : ProjValMeasure X H) {B : Set X}
    (hB : MeasurableSet B) :
    P.spectralIntegral (B.indicator 1) (measurable_const.indicator hB) =
      (P.proj B hB).toPMap ⊤ := by
  simpa only [BoundedBorelFunction.coe_indicator, BoundedBorelFunction.coe_one,
    P.integral_indicator hB] using
    P.spectralIntegral_coe_boundedBorelFunction (BoundedBorelFunction.indicator B hB 1)

/-- Negating the symbol negates the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_neg (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (-f) hf.neg = -P.spectralIntegral f hf := by
  symm
  refine P.eq_spectralIntegral_of_domain_of_inner hf.neg (fun x => ?_) (fun x y => ?_)
  · simp [LinearPMap.neg_domain]
  · simp only [LinearPMap.neg_apply, inner_neg_right, Pi.neg_apply,
      VectorMeasure.integral_fun_neg]
    exact neg_inj.2 (P.inner_spectralIntegral_apply hf x y)

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
    have hxf : (x : H) ∈ (P.spectralIntegral f hf).domain := x.2.1
    have hxg : (x : H) ∈ (P.spectralIntegral g hg).domain := x.2.2
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
  simpa only [sub_eq_add_neg, P.spectralIntegral_neg hg] using
    P.add_le_spectralIntegral_add hf hg.neg

/-- Measurable symbols that agree `P`-almost everywhere have equal unbounded spectral integrals. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : f =ᶠ[P.ae] g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg := by
  have hdom : (P.spectralIntegral f hf).domain = (P.spectralIntegral g hg).domain := by
    ext x
    simp only [P.mem_spectralIntegral_domain_iff]
    have hlin : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) = ∫⁻ t, ‖g t‖ₑ ^ 2 ∂(P.diag x) :=
      lintegral_congr_ae ((P.ae_diag_of_ae x h).mono fun _ ht => by dsimp only; rw [ht])
    rw [hlin]
  refine LinearPMap.ext hdom fun x hx₁ hx₂ => ?_
  have htr (n : ℕ) : P.integral (BoundedBorelFunction.truncate f hf n) x =
      P.integral (BoundedBorelFunction.truncate g hg n) x := by
    have htr_ae :
        (BoundedBorelFunction.truncate f hf n : X → ℂ) =ᶠ[P.ae]
          BoundedBorelFunction.truncate g hg n := by
      filter_upwards [h] with t ht
      simp [Set.indicator_apply, ht]
    rw [P.integral_congr_ae htr_ae]
  exact tendsto_nhds_unique (P.tendsto_integral_truncate_spectralIntegral hf ⟨x, hx₁⟩)
    ((P.tendsto_integral_truncate_spectralIntegral hg ⟨x, hx₂⟩).congr fun n => (htr n).symm)

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
      rw [← P.spectralIntegral_proj_eq_integral_indicator_of_eq_on hf hB hfx x,
        ← P.spectralIntegral_proj_eq_integral_indicator_of_eq_on hg hB hgx x]
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
  have htr (n : ℕ) : (P.map κ hκ).integral (BoundedBorelFunction.truncate f hf n) x =
      P.integral (BoundedBorelFunction.truncate (f ∘ κ) (hf.comp hκ) n) x := by
    rw [P.integral_map κ hκ, BoundedBorelFunction.compStarAlgHom'_truncate]
  exact tendsto_nhds_unique
    ((P.map κ hκ).tendsto_integral_truncate_spectralIntegral hf ⟨x, hx₁⟩)
    ((P.tendsto_integral_truncate_spectralIntegral (hf.comp hκ) ⟨x, hx₂⟩).congr
      fun n => (htr n).symm)

/-! ## Hilbert adjoint, closedness, normality, self-adjointness, and uniqueness -/

/-- `P.spectralIntegral f hf` and `P.spectralIntegral (star f) _` are formal adjoints. -/
private theorem isFormalAdjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).IsFormalAdjoint
      (P.spectralIntegral (star f) (continuous_star.measurable.comp hf : Measurable (star f))) := by
  intro x y
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have hcont₁ : Continuous fun u : H => ⟪u, (y : H)⟫_ℂ := continuous_id.inner continuous_const
  have hcont₂ : Continuous fun v : H => ⟪(x : H), v⟫_ℂ := continuous_const.inner continuous_id
  refine tendsto_nhds_unique
    ((hcont₁.tendsto _).comp (P.tendsto_integral_truncate_spectralIntegral hf x))
    (((hcont₂.tendsto _).comp
      (P.tendsto_integral_truncate_spectralIntegral hsf y)).congr fun n => ?_)
  dsimp only [Function.comp_apply]
  rw [← BoundedBorelFunction.star_truncate f hf n, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- Every vector in the domain of `(P.spectralIntegral f hf).adjoint` belongs to the second-moment
domain of `star f`. -/
private theorem adjoint_domain_le_spectralIntegral_star (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain ≤
      (P.spectralIntegral (star f)
        (continuous_star.measurable.comp hf : Measurable (star f))).domain := by
  intro y hy
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
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
          = ⟪y, P.integral (BoundedBorelFunction.truncate f hf n) x⟫_ℂ := by
        rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪y, P.spectralIntegral f hf xn⟫_ℂ := by
        rw [← P.spectralIntegral_proj_norm_le_eq_integral_truncate hf n x]
      _ = ⟪(P.spectralIntegral f hf).adjoint y', (xn : H)⟫_ℂ :=
        ((LinearPMap.adjoint_isFormalAdjoint hdense) y' xn).symm
      _ = ⟪P.proj {t | ‖f t‖ ≤ (n : ℝ)} hBn ((P.spectralIntegral f hf).adjoint y'), x⟫_ℂ := by
        dsimp only [xn]
        rw [← ContinuousLinearMap.adjoint_inner_left, (P.isSelfAdjoint_proj _ hBn).adjoint_eq]
  rw [P.mem_spectralIntegral_domain_iff hsf]
  have hstar : (fun t => ‖(star f) t‖ₑ ^ 2) = fun t => ‖f t‖ₑ ^ 2 := by
    ext t
    simp [← ofReal_norm]
  rw [hstar]
  have hlhs : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag y) =
      ⨆ n : ℕ, ∫⁻ t, ‖BoundedBorelFunction.truncate f hf n t‖ₑ ^ 2 ∂(P.diag y) := by
    rw [← lintegral_iSup
      (fun n => (BoundedBorelFunction.truncate f hf n).measurable.eNorm.pow_const 2)
      (fun m n hmn t => pow_le_pow_left'
        (BoundedBorelFunction.enorm_truncate_apply_mono hf (Nat.cast_le.2 hmn) t) 2)]
    exact lintegral_congr fun t => (BoundedBorelFunction.iSup_enorm_pow_truncate_apply hf 2 t).symm
  rw [hlhs]
  refine (iSup_le (a := ‖(P.spectralIntegral f hf).adjoint y'‖ₑ ^ 2) fun n => ?_).trans_lt
    (ENNReal.pow_lt_top eNorm_lt_top)
  have hdiag : ∫⁻ t, ‖BoundedBorelFunction.truncate f hf n t‖ₑ ^ 2 ∂(P.diag y) =
      P.diag (P.integral (star (BoundedBorelFunction.truncate f hf n)) y) Set.univ := by
    rw [P.diag_integral, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact lintegral_congr fun t => by
      simp only [BoundedBorelFunction.star_apply, ← ofReal_norm, norm_star]
  rw [hdiag, P.diag_univ, hproj_eq n]
  exact pow_le_pow_left' (eNorm_le_iff_norm_le.2 (P.norm_proj_apply_le _ _ _)) 2

/-- **Hilbert adjoint of the unbounded spectral integral.** The adjoint of `P.spectralIntegral f hf`
is `P.spectralIntegral (star f) _`. -/
@[simp]
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf : Measurable (star f)) := by
  have hle :
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf : Measurable (star f)) ≤
        (P.spectralIntegral f hf).adjoint :=
    (P.isFormalAdjoint_spectralIntegral hf).le_adjoint (P.dense_spectralIntegral_domain hf)
  exact (LinearPMap.eq_of_le_of_domain_eq hle
    (le_antisymm hle.1 (P.adjoint_domain_le_spectralIntegral_star hf))).symm

/-- Conjugating the symbol preserves the domain of the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_star_domain (P : ProjValMeasure X H) {f : X → ℂ}
    {hsf : Measurable (star f)} :
    (P.spectralIntegral (star f) hsf).domain =
      (P.spectralIntegral f (star_star f ▸ continuous_star.measurable.comp hsf)).domain := by
  ext x
  simp [P.mem_spectralIntegral_domain_iff, ← ofReal_norm]

/-- The Hilbert adjoint `(P.spectralIntegral f hf).adjoint` has the same domain as
`P.spectralIntegral f hf`. -/
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain = (P.spectralIntegral f hf).domain := by
  simp

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

/-- The supremum of the spectral cutoff ranges `LinearMap.range (P.proj {t | ‖f t‖ ≤ n} _)` is a
graph core for `P.spectralIntegral f hf`. -/
theorem spectralIntegral_hasCore_iSup_range_proj_norm_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, LinearMap.range
        (P.proj {t | ‖f t‖ ≤ (n : ℝ)}
          (measurableSet_le hf.norm measurable_const) : H →ₗ[ℂ] H)) := by
  let S : Submodule ℂ H :=
    ⨆ n : ℕ, LinearMap.range
      (P.proj {t | ‖f t‖ ≤ (n : ℝ)} (measurableSet_le hf.norm measurable_const) : H →ₗ[ℂ] H)
  have hS : S ≤ (P.spectralIntegral f hf).domain := by
    refine iSup_le fun n => ?_
    rintro _ ⟨x, rfl⟩
    exact P.proj_norm_le_mem_spectralIntegral_domain hf n x
  rw [(P.isClosed_spectralIntegral hf).hasCore_iff_graph_subset_closure hS]
  rintro ⟨x, y⟩ hxy
  have hx : x ∈ (P.spectralIntegral f hf).domain := LinearPMap.mem_domain_of_mem_graph hxy
  have hy : y = P.spectralIntegral f hf ⟨x, hx⟩ := (LinearPMap.image_iff hx).2 hxy
  rw [hy]
  refine mem_closure_of_tendsto
    ((P.tendsto_proj_norm_le_apply hf x).prodMk_nhds
      (P.tendsto_spectralIntegral_proj_norm_le_apply hf ⟨x, hx⟩))
    (Eventually.of_forall fun n => ?_)
  let hBn : MeasurableSet {t | ‖f t‖ ≤ (n : ℝ)} := measurableSet_le hf.norm measurable_const
  have hmemS : P.proj {t | ‖f t‖ ≤ (n : ℝ)} hBn x ∈ S :=
    Submodule.mem_iSup_of_mem n ⟨x, rfl⟩
  have hmemD : P.proj {t | ‖f t‖ ≤ (n : ℝ)} hBn x ∈
      ((P.spectralIntegral f hf).domRestrict S).domain := by
    rw [LinearPMap.domRestrict_domain, Submodule.mem_inf]
    exact ⟨hmemS, P.proj_norm_le_mem_spectralIntegral_domain hf n x⟩
  have happly : (P.spectralIntegral f hf).domRestrict S ⟨_, hmemD⟩ =
      P.spectralIntegral f hf ⟨_, P.proj_norm_le_mem_spectralIntegral_domain hf n x⟩ :=
    LinearPMap.domRestrict_apply rfl
  rw [← happly]
  exact ((P.spectralIntegral f hf).domRestrict S).mem_graph ⟨_, hmemD⟩

/-- **Normality of the unbounded spectral integral:** on their common domain,
`(P.spectralIntegral f hf).adjoint` and `P.spectralIntegral f hf` have equal norms at every
vector. -/
theorem norm_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    ‖(P.spectralIntegral f hf).adjoint
      ⟨x, (P.adjoint_spectralIntegral_domain hf).symm ▸ x.2⟩‖ =
      ‖P.spectralIntegral f hf x‖ := by
  let hsf : Measurable (star f) := continuous_star.measurable.comp hf
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) hsf).domain := by
    simpa [P.mem_spectralIntegral_domain_iff, ← ofReal_norm] using x.2
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
      P.norm_sq_spectralIntegral_apply hf, P.adjoint_spectralIntegral_domain hf,
      P.inner_adjoint_spectralIntegral_apply hf⟩,
    fun _ hT => P.eq_spectralIntegral_of_domain_of_inner hf hT.1 hT.2.1⟩

end ProjValMeasure
end TauCeti
