/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.SpectralIntegral.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Adjoint, closedness, graph cores, and self-adjointness of unbounded spectral integrals

Let `P` be a normalized projection-valued measure on a measurable space `X` acting on a complex
Hilbert space `H`, and let `f : X → ℂ` be measurable. Continuing from
`TauCeti.Analysis.InnerProductSpace.ProjValMeasure.SpectralIntegral.Basic`, this file proves the
unbounded Hilbert-space operator properties of `P.spectralIntegral f hf`:

* **Hilbert adjoint (`adjoint_spectralIntegral`):** the Hilbert adjoint of `P.spectralIntegral f hf`
  is `P.spectralIntegral (star f) (continuous_star.measurable.comp hf)`, with the same maximal
  second-moment domain (`adjoint_spectralIntegral_domain`) and conjugate matrix elements
  (`inner_adjoint_spectralIntegral_apply`).
* **Normality (`norm_adjoint_spectralIntegral_apply`):** for every vector in the common domain,
  `‖(P.spectralIntegral f hf).adjoint x‖ = ‖P.spectralIntegral f hf x‖`.
* **Closedness and spectral cutoff core (`isClosed_spectralIntegral`,
  `hasCore_iSup_range_proj_spectralIntegral`):** `P.spectralIntegral f hf` is closed, and the union
  (supremum) of the ranges of the cutoff projections `P({t | ‖f t‖ ≤ n})` is a graph core.
* **Self-adjointness (`isSelfAdjoint_spectralIntegral_iff`):** `P.spectralIntegral f hf` is
  self-adjoint if and only if `f` is `P`-almost everywhere real-valued (`star (f t) = f t`).
* **Existence and uniqueness package (`existsUnique_spectralIntegral`):** there is a unique partial
  linear operator having the second-moment domain and polarized matrix elements of `f`, and it is
  densely defined, closed, satisfies the second-moment norm identity, and has Hilbert adjoint on the
  same domain with the polarized matrix elements of `star f`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1,
  Theorem 3.2 and equations (3.25)–(3.29).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.3, Theorem 4.16.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Hilbert adjoint and normality -/

private theorem lintegral_indicator_norm_le_adjoint (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : (P.spectralIntegral f hf).adjoint.domain) (n : ℕ) :
    (∫⁻ t, {s | ‖f s‖ ≤ (n : ℝ)}.indicator (fun s => ‖f s‖ₑ ^ 2) t ∂(P.diag y)) ≤
      ‖(P.spectralIntegral f hf).adjoint y‖ₑ ^ 2 := by
  let B : Set X := {s | ‖f s‖ ≤ (n : ℝ)}
  have hB : MeasurableSet B := measurableSet_le hf.norm measurable_const
  let fn : BoundedBorelFunction X :=
    BoundedBorelFunction.ofFunction (B.indicator f) (hf.indicator hB)
      ⟨n, Nat.cast_nonneg n, fun t => by
        by_cases ht : t ∈ B
        · simpa [B, Set.indicator_of_mem ht] using ht
        · simp [Set.indicator_of_notMem ht]⟩
  have hfn : BoundedBorelFunction.indicator B hB fn = fn := by
    ext t
    by_cases ht : t ∈ B <;> simp [fn, ht]
  let z : H := (P.spectralIntegral f hf).adjoint y
  have hz : P.proj B hB z = P.integral (star fn) y := by
    refine ext_inner_right ℂ fun w => ?_
    let pw : (P.spectralIntegral f hf).domain :=
      ⟨P.proj B hB w, P.proj_apply_mem_spectralIntegral_domain hf hB (M := n)
        (Eventually.of_forall fun _ ht => ht) w⟩
    have hTpw : P.spectralIntegral f hf pw = P.integral fn w := by
      have h := P.spectralIntegral_apply_proj_eq_integral hf hB fn
        (Eventually.of_forall fun t ht => by simp [fn, Set.indicator_of_mem ht]) w
      rwa [hfn] at h
    calc ⟪P.proj B hB z, w⟫_ℂ
        = ⟪z, P.proj B hB w⟫_ℂ := (P.isSelfAdjoint_proj B hB).isSymmetric z w
      _ = ⟪(y : H), P.spectralIntegral f hf pw⟫_ℂ :=
            (LinearPMap.adjoint_isFormalAdjoint (P.dense_spectralIntegral_domain f hf)) y pw
      _ = ⟪(y : H), P.integral fn w⟫_ℂ := by rw [hTpw]
      _ = ⟪P.integral (star fn) y, w⟫_ℂ := by
            rw [← ContinuousLinearMap.adjoint_inner_left,
              ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  have hnorm : ∫ t, ‖(star fn) t‖ ^ 2 ∂(P.diag y) ≤ ‖z‖ ^ 2 := by
    rw [← P.norm_sq_integral_apply (star fn) y, ← hz]
    exact pow_le_pow_left₀ (norm_nonneg _) (P.norm_proj_apply_le B hB z) 2
  have hint : Integrable (fun t => ‖(star fn) t‖ ^ 2) (P.diag y) :=
    .of_bound ((star fn).measurable.norm.pow_const 2).aestronglyMeasurable (‖star fn‖ ^ 2)
      (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((star fn).norm_coe_le_norm t) 2)
  have hle := ENNReal.ofReal_le_ofReal hnorm
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm] at hle
  refine (lintegral_congr fun t => ?_).le.trans hle
  by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)}
  · have htB : t ∈ B := ht
    simp [fn, Set.indicator_of_mem ht, Set.indicator_of_mem htB,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  · have htB : t ∉ B := ht
    simp [fn, Set.indicator_of_notMem ht, Set.indicator_of_notMem htB]

/-- **Hilbert adjoint** of the unbounded spectral integral: the adjoint of `P.spectralIntegral f hf`
is the spectral integral of the complex-conjugate symbol `star f`. -/
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf) := by
  let hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have hdense := P.dense_spectralIntegral_domain f hf
  have hformal : (P.spectralIntegral f hf).IsFormalAdjoint (P.spectralIntegral (star f) hfs) :=
    fun x y => P.inner_spectralIntegral_star hf x y
  have hle := hformal.le_adjoint hdense
  have hdom :
      (P.spectralIntegral f hf).adjoint.domain ≤ (P.spectralIntegral (star f) hfs).domain := by
    intro y hy
    rw [P.mem_spectralIntegral_domain_iff]
    let g : ℕ → X → ℝ≥0∞ := fun n t =>
      {s | ‖f s‖ ≤ (n : ℝ)}.indicator (fun s => ‖f s‖ₑ ^ 2) t
    have hg_meas : ∀ n, Measurable (g n) := fun n =>
      (hf.eNorm.pow_const 2).indicator (measurableSet_le hf.norm measurable_const)
    have hg_mono : Monotone g := by
      intro m n hmn t
      by_cases ht : t ∈ {s | ‖f s‖ ≤ (m : ℝ)}
      · have htn : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} :=
          Set.mem_ofPred.2 ((Set.mem_ofPred.1 ht).trans (Nat.cast_le.2 hmn))
        simp [g, Set.indicator_of_mem ht, Set.indicator_of_mem htn]
      · simp [g, Set.indicator_of_notMem ht]
    have hg_sup : ∀ t, (⨆ n, g n t) = ‖(star f) t‖ₑ ^ 2 := by
      intro t
      rw [Pi.star_apply, ← ofReal_norm, norm_star, ofReal_norm]
      refine le_antisymm (iSup_le fun n => ?_) ?_
      · by_cases ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} <;> simp [g, ht]
      · obtain ⟨n, hn⟩ := exists_nat_ge ‖f t‖
        have ht : t ∈ {s | ‖f s‖ ≤ (n : ℝ)} := hn
        exact le_trans (by simp [g, Set.indicator_of_mem ht]) (le_iSup (fun k => g k t) n)
    calc (∫⁻ t, ‖(star f) t‖ₑ ^ 2 ∂(P.diag y))
        = ∫⁻ t, (⨆ n, g n t) ∂(P.diag y) := lintegral_congr fun t => (hg_sup t).symm
      _ = ⨆ n, ∫⁻ t, g n t ∂(P.diag y) := lintegral_iSup hg_meas hg_mono
      _ ≤ ‖(P.spectralIntegral f hf).adjoint ⟨y, hy⟩‖ₑ ^ 2 :=
            iSup_le (lintegral_indicator_norm_le_adjoint P hf ⟨y, hy⟩)
      _ < ∞ := ENNReal.pow_lt_top eNorm_lt_top
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

/-- The Hilbert adjoint of `P.spectralIntegral f hf` has the same domain as
`P.spectralIntegral f hf`. -/
@[simp]
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain = (P.spectralIntegral f hf).domain := by
  rw [P.adjoint_spectralIntegral f hf, spectralIntegral_domain, spectralIntegral_domain,
    spectralIntegralDomain_star]

/-- **Adjoint matrix-element identity**: for `x` in the adjoint domain and every `y : H`,
`⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ` is the polarized integral of `t ↦ star (f t)`. -/
theorem inner_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : Measurable f) (x : (P.spectralIntegral f hf).adjoint.domain) (y : H) :
    ⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ =
      ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hadj := P.adjoint_spectralIntegral f hf
  let x' : (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)).domain :=
    ⟨x, (LinearPMap.ext_iff.1 hadj).1 ▸ x.2⟩
  have hx : (P.spectralIntegral f hf).adjoint x =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf) x' :=
    @(LinearPMap.ext_iff.1 hadj).2 x x.2 x'.2
  rw [hx]
  exact P.inner_spectralIntegral_apply (star f) (continuous_star.measurable.comp hf) x' y

/-- **Normality** of the unbounded spectral integral: on the common domain
`D(T†) = D(T)`, the operator and its Hilbert adjoint have equal norms on every vector. -/
theorem norm_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    ‖(P.spectralIntegral f hf).adjoint ⟨x, (P.adjoint_spectralIntegral_domain f hf).symm ▸ x.2⟩‖ =
      ‖P.spectralIntegral f hf x‖ := by
  have hadj := P.adjoint_spectralIntegral f hf
  have hmem : (x : H) ∈ (P.spectralIntegral f hf).adjoint.domain :=
    (P.adjoint_spectralIntegral_domain f hf).symm ▸ x.2
  let x' : (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)).domain :=
    ⟨x, (LinearPMap.ext_iff.1 hadj).1 ▸ hmem⟩
  have hx : (P.spectralIntegral f hf).adjoint ⟨x, hmem⟩ =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf) x' :=
    @(LinearPMap.ext_iff.1 hadj).2 x hmem x'.2
  rw [hx, P.norm_spectralIntegral_apply, P.norm_spectralIntegral_apply]
  simp [x']

/-! ### Closedness, spectral cutoff cores, self-adjointness, and uniqueness package -/

/-- Every unbounded spectral integral `P.spectralIntegral f hf` is a closed operator. -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).IsClosed := by
  have hstar : Measurable (star f) := continuous_star.measurable.comp hf
  have hadj := P.adjoint_spectralIntegral (star f) hstar
  have heq : P.spectralIntegral (star (star f)) (continuous_star.measurable.comp hstar) =
      P.spectralIntegral f hf :=
    P.spectralIntegral_congr_ae _ hf (Eventually.of_forall fun t => star_star (f t))
  rw [← heq, ← hadj]
  exact LinearPMap.adjoint_isClosed (P.dense_spectralIntegral_domain (star f) hstar)

/-- The supremum of the ranges of the spectral cutoff projections `P({t | ‖f t‖ ≤ n})` is a graph
core for `P.spectralIntegral f hf`. -/
theorem hasCore_iSup_range_proj_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).range) := by
  let S : Submodule ℂ H :=
    ⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).range
  have hS : S ≤ (P.spectralIntegral f hf).domain := by
    refine iSup_le fun n => ?_
    rintro _ ⟨w, rfl⟩
    exact P.proj_apply_mem_spectralIntegral_domain hf
      (measurableSet_le hf.norm measurable_const) (M := n)
      (Eventually.of_forall fun _ ht => ht) w
  rw [(P.isClosed_spectralIntegral f hf).hasCore_iff_graph_subset_closure hS]
  intro p hp
  obtain ⟨x, hx1, hx2⟩ := (P.spectralIntegral f hf).mem_graph_iff.1 hp
  have hp_eq : p = ((x : H), P.spectralIntegral f hf x) := Prod.ext hx1.symm hx2.symm
  rw [hp_eq]
  have hlim := (P.tendsto_proj_norm_le hf x).prodMk_nhds
    (P.tendsto_spectralIntegral_proj_norm_le hf x)
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  let u := P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const) x
  have huS : u ∈ S := Submodule.mem_iSup_of_mem n ⟨x, rfl⟩
  have huT : u ∈ (P.spectralIntegral f hf).domain :=
    P.proj_apply_mem_spectralIntegral_domain hf (measurableSet_le hf.norm measurable_const)
      (M := n) (Eventually.of_forall fun _ ht => ht) x
  let un : ↥(S ⊓ (P.spectralIntegral f hf).domain) := ⟨u, ⟨huS, huT⟩⟩
  have hdom_apply : (P.spectralIntegral f hf).domRestrict S un =
      P.spectralIntegral f hf ⟨u, huT⟩ :=
    LinearPMap.domRestrict_apply (x := un) (y := ⟨u, huT⟩) rfl
  rw [← hdom_apply]
  exact ((P.spectralIntegral f hf).domRestrict S).mem_graph un

/-- **Self-adjointness criterion** for the unbounded spectral integral: `P.spectralIntegral f hf`
is self-adjoint if and only if `f` is `P`-almost everywhere real-valued (`star (f t) = f t`). -/
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔ ∀ᶠ t in P.ae, star (f t) = f t := by
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral f hf,
    P.spectralIntegral_eq_spectralIntegral_iff]
  rfl

/-- A measurable symbol that is `P`-almost everywhere real-valued defines a self-adjoint unbounded
spectral integral. -/
theorem isSelfAdjoint_spectralIntegral_of_ae (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (h : ∀ᶠ t in P.ae, star (f t) = f t) :
    IsSelfAdjoint (P.spectralIntegral f hf) :=
  (P.isSelfAdjoint_spectralIntegral_iff hf).2 h

/-- **Existence and uniqueness** of the unbounded spectral integral: for every normalized
projection-valued measure `P` on a measurable space `X` and every measurable symbol `f : X → ℂ`,
there is a unique partial linear operator `T : H →ₗ.[ℂ] H` whose domain is the second-moment
subspace `{x | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` and whose matrix elements are the polarized
integrals of `f`; moreover, `T` is densely defined and closed, satisfies the second-moment norm
identity, and has Hilbert adjoint on the same domain with the polarized matrix elements of
`star f`. -/
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
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  refine ⟨P.spectralIntegral f hf,
    ⟨fun x => P.mem_spectralIntegral_domain_iff f hf x,
      P.inner_spectralIntegral_apply f hf,
      P.dense_spectralIntegral_domain f hf,
      P.isClosed_spectralIntegral f hf,
      P.norm_sq_spectralIntegral_apply f hf,
      P.adjoint_spectralIntegral_domain f hf,
      P.inner_adjoint_spectralIntegral_apply f hf⟩, ?_⟩
  rintro T ⟨hdom, hinner, -⟩
  exact (P.eq_spectralIntegral_iff hf T).2 ⟨hdom, hinner⟩

end TauCeti.ProjValMeasure
