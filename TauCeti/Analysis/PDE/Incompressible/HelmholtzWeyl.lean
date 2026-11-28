/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.CurlFree
public import TauCeti.Analysis.PDE.Incompressible.LerayProjection
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.Sobolev.D1p0.Restriction

/-!
# The Helmholtz–Weyl decomposition on `L²`

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`. The
**Helmholtz–Weyl decomposition** identifies the orthogonal complement of the solenoidal fields
`L²_σ` in `L²(μ; E)` with the square integrable gradients: a field `w ∈ L²(μ; E)` is orthogonal
to `L²_σ` exactly when `w = ∇q` weakly on the whole space for some locally integrable
`q : E → ℝ`. So every `u ∈ L²(μ; E)` is uniquely `u = ℙu + ∇q`, with `ℙ` the Leray projection
(`TauCeti.lerayProjection`). The orthogonal complement of `L²_σ` is by construction the closure of
the gradients of test functions (`TauCeti.orthogonal_solenoidalLp_two`), so this is equivalently
the statement that this closure consists of the square integrable weak gradients.

## The argument

*Limits of test gradients are gradients.* A limit `w` of test gradients lies in the homogeneous
Sobolev space `D^{1,2}_0(E)` (`TauCeti.wassersteinTangentSpace_le_comap_d1p0Submodule`), and every
element of that space is the weak gradient of a function on the whole space
(`TauCeti.D1p0.exists_hasWeakFDerivOn`).

*Gradients are limits of test gradients.* A square integrable weak gradient `w = ∇q` is curl
free in distributions: `∫ ∂_b φ ⟪a, w⟫ = ∫ ∂_a φ ⟪b, w⟫` for every test function `φ`, by the
symmetry of second derivatives. So is every limit of test gradients, hence `ℙw`, which is also
solenoidal. A field that is both divergence free and curl free is weakly harmonic, since
`∫ Δφ ⟪a, u⟫ = ∑ᵢ ∫ ∂ᵢ(∂_a φ) ⟪bᵢ, u⟫ = ∫ ⟪u, ∇(∂_a φ)⟫ = 0`; by Weyl's lemma it is harmonic, and
a square integrable harmonic function on the whole space vanishes
(`TauCeti.eq_zero_of_memLp_of_laplacian_eq_smul`). Hence `ℙw = 0`.

## Main declarations

* `TauCeti.mem_orthogonal_solenoidalLp_two_iff`: **the Helmholtz–Weyl decomposition**, the
  orthogonal complement of `L²_σ` is the space of square integrable weak gradients.
* `TauCeti.mem_wassersteinTangentSpace_iff_exists_hasWeakFDerivOn`: the closure in `L²` of the
  test gradients is the space of square integrable weak gradients.
* `TauCeti.lerayProjection_eq_iff_exists_hasWeakFDerivOn`: `ℙu = v` for solenoidal `v` exactly
  when `u - v` is a weak gradient, so `u = ℙu + ∇q` uniquely.
* `TauCeti.orthogonal_solenoidalLp_two_eq_curlFreeLp`: the orthogonal complement of `L²_σ` is the
  space of curl-free fields (`TauCeti.curlFreeLp`).
* `TauCeti.wassersteinTangentSpace_le_comap_d1p0Submodule`: the limits of test gradients lie in
  `D^{1,2}_0(E)`.
* `TauCeti.eq_zero_of_mem_solenoidalLp_of_mem_curlFreeLp`: a square integrable field that is
  divergence free and curl free vanishes.
* `TauCeti.HasWeakFDerivOn.mem_orthogonal_solenoidalLp_two` and
  `TauCeti.HasWeakFDerivOn.lerayProjection_eq_zero`: a square integrable weak gradient is
  orthogonal to `L²_σ` and is annihilated by `ℙ`.

## References

* T. Tao, *254A, Notes 1: Local well-posedness of the Navier–Stokes equations*, 2018,
  Exercise 17.
* G. P. Galdi, *An Introduction to the Mathematical Theory of the Navier–Stokes Equations*,
  2nd ed., Springer, 2011, Section III.1.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace InnerProductSpace LineDeriv
open scoped ENNReal Gradient Distributions RealInnerProductSpace Laplacian

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-! ### Divergence-free and curl-free fields -/

/-- Limits of test gradients are curl free. -/
private theorem wassersteinTangentSpace_le_curlFreeLp :
    wassersteinTangentSpace μ ≤ (curlFreeLp μ).toSubmodule := by
  refine (wassersteinTangentSpace_le_iff (curlFreeLp μ).isClosed).2 fun φ hφ hφc f hf ↦ ?_
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hφc, by simp⟩
  have hq : HasWeakFDerivOn μ ⊤ φ fun x ↦ innerSL ℝ (f x) :=
    (hasWeakFDerivOn_testFunction (μ := μ) ψ).congr_ae_deriv (by
      rw [Opens.coe_top, Measure.restrict_univ]
      exact hf.mono fun x hx ↦ congrArg (innerSL ℝ) hx.symm)
  exact hq.mem_curlFreeLp

/-- **A square integrable field that is divergence free and curl free is weakly harmonic.** Its
pairing with `Δφ = ∑ᵢ ∂ᵢ∂ᵢφ` moves, by the curl-free identities, to a pairing with the gradient of
`∂_a φ`, which vanishes since the field is solenoidal. -/
private theorem weaklyHarmonicOn_of_mem_curlFreeLp {u : Lp E 2 μ}
    (hs : u ∈ solenoidalLp E 2 μ) (hc : u ∈ curlFreeLp μ) : WeaklyHarmonicOn μ ⊤ (u : E → E) := by
  have hu : MemLp (u : E → E) 2 μ := Lp.memLp u
  have hloc : LocallyIntegrableOn (u : E → E) (⊤ : Opens E) μ :=
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  let b := stdOrthonormalBasis ℝ E
  -- The scalar identity `∫ Δφ ⟪a, u⟫ = 0`, for every direction `a`.
  have key (φ : 𝓓((⊤ : Opens E), ℝ)) (a : E) : ∫ x, Δ (φ : E → ℝ) x * ⟪a, u x⟫ ∂μ = 0 := by
    let χ : 𝓓((⊤ : Opens E), ℝ) := ∂_{a} φ
    have hcurl (i) : ∫ x, (∂_{b i} (∂_{b i} φ)) x * ⟪a, u x⟫ ∂μ =
        ∫ x, (∂_{b i} (∂_{a} φ)) x * ⟪b i, u x⟫ ∂μ := by
      rw [TestFunction.lineDerivOp_comm φ (b i) a]
      exact mem_curlFreeLp_iff.1 hc _ a (b i)
    calc ∫ x, Δ (φ : E → ℝ) x * ⟪a, u x⟫ ∂μ
        = ∑ i, ∫ x, (∂_{b i} (∂_{b i} φ)) x * ⟪a, u x⟫ ∂μ := by
          have hΔ (x : E) : Δ (φ : E → ℝ) x = ∑ i, (∂_{b i} (∂_{b i} φ)) x := by
            rw [← TestFunction.laplacianCLM_apply, laplacianCLM_eq_sum b]
            simp
          simp_rw [hΔ, Finset.sum_mul]
          exact integral_finsetSum _ fun i _ ↦
            (∂_{b i} (∂_{b i} φ)).integrable_mul_inner_of_memLp hu a
      _ = ∑ i, ∫ x, (∂_{b i} χ) x * ⟪b i, u x⟫ ∂μ := Finset.sum_congr rfl fun i _ ↦ hcurl i
      _ = ∫ x, ⟪u x, ∇ (χ : E → ℝ) x⟫ ∂μ := by
          rw [← integral_finsetSum _ fun i _ ↦ (∂_{b i} χ).integrable_mul_inner_of_memLp hu (b i)]
          refine integral_congr_ae (.of_forall fun x ↦ ?_)
          simp only [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ,
            TestFunction.lineDerivCLM_apply_eq_inner]
          rw [← b.sum_inner_mul_inner (u x)]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm (u x) (b i), mul_comm]
      _ = 0 := mem_solenoidalLp_iff_integral_inner_eq_zero.1 hs _
  refine weaklyHarmonicOn_iff.2 ⟨hloc, fun φ ↦ ?_⟩
  set I := ∫ x, Δ (φ : E → ℝ) x • u x ∂μ
  refine (inner_self_eq_zero (𝕜 := ℝ)).1 ?_
  rw [← integral_inner (TestFunction.integrable_laplacian_smul φ hloc) I]
  simpa only [real_inner_smul_right] using key φ I

/-- **A square integrable field that is divergence free and curl free vanishes**: it is harmonic
by Weyl's lemma, and a square integrable harmonic function on the whole space is zero. -/
theorem eq_zero_of_mem_solenoidalLp_of_mem_curlFreeLp {u : Lp E 2 μ}
    (hs : u ∈ solenoidalLp E 2 μ) (hc : u ∈ curlFreeLp μ) : u = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Lp.ext (.of_forall fun _ ↦ Subsingleton.elim _ _)
  obtain ⟨h, hh, hae⟩ := (weaklyHarmonicOn_of_mem_curlFreeLp hs hc).exists_harmonicOnNhd_ae_eq
  rw [Opens.coe_top, Measure.restrict_univ] at hae
  have h0 : h = 0 := eq_zero_of_memLp_of_laplacian_eq_smul (μ := μ) (V := 0)
    (contDiff_iff_contDiffAt.2 fun x ↦ (hh x (by simp)).1) ((Lp.memLp u).ae_eq hae)
    (fun _ ↦ le_rfl) fun x ↦ by
      rw [(hh x (by simp)).2.eq_of_nhds, Pi.zero_apply, Pi.zero_apply, zero_smul]
  exact Lp.ext (hae.trans (by rw [h0]; exact (Lp.coeFn_zero E 2 μ).symm))

variable (μ) in
/-- **The orthogonal complement of the solenoidal fields is the space of curl-free fields.** -/
theorem orthogonal_solenoidalLp_two_eq_curlFreeLp :
    (solenoidalLp E 2 μ).toSubmoduleᗮ = (curlFreeLp μ).toSubmodule := by
  refine le_antisymm (orthogonal_solenoidalLp_two μ ▸ wassersteinTangentSpace_le_curlFreeLp)
    fun u hu ↦ ?_
  rw [orthogonal_solenoidalLp_two, ← lerayProjection_eq_zero_iff]
  -- `ℙ u = u - (u - ℙ u)` is solenoidal and, as a difference of curl-free fields, curl free.
  refine eq_zero_of_mem_solenoidalLp_of_mem_curlFreeLp (lerayProjection_apply_mem u) ?_
  simpa only [sub_sub_cancel, ClosedSubmodule.mem_toSubmodule_iff] using
    (curlFreeLp μ).toSubmodule.sub_mem hu
    (wassersteinTangentSpace_le_curlFreeLp (sub_lerayProjection_mem_wassersteinTangentSpace u))

/-! ### Potentials of limits of test gradients -/

variable (μ) in
/-- **Limits of test gradients lie in `D^{1,2}_0(E)`.** Moved to `L²(μ.restrict ⊤; E)`, where the
homogeneous Sobolev space `D^{1,2}_0(E)` lives, the closure in `L²(μ; E)` of the test gradients
lands in `D^{1,2}_0(E)`. -/
theorem wassersteinTangentSpace_le_comap_d1p0Submodule :
    wassersteinTangentSpace μ ≤ (d1p0Submodule μ ⊤ 2).toSubmodule.comap
      (LpToLpRestrictCLM E E ℝ μ 2 ((⊤ : Opens E) : Set E)).toLinearMap := by
  set ρ := LpToLpRestrictCLM E E ℝ μ 2 ((⊤ : Opens E) : Set E)
  refine (wassersteinTangentSpace_le_iff ((d1p0Submodule μ ⊤ 2).isClosed.preimage
    ρ.continuous)).2 fun φ hφ hφc f hf ↦ ?_
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hφc, by simp⟩
  have heq : ρ f = D1p0.ofTestFunctionₗ μ ⊤ 2 ψ := by
    rw [D1p0.coe_ofTestFunctionₗ]
    refine Lp.ext ?_
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ _ f, ae_restrict_of_ae hf,
      gradientTestFunctionLp_apply_ae 2 ψ] with x h₁ h₂ h₃
    simp only [ρ, ψ, h₁, h₂, h₃, TestFunction.coe_mk]
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, heq]
  exact (D1p0.ofTestFunctionₗ μ ⊤ 2 ψ).property

/-- **Limits of test gradients are weak gradients.** Every element of the closure in `L²(μ; E)`
of the test gradients is the weak gradient on the whole space of a function `q : E → ℝ`. -/
private theorem exists_hasWeakFDerivOn_of_mem_wassersteinTangentSpace {w : Lp E 2 μ}
    (hw : w ∈ wassersteinTangentSpace μ) :
    ∃ q : E → ℝ, HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x) := by
  obtain ⟨q, hq⟩ := D1p0.exists_hasWeakFDerivOn
    (⟨_, wassersteinTangentSpace_le_comap_d1p0Submodule μ hw⟩ : D1p0 μ ⊤ 2)
  refine ⟨q, hq.congr_ae_deriv ?_⟩
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ _ w] with x hx
  simp only [ContinuousLinearMap.coe_coe, hx]

/-! ### The Helmholtz–Weyl decomposition -/

/-- **Square integrable weak gradients are orthogonal to the solenoidal fields.** If a locally
integrable `q` has weak gradient `w ∈ L²`, then `w` lies in the orthogonal complement of
`L²_σ`, which is the closure of the test gradients. -/
theorem HasWeakFDerivOn.mem_orthogonal_solenoidalLp_two {q : E → ℝ} {w : Lp E 2 μ}
    (hq : HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x)) :
    w ∈ (solenoidalLp E 2 μ).toSubmoduleᗮ := by
  rw [orthogonal_solenoidalLp_two_eq_curlFreeLp]
  exact hq.mem_curlFreeLp

/-- **The Helmholtz–Weyl decomposition.** The orthogonal complement of the solenoidal fields in
`L²(μ; E)` is the space of square integrable weak gradients: `w ⊥ L²_σ` exactly when `w` is the
weak gradient on the whole space of some locally integrable `q : E → ℝ`. -/
theorem mem_orthogonal_solenoidalLp_two_iff {w : Lp E 2 μ} :
    w ∈ (solenoidalLp E 2 μ).toSubmoduleᗮ ↔
      ∃ q : E → ℝ, HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x) :=
  ⟨fun h ↦ exists_hasWeakFDerivOn_of_mem_wassersteinTangentSpace
      (orthogonal_solenoidalLp_two μ ▸ h),
    fun ⟨_, hq⟩ ↦ hq.mem_orthogonal_solenoidalLp_two⟩

/-- **Limits of test gradients are exactly the square integrable weak gradients.** For an
additive Haar measure, the closure in `L²(μ; E)` of the gradients of smooth compactly supported
functions consists of the weak gradients in `L²` of locally integrable functions. -/
theorem mem_wassersteinTangentSpace_iff_exists_hasWeakFDerivOn {w : Lp E 2 μ} :
    w ∈ wassersteinTangentSpace μ ↔ ∃ q : E → ℝ, HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x) := by
  rw [← orthogonal_solenoidalLp_two, mem_orthogonal_solenoidalLp_two_iff]

/-- **The Helmholtz–Weyl decomposition, existence and uniqueness.** A solenoidal field `v` is the
Leray projection of `u` exactly when `u - v` is the weak gradient of a locally integrable
function: every `u ∈ L²(μ; E)` is uniquely `u = ℙu + ∇q`. -/
theorem lerayProjection_eq_iff_exists_hasWeakFDerivOn {u v : Lp E 2 μ}
    (hv : v ∈ solenoidalLp E 2 μ) :
    lerayProjection μ u = v ↔ ∃ q : E → ℝ, HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ ((u - v) x) := by
  rw [lerayProjection_eq_iff hv, mem_wassersteinTangentSpace_iff_exists_hasWeakFDerivOn]

/-- The Leray projection annihilates a square integrable weak gradient. -/
theorem HasWeakFDerivOn.lerayProjection_eq_zero {q : E → ℝ} {w : Lp E 2 μ}
    (hq : HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x)) : lerayProjection μ w = 0 :=
  lerayProjection_eq_zero_iff.2 (mem_wassersteinTangentSpace_iff_exists_hasWeakFDerivOn.2 ⟨q, hq⟩)

end TauCeti
