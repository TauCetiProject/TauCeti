/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.LerayProjection
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.Sobolev.D1p0.Restriction
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.MeasureTheory.Function.Gluing
import TauCeti.MeasureTheory.Function.Lp.Duality

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

*Limits of test gradients are gradients.* On every ball `ball 0 (k + 1)` a limit `w` of test
gradients is the weak gradient of a Sobolev function, because the gradients of `W^{1,2}` on a
bounded convex set form a closed subspace (`TauCeti.D1p0.exists_w1p_gradient_ae_eq`, from the
Poincaré–Wirtinger inequality). Normalized to have mean zero on the unit ball, two of these
potentials agree on the smaller ball, since their difference has zero gradient on a connected set,
and they glue to a potential on the whole space.

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

open MeasureTheory Metric Set TopologicalSpace InnerProductSpace LineDeriv
open scoped ENNReal Gradient Distributions RealInnerProductSpace Laplacian

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-! ### Curl-free fields -/

/-- The test field `∂_b φ • a - ∂_a φ • b`, whose pairing with a field `u` tests the symmetry
`∂_a u_b = ∂_b u_a` of the derivatives of `u` in distributions. -/
private def curlTestField (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) (x : E) : E :=
  (∂_{b} φ) x • a - (∂_{a} φ) x • b

private theorem memLp_curlTestField (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) :
    MemLp (curlTestField φ a b) 2 μ :=
  (((∂_{b} φ).continuous.smul continuous_const).sub
    ((∂_{a} φ).continuous.smul continuous_const)).memLp_of_hasCompactSupport
    (((∂_{b} φ).hasCompactSupport.smul_right).sub (∂_{a} φ).hasCompactSupport.smul_right)

/-- The pairing of a square integrable field with a curl test field. -/
private theorem integral_inner_curlTestField {u : E → E} (hu : MemLp u 2 μ)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) :
    ∫ x, ⟪curlTestField φ a b x, u x⟫ ∂μ =
      ∫ x, (∂_{b} φ) x * ⟪a, u x⟫ ∂μ - ∫ x, (∂_{a} φ) x * ⟪b, u x⟫ ∂μ := by
  have hint (ψ : 𝓓((⊤ : Opens E), ℝ)) (c : E) : Integrable (fun x ↦ ψ x * ⟪c, u x⟫) μ :=
    (ψ.integrable_smul_of_memLp (hu.const_inner c)).congr (.of_forall fun x ↦ smul_eq_mul _ _)
  rw [← integral_sub (hint _ a) (hint _ b)]
  simp only [curlTestField, inner_sub_left, real_inner_smul_left]

/-- A square integrable weak gradient is curl free: it annihilates every curl test field. -/
private theorem integral_inner_curlTestField_eq_zero {q : E → ℝ} {w : E → E} (hw : MemLp w 2 μ)
    (hq : HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x)) (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) :
    ∫ x, ⟪curlTestField φ a b x, w x⟫ ∂μ = 0 := by
  rw [integral_inner_curlTestField hw, sub_eq_zero]
  have h := (hq.hasWeakLineDerivOn a).integral_inner_lineDeriv_comm (hq.hasWeakLineDerivOn b) φ
  simpa [TestFunction.lineDerivOp_apply, real_inner_comm, mul_comm] using h

variable (μ) in
/-- The closed subspace of `L²(μ; E)` of curl-free fields, those annihilating every curl test
field. -/
private def curlFreeLp : ClosedSubmodule ℝ (Lp E 2 μ) :=
  ⨅ t : 𝓓((⊤ : Opens E), ℝ) × E × E, (⊥ : ClosedSubmodule ℝ ℝ).comap
    (MemLp.innerLpCLM ℝ (memLp_curlTestField (μ := μ) t.1 t.2.1 t.2.2))

private theorem mem_curlFreeLp_iff {u : Lp E 2 μ} :
    u ∈ curlFreeLp μ ↔ ∀ φ a b, ∫ x, ⟪curlTestField φ a b x, u x⟫ ∂μ = 0 := by
  simp only [curlFreeLp, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, MemLp.innerLpCLM_apply, Prod.forall]

variable [FiniteDimensional ℝ E]

/-- Limits of test gradients are curl free. -/
private theorem wassersteinTangentSpace_le_curlFreeLp :
    wassersteinTangentSpace μ ≤ (curlFreeLp μ).toSubmodule := by
  refine (wassersteinTangentSpace_le_iff (curlFreeLp μ).isClosed).2 fun φ hφ hφc f hf ↦ ?_
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hφc, by simp⟩
  have hq : HasWeakFDerivOn μ ⊤ φ fun x ↦ innerSL ℝ (f x) :=
    (hasWeakFDerivOn_testFunction (μ := μ) ψ).congr_ae_deriv (by
      rw [Opens.coe_top, Measure.restrict_univ]
      exact hf.mono fun x hx ↦ congrArg (innerSL ℝ) hx.symm)
  exact mem_curlFreeLp_iff.2 fun φ' a b ↦
    integral_inner_curlTestField_eq_zero (Lp.memLp f) hq φ' a b

/-- **A square integrable field that is divergence free and curl free is weakly harmonic.** Its
pairing with `Δφ = ∑ᵢ ∂ᵢ∂ᵢφ` moves, by the curl-free identities, to a pairing with the gradient of
`∂_a φ`, which vanishes since the field is solenoidal. -/
private theorem weaklyHarmonicOn_of_mem_curlFreeLp {u : Lp E 2 μ}
    (hs : u ∈ solenoidalLp E 2 μ) (hc : u ∈ curlFreeLp μ) : WeaklyHarmonicOn μ ⊤ (u : E → E) := by
  have hu : MemLp (u : E → E) 2 μ := Lp.memLp u
  have hloc : LocallyIntegrableOn (u : E → E) (⊤ : Opens E) μ :=
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hint (ψ : 𝓓((⊤ : Opens E), ℝ)) (c : E) : Integrable (fun x ↦ ψ x * ⟪c, u x⟫) μ :=
    (ψ.integrable_smul_of_memLp (hu.const_inner c)).congr (.of_forall fun x ↦ smul_eq_mul _ _)
  let b := stdOrthonormalBasis ℝ E
  -- The scalar identity `∫ Δφ ⟪a, u⟫ = 0`, for every direction `a`.
  have key (φ : 𝓓((⊤ : Opens E), ℝ)) (a : E) : ∫ x, Δ (φ : E → ℝ) x * ⟪a, u x⟫ ∂μ = 0 := by
    let χ : 𝓓((⊤ : Opens E), ℝ) := ∂_{a} φ
    have hcurl (i) : ∫ x, (∂_{b i} (∂_{b i} φ)) x * ⟪a, u x⟫ ∂μ =
        ∫ x, (∂_{b i} (∂_{a} φ)) x * ⟪b i, u x⟫ ∂μ := by
      rw [TestFunction.lineDerivOp_comm φ (b i) a, ← sub_eq_zero,
        ← integral_inner_curlTestField hu]
      exact mem_curlFreeLp_iff.1 hc _ a (b i)
    calc ∫ x, Δ (φ : E → ℝ) x * ⟪a, u x⟫ ∂μ
        = ∑ i, ∫ x, (∂_{b i} (∂_{b i} φ)) x * ⟪a, u x⟫ ∂μ := by
          have hΔ (x : E) : Δ (φ : E → ℝ) x = ∑ i, (∂_{b i} (∂_{b i} φ)) x := by
            rw [← TestFunction.laplacianCLM_apply, laplacianCLM_eq_sum b]
            simp
          simp_rw [hΔ, Finset.sum_mul]
          exact integral_finsetSum _ fun i _ ↦ hint _ a
      _ = ∑ i, ∫ x, (∂_{b i} χ) x * ⟪b i, u x⟫ ∂μ := Finset.sum_congr rfl fun i _ ↦ hcurl i
      _ = ∫ x, ⟪u x, ∇ (χ : E → ℝ) x⟫ ∂μ := by
          rw [← integral_finsetSum _ fun i _ ↦ hint _ (b i)]
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
private theorem eq_zero_of_mem_curlFreeLp {u : Lp E 2 μ} (hs : u ∈ solenoidalLp E 2 μ)
    (hc : u ∈ curlFreeLp μ) : u = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Lp.ext (.of_forall fun _ ↦ Subsingleton.elim _ _)
  obtain ⟨h, hh, hae⟩ := (weaklyHarmonicOn_of_mem_curlFreeLp hs hc).exists_harmonicOnNhd_ae_eq
  rw [Opens.coe_top, Measure.restrict_univ] at hae
  have h0 : h = 0 := eq_zero_of_memLp_of_laplacian_eq_smul (μ := μ) (V := 0)
    (contDiff_iff_contDiffAt.2 fun x ↦ (hh x (by simp)).1) ((Lp.memLp u).ae_eq hae)
    (fun _ ↦ le_rfl) fun x ↦ by
      rw [(hh x (by simp)).2.eq_of_nhds, Pi.zero_apply, Pi.zero_apply, zero_smul]
  exact Lp.ext (hae.trans (by rw [h0]; exact (Lp.coeFn_zero E 2 μ).symm))

/-! ### Potentials of limits of test gradients -/

/-- On a bounded convex open set, a limit in `L²(μ; E)` of test gradients agrees with the weak
gradient of a Sobolev function. -/
private theorem exists_w1p_gradient_ae_eq_of_mem_wassersteinTangentSpace {U : Opens E}
    (hconv : Convex ℝ (U : Set E)) (hb : Bornology.IsBounded (U : Set E)) {w : Lp E 2 μ}
    (hw : w ∈ wassersteinTangentSpace μ) :
    ∃ v : W1p μ U 2, W1p.gradient v =ᵐ[μ.restrict U] w := by
  -- Transport `w` to `L²(μ.restrict ⊤; E)`, where `D^{1,2}_0(E)` lives.
  have hle : μ.restrict ((⊤ : Opens E) : Set E) ≤ (1 : ℝ≥0∞) • μ := by
    rw [one_smul]
    exact Measure.restrict_le_self
  set ρ : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict ((⊤ : Opens E) : Set E)) :=
    Lp.LpToLpOfMeasureLeSMul (by simp) hle
  have hρ (f : Lp E 2 μ) : ρ f =ᵐ[μ.restrict ((⊤ : Opens E) : Set E)] f :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hle f
  -- It maps the test gradients, hence their closure, into `D^{1,2}_0(E)`.
  have hK : wassersteinTangentSpace μ ≤ (d1p0Submodule μ ⊤ 2).toSubmodule.comap ρ.toLinearMap :=
    (wassersteinTangentSpace_le_iff ((d1p0Submodule μ ⊤ 2).isClosed.preimage ρ.continuous)).2
      fun φ hφ hφc f hf ↦ by
        let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hφc, by simp⟩
        have heq : ρ f = gradientTestFunctionLp 2 ψ := Lp.ext <| by
          filter_upwards [hρ f, ae_restrict_of_ae hf, gradientTestFunctionLp_apply_ae 2 ψ]
            with x h₁ h₂ h₃
          rw [h₁, h₂, h₃]
          rfl
        rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, heq,
          ClosedSubmodule.mem_toSubmodule_iff, ← SetLike.mem_coe, coe_d1p0Submodule]
        exact subset_closure ⟨ψ, rfl⟩
  obtain ⟨v, hv⟩ := D1p0.exists_w1p_gradient_ae_eq le_top hconv hb
    (⟨ρ w, hK hw⟩ : D1p0 μ ⊤ 2)
  exact ⟨v, hv.trans (ae_restrict_of_ae_restrict_of_subset (subset_univ _) (hρ w))⟩

/-- Two Sobolev potentials of the same field, on a preconnected open set `U` and on a larger open
set, differ almost everywhere on `U` by a constant. -/
private theorem exists_value_ae_eq_add_const {U V : Opens E} (hUV : U ≤ V)
    (hU : IsPreconnected (U : Set E)) {w : Lp E 2 μ} {u : W1p μ U 2} {v : W1p μ V 2}
    (hu : W1p.gradient u =ᵐ[μ.restrict U] w) (hv : W1p.gradient v =ᵐ[μ.restrict V] w) :
    ∃ e : ℝ, ∀ᵐ x ∂μ.restrict U, W1p.value v x = W1p.value u x + e := by
  have hd : W1p.gradient (W1p.restrictL hUV v - u) = 0 := Lp.ext <| by
    filter_upwards [W1p.gradient_sub_ae (W1p.restrictL hUV v) u, W1p.gradient_restrictL_ae hUV v,
      hu, ae_restrict_of_ae_restrict_of_subset hUV hv, Lp.coeFn_zero E 2 (μ.restrict U)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.sub_apply, h₂, h₃, h₄, h₅, sub_self, Pi.zero_apply]
  obtain ⟨e, he⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hU hd
  refine ⟨e, ?_⟩
  filter_upwards [he, W1p.value_sub_ae (W1p.restrictL hUV v) u, W1p.value_restrictL_ae hUV v]
    with x h₁ h₂ h₃
  rw [← h₃]
  linarith [h₂ ▸ h₁, Pi.sub_apply (W1p.value (W1p.restrictL hUV v)) (W1p.value u) x]

/-- **Limits of test gradients are weak gradients.** Every element of the closure in `L²(μ; E)`
of the test gradients is the weak gradient on the whole space of a locally integrable function.
The potentials on the balls `ball 0 (k + 1)`, normalized to have mean zero on the unit ball, agree
on overlaps, since the space is connected, and glue. -/
private theorem exists_hasWeakFDerivOn_of_mem_wassersteinTangentSpace {w : Lp E 2 μ}
    (hw : w ∈ wassersteinTangentSpace μ) :
    ∃ q : E → ℝ, HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x) := by
  let B : ℕ → Opens E := fun k ↦ ⟨ball 0 (k + 1), isOpen_ball⟩
  have hBmono {k m : ℕ} (hkm : k ≤ m) : B k ≤ B m :=
    ball_subset_ball (by simp only [add_le_add_iff_right, Nat.cast_le, hkm])
  have hfin (k) : IsFiniteMeasure (μ.restrict (B k : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hB0 (k) : ball (0 : E) 1 ⊆ B k := fun x hx ↦ hBmono (Nat.zero_le k) (by simpa [B] using hx)
  choose v hv using fun k ↦ exists_w1p_gradient_ae_eq_of_mem_wassersteinTangentSpace
    (U := B k) (convex_ball _ _) isBounded_ball hw
  let c : ℕ → ℝ := fun k ↦ ⨍ x in ball (0 : E) 1, W1p.value (v k) x ∂μ
  let a : ℕ → E → ℝ := fun k x ↦ W1p.value (v k) x - c k
  -- Each normalized potential has weak gradient `w` on its ball.
  have ha (k) : HasWeakFDerivOn μ (B k) (a k) fun x ↦ innerSL ℝ (w x) := by
    have hconst : HasWeakFDerivOn μ (B k) (fun _ ↦ c k) fun _ ↦ 0 :=
      hasWeakFDerivOn_iff.2 fun e ↦ by
        simpa only [zero_apply] using hasWeakLineDerivOn_const (μ := μ) (Ω := B k) (v := e) (c k)
    refine ((W1p.hasWeakFDerivOn (v k)).sub hconst).congr_ae_deriv ?_
    filter_upwards [hv k] with x hx
    simp only [Pi.sub_apply, sub_zero, hx]
  -- Two potentials differ by a constant on the smaller ball, so their normalizations agree.
  have hle {k m : ℕ} (hkm : k ≤ m) : a m =ᵐ[μ.restrict (B k)] a k := by
    obtain ⟨e, hdiff⟩ := exists_value_ae_eq_add_const (hBmono hkm)
      (convex_ball (0 : E) _).isPreconnected (hv k) (hv m)
    have hint : IntegrableOn (W1p.value (v k)) (ball (0 : E) 1) μ :=
      IntegrableOn.mono_set ((Lp.memLp (W1p.value (v k))).integrable one_le_two) (hB0 k)
    have hc : c m = c k + e := by
      have h₁ := setAverage_congr_fun (μ := μ) measurableSet_ball ((ae_restrict_iff'
        measurableSet_ball).1 (ae_restrict_of_ae_restrict_of_subset (hB0 k) hdiff))
      have h₂ := setAverage_add hint (integrableOn_const (C := e) measure_ball_lt_top.ne)
      rw [setAverage_const (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne] at h₂
      exact h₁.trans h₂
    filter_upwards [hdiff] with x hx
    simp only [a, hx, hc]
    ring
  have hcompat (k m : ℕ) : a k =ᵐ[μ.restrict ((B k : Set E) ∩ B m)] a m := by
    rcases le_total k m with hkm | hmk
    · rw [inter_eq_left.2 (hBmono hkm)]
      exact (hle hkm).symm
    · rw [inter_eq_right.2 (hBmono hmk)]
      exact hle hmk
  obtain ⟨q, hq⟩ := exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter
    (fun k ↦ (B k).isOpen.measurableSet) hcompat
  have hsup : (⨆ k, B k) = ⊤ := eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2
    ⟨⌈‖x‖⌉₊, by simpa [B] using (Nat.le_ceil ‖x‖).trans_lt (lt_add_one _)⟩
  refine ⟨q, ?_⟩
  rw [← hsup, hasWeakFDerivOn_iSup_iff]
  exact fun k ↦ (ha k).congr_ae (hq k).symm

/-! ### The Helmholtz–Weyl decomposition -/

/-- **Square integrable weak gradients are orthogonal to the solenoidal fields.** If a locally
integrable `q` has weak gradient `w ∈ L²`, then `w` lies in the orthogonal complement of
`L²_σ`, which is the closure of the test gradients. -/
theorem HasWeakFDerivOn.mem_orthogonal_solenoidalLp_two {q : E → ℝ} {w : Lp E 2 μ}
    (hq : HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x)) :
    w ∈ (solenoidalLp E 2 μ).toSubmoduleᗮ := by
  rw [orthogonal_solenoidalLp_two, ← lerayProjection_eq_zero_iff]
  -- `ℙ w = w - (w - ℙ w)` is solenoidal and, as a difference of curl-free fields, curl free.
  refine eq_zero_of_mem_curlFreeLp (lerayProjection_apply_mem w) ?_
  have hw : w ∈ curlFreeLp μ := mem_curlFreeLp_iff.2 fun φ a b ↦
    integral_inner_curlTestField_eq_zero (Lp.memLp w) hq φ a b
  simpa only [sub_sub_cancel, ClosedSubmodule.mem_toSubmodule_iff] using
    (curlFreeLp μ).toSubmodule.sub_mem hw
    (wassersteinTangentSpace_le_curlFreeLp (sub_lerayProjection_mem_wassersteinTangentSpace w))

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
