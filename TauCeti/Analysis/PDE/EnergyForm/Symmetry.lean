/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Antisymmetric
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.MeasureTheory.Function.Holder

/-!
# Symmetry of the energy form

Let `Ω ⊆ ℝⁿ` be open and let `a(u, v) = ∫_Ω ⟨a ∇u, ∇v⟩ + ⟪b, ∇u⟫ v + c u v` be the energy form of a
bounded coefficient triple `(a, b, c)` on `H¹(Ω)` (`TauCeti.PDE.energyFormH1`). When `a` is almost
everywhere symmetric and `b = 0`, the form is symmetric
(`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`). This file treats the converse.

For an almost everywhere symmetric `a`, the form is symmetric exactly when `b = 0` almost everywhere
on `Ω` (`TauCeti.PDE.forall_energyFormH1_comm_iff`), and symmetry on test functions already forces
`b = 0` (`TauCeti.PDE.ae_eq_zero_of_forall_energyFormH1_ofTestFunctionₗ_comm`). Indeed the
antisymmetric part of the form is `a(u, v) - a(v, u) = ∫_Ω ⟪b, ∇u⟫ v - ⟪b, ∇v⟫ u`. For a test
function `φ`, a cutoff `ψ` equal to `1` near the support of `φ` and a coordinate `x_k`, the pairs
`(x_k ψ, φ)` and `(x_k φ, ψ)` give `∫_Ω b_k φ - x_k ⟪b, ∇φ⟫` and `∫_Ω b_k φ + x_k ⟪b, ∇φ⟫`, so
symmetry gives `∫_Ω b_k φ = 0` for every `φ`, and `b_k = 0` almost everywhere on `Ω` by the
fundamental lemma of the calculus of variations.

Without the symmetry of `a` the converse fails, in every dimension `n ≥ 2` and on every nonempty
open set (`TauCeti.PDE.exists_forall_energyFormH1_comm_and_not_ae_isSymm`): a symmetric energy form
need not have a symmetric principal coefficient. If `K` is a smooth antisymmetric matrix field with
compact support inside `Ω` and `g` is its row divergence, then adding `K` to the principal
coefficient has the same effect on the form on `H¹(Ω) × H¹(Ω)` as adding `g` to the drift
(`TauCeti.PDE.energyFormH1_add_eq_of_transpose_eq_neg_of_hasCompactSupport`). So the coefficients
`a = 1 + K` and `b = -g` give the energy form of the Laplacian, which is symmetric, while `a` is not
symmetric wherever `K ≠ 0`. For `K = φ (E_ij - E_ji)`, with `φ` a bump function and `E_ij` the
matrix units, `a` is moreover uniformly elliptic, with `ξ · a ξ = ‖ξ‖²`. So the energy form does
not determine the antisymmetric part of its principal coefficient.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `ae_eq_zero_of_forall_energyFormH1_ofTestFunctionₗ_comm`: for an almost everywhere symmetric
  principal coefficient, symmetry of the energy form on test functions forces the drift to vanish
  almost everywhere on `Ω`.
* `forall_energyFormH1_comm_iff`: for an almost everywhere symmetric principal coefficient, the
  energy form on `H¹(Ω)` is symmetric exactly when the drift vanishes almost everywhere on `Ω`.
* `exists_forall_energyFormH1_comm_and_not_ae_isSymm`: on every nonempty open subset of `ℝⁿ`,
  `n ≥ 2`, a bounded uniformly elliptic coefficient field whose principal coefficient is not almost
  everywhere symmetric has a symmetric energy form.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.1 (the weak formulation of divergence-form operators).
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction Filter
open scoped ContDiff Distributions InnerProductSpace Gradient Matrix Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {Ω : Opens (EuclideanSpace ℝ ι)}
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-! ### Symmetric principal coefficients -/

omit [Fintype ι] in
/-- For a symmetric principal coefficient, the antisymmetric part of the jet form comes from the
drift alone. -/
private theorem energyIntegrand_sub_energyIntegrand_swap [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) (β : EuclideanSpace ℝ ι) (γ : ℝ) (U V : ℝ × EuclideanSpace ℝ ι) :
    energyIntegrand A β γ U V - energyIntegrand A β γ V U =
      ⟪β, U.2⟫_ℝ * V.1 - ⟪β, V.2⟫_ℝ * U.1 := by
  rw [energyIntegrand_apply, energyIntegrand_apply, ← matrixBilinearForm_transpose_apply A U.2,
    hA.eq, driftForm_apply, driftForm_apply, massForm_apply, massForm_apply]
  ring

/-- For an almost everywhere symmetric principal coefficient, the antisymmetric part
`a(u, v) - a(v, u)` of the energy form is the integral of `⟪b, ∇u⟫ v - ⟪b, ∇v⟫ u`, which is
integrable. -/
private theorem energyFormH1_sub_energyFormH1_swap
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    (ha : ∀ᵐ x ∂mu.restrict Ω, (a x).IsSymm) (u v : W1p mu Ω 2) :
    Integrable (fun x ↦ ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x -
        ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value u x) (mu.restrict Ω) ∧
      energyFormH1 a b c u v - energyFormH1 a b c v u =
        ∫ x in Ω, (⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x -
          ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value u x) ∂mu := by
  have huv := integrable_energyIntegrand_jetField hcoeff u v
  have hvu := integrable_energyIntegrand_jetField hcoeff v u
  have hpt : (fun x ↦ energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x) -
      energyIntegrand (a x) (b x) (c x) (jetField v x) (jetField u x)) =ᵐ[mu.restrict Ω]
      fun x ↦ ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x -
        ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value u x := by
    filter_upwards [ha] with x hx
    rw [energyIntegrand_sub_energyIntegrand_swap hx, jetField_apply, jetField_apply]
  refine ⟨(huv.sub hvu).congr hpt, ?_⟩
  rw [energyFormH1_def, energyFormH1_def, ← integral_sub huv hvu]
  exact integral_congr_ae hpt

omit [mu.IsAddHaarMeasure] in
/-- The coordinates of an essentially bounded drift are essentially bounded. -/
private theorem memLp_drift_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω)) (k : ι) :
    MemLp (fun x ↦ b x k) ⊤ (mu.restrict Ω) := by
  classical
  -- The drift coordinate `b_k` is the jet form evaluated at `((0, e_k), (1, 0))`.
  set U : ℝ × EuclideanSpace ℝ ι := (0, EuclideanSpace.single k 1)
  set V : ℝ × EuclideanSpace ℝ ι := (1, 0)
  have h₁ : eLpNorm (fun x ↦ energyIntegrand (a x) (b x) (c x) U) ⊤ (mu.restrict Ω) ≤
      ‖U‖₊ * eLpNorm (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω) :=
    eLpNorm_clm_apply_const_le U
  have h₂ : eLpNorm (fun x ↦ energyIntegrand (a x) (b x) (c x) U V) ⊤ (mu.restrict Ω) ≤
      ‖V‖₊ * eLpNorm (fun x ↦ energyIntegrand (a x) (b x) (c x) U) ⊤ (mu.restrict Ω) :=
    eLpNorm_clm_apply_const_le V
  have hUV : (fun x ↦ energyIntegrand (a x) (b x) (c x) U V) = fun x ↦ b x k := by
    funext x
    simp [U, V, energyIntegrand_apply, EuclideanSpace.inner_single_right]
  rw [← hUV]
  exact memLp_iff.2 (h₂.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (h₁.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hcoeff))))

/-- For an almost everywhere symmetric principal coefficient, if `a(f, f') = a(f', f)` for two test
functions `f, f'`, then `∂_b f · f' - ∂_b f' · f` is integrable on `Ω` with integral zero, where
`∂_b` is the derivative in the direction of the drift. -/
private theorem integrable_and_setIntegral_eq_zero_of_energyFormH1_comm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    (ha : ∀ᵐ x ∂mu.restrict Ω, (a x).IsSymm) {f f' : 𝓓(Ω, ℝ)}
    (hff' : energyFormH1 a b c (W1p.ofTestFunctionₗ mu Ω 2 f) (W1p.ofTestFunctionₗ mu Ω 2 f') =
      energyFormH1 a b c (W1p.ofTestFunctionₗ mu Ω 2 f') (W1p.ofTestFunctionₗ mu Ω 2 f)) :
    Integrable (fun x ↦ fderiv ℝ f x (b x) * f' x - fderiv ℝ f' x (b x) * f x) (mu.restrict Ω) ∧
      ∫ x in Ω, (fderiv ℝ f x (b x) * f' x - fderiv ℝ f' x (b x) * f x) ∂mu = 0 := by
  obtain ⟨hint, heq⟩ := energyFormH1_sub_energyFormH1_swap hcoeff ha
    (W1p.ofTestFunctionₗ mu Ω 2 f) (W1p.ofTestFunctionₗ mu Ω 2 f')
  have hd : ∀ (h : 𝓓(Ω, ℝ)) (x : EuclideanSpace ℝ ι),
      ⟪b x, ∇ (h : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ = fderiv ℝ h x (b x) := fun h x ↦ by
    rw [real_inner_comm, inner_gradient_left]
  have hpt : (fun x ↦ ⟪b x, W1p.gradient (W1p.ofTestFunctionₗ mu Ω 2 f) x⟫_ℝ *
        W1p.value (W1p.ofTestFunctionₗ mu Ω 2 f') x -
      ⟪b x, W1p.gradient (W1p.ofTestFunctionₗ mu Ω 2 f') x⟫_ℝ *
        W1p.value (W1p.ofTestFunctionₗ mu Ω 2 f) x) =ᵐ[mu.restrict Ω]
      fun x ↦ fderiv ℝ f x (b x) * f' x - fderiv ℝ f' x (b x) * f x := by
    filter_upwards [jetField_ofTestFunctionₗ_ae (mu := mu) (p := 2) f,
      jetField_ofTestFunctionₗ_ae (mu := mu) (p := 2) f'] with x hx hx'
    simp only [jetField_apply, Prod.mk.injEq] at hx hx'
    rw [hx.1, hx.2, hx'.1, hx'.2, hd, hd]
  rw [hff', sub_self, integral_congr_ae hpt] at heq
  exact ⟨hint.congr hpt, heq.symm⟩

/-- The pointwise identities behind the vanishing of the drift. Let `ψ` be equal to `1` near the
support of `φ`, and let `Φ = x_k ψ` and `Φ' = x_k φ`. For every direction `v`, writing `∂_v` for the
derivative in the direction `v`, `∂_v Φ · φ - ∂_v φ · Φ = φ v_k - x_k ∂_v φ` and
`∂_v Φ' · ψ - ∂_v ψ · Φ' = φ v_k + x_k ∂_v φ`. -/
private theorem fderiv_mul_sub_fderiv_mul_of_coord {φ ψ Φ Φ' : 𝓓(Ω, ℝ)} {k : ι}
    (hψ : ∀ x ∈ tsupport φ, ∀ᶠ y in 𝓝 x, ψ y = 1) (hΦ : ⇑Φ = fun x ↦ x k • ψ x)
    (hΦ' : ⇑Φ' = fun x ↦ x k • φ x) (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ Φ x v * φ x - fderiv ℝ φ x v * Φ x = φ x * v k - x k * fderiv ℝ φ x v ∧
      fderiv ℝ Φ' x v * ψ x - fderiv ℝ ψ x v * Φ' x = φ x * v k + x k * fderiv ℝ φ x v := by
  have hfd0 : ∀ {f : EuclideanSpace ℝ ι → ℝ} {r : ℝ}, f =ᶠ[𝓝 x] (fun _ ↦ r) → fderiv ℝ f x = 0 :=
    fun h ↦ by rw [h.fderiv_eq, fderiv_const_apply]
  have hcoord : HasFDerivAt (fun y : EuclideanSpace ℝ ι ↦ y k) (EuclideanSpace.proj (𝕜 := ℝ) k)
      x := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt
  by_cases hx : x ∈ tsupport φ
  · have hΦx : (Φ : EuclideanSpace ℝ ι → ℝ) =ᶠ[𝓝 x] fun y ↦ y k :=
      Eventually.mono (hψ x hx) fun y hy ↦ by simp [hΦ, hy]
    have hψx : (ψ : EuclideanSpace ℝ ι → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := hψ x hx
    have hΦ'f : (Φ' : EuclideanSpace ℝ ι → ℝ) = fun y ↦ y k * φ y := by simp [hΦ']
    rw [hΦx.fderiv_eq, hΦx.eq_of_nhds, hfd0 hψx, hψx.eq_of_nhds, hΦ'f,
      fderiv_fun_mul hcoord.differentiableAt (φ.contDiff.differentiable (by simp) x),
      hcoord.fderiv]
    constructor
    · simp only [PiLp.proj_apply]
      ring
    · simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, PiLp.proj_apply]
      ring
  · have h0 : (φ : EuclideanSpace ℝ ι → ℝ) =ᶠ[𝓝 x] fun _ ↦ 0 :=
      notMem_tsupport_iff_eventuallyEq.1 hx
    have h0' : (Φ' : EuclideanSpace ℝ ι → ℝ) =ᶠ[𝓝 x] fun _ ↦ 0 := h0.mono fun y hy ↦ by
      simp [hΦ', hy]
    simp [hfd0 h0, h0.eq_of_nhds, hfd0 h0', h0'.eq_of_nhds]

/-- For an almost everywhere symmetric principal coefficient, symmetry of the energy form on test
functions makes every coordinate of the drift orthogonal to every test function on `Ω`. -/
private theorem setIntegral_mul_drift_apply_eq_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    (ha : ∀ᵐ x ∂mu.restrict Ω, (a x).IsSymm)
    (hB : ∀ φ ψ : 𝓓(Ω, ℝ), energyFormH1 a b c (W1p.ofTestFunctionₗ mu Ω 2 φ)
      (W1p.ofTestFunctionₗ mu Ω 2 ψ) = energyFormH1 a b c (W1p.ofTestFunctionₗ mu Ω 2 ψ)
        (W1p.ofTestFunctionₗ mu Ω 2 φ))
    (φ : 𝓓(Ω, ℝ)) (k : ι) : ∫ x in Ω, φ x * b x k ∂mu = 0 := by
  -- A test function `ψ` equal to `1` near the support of `φ`, and the products `x_k ψ`, `x_k φ`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχΩ⟩ :=
    φ.hasCompactSupport.isCompact.exists_contDiff_cutoff_eventuallyEq_one Ω.isOpen
      φ.tsupport_subset
  let ψ : 𝓓(Ω, ℝ) := ⟨χ, hχ, hχc, hχΩ⟩
  have hcoord : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ ι ↦ x k) Ω :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffOn
  obtain ⟨Φ, hΦ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hcoord ψ
  obtain ⟨Φ', hΦ'⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hcoord φ
  have hid := fun x ↦ fderiv_mul_sub_fderiv_mul_of_coord (ψ := ψ) hχ1 hΦ hΦ' x (b x)
  -- The antisymmetric parts `a(x_k ψ, φ) - a(φ, x_k ψ)` and `a(x_k φ, ψ) - a(ψ, x_k φ)` vanish.
  obtain ⟨hi₁, he₁⟩ := integrable_and_setIntegral_eq_zero_of_energyFormH1_comm hcoeff ha (hB Φ φ)
  obtain ⟨hi₂, he₂⟩ := integrable_and_setIntegral_eq_zero_of_energyFormH1_comm hcoeff ha (hB Φ' ψ)
  simp only [fun x ↦ (hid x).1, fun x ↦ (hid x).2] at hi₁ he₁ hi₂ he₂
  -- Their sum is `2 ∫_Ω φ b_k`.
  have hsum : ∫ x in Ω, φ x * b x k ∂mu = (∫ x in Ω, (φ x * b x k - x k * fderiv ℝ φ x (b x)) ∂mu +
      ∫ x in Ω, (φ x * b x k + x k * fderiv ℝ φ x (b x)) ∂mu) / 2 := by
    rw [← integral_add hi₁ hi₂, ← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [hsum, he₁, he₂]
  simp

/-- **A symmetric energy form with a symmetric principal coefficient has no drift.** For a bounded
coefficient triple `(a, b, c)` with `a` almost everywhere symmetric, if `a(φ, ψ) = a(ψ, φ)` for all
test functions `φ, ψ` on `Ω`, then `b = 0` almost everywhere on `Ω`. -/
theorem ae_eq_zero_of_forall_energyFormH1_ofTestFunctionₗ_comm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    (ha : ∀ᵐ x ∂mu.restrict Ω, (a x).IsSymm)
    (hB : ∀ φ ψ : 𝓓(Ω, ℝ), energyFormH1 a b c (W1p.ofTestFunctionₗ mu Ω 2 φ)
      (W1p.ofTestFunctionₗ mu Ω 2 ψ) = energyFormH1 a b c (W1p.ofTestFunctionₗ mu Ω 2 ψ)
        (W1p.ofTestFunctionₗ mu Ω 2 φ)) :
    b =ᵐ[mu.restrict Ω] 0 := by
  have hk : ∀ k, ∀ᵐ x ∂mu.restrict Ω, b x k = 0 := fun k ↦ by
    have hloc : LocallyIntegrableOn (fun x ↦ b x k) Ω mu :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((memLp_drift_apply hcoeff k).locallyIntegrable le_top)
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun f hf hfc hfΩ ↦ ?_)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfΩ h), zero_smul]]
    exact setIntegral_mul_drift_apply_eq_zero hcoeff ha hB ⟨f, hf, hfc, hfΩ⟩ k
  filter_upwards [ae_all_iff.2 hk] with x hx
  ext k
  simpa using hx k

/-- **Symmetry of the energy form, for a symmetric principal coefficient.** For a bounded
coefficient triple `(a, b, c)` with `a` almost everywhere symmetric, the energy form on `H¹(Ω)` is
symmetric exactly when `b = 0` almost everywhere on `Ω`. -/
theorem forall_energyFormH1_comm_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    (ha : ∀ᵐ x ∂mu.restrict Ω, (a x).IsSymm) :
    (∀ u v : W1p mu Ω 2, energyFormH1 a b c u v = energyFormH1 a b c v u) ↔
      b =ᵐ[mu.restrict Ω] 0 := by
  refine ⟨fun h ↦ ae_eq_zero_of_forall_energyFormH1_ofTestFunctionₗ_comm hcoeff ha
    fun _ _ ↦ h _ _, fun hb u v ↦ ?_⟩
  rw [energyFormH1_congr_ae .rfl hb .rfl u v, energyFormH1_congr_ae .rfl hb .rfl v u]
  exact energyFormH1_comm_of_isSymm_ae ha u v

/-! ### Symmetric forms with non-symmetric principal coefficients -/

section Skew

variable [DecidableEq ι] {i j : ι}

omit [Fintype ι] in
/-- Adding a multiple of `E_ij - E_ji` to the identity does not change the quadratic form. -/
private theorem dotProduct_one_add_smul_skew_mulVec [Fintype ι] (t : ℝ) (ξ : ι → ℝ) :
    ξ ⬝ᵥ ((1 + t • (Matrix.single i j 1 - Matrix.single j i 1)) *ᵥ ξ) = ξ ⬝ᵥ ξ := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, Matrix.single_mulVec, one_mul]
  simp [dotProduct, Function.update_apply, mul_comm]

omit [Fintype ι] in
/-- The matrix `1 + t (E_ij - E_ji)`, for `i ≠ j`, is symmetric only for `t = 0`. -/
private theorem eq_zero_of_isSymm_one_add_smul_skew (hij : i ≠ j) {t : ℝ}
    (h : (1 + t • (Matrix.single i j (1 : ℝ) - Matrix.single j i 1)).IsSymm) : t = 0 := by
  have h' := h.apply i j
  simp [hij, Ne.symm hij] at h'
  linarith

/-- The row divergence of `φ (E_ij - E_ji)` is `∂_j φ e_i - ∂_i φ e_j`. -/
private theorem rowDivergence_smul_skew {φ : EuclideanSpace ℝ ι → ℝ} (hij : i ≠ j)
    {x : EuclideanSpace ℝ ι} (hφ : DifferentiableAt ℝ φ x) (i' : ι) :
    (fderiv ℝ φ x (EuclideanSpace.single j 1) • EuclideanSpace.single i (1 : ℝ) -
        fderiv ℝ φ x (EuclideanSpace.single i 1) • EuclideanSpace.single j (1 : ℝ)) i' =
      ∑ j', fderiv ℝ (fun y ↦ (φ y • (Matrix.single i j 1 - Matrix.single j i 1) : Matrix ι ι ℝ)
        i' j') x (EuclideanSpace.single j' 1) := by
  have hKij : ∀ j', fderiv ℝ (fun y ↦ (φ y • (Matrix.single i j 1 - Matrix.single j i 1) :
      Matrix ι ι ℝ) i' j') x =
      (Matrix.single i j 1 - Matrix.single j i 1 : Matrix ι ι ℝ) i' j' • fderiv ℝ φ x :=
    fun j' ↦ by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact fderiv_mul_const hφ _
  simp only [hKij, smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.single_apply]
  by_cases hi : i' = i
  · subst hi
    simp [Ne.symm hij, eq_comm]
  · by_cases hj : i' = j
    · subst hj
      simp [hij, eq_comm]
    · simp [hi, hj, Ne.symm hi, Ne.symm hj]

omit [mu.IsAddHaarMeasure] in
/-- A continuous bounded principal coefficient and the drift `-(∂_j φ e_i - ∂_i φ e_j)` of a smooth
compactly supported `φ` have an essentially bounded field of energy forms. -/
private theorem memLp_energyIntegrand_neg_rowDivergence {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {A : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hA : Continuous A) {Λ : ℝ} (hAΛ : ∀ x, ‖matrixBilinearForm (A x)‖ ≤ Λ) :
    MemLp (fun x ↦ energyIntegrand (A x)
      (-(fderiv ℝ φ x (EuclideanSpace.single j 1) • EuclideanSpace.single i (1 : ℝ) -
        fderiv ℝ φ x (EuclideanSpace.single i 1) • EuclideanSpace.single j (1 : ℝ)))
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Ω) := by
  obtain ⟨D, hD⟩ := (hφ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hφc.fderiv ℝ).norm
  have hφ' := hφ.continuous_fderiv (by simp)
  refine memLp_energyIntegrand_of_continuousOn_of_norm_le hA.continuousOn
    (((hφ'.clm_apply continuous_const).smul continuous_const).sub
      ((hφ'.clm_apply continuous_const).smul continuous_const)).neg.continuousOn
    continuousOn_const (fun x _ ↦ hAΛ x) (beta := D + D) (fun x _ ↦ ?_) (gamma := 0)
    (fun _ _ ↦ by simp)
  rw [norm_neg]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;>
  · rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    exact ((fderiv ℝ φ x).le_opNorm _).trans (by simpa [PiLp.norm_single] using hD ⟨x, rfl⟩)

end Skew

/-- **A symmetric energy form need not have a symmetric principal coefficient.** On every nonempty
open subset `Ω` of `ℝⁿ`, `n ≥ 2`, there is a bounded coefficient field `(a, b)`, with
`ξ · a(x) ξ = ‖ξ‖²` for all `x` and `ξ`, whose energy form `a(u, v)` on `H¹(Ω)` is symmetric
although `a` is not almost everywhere symmetric on `Ω`. With `φ` a bump function supported in `Ω`
and `E_ij` the matrix units, `a = 1 + φ (E_ij - E_ji)` and `b` is minus the row divergence of
`φ (E_ij - E_ji)`, and the energy form is that of the Laplacian. -/
theorem exists_forall_energyFormH1_comm_and_not_ae_isSymm {i j : ι} (hij : i ≠ j)
    (hΩ : (Ω : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι),
      MemLp (fun x ↦ energyIntegrand (a x) (b x) 0) ⊤ (mu.restrict Ω) ∧
        (∀ x (ξ : ι → ℝ), ξ ⬝ᵥ (a x *ᵥ ξ) = ξ ⬝ᵥ ξ) ∧ ¬ (∀ᵐ x ∂mu.restrict Ω, (a x).IsSymm) ∧
          ∀ u v : W1p mu Ω 2, energyFormH1 a b 0 u v = energyFormH1 a b 0 v u := by
  classical
  obtain ⟨x₀, hx₀⟩ := hΩ
  obtain ⟨φ, hφΩ, hφc, hφ, hφ01, hφx₀⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Ω.isOpen.mem_nhds hx₀)
  -- The antisymmetric field `K = φ S`, `S = E_ij - E_ji`, and its row divergence `g`.
  set S : Matrix ι ι ℝ := Matrix.single i j 1 - Matrix.single j i 1
  set K : EuclideanSpace ℝ ι → Matrix ι ι ℝ := fun x ↦ φ x • S with hKdef
  set g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x ↦
    fderiv ℝ φ x (EuclideanSpace.single j 1) • EuclideanSpace.single i 1 -
      fderiv ℝ φ x (EuclideanSpace.single i 1) • EuclideanSpace.single j 1
  have hK : ∀ i' j', ContDiffOn ℝ ∞ (fun x ↦ K x i' j') Ω := fun i' j' ↦ by
    simpa [K, Matrix.smul_apply] using (hφ.mul (contDiff_const (c := S i' j'))).contDiffOn
  have hab : ∀ x, ‖matrixBilinearForm ((1 + K) x)‖ ≤
      ∑ i', ∑ j', (|(1 : Matrix ι ι ℝ) i' j'| + |S i' j'|) := fun x ↦ by
    refine (norm_matrixBilinearForm_le_sum_abs _).trans (Finset.sum_le_sum fun i' _ ↦
      Finset.sum_le_sum fun j' _ ↦ (abs_add_le _ _).trans (add_le_add le_rfl ?_))
    simp only [hKdef, Matrix.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨by linarith
      [(hφ01 (mem_range_self x)).1], (hφ01 (mem_range_self x)).2⟩)
  refine ⟨1 + K, -g, memLp_energyIntegrand_neg_rowDivergence (i := i) (j := j) hφ hφc
    (continuous_const.add (hφ.continuous.smul continuous_const)) hab,
    fun x ξ ↦ dotProduct_one_add_smul_skew_mulVec _ ξ, fun hsymm ↦ ?_, fun u v ↦ ?_⟩
  · -- `a` is not symmetric where `φ ≠ 0`, an open set containing `x₀`.
    have hU : IsOpen ({x | φ x ≠ 0} ∩ Ω) :=
      (isOpen_ne_fun hφ.continuous continuous_const).inter Ω.isOpen
    have hpos : 0 < mu.restrict Ω ({x | φ x ≠ 0} ∩ Ω) := by
      rw [Measure.restrict_apply hU.measurableSet, inter_assoc, inter_self]
      exact hU.measure_pos mu ⟨x₀, by simp [hφx₀], hx₀⟩
    refine hpos.ne' (measure_mono_null (fun x hx ↦ ?_) (ae_iff.1 hsymm))
    rw [mem_ofPred_eq]
    exact fun hxs ↦ hx.1 (eq_zero_of_isSymm_one_add_smul_skew hij hxs)
  · -- Moving `K` into the drift leaves the energy form of the Laplacian.
    have key : ∀ w w' : W1p mu Ω 2,
        energyFormH1 (1 + K) (-g) 0 w w' = energyFormH1 1 0 0 w w' := fun w w' ↦ by
      have h := energyFormH1_add_eq_of_transpose_eq_neg_of_hasCompactSupport (a := 1) (b := -g)
        (c := 0) (memLp_energyIntegrand_neg_rowDivergence (i := i) (j := j) hφ hφc continuous_const
          (fun _ ↦ norm_matrixBilinearForm_le_sum_abs (1 : Matrix ι ι ℝ))) hK
        (fun x _ ↦ by simp [K, S, Matrix.transpose_single, smul_sub])
        (fun x _ i' ↦ rowDivergence_smul_skew hij (hφ.differentiable (by simp) x) i')
        hφc.smul_right ((tsupport_smul_subset_left _ _).trans hφΩ) w w'
      rwa [neg_add_cancel] at h
    rw [key, key]
    exact energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) u v

end PDE

end TauCeti
