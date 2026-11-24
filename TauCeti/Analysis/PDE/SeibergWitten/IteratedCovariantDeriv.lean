/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Iterated covariant derivatives of a section of the trivial line

Let `(a, α)` be an abelian Higgs pair on a real normed space `E`: an imaginary connection form
`a = i b` on the trivial Hermitian line, with `b` a real one-form, and a section `α : E → ℂ`, with
covariant derivative `∇_a α = dα + i b α` (`TauCeti.SeibergWitten.covariantDeriv`). The same
formula `∇_a T = dT + i b ⊗ T` differentiates sections `T` with values in complex multilinear
maps, and iterating it gives the **iterated covariant derivatives**

`∇⁰ α = α`,  `∇ⁿ⁺¹ α (v₀, v₁, …, vₙ) = (∇_{v₀} ∇ⁿ α)(v₁, …, vₙ)`

(`TauCeti.SeibergWitten.iteratedCovariantDeriv b α n`), with values in the real multilinear maps
`E [×n]→L[ℝ] ℂ`, in the convention of Mathlib's `iteratedFDeriv`
(`iteratedCovariantDeriv_succ_apply`). The first one is the covariant derivative
(`iteratedCovariantDeriv_one_apply`).

They are the gauge covariant counterparts of the iterated derivatives: a gauge transformation
`(b, α) ↦ (b - Im (u⁻¹ du), u α)` by a smooth circle-valued `u` multiplies all of them by `u`
(`iteratedCovariantDeriv_sub_phaseForm_mul`), so their norms are gauge invariant. Estimates on
solutions of gauge-invariant equations, such as Taubes's derivative bounds for Seiberg–Witten
solutions at large parameter, are stated for them.

Conversely, the iterated derivatives of `α` are controlled by its iterated covariant derivatives
and the derivatives of the connection form: if `|∇ʲ α| ≤ C` for `j ≤ m` and `|Dⁱ b| ≤ M` for
`i < m` on a set `s`, then `|Dᵐ α| ≤ K` on `s`, with `K` depending only on `m`, `C` and `M`
(`exists_norm_iteratedFDeriv_le_of_norm_iteratedCovariantDeriv_le`). The proof differentiates
`d ∇ʲ α = ∇ʲ⁺¹ α - i b ⊗ ∇ʲ α` and bounds the derivatives of the product by the Leibniz rule.
In a gauge where the connection form is controlled, such as the radial gauge of
`TauCeti.Analysis.PDE.SeibergWitten.RadialGauge.Connection`, this turns gauge invariant bounds into
bounds on the derivatives of the section itself.

## Main definitions

* `TauCeti.SeibergWitten.iteratedCovariantDeriv b α n`: the `n`-th covariant derivative of `α`.

## Main results

* `TauCeti.SeibergWitten.iteratedCovariantDeriv_succ_apply`: the recursion
  `∇ⁿ⁺¹ α (v) = D(∇ⁿ α)(v₀)(tail v) + i b(v₀) ∇ⁿ α (tail v)`.
* `TauCeti.SeibergWitten.iteratedCovariantDeriv_one_apply`: `∇¹ α (v) = ∇_a α (v₀)`.
* `TauCeti.SeibergWitten.contDiff_iteratedCovariantDeriv`: regularity.
* `TauCeti.SeibergWitten.iteratedCovariantDeriv_sub_phaseForm_mul`: gauge covariance.
* `TauCeti.SeibergWitten.exists_norm_iteratedFDeriv_le_of_norm_iteratedCovariantDeriv_le`:
  derivative bounds from covariant derivative bounds.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex ContinuousAlternatingMap Filter Set
open scoped Topology

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α u : E → ℂ} {x : E}

/-- The iterated covariant derivatives `∇ⁿ α` of a section `α` of the trivial line for the
imaginary connection form `a = i b`: `∇⁰ α = α` and `∇ⁿ⁺¹ α (v₀, …, vₙ) = (∇_{v₀} ∇ⁿ α)(v₁, …, vₙ)`,
where `∇_v T = dT(v) + i b(v) T` (`iteratedCovariantDeriv_succ_apply`). -/
def iteratedCovariantDeriv (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) :
    (n : ℕ) → E → (E [×n]→L[ℝ] ℂ)
  | 0 => fun x ↦ (continuousMultilinearCurryFin0 ℝ E ℂ).symm (α x)
  | n + 1 => fun x ↦ (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ).symm
      (fderiv ℝ (iteratedCovariantDeriv b α n) x +
        ((ofSubsingletonLIE (0 : Fin 1)).symm (b x)).smulRight (I • iteratedCovariantDeriv b α n x))

@[simp]
theorem iteratedCovariantDeriv_zero_apply (m : Fin 0 → E) :
    iteratedCovariantDeriv b α 0 x m = α x :=
  (rfl)

/-- The zeroth iterated covariant derivative is the section, read as a `0`-multilinear map. -/
theorem iteratedCovariantDeriv_zero :
    iteratedCovariantDeriv b α 0 = (continuousMultilinearCurryFin0 ℝ E ℂ).symm ∘ α :=
  (rfl)

@[simp]
theorem norm_iteratedCovariantDeriv_zero : ‖iteratedCovariantDeriv b α 0 x‖ = ‖α x‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- The recursion for the iterated covariant derivatives:
`∇ⁿ⁺¹ α (v) = D(∇ⁿ α)(v₀)(tail v) + i b(v₀) ∇ⁿ α (tail v)`. -/
theorem iteratedCovariantDeriv_succ_apply {n : ℕ} (m : Fin (n + 1) → E) :
    iteratedCovariantDeriv b α (n + 1) x m =
      fderiv ℝ (iteratedCovariantDeriv b α n) x (m 0) (Fin.tail m) +
        I * b x (fun _ ↦ m 0) * iteratedCovariantDeriv b α n x (Fin.tail m) := by
  simp [iteratedCovariantDeriv, ofSubsingletonLIE_symm_apply]
  ring

/-- The first iterated covariant derivative is the covariant derivative. -/
@[simp]
theorem iteratedCovariantDeriv_one_apply (m : Fin 1 → E) :
    iteratedCovariantDeriv b α 1 x m = covariantDeriv b α x (m 0) := by
  rw [iteratedCovariantDeriv_succ_apply, covariantDeriv_apply, iteratedCovariantDeriv_zero,
    (continuousMultilinearCurryFin0 ℝ E ℂ).symm.comp_fderiv]
  simp
  ring

@[simp]
theorem norm_iteratedCovariantDeriv_one :
    ‖iteratedCovariantDeriv b α 1 x‖ = ‖covariantDeriv b α x‖ := by
  have h : iteratedCovariantDeriv b α 1 x =
      (continuousMultilinearCurryFin1 ℝ E ℂ).symm (covariantDeriv b α x) := by
    ext m
    rw [iteratedCovariantDeriv_one_apply, continuousMultilinearCurryFin1_symm_apply]
  rw [h, LinearIsometryEquiv.norm_map]

/-! ### Regularity -/

/-- The operator norm group structure on `E [×n]→L[ℝ] ℂ →L[ℝ] E [×(n + 1)]→L[ℝ] ℂ`, the
codomain of the bilinear connection term below. Instance synthesis does not find it at the default
pending depth when it occurs as the codomain of a further continuous linear map, so it is provided
here as a local instance. -/
private local instance normedAddCommGroupConnectionTermCodomain (n : ℕ) :
    NormedAddCommGroup ((E [×n]→L[ℝ] ℂ) →L[ℝ] (E [×(n + 1)]→L[ℝ] ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The real normed space structure on the codomain of the connection term, provided locally for
the same reason as `normedAddCommGroupConnectionTermCodomain`. -/
private local instance normedSpaceConnectionTermCodomain (n : ℕ) :
    NormedSpace ℝ ((E [×n]→L[ℝ] ℂ) →L[ℝ] (E [×(n + 1)]→L[ℝ] ℂ)) :=
  ContinuousLinearMap.toNormedSpace

variable (E) in
/-- The connection term `(ω, S) ↦ i ω ⊗ S` of the covariant derivative, as a bounded bilinear map
with values in multilinear maps of one more variable: `(ω, S)(v) = i ω(v₀) S(tail v)`. -/
private def connectionTerm (n : ℕ) :
    (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℂ) →L[ℝ] (E [×(n + 1)]→L[ℝ] ℂ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun ω S ↦ (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ).symm
        (((ofSubsingletonLIE (0 : Fin 1)).symm ω).smulRight (I • S)))
      (fun ω ω' S ↦ by ext m; simp [ofSubsingletonLIE_symm_apply, add_mul])
      (fun c ω S ↦ by ext m; simp [ofSubsingletonLIE_symm_apply, mul_assoc, mul_left_comm])
      (fun ω S S' ↦ by ext m; simp [ofSubsingletonLIE_symm_apply])
      (fun c ω S ↦ by ext m; simp [ofSubsingletonLIE_symm_apply, mul_left_comm]))
    1 fun ω S ↦ by
      simp only [LinearMap.mk₂_apply, LinearIsometryEquiv.norm_map,
        ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_I, one_mul]
      exact le_rfl

private theorem connectionTerm_apply (n : ℕ) (ω : E [⋀^Fin 1]→L[ℝ] ℝ) (S : E [×n]→L[ℝ] ℂ)
    (m : Fin (n + 1) → E) :
    connectionTerm E n ω S m = I * ω (fun _ ↦ m 0) * S (Fin.tail m) := by
  simp [connectionTerm, ofSubsingletonLIE_symm_apply]
  ring

/-- The `(n + 1)`-th iterated covariant derivative is the derivative of the `n`-th one, uncurried,
plus the connection term. -/
private theorem iteratedCovariantDeriv_succ_eq (n : ℕ) :
    iteratedCovariantDeriv b α (n + 1) =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ).symm ∘
          fderiv ℝ (iteratedCovariantDeriv b α n) +
        fun y ↦ connectionTerm E n (b y) (iteratedCovariantDeriv b α n y) := by
  funext y
  ext m
  rw [iteratedCovariantDeriv_succ_apply, Pi.add_apply, _root_.add_apply, connectionTerm_apply,
    Function.comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply]

/-- The derivative of the `n`-th iterated covariant derivative is the `(n + 1)`-th one minus the
connection term, curried in the first variable: `d ∇ⁿ α = ∇ⁿ⁺¹ α - i b ⊗ ∇ⁿ α`. -/
private theorem fderiv_iteratedCovariantDeriv (n : ℕ) :
    fderiv ℝ (iteratedCovariantDeriv b α n) =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ) ∘
        (iteratedCovariantDeriv b α (n + 1) -
          fun y ↦ connectionTerm E n (b y) (iteratedCovariantDeriv b α n y)) := by
  rw [iteratedCovariantDeriv_succ_eq, add_sub_cancel_right]
  funext y
  simp

/-- The `n`-th iterated covariant derivative of a `C^(n + m)` section for a `C^(n + m - 1)`
connection form is `Cᵐ`. -/
theorem contDiff_iteratedCovariantDeriv {n m : ℕ} (hα : ContDiff ℝ (n + m : ℕ) α)
    (hb : ContDiff ℝ (n + m - 1 : ℕ) b) :
    ContDiff ℝ m (iteratedCovariantDeriv b α n) := by
  induction n generalizing m with
  | zero =>
    simp only [zero_add] at hα
    exact (continuousMultilinearCurryFin0 ℝ E ℂ).symm.contDiff.comp hα
  | succ n ih =>
    have h1 : ContDiff ℝ (m + 1 : ℕ) (iteratedCovariantDeriv b α n) :=
      ih (by rwa [show n + (m + 1) = n + 1 + m by omega])
        (by rwa [show n + (m + 1) - 1 = n + 1 + m - 1 by omega])
    have h2 : ContDiff ℝ m (fderiv ℝ (iteratedCovariantDeriv b α n)) :=
      h1.fderiv_right (by push_cast; exact le_rfl)
    have hbm : ContDiff ℝ m b := hb.of_le (by norm_cast; omega)
    have h3 : ContDiff ℝ m
        (fun y ↦ connectionTerm E n (b y) (iteratedCovariantDeriv b α n y)) :=
      ((connectionTerm E n).contDiff.comp hbm).clm_apply (h1.of_le (by norm_cast; omega))
    rw [iteratedCovariantDeriv_succ_eq]
    refine ContDiff.add ?_ h3
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ).symm.contDiff.comp h2

/-! ### Gauge covariance -/

/-- **Gauge covariance of the iterated covariant derivatives.** A gauge transformation
`(b, α) ↦ (b - Im (u⁻¹ du), u α)` by a differentiable circle-valued function `u` multiplies every
iterated covariant derivative by `u`: `∇ⁿ_{b - Im (u⁻¹ du)} (u α) = u ∇ⁿ_b α`. -/
theorem iteratedCovariantDeriv_sub_phaseForm_mul (hu : ∀ y, ‖u y‖ = 1) (hud : Differentiable ℝ u)
    {n : ℕ} (hα : ContDiff ℝ n α) (hb : ContDiff ℝ (n - 1 : ℕ) b) :
    iteratedCovariantDeriv (b - phaseForm u) (u * α) n =
      fun y ↦ u y • iteratedCovariantDeriv b α n y := by
  induction n with
  | zero =>
    funext y
    ext m
    simp
  | succ n ih =>
    have hT : Differentiable ℝ (iteratedCovariantDeriv b α n) :=
      (contDiff_iteratedCovariantDeriv (n := n) (m := 1) hα hb).differentiable one_ne_zero
    have ih' := ih (hα.of_le (by norm_cast; omega)) (hb.of_le (by norm_cast; omega))
    funext y
    ext m
    rw [iteratedCovariantDeriv_succ_apply, _root_.smul_apply,
      iteratedCovariantDeriv_succ_apply, ih', fderiv_fun_smul (hud y) (hT y)]
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, Pi.sub_apply,
      ContinuousAlternatingMap.sub_apply, ofReal_sub,
      fderiv_apply_eq_mul_I_mul_phaseForm (.of_forall hu) (m 0)]
    ring

/-! ### Derivative bounds from covariant derivative bounds -/

/-- Bounds on the iterated covariant derivatives of order at most `m + j` and on the derivatives of
order less than `m` of the connection form bound the derivatives of order `m` of `∇ʲ α`, with a
constant depending only on `m`, `j` and the two bounds. -/
private theorem exists_norm_iteratedFDeriv_iteratedCovariantDeriv_le (C M : ℝ) (m : ℕ) :
    ∀ j : ℕ, ∃ K, ∀ {s : Set E} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ},
      ContDiff ℝ (m + j : ℕ) α → ContDiff ℝ (m + j - 1 : ℕ) b →
      (∀ i ≤ m + j, ∀ x ∈ s, ‖iteratedCovariantDeriv b α i x‖ ≤ C) →
      (∀ i < m, ∀ x ∈ s, ‖iteratedFDeriv ℝ i b x‖ ≤ M) →
      ∀ x ∈ s, ‖iteratedFDeriv ℝ m (iteratedCovariantDeriv b α j) x‖ ≤ K := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j
  rcases m with _ | m
  · exact ⟨C, fun _ _ hcov _ x hx ↦ by
      simpa [norm_iteratedFDeriv_zero] using hcov j (by omega) x hx⟩
  -- Derivatives of order at most `m` of `∇ʲ α` and of order `m` of `∇ʲ⁺¹ α` are bounded.
  choose K hK using fun i (hi : i ≤ m) ↦ ih i (by omega) j
  obtain ⟨K', hK'⟩ := ih m (by omega) (j + 1)
  refine ⟨K' + ‖connectionTerm E j‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * M *
      K (m - i) (Nat.sub_le m i), fun {s b α} hα hb hcov hconn x hx ↦ ?_⟩
  have hT : ContDiff ℝ (m + 1 : ℕ) (iteratedCovariantDeriv b α j) :=
    contDiff_iteratedCovariantDeriv (by simpa [Nat.add_comm] using hα)
      (hb.of_le (by norm_cast; omega))
  have hT' : ContDiff ℝ m (iteratedCovariantDeriv b α (j + 1)) :=
    contDiff_iteratedCovariantDeriv (by rw [show j + 1 + m = m + 1 + j by omega]; exact hα)
      (hb.of_le (by norm_cast; omega))
  have hbm : ContDiff ℝ m b := hb.of_le (by norm_cast; omega)
  have hTm : ContDiff ℝ m (iteratedCovariantDeriv b α j) := hT.of_le (by norm_cast; omega)
  have hB : ContDiff ℝ m
      (fun y ↦ connectionTerm E j (b y) (iteratedCovariantDeriv b α j y)) :=
    ((connectionTerm E j).contDiff.comp hbm).clm_apply hTm
  rw [← norm_iteratedFDeriv_fderiv, fderiv_iteratedCovariantDeriv,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
    iteratedFDeriv_sub_apply hT'.contDiffAt hB.contDiffAt]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact hK' (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hα)
      (hb.of_le (by norm_cast; omega)) (fun i hi ↦ hcov i (by omega))
      (fun i hi ↦ hconn i (by omega)) x hx
  refine ((connectionTerm E j).norm_iteratedFDeriv_le_of_bilinear hbm hTm x le_rfl).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ ?_) (norm_nonneg _))
  have hi : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hmi : m - i ≤ m := Nat.sub_le m i
  rw [mul_assoc, mul_assoc]
  gcongr
  · exact (norm_nonneg _).trans (hconn i (by omega) x hx)
  · exact hconn i (by omega) x hx
  · exact hK (m - i) hmi (hα.of_le (by norm_cast; omega)) (hb.of_le (by norm_cast; omega))
      (fun i' hi' ↦ hcov i' (by omega)) (fun i' hi' ↦ hconn i' (by omega)) x hx

/-- **Derivative bounds from covariant derivative bounds.** If on a set `s` the iterated covariant
derivatives of a `Cᵐ` section `α` of order at most `m` are bounded by `C` and the derivatives of
order less than `m` of a `C^(m - 1)` connection form `b` are bounded by `M`, then the derivatives
of order `m` of `α` are bounded on `s` by a constant depending only on `m`, `C` and `M`. -/
theorem exists_norm_iteratedFDeriv_le_of_norm_iteratedCovariantDeriv_le (C M : ℝ) (m : ℕ) :
    ∃ K, ∀ {s : Set E} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ},
      ContDiff ℝ m α → ContDiff ℝ (m - 1 : ℕ) b →
      (∀ i ≤ m, ∀ x ∈ s, ‖iteratedCovariantDeriv b α i x‖ ≤ C) →
      (∀ i < m, ∀ x ∈ s, ‖iteratedFDeriv ℝ i b x‖ ≤ M) →
      ∀ x ∈ s, ‖iteratedFDeriv ℝ m α x‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_norm_iteratedFDeriv_iteratedCovariantDeriv_le (E := E) C M m 0
  refine ⟨K, fun {s b α} hα hb hcov hconn x hx ↦ ?_⟩
  have := hK (s := s) (by simpa using hα) (by simpa using hb) (by simpa using hcov) hconn x hx
  rwa [iteratedCovariantDeriv_zero, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left] at this

end TauCeti.SeibergWitten
