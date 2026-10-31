/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The negative index of a path of symmetric forms at a regular crossing

Let `t ↦ V t` be a path of continuous bilinear forms on a finite-dimensional real normed space,
symmetric at `t₀` and differentiable there with derivative `V'`. A *crossing* is a parameter `t₀`
at which `V t₀` is degenerate. The *crossing form* (`ContinuousLinearMap.crossingForm`) is the
quadratic form `v ↦ V' v v` restricted to the kernel of `V t₀`, and the crossing is *regular*
when the crossing form is nondegenerate.

At a regular crossing the negative index of `V t` jumps by an amount read off from the crossing
form alone: just after the crossing it is the negative index of `V t₀` plus the negative index of
the crossing form, and just before it is the negative index of `V t₀` plus the positive index of
the crossing form. The negative index therefore drops across the crossing by the signature of the
crossing form. If moreover `V t` is symmetric for all `t` near `t₀`, then `V t` is nondegenerate
on both sides, so regular crossings are isolated. This is the local computation behind the
formula of Robbin and Salamon expressing the spectral flow of a path of symmetric operators as the
sum of the signatures of its crossing forms, which in turn computes the Fredholm index of
`d/ds + A(s)` and of linear Cauchy--Riemann operators with Lagrangian boundary conditions as a
Maslov index. The summation of these local jumps over the crossings of a path on a compact interval
is not carried out here.

The proof compares indices by dimension counting. A subspace on which `V t₀` is negative definite,
plus a subspace of the kernel on which the crossing form is negative definite, is a subspace on
which `V t` is negative definite for `t > t₀` close to `t₀`; the same holds for positive definite
subspaces. These two lower bounds already add up to the dimension of the space, so both are
equalities and the quadratic form of `V t` has trivial radical. One-sided derivatives suffice for
the one-sided statements.

## Main definitions

* `ContinuousLinearMap.crossingForm`: the crossing form of a bilinear form `B` and a derivative
  `V'`, the quadratic form of `V'` on the kernel of `B`.

## Main results

* `ContinuousLinearMap.eventually_sigNeg_eq_add_sigNeg_crossingForm`: just after a regular
  crossing, the negative index of `V t` is that of `V t₀` plus that of the crossing form.
* `ContinuousLinearMap.eventually_sigNeg_eq_add_sigPos_crossingForm`: just before a regular
  crossing, the negative index of `V t` is that of `V t₀` plus the positive index of the crossing
  form.
* `ContinuousLinearMap.eventually_nondegenerate_of_crossingForm_nondegenerate`: a path of forms
  symmetric near a regular crossing is nondegenerate near it, except at the crossing itself.
* `ContinuousLinearMap.eventually_sigNeg_sub_sigNeg_eq_sigPos_sub_sigNeg_crossingForm`: across a
  regular crossing the negative index drops by the signature of the crossing form.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Section 2 (crossing forms and regular crossings).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4 (the crossing operator and the spectral flow of a path of
  symmetric operators).
-/

public section

open Filter Set Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The *crossing form* of a bilinear form `B` and a bilinear form `V'`: the quadratic form
`v ↦ V' v v` restricted to the kernel of `B`. For a path `V` of symmetric forms with derivative
`V'` at `t₀`, the crossing form of `V t₀` and `V'` governs how the negative index of `V t` changes
as `t` passes `t₀`. -/
noncomputable def crossingForm (B V' : E →L[ℝ] E →L[ℝ] ℝ) :
    QuadraticForm ℝ B.ker :=
  V'.toBilinForm.toQuadraticMap.restrict B.ker

/-- The crossing form evaluates `V'` on the diagonal of the kernel. -/
@[simp]
theorem crossingForm_apply (B V' : E →L[ℝ] E →L[ℝ] ℝ) (v : B.ker) :
    crossingForm B V' v = V' v v := by
  simp [crossingForm]

/-- Negating the derivative negates the crossing form. -/
@[simp]
theorem crossingForm_neg (B V' : E →L[ℝ] E →L[ℝ] ℝ) :
    crossingForm B (-V') = -crossingForm B V' := by
  ext v
  simp

/-- A subspace of the kernel of `B` on which the crossing form of `B` and `D` is negative definite
gives a subspace of `E` of the same dimension, inside the kernel, on which `D` is negative
definite. -/
private theorem exists_le_ker_of_posDef_neg_crossingForm (B D : E →L[ℝ] E →L[ℝ] ℝ)
    {M' : Submodule ℝ B.ker} (hM' : ((-crossingForm B D).restrict M').PosDef) :
    ∃ M : Submodule ℝ E, Module.finrank ℝ M = Module.finrank ℝ M' ∧ M ≤ B.ker ∧
      ∀ x ∈ M, x ≠ 0 → D x x < 0 := by
  refine ⟨M'.map B.ker.subtype, Submodule.finrank_map_subtype_eq _ _, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩ hy0
    have hy0' : (⟨y, hy⟩ : M') ≠ 0 := by
      intro h
      exact hy0 (by simpa using congrArg (fun z : M' ↦ ((z : B.ker) : E)) h)
    simpa using hM' ⟨y, hy⟩ hy0'

variable [FiniteDimensional ℝ E] {V : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {t₀ : ℝ}

/-- The scalar inequality behind the key estimate: a term bounded by `-c₁ a²`, plus `h` times a
term bounded by `C a² + 2 C a b - c₂ b²`, plus an error bounded by `c₂ h (2 a² + 2 b²) / 8`, is
negative once `0 < h < c₁ / (2 (K₀ + 1))` for `K₀ = C + 2 C² / c₂ + c₂ / 4`, provided `a` or `b`
is positive. -/
private theorem add_mul_add_lt_zero {a b c₁ c₂ C h q d r : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hC : 0 ≤ C) (hh : 0 < h)
    (hsmall : h < c₁ / (2 * (C + 2 * C ^ 2 / c₂ + c₂ / 4 + 1))) (hab : 0 < a ∨ 0 < b)
    (hq : q ≤ -(c₁ * a ^ 2)) (hd : d ≤ C * a ^ 2 + 2 * C * a * b - c₂ * b ^ 2)
    (hr : r ≤ c₂ / 8 * h * (2 * a ^ 2 + 2 * b ^ 2)) :
    q + h * d + r < 0 := by
  set K₀ := C + 2 * C ^ 2 / c₂ + c₂ / 4
  have hK₀ : 0 ≤ K₀ := by positivity
  -- Absorb the cross term `2 C a b` into the two squares.
  have hcross : 2 * C * a * b ≤ c₂ / 2 * b ^ 2 + 2 * C ^ 2 / c₂ * a ^ 2 := by
    have h := two_mul_le_add_mul_sq (a := b) (b := C * a) (half_pos hc₂)
    rw [inv_div] at h
    calc 2 * C * a * b = 2 * b * (C * a) := by ring
      _ ≤ c₂ / 2 * b ^ 2 + 2 / c₂ * (C * a) ^ 2 := h
      _ = c₂ / 2 * b ^ 2 + 2 * C ^ 2 / c₂ * a ^ 2 := by ring
  -- The coefficient of `a²` stays below `-c₁ / 2`, that of `b²` is `-c₂ h / 4`.
  have hK : h * K₀ * a ^ 2 ≤ c₁ / 2 * a ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg a)
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (K₀ + 1))).1 hsmall
    nlinarith
  have hsum : q + h * d + r ≤ -(c₁ / 2 * a ^ 2) - c₂ / 4 * h * b ^ 2 := by
    simp only [K₀] at hK
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le, mul_le_mul_of_nonneg_left hcross hh.le]
  have ha2 : 0 ≤ c₁ / 2 * a ^ 2 := by positivity
  have hb2 : 0 ≤ c₂ / 4 * h * b ^ 2 := by positivity
  rcases hab with ha' | hb'
  · have : 0 < c₁ / 2 * a ^ 2 := by positivity
    linarith
  · have : 0 < c₂ / 4 * h * b ^ 2 := by positivity
    linarith

/-- The key estimate. Let `V t = V t₀ + h t • D + o(h t)` with `h t → 0⁺` along `l`. If `V t₀`
is negative definite on `N` and `D` is negative definite on a subspace `M` of the kernel of `V t₀`,
then eventually along `l` the form `V t` is negative definite on `N ⊔ M`. -/
private theorem eventually_forall_lt_zero {l : Filter ℝ} {h : ℝ → ℝ} {D : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ t in l, 0 < h t)
    (hrem : (fun t ↦ V t - V t₀ - h t • D) =o[l] h) {N M : Submodule ℝ E}
    (hN : ∀ x ∈ N, x ≠ 0 → V t₀ x x < 0) (hMK : M ≤ (V t₀).ker)
    (hM : ∀ x ∈ M, x ≠ 0 → D x x < 0) :
    ∀ᶠ t in l, ∀ x ∈ N ⊔ M, x ≠ 0 → V t x x < 0 := by
  obtain ⟨c₁, hc₁, hN'⟩ := exists_pos_forall_le_neg_mul_sq (V t₀) N hN
  obtain ⟨c₂, hc₂, hM'⟩ := exists_pos_forall_le_neg_mul_sq D M hM
  set C := ‖D‖
  have hsmall : ∀ᶠ t in l, h t < c₁ / (2 * (C + 2 * C ^ 2 / c₂ + c₂ / 4 + 1)) :=
    hh.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hpos, hsmall, hrem.bound (by positivity : 0 < c₂ / 8)]
    with t ht0 htδ hR x hx hx0
  obtain ⟨n, hn, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
  set R := V t - V t₀ - h t • D
  have hVt : V t (n + m) (n + m) =
      V t₀ (n + m) (n + m) + h t * D (n + m) (n + m) + R (n + m) (n + m) := by
    simp only [R, sub_apply, smul_apply, smul_eq_mul]
    ring
  have hm0 : V t₀ m = 0 := hMK hm
  have hnm : V t₀ n m = 0 := by
    rw [← ContinuousLinearMap.toBilinForm_apply, hsymm.eq]
    simp [hm0]
  -- Bound the three terms of `V t (n + m) (n + m)` in terms of `‖n‖` and `‖m‖`.
  have h₀ : V t₀ (n + m) (n + m) ≤ -(c₁ * ‖n‖ ^ 2) := by
    simpa [hm0, hnm] using hN' n hn
  have hD : D (n + m) (n + m) ≤ C * ‖n‖ ^ 2 + 2 * C * ‖n‖ * ‖m‖ - c₂ * ‖m‖ ^ 2 := by
    have h₁ : |D n n| ≤ C * ‖n‖ * ‖n‖ := by
      simpa [Real.norm_eq_abs] using D.le_opNorm₂ n n
    have h₂ : |D n m| ≤ C * ‖n‖ * ‖m‖ := by
      simpa [Real.norm_eq_abs] using D.le_opNorm₂ n m
    have h₃ : |D m n| ≤ C * ‖m‖ * ‖n‖ := by
      simpa [Real.norm_eq_abs] using D.le_opNorm₂ m n
    have h₄ := hM' m hm
    simp only [map_add, add_apply]
    nlinarith [abs_le.1 h₁, abs_le.1 h₂, abs_le.1 h₃]
  have hRx : R (n + m) (n + m) ≤ c₂ / 8 * h t * (2 * ‖n‖ ^ 2 + 2 * ‖m‖ ^ 2) := by
    have h₁ : |R (n + m) (n + m)| ≤ ‖R‖ * ‖n + m‖ * ‖n + m‖ := by
      simpa [Real.norm_eq_abs] using R.le_opNorm₂ (n + m) (n + m)
    have hR' : ‖R‖ ≤ c₂ / 8 * h t := by
      simpa [Real.norm_eq_abs, abs_of_pos ht0] using hR
    have h₂ : ‖R‖ * ‖n + m‖ * ‖n + m‖ ≤ c₂ / 8 * h t * (‖n‖ + ‖m‖) ^ 2 := by
      rw [mul_assoc, ← sq]
      exact mul_le_mul hR' (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le n m) 2)
        (by positivity) (by positivity)
    have h₃ : c₂ / 8 * h t * (‖n‖ + ‖m‖) ^ 2 ≤ c₂ / 8 * h t * (2 * ‖n‖ ^ 2 + 2 * ‖m‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖n‖ - ‖m‖)])
        (mul_nonneg (by positivity) ht0.le)
    linarith [le_abs_self (R (n + m) (n + m))]
  have hab : 0 < ‖n‖ ∨ 0 < ‖m‖ := by
    by_contra! hab
    simp [norm_le_zero_iff.1 hab.1, norm_le_zero_iff.1 hab.2] at hx0
  rw [hVt]
  exact add_mul_add_lt_zero hc₁ hc₂ (norm_nonneg D) ht0 htδ hab h₀ hD hRx

/-- Lower bound for the negative index: eventually along `l`, the negative index of `V t` is at
least that of `V t₀` plus that of the crossing form of `V t₀` and `D`. -/
private theorem eventually_add_sigNeg_le {l : Filter ℝ} {h : ℝ → ℝ} {D : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ t in l, 0 < h t)
    (hrem : (fun t ↦ V t - V t₀ - h t • D) =o[l] h) :
    ∀ᶠ t in l, sigNeg (V t₀).toBilinForm.toQuadraticMap + sigNeg (crossingForm (V t₀) D) ≤
      sigNeg (V t).toBilinForm.toQuadraticMap := by
  obtain ⟨N, hNr, hN⟩ := exists_finrank_eq_sigNeg_and_negDef (V t₀).toBilinForm.toQuadraticMap
  obtain ⟨M', hM'r, hM'⟩ := exists_finrank_eq_sigNeg_and_negDef (crossingForm (V t₀) D)
  obtain ⟨M, hMr, hMK, hM⟩ := exists_le_ker_of_posDef_neg_crossingForm (V t₀) D hM'
  have hN' : ∀ x ∈ N, x ≠ 0 → V t₀ x x < 0 := fun x hx hx0 ↦ by
    simpa using hN ⟨x, hx⟩ (by simpa using hx0)
  filter_upwards [eventually_forall_lt_zero hsymm hh hpos hrem hN' hMK hM] with t ht
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq N M
  rw [inf_eq_bot_of_le_ker (fun x hx hx0 ↦ (hN' x hx hx0).ne) hMK, finrank_bot, add_zero] at hdim
  rw [← hNr, ← hM'r, ← hMr, ← hdim]
  exact le_sigNeg_of_negDef _ fun x hx0 ↦ by simpa using ht x x.2 (by simpa using hx0)

/-- Lower bound for the positive index: eventually along `l`, the positive index of `V t` is at
least that of `V t₀` plus that of the crossing form of `V t₀` and `D`. This is the negative-index
bound applied to the path `-V`. -/
private theorem eventually_add_sigPos_le {l : Filter ℝ} {h : ℝ → ℝ} {D : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ t in l, 0 < h t)
    (hrem : (fun t ↦ V t - V t₀ - h t • D) =o[l] h) :
    ∀ᶠ t in l, sigPos (V t₀).toBilinForm.toQuadraticMap + sigPos (crossingForm (V t₀) D) ≤
      sigPos (V t).toBilinForm.toQuadraticMap := by
  have hsymm' : (-V t₀).toBilinForm.IsSymm := ⟨fun x y ↦ by simpa using hsymm.eq x y⟩
  have hrem' : (fun t ↦ -V t - -V t₀ - h t • -D) =o[l] h := by
    have hneg := (Asymptotics.isLittleO_neg_left (f' := fun t ↦ V t - V t₀ - h t • D) (g := h)
      (l := l)).2 hrem
    exact hneg.congr_left fun t ↦ by module
  -- The kernels of `-V t₀` and `V t₀` agree, so the two crossing forms are equivalent.
  have hK : (-V t₀).ker = (V t₀).ker := by
    ext x
    simp
  have hΓ : sigPos (crossingForm (-V t₀) D) = sigPos (crossingForm (V t₀) D) :=
    QuadraticMap.Equivalent.sigPos_eq ⟨⟨LinearEquiv.ofEq _ _ hK, fun v ↦ by simp [crossingForm]⟩⟩
  have hQ (L : E →L[ℝ] E →L[ℝ] ℝ) :
      (-L).toBilinForm.toQuadraticMap = -L.toBilinForm.toQuadraticMap := by
    ext x
    simp
  filter_upwards [eventually_add_sigNeg_le (V := fun t ↦ -V t) hsymm' hh hpos hrem'] with t ht
  simpa [hQ, hΓ] using ht

/-- At a regular crossing, eventually along `l` the negative index of `V t` is that of `V t₀`
plus that of the crossing form, and `V t` has trivial radical: the two lower bounds add up to the
dimension of the space. -/
private theorem eventually_sigNeg_eq_and_radical_eq_bot {l : Filter ℝ} {h : ℝ → ℝ}
    {D : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : (V t₀).toBilinForm.IsSymm) (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ t in l, 0 < h t) (hrem : (fun t ↦ V t - V t₀ - h t • D) =o[l] h)
    (hreg : (crossingForm (V t₀) D).Nondegenerate) :
    ∀ᶠ t in l, sigNeg (V t).toBilinForm.toQuadraticMap =
      sigNeg (V t₀).toBilinForm.toQuadraticMap + sigNeg (crossingForm (V t₀) D) ∧
        (V t).toBilinForm.toQuadraticMap.radical = ⊥ := by
  filter_upwards [eventually_add_sigNeg_le hsymm hh hpos hrem,
    eventually_add_sigPos_le hsymm hh hpos hrem] with t hneg hpos
  have h₁ := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := (V t).toBilinForm.toQuadraticMap)
  have h₀ := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := (V t₀).toBilinForm.toQuadraticMap)
  rw [LinearMap.BilinForm.radical_toQuadraticMap _ hsymm, ker_toBilinForm] at h₀
  have hΓ := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _ hreg
  have hrad : Module.finrank ℝ (V t).toBilinForm.toQuadraticMap.radical = 0 := by omega
  exact ⟨by omega, Submodule.finrank_eq_zero.1 hrad⟩

/-- The conclusion of `eventually_sigNeg_eq_and_radical_eq_bot` just after a regular crossing,
from a right derivative, with `h t = t - t₀`. -/
private theorem eventually_nhdsGT_sigNeg_eq_and_radical_eq_bot {V' : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hV : HasDerivWithinAt V V' (Ici t₀) t₀)
    (hreg : (crossingForm (V t₀) V').Nondegenerate) :
    ∀ᶠ t in 𝓝[>] t₀, sigNeg (V t).toBilinForm.toQuadraticMap =
      sigNeg (V t₀).toBilinForm.toQuadraticMap + sigNeg (crossingForm (V t₀) V') ∧
        (V t).toBilinForm.toQuadraticMap.radical = ⊥ := by
  refine eventually_sigNeg_eq_and_radical_eq_bot hsymm
    (((continuous_sub_right t₀).tendsto' t₀ 0 (sub_self t₀)).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _ ht ↦ sub_pos.2 ht) ?_ hreg
  exact ((hasDerivWithinAt_iff_isLittleO (f := V) (f' := V') (s := Ici t₀) (x := t₀)).1
    hV).mono (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- The conclusion of `eventually_sigNeg_eq_and_radical_eq_bot` just before a regular crossing,
from a left derivative `V'`, with `h t = t₀ - t` and `D = -V'`. -/
private theorem eventually_nhdsLT_sigNeg_eq_and_radical_eq_bot {V' : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hV : HasDerivWithinAt V V' (Iic t₀) t₀)
    (hreg : (crossingForm (V t₀) V').Nondegenerate) :
    ∀ᶠ t in 𝓝[<] t₀, sigNeg (V t).toBilinForm.toQuadraticMap =
      sigNeg (V t₀).toBilinForm.toQuadraticMap + sigPos (crossingForm (V t₀) V') ∧
        (V t).toBilinForm.toQuadraticMap.radical = ⊥ := by
  have hreg' : (crossingForm (V t₀) (-V')).Nondegenerate := by
    rwa [crossingForm_neg, QuadraticMap.nondegenerate_neg]
  have hrem : (fun t ↦ V t - V t₀ - (t₀ - t) • -V') =o[𝓝[<] t₀] fun t ↦ t₀ - t := by
    have hrem := ((hasDerivWithinAt_iff_isLittleO (f := V) (f' := V') (s := Iic t₀)
      (x := t₀)).1 hV).mono (nhdsWithin_mono _ Iio_subset_Iic_self)
    refine hrem.neg_right.congr (fun t ↦ ?_) fun t ↦ ?_
    · module
    · rw [neg_sub]
  filter_upwards [eventually_sigNeg_eq_and_radical_eq_bot hsymm
    (((continuous_sub_left t₀).tendsto' t₀ 0 (sub_self t₀)).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _ ht ↦ sub_pos.2 ht) hrem hreg'] with t ht
  rwa [crossingForm_neg, sigNeg_neg] at ht

/-- **The negative index just after a regular crossing.** Let `V` be a path of continuous bilinear
forms, symmetric at `t₀` and with right derivative `V'` there, whose crossing form at `t₀` is
nondegenerate. For `t > t₀` close to `t₀`, the negative index of `V t` is the negative index of
`V t₀` plus the negative index of the crossing form. -/
theorem eventually_sigNeg_eq_add_sigNeg_crossingForm {V' : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hV : HasDerivWithinAt V V' (Ici t₀) t₀)
    (hreg : (crossingForm (V t₀) V').Nondegenerate) :
    ∀ᶠ t in 𝓝[>] t₀, sigNeg (V t).toBilinForm.toQuadraticMap =
      sigNeg (V t₀).toBilinForm.toQuadraticMap + sigNeg (crossingForm (V t₀) V') :=
  (eventually_nhdsGT_sigNeg_eq_and_radical_eq_bot hsymm hV hreg).mono fun _ ht ↦ ht.1

/-- **The negative index just before a regular crossing.** Let `V` be a path of continuous
bilinear forms, symmetric at `t₀` and with left derivative `V'` there, whose crossing form at `t₀`
is nondegenerate. For `t < t₀` close to `t₀`, the negative index of `V t` is the negative index of
`V t₀` plus the positive index of the crossing form. -/
theorem eventually_sigNeg_eq_add_sigPos_crossingForm {V' : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : (V t₀).toBilinForm.IsSymm) (hV : HasDerivWithinAt V V' (Iic t₀) t₀)
    (hreg : (crossingForm (V t₀) V').Nondegenerate) :
    ∀ᶠ t in 𝓝[<] t₀, sigNeg (V t).toBilinForm.toQuadraticMap =
      sigNeg (V t₀).toBilinForm.toQuadraticMap + sigPos (crossingForm (V t₀) V') :=
  (eventually_nhdsLT_sigNeg_eq_and_radical_eq_bot hsymm hV hreg).mono fun _ ht ↦ ht.1

/-- **Regular crossings are isolated.** A path of symmetric continuous bilinear forms,
differentiable at `t₀` with nondegenerate crossing form there, is nondegenerate at every `t ≠ t₀`
close to `t₀`. -/
theorem eventually_nondegenerate_of_crossingForm_nondegenerate {V' : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ᶠ t in 𝓝 t₀, (V t).toBilinForm.IsSymm) (hV : HasDerivAt V V' t₀)
    (hreg : (crossingForm (V t₀) V').Nondegenerate) :
    ∀ᶠ t in 𝓝[≠] t₀, (V t).toBilinForm.Nondegenerate := by
  have hsymm₀ := hsymm.self_of_nhds
  have hl := HasDerivAt.hasDerivWithinAt (f := V) (f' := V') (x := t₀) (s := Iic t₀) hV
  have hr := HasDerivAt.hasDerivWithinAt (f := V) (f' := V') (x := t₀) (s := Ici t₀) hV
  have hrad : ∀ᶠ t in 𝓝[≠] t₀, (V t).toBilinForm.toQuadraticMap.radical = ⊥ := by
    rw [← nhdsLT_sup_nhdsGT, eventually_sup]
    exact ⟨(eventually_nhdsLT_sigNeg_eq_and_radical_eq_bot hsymm₀ hl hreg).mono fun _ ht ↦ ht.2,
      (eventually_nhdsGT_sigNeg_eq_and_radical_eq_bot hsymm₀ hr hreg).mono fun _ ht ↦ ht.2⟩
  filter_upwards [hrad, nhdsWithin_le_nhds hsymm] with t ht hts
  rw [← QuadraticMap.nondegenerate_iff_radical_eq_bot, ← QuadraticMap.nondegenerate_associated_iff,
    QuadraticMap.associated_left_inverse (S := ℝ) hts.eq] at ht
  exact ht

/-- **The jump of the negative index across a regular crossing.** For a path of continuous
bilinear forms, symmetric at `t₀` and differentiable there with nondegenerate crossing form, the
negative index of `V t₁` for `t₁ < t₀` exceeds that of `V t₂` for `t₂ > t₀`, both close to `t₀`, by
the signature of the crossing form. -/
theorem eventually_sigNeg_sub_sigNeg_eq_sigPos_sub_sigNeg_crossingForm
    {V' : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : (V t₀).toBilinForm.IsSymm) (hV : HasDerivAt V V' t₀)
    (hreg : (crossingForm (V t₀) V').Nondegenerate) :
    ∀ᶠ t₁ in 𝓝[<] t₀, ∀ᶠ t₂ in 𝓝[>] t₀,
      (sigNeg (V t₁).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V t₂).toBilinForm.toQuadraticMap =
        sigPos (crossingForm (V t₀) V') - sigNeg (crossingForm (V t₀) V') := by
  have hl := HasDerivAt.hasDerivWithinAt (f := V) (f' := V') (x := t₀) (s := Iic t₀) hV
  have hr := HasDerivAt.hasDerivWithinAt (f := V) (f' := V') (x := t₀) (s := Ici t₀) hV
  filter_upwards [eventually_sigNeg_eq_add_sigPos_crossingForm hsymm hl hreg] with t₁ ht₁
  filter_upwards [eventually_sigNeg_eq_add_sigNeg_crossingForm hsymm hr hreg] with t₂ ht₂
  rw [ht₁, ht₂]
  push_cast
  ring

end ContinuousLinearMap
