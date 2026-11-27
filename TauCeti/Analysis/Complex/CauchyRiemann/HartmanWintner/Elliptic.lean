/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.CauchyRiemann.HartmanWintner.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Determinant
import TauCeti.Analysis.Asymptotics.PowSubPow
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Complex.Beltrami.Isothermal
import TauCeti.Analysis.Holder.FaaDiBruno
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# The Hartman–Wintner expansion for a variable elliptic principal part

Let `X` be a finite-dimensional real normed space and `u : ℂ → X` a `C²` map on an open set
`Ω ⊆ ℂ`, with `s + i t` the coordinate on `ℂ`, satisfying the differential inequality

`‖a u_ss + 2 b u_st + c u_tt‖ ≤ K (‖u‖ + ‖Du‖)`

on `Ω`, where the coefficients `a, b, c : ℂ → ℝ` are of class `C^{1,α}` on `Ω` for some
`0 < α < 1`, and the principal part is elliptic at a zero `z₀ ∈ Ω` of `u`: `a c - b² > 0` at `z₀`.
Hartman and Wintner proved that either `u` vanishes near `z₀`, or `u` has a nonzero homogeneous
leading polynomial of some degree `k ≥ 1` at `z₀`, together with the corresponding asymptotic of
its derivative (`TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul_of_elliptic`).
The leading polynomial is `h ↦ Re ((T h) ^ k • c)`, with `c ≠ 0` in the complexification of `X`
and `T` a real-linear automorphism of the plane that carries the complex structure
`TauCeti.ellipticStructure` of the principal part frozen at `z₀` to multiplication by `i`: a
homogeneous harmonic polynomial read in the linear coordinates `T`, in which the principal part
frozen at `z₀` is a multiple of the Laplacian.
This is the analytic input to the Micallef–White normal form of a pseudoholomorphic curve, where
the operator comes from an almost complex structure that is not constant.

## The proof

The principal part `a ∂ₛ² + 2 b ∂ₛ∂ₜ + c ∂ₜ²` determines the field of complex structures

`J = (a c - b²)^(-1/2) A ∘ i`, `A = [[a, b], [b, c]]`,

which squares to `-1` where `a c - b² > 0`. Composed with the `C^{1,α}` coefficients, the smooth
map `(a, b, c) ↦ J` gives a `C^{1,α}` field near `z₀`
(`TauCeti.exists_ball_contDiffOn_holderOnWith_fderiv_comp`), so `z₀` has a `C²` isothermal chart
`e` with `C²` inverse, centred at `z₀`, in which `J` is multiplication by `i`
(`TauCeti.Beltrami.exists_isothermal_chart_ckHolder`). In such a chart the principal part becomes a
multiple of the Laplacian: for `v = u ∘ e⁻¹`, the second-order chain rule gives

`a u_ss + 2 b u_st + c u_tt = λ Δv(e z) + Dv(e z) (a e_ss + 2 b e_st + c e_tt)`,

with `λ = (a c - b²)^(1/2) det De(z)`. Indeed, writing `p = De(z) 1` and `q = De(z) i`, the chart
condition `De J = i De` says `b p + c q = (a c - b²)^(1/2) i p` and
`a p + b q = -(a c - b²)^(1/2) i q`, and these turn the trace of the Hessian of `v` against `A`
into `λ` times the trace against the identity. As `λ` does not vanish at `z₀`, `v` satisfies
`‖Δv‖ ≤ K' (‖v‖ + ‖Dv‖)` near `0 = e z₀`, and the Hartman–Wintner expansion for the Laplacian
(`TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul`) applies to `v`. Its leading
polynomial `Re (w ^ k • c)` pulls back along `e z = De(z₀) (z - z₀) + o(‖z - z₀‖)` to
`Re ((De(z₀) (z - z₀)) ^ k • c)`, since the powers of two asymptotically close maps are close
(`Asymptotics.IsLittleO.pow_sub_pow`), and the derivative asymptotic pulls back by the chain rule.

## Main results

* `TauCeti.ellipticStructure`: the complex structure of an elliptic principal part.
* `TauCeti.exists_isothermal_chart_of_elliptic`: a centred `C²` isothermal chart for it, when the
  coefficients are `C^{1,α}`.
* `TauCeti.elliptic_comp_eq_smul_laplacian_add`: in such a chart the principal part is a multiple
  of the Laplacian plus a first-order term.
* `TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul_of_elliptic`: the
  Hartman–Wintner alternative at a zero of `u` for a `C^{1,α}` elliptic principal part.

## References

* P. Hartman and A. Wintner, *On the local behavior of solutions of non-parabolic partial
  differential equations*, Amer. J. Math. **75** (1953), 449–476.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E (the Micallef–White theorem, and isothermal coordinates for the principal part).
* M. J. Micallef and B. White, *The structure of branch points in minimal surfaces and in
  pseudoholomorphic curves*, Ann. of Math. **141** (1995), 35–85.
-/

public section

open Complex Asymptotics Filter Set Topology InnerProductSpace Laplacian
open scoped NNReal

namespace TauCeti

/-! ### The complex structure of an elliptic principal part -/

section Structure

/-- The complex structure `(a c - b²)^(-1/2) A ∘ i` of the principal part
`a ∂ₛ² + 2 b ∂ₛ∂ₜ + c ∂ₜ²`, where `A` is the symmetric matrix `[[a, b], [b, c]]`. It squares to `-1`
where `a c - b² > 0` (`TauCeti.ellipticStructure_ellipticStructure`). -/
noncomputable def ellipticStructure (a b c : ℝ) : ℂ →L[ℝ] ℂ :=
  (√(a * c - b ^ 2))⁻¹ •
    (reCLM.smulRight ((b : ℂ) + c * I) + imCLM.smulRight (-(a : ℂ) - b * I))

@[simp]
theorem ellipticStructure_apply (a b c : ℝ) (v : ℂ) :
    ellipticStructure a b c v =
      (√(a * c - b ^ 2))⁻¹ • (v.re • ((b : ℂ) + c * I) + v.im • (-(a : ℂ) - b * I)) := by
  simp [ellipticStructure]

/-- Where the principal part is elliptic, `ellipticStructure a b c` is a complex structure: it
squares to `-1`. -/
theorem ellipticStructure_ellipticStructure {a b c : ℝ} (h : 0 < a * c - b ^ 2) (v : ℂ) :
    ellipticStructure a b c (ellipticStructure a b c v) = -v := by
  have hs : √(a * c - b ^ 2) ^ 2 = a * c - b ^ 2 := Real.sq_sqrt h.le
  have hs0 : √(a * c - b ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  simp only [ellipticStructure_apply]
  apply Complex.ext
  · simp
    field_simp
    linear_combination v.re * hs
  · simp
    field_simp
    linear_combination v.im * hs

/-- The complex structure depends smoothly on the coefficients where the principal part is
elliptic. -/
private theorem contDiffAt_ellipticStructure {q : ℝ × ℝ × ℝ}
    (hq : 0 < q.1 * q.2.2 - q.2.1 ^ 2) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ × ℝ ↦ ellipticStructure q.1 q.2.1 q.2.2) q := by
  have hD : ContDiff ℝ 2 fun q : ℝ × ℝ × ℝ ↦ q.1 * q.2.2 - q.2.1 ^ 2 := by fun_prop
  have hM : ContDiff ℝ 2 fun q : ℝ × ℝ × ℝ ↦
      reCLM.smulRight ((q.2.1 : ℂ) + q.2.2 * I) + imCLM.smulRight (-(q.1 : ℂ) - q.2.1 * I) := by
    have hof : ContDiff ℝ 2 fun x : ℝ ↦ (x : ℂ) := ofRealCLM.contDiff
    have h₁ : ContDiff ℝ 2 fun q : ℝ × ℝ × ℝ ↦ (q.2.1 : ℂ) + q.2.2 * I := by fun_prop
    have h₂ : ContDiff ℝ 2 fun q : ℝ × ℝ × ℝ ↦ -(q.1 : ℂ) - q.2.1 * I := by fun_prop
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ ℂ reCLM).contDiff.comp h₁).add
      ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ ℂ imCLM).contDiff.comp h₂)
  exact (((Real.contDiffAt_sqrt hq.ne').comp q hD.contDiffAt).inv
    (Real.sqrt_pos.mpr hq).ne').smul hM.contDiffAt

end Structure

/-! ### The principal part in isothermal coordinates -/

section Chart

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The trace of a symmetric bilinear form against the matrix `[[a, b], [b, c]]`, in a frame
`p, q` which the conformal relations of the chart make orthogonal of equal length, is a multiple of
its trace against the identity. -/
private theorem elliptic_trace_eq (B : ℂ →L[ℝ] ℂ →L[ℝ] X) (hB : ∀ v w, B v w = B w v)
    {a b c s : ℝ} {p q : ℂ} (h₁ : b • p + c • q = s • (I * p))
    (h₂ : a • p + b • q = -(s • (I * q))) :
    a • B p p + (2 * b) • B p q + c • B q q =
      (s * (p.re * q.im - q.re * p.im)) • (B 1 1 + B I I) := by
  calc a • B p p + (2 * b) • B p q + c • B q q = B p (a • p + b • q) + B q (b • p + c • q) := by
        simp only [map_add, map_smul, hB q p]
        module
    _ = s • (B q (I * p) - B p (I * q)) := by
        rw [h₁, h₂, map_neg, map_smul, map_smul, smul_sub]
        abel
    _ = (s * (p.re * q.im - q.re * p.im)) • (B 1 1 + B I I) := by
        obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, p = x • (1 : ℂ) + y • I := ⟨p.re, p.im, by simp⟩
        obtain ⟨x', y', rfl⟩ : ∃ x y : ℝ, q = x • (1 : ℂ) + y • I := ⟨q.re, q.im, by simp⟩
        have hI (x y : ℝ) : I * (x • (1 : ℂ) + y • I) = (-y) • (1 : ℂ) + x • I := by
          apply Complex.ext <;> simp
        simp only [hI, map_add, map_smul, add_apply,
          smul_apply, hB I 1]
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
          Complex.I_re, Complex.I_im]
        module

/-- **The principal part in isothermal coordinates.** If `e` is `C²` at `z` and its derivative
intertwines the complex structure of the principal part `a ∂ₛ² + 2 b ∂ₛ∂ₜ + c ∂ₜ²` with
multiplication by `i`, then for every `v` that is `C²` at `e z` the principal part of `v ∘ e` at
`z` is `(a c - b²)^(1/2) det De(z)` times the Laplacian of `v` at `e z`, plus the first-order term
`Dv(e z) (a e_ss + 2 b e_st + c e_tt)`. -/
theorem elliptic_comp_eq_smul_laplacian_add {v : ℂ → X} {e : ℂ → ℂ} {z : ℂ}
    (hv : ContDiffAt ℝ 2 v (e z)) (he : ContDiffAt ℝ 2 e z) {a b c : ℝ} (hD : 0 < a * c - b ^ 2)
    (hJ : ∀ w, fderiv ℝ e z (ellipticStructure a b c w) = I * fderiv ℝ e z w) :
    a • fderiv ℝ (fderiv ℝ (v ∘ e)) z 1 1 + (2 * b) • fderiv ℝ (fderiv ℝ (v ∘ e)) z 1 I +
        c • fderiv ℝ (fderiv ℝ (v ∘ e)) z I I =
      (√(a * c - b ^ 2) * LinearMap.det (fderiv ℝ e z : ℂ →ₗ[ℝ] ℂ)) • Δ v (e z) +
        fderiv ℝ v (e z) (a • fderiv ℝ (fderiv ℝ e) z 1 1 +
          (2 * b) • fderiv ℝ (fderiv ℝ e) z 1 I + c • fderiv ℝ (fderiv ℝ e) z I I) := by
  rw [LinearMap.det_complex, ContinuousLinearMap.coe_coe]
  set P := fderiv ℝ e z
  set B := fderiv ℝ (fderiv ℝ v) (e z)
  have hs : √(a * c - b ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  -- The chart condition at `1` and at `i`.
  have hbc : ((b : ℂ) + c * I) = b • (1 : ℂ) + c • I := by simp
  have hab : (-(a : ℂ) - b * I) = -(a • (1 : ℂ) + b • I) := by simp; ring
  have h₁ : b • P 1 + c • P I = √(a * c - b ^ 2) • (I * P 1) := by
    have h := hJ 1
    simp only [ellipticStructure_apply, Complex.one_re, Complex.one_im, one_smul, zero_smul,
      add_zero, hbc, map_smul, map_add] at h
    exact (inv_smul_eq_iff₀ hs).mp h
  have h₂ : a • P 1 + b • P I = -(√(a * c - b ^ 2) • (I * P I)) := by
    have h := hJ I
    simp only [ellipticStructure_apply, Complex.I_re, Complex.I_im, one_smul, zero_smul,
      zero_add, hab, map_smul, map_add, map_neg] at h
    exact neg_eq_iff_eq_neg.mp ((inv_smul_eq_iff₀ hs).mp h)
  have hΔ : Δ v (e z) = B 1 1 + B I I := by
    rw [laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, B]
  rw [fderiv_fderiv_comp_apply hv he, fderiv_fderiv_comp_apply hv he,
    fderiv_fderiv_comp_apply hv he, hΔ,
    ← elliptic_trace_eq B (hv.isSymmSndFDerivAt (by simp)) h₁ h₂]
  simp only [map_add, map_smul, smul_add]
  abel

/-- **Isothermal coordinates for an elliptic principal part.** If the coefficients `a, b, c` are
`C^{1,α}` on an open set `Ω`, `0 < α < 1`, and `a c - b² > 0` at `z₀ ∈ Ω`, then `z₀` has a
centred `C²` chart with `C²` inverse, with source in `Ω` on which `a c - b² > 0`, whose derivative
intertwines the complex structure of the principal part with multiplication by `i`. -/
theorem exists_isothermal_chart_of_elliptic {Ω : Set ℂ} (hΩ : IsOpen Ω) {a b c : ℂ → ℝ}
    {α Ha Hb Hc : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) (ha : ContDiffOn ℝ 1 a Ω)
    (haH : HolderOnWith Ha α (fderiv ℝ a) Ω) (hb : ContDiffOn ℝ 1 b Ω)
    (hbH : HolderOnWith Hb α (fderiv ℝ b) Ω) (hc : ContDiffOn ℝ 1 c Ω)
    (hcH : HolderOnWith Hc α (fderiv ℝ c) Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hell : 0 < a z₀ * c z₀ - b z₀ ^ 2) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ e.source ∧ e z₀ = 0 ∧ e.source ⊆ Ω ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      ∀ z ∈ e.source, 0 < a z * c z - b z ^ 2 ∧
        ∀ w, fderiv ℝ e z (ellipticStructure (a z) (b z) (c z) w) = I * fderiv ℝ e z w := by
  -- The coefficient map `p = (a, b, c)` is `C^{1,α}` on `Ω`.
  set p : ℂ → ℝ × ℝ × ℝ := fun z ↦ (a z, b z, c z)
  have hp : ContDiffOn ℝ 1 p Ω := ha.prodMk (hb.prodMk hc)
  have hpH : HolderOnWith (max Ha (max Hb Hc)) α (fderiv ℝ p) Ω := by
    open ContinuousLinearMap in
    refine ((prodₗᵢ ℝ).isometry.comp_holderOnWith
      (haH.prodMk ((prodₗᵢ ℝ).isometry.comp_holderOnWith (hbH.prodMk hcH)))).congr
        fun z hz ↦ ?_
    have hd (f : ℂ → ℝ) (hf : ContDiffOn ℝ 1 f Ω) : DifferentiableAt ℝ f z :=
      (hf.contDiffAt (hΩ.mem_nhds hz)).differentiableAt one_ne_zero
    rw [(hd a ha).fderiv_prodMk ((hd b hb).prodMk (hd c hc)), (hd b hb).fderiv_prodMk (hd c hc)]
    rfl
  -- So is the complex structure `J = Φ ∘ p` near `z₀`, and it squares to `-1` where `D > 0`.
  obtain ⟨r, hr, hrΩ, hJ, H, hJH⟩ := exists_ball_contDiffOn_holderOnWith_fderiv_comp hα1.le
    (hΩ.mem_nhds hz₀) hp hpH (contDiffAt_ellipticStructure (q := p z₀) hell)
  have hDc : ContinuousAt (fun z ↦ a z * c z - b z ^ 2) z₀ := by
    have h (f : ℂ → ℝ) (hf : ContDiffOn ℝ 1 f Ω) : ContinuousAt f z₀ :=
      hf.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
    exact ((h a ha).mul (h c hc)).sub ((h b hb).pow 2)
  have hU : Metric.ball z₀ r ∩ {z | 0 < a z * c z - b z ^ 2} ∈ 𝓝 z₀ :=
    inter_mem (Metric.ball_mem_nhds z₀ hr) (continuousAt_const.eventually_lt hDc hell)
  obtain ⟨e, hce, he0, heU, he2, hes2, -, -, heJ⟩ := Beltrami.exists_isothermal_chart_ckHolder 1
    hα0 hα1 hU (hJ.mono inter_subset_left)
    (holderOnWith_iteratedFDeriv_one_iff.mpr (hJH.mono inter_subset_left))
    fun z hz v ↦ ellipticStructure_ellipticStructure hz.2 v
  exact ⟨e, hce, he0, fun z hz ↦ hrΩ (heU hz).1, by exact_mod_cast he2, by exact_mod_cast hes2,
    fun z hz ↦ ⟨(heU hz).2, heJ z hz⟩⟩

end Chart

/-! ### Pulling the expansion back along a chart -/

section Pullback

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Complexification

/-- The derivative of `w ↦ Re (w ^ k • c)` at `y` sends `h` to `Re ((k h y ^ (k - 1)) • c)`. -/
private theorem fderiv_re_pow_smul_apply (k : ℕ) (c : Complexification X) (y h : ℂ) :
    fderiv ℝ (fun w ↦ (w ^ k • c).re) y h = (h • ((k : ℂ) * y ^ (k - 1)) • c).re := by
  simpa using fderiv_re_sub_pow_smul_apply k c 0 y h

/-- The norm of `Re ((k h w) • c)` is at most `k ‖c‖ ‖w‖ ‖h‖`. -/
private theorem norm_re_smul_natCast_mul_smul_le (k : ℕ) (c : Complexification X) (h w : ℂ) :
    ‖(h • ((k : ℂ) * w) • c).re‖ ≤ k * ‖c‖ * ‖w‖ * ‖h‖ := by
  refine (norm_re_le _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, norm_mul, Complex.norm_natCast]
  ring

/-- The derivative of `w ↦ Re (w ^ k • c)` at `y` is bounded by `k ‖c‖ ‖y ^ (k - 1)‖`. -/
private theorem norm_fderiv_re_pow_smul_le (k : ℕ) (c : Complexification X) (y : ℂ) :
    ‖fderiv ℝ (fun w ↦ (w ^ k • c).re) y‖ ≤ k * ‖c‖ * ‖y ^ (k - 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [fderiv_re_pow_smul_apply]
  exact norm_re_smul_natCast_mul_smul_le k c h _

/-- The derivative of `w ↦ Re (w ^ k • c)` changes by at most
`k ‖c‖ ‖y ^ (k - 1) - y' ^ (k - 1)‖` from `y` to `y'`. -/
private theorem norm_fderiv_re_pow_smul_sub_le (k : ℕ) (c : Complexification X) (y y' : ℂ) :
    ‖fderiv ℝ (fun w ↦ (w ^ k • c).re) y - fderiv ℝ (fun w ↦ (w ^ k • c).re) y'‖ ≤
      k * ‖c‖ * ‖y ^ (k - 1) - y' ^ (k - 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [sub_apply, fderiv_re_pow_smul_apply, fderiv_re_pow_smul_apply, ← Complexification.sub_re,
    ← smul_sub, ← sub_smul, ← mul_sub]
  exact norm_re_smul_natCast_mul_smul_le k c h _

/-- If `e z₀ = 0` and `e` has derivative `T` at `z₀`, then `e z = T (z - z₀) + o(‖z - z₀‖)` and
`e z = O(‖z - z₀‖)`. -/
private theorem isLittleO_sub_apply_sub_and_isBigO {e : ℂ → ℂ} {z₀ : ℂ} {T : ℂ →L[ℝ] ℂ}
    (hTd : HasFDerivAt e T z₀) (he₀ : e z₀ = 0) :
    (fun z ↦ e z - T (z - z₀)) =o[𝓝 z₀] (fun z ↦ ‖z - z₀‖) ∧
      e =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ :=
  ⟨by simpa [he₀] using hTd.isLittleO.norm_right,
    by simpa [he₀] using hTd.isBigO_sub.norm_right⟩

/-- **The leading polynomial pulls back along a differentiable map.** If `e z₀ = 0`, `e` has
derivative `T` at `z₀`, `v w = Re (w ^ k • c) + o(‖w‖ ^ k)` at `0` and `u = v ∘ e` near `z₀`, then
`u z = Re ((T (z - z₀)) ^ k • c) + o(‖z - z₀‖ ^ k)`. -/
private theorem isLittleO_sub_re_pow_smul_of_eventuallyEq_comp {u v : ℂ → X} {e : ℂ → ℂ}
    {z₀ : ℂ} {T : ℂ →L[ℝ] ℂ} (hTd : HasFDerivAt e T z₀) (he₀ : e z₀ = 0)
    (huv : u =ᶠ[𝓝 z₀] v ∘ e) {k : ℕ} {c : Complexification X}
    (h₀ : (fun w ↦ v w - (w ^ k • c).re) =o[𝓝 0] fun w ↦ ‖w‖ ^ k) :
    (fun z ↦ u z - ((T (z - z₀)) ^ k • c).re) =o[𝓝 z₀] (fun z ↦ ‖z - z₀‖ ^ k) := by
  obtain ⟨hlin, heO⟩ := isLittleO_sub_apply_sub_and_isBigO hTd he₀
  -- `u z = v (e z)`, and `Re (w ^ k • c)` moves by `o(‖z - z₀‖ ^ k)` from `e z` to `T (z - z₀)`.
  have hA := (h₀.comp_tendsto (he₀ ▸ hTd.continuousAt.tendsto)).trans_isBigO
    (heO.norm_left.pow k)
  have hB : (fun z ↦ ((e z) ^ k • c).re - ((T (z - z₀)) ^ k • c).re) =o[𝓝 z₀]
      fun z ↦ ‖z - z₀‖ ^ k := by
    refine (IsBigO.of_bound ‖c‖ (Eventually.of_forall fun z ↦ ?_)).trans_isLittleO
      (hlin.pow_sub_pow heO (T.isBigO_sub _ _).norm_right k)
    rw [← Complexification.sub_re, ← sub_smul, mul_comm]
    exact (norm_re_le _).trans (norm_smul_le _ _)
  refine (hA.add hB).congr' (huv.mono fun z hz ↦ ?_) EventuallyEq.rfl
  simp [hz]

/-- **The derivative asymptotic pulls back along a `C¹` map.** If `e` is differentiable near `z₀`
with `e z₀ = 0`, derivative `T` at `z₀` and derivative continuous at `z₀`, `v` is differentiable
near `0` with `Dv(w) = D (Re (· ^ k • c)) (w) + o(‖w‖ ^ (k - 1))`, and `u = v ∘ e` near `z₀`,
then `Du(z) = D (Re ((T (· - z₀)) ^ k • c)) (z) + o(‖z - z₀‖ ^ (k - 1))`. -/
private theorem isLittleO_fderiv_sub_fderiv_re_pow_smul_of_eventuallyEq_comp {u v : ℂ → X}
    {e : ℂ → ℂ} {z₀ : ℂ} {T : ℂ →L[ℝ] ℂ} (he : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ e z)
    (he₀ : e z₀ = 0) (hT : fderiv ℝ e z₀ = T) (hDe : ContinuousAt (fderiv ℝ e) z₀)
    (hv : ∀ᶠ w in 𝓝 0, DifferentiableAt ℝ v w) (huv : u =ᶠ[𝓝 z₀] v ∘ e) {k : ℕ}
    {c : Complexification X}
    (h₁ : (fun w ↦ fderiv ℝ v w - fderiv ℝ (fun y ↦ (y ^ k • c).re) w) =o[𝓝 0]
      fun w ↦ ‖w‖ ^ (k - 1)) :
    (fun z ↦ fderiv ℝ u z - fderiv ℝ (fun w ↦ ((T (w - z₀)) ^ k • c).re) z) =o[𝓝 z₀]
      fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
  have hTd : HasFDerivAt e T z₀ := hT ▸ he.self_of_nhds.hasFDerivAt
  obtain ⟨hlin, heO⟩ := isLittleO_sub_apply_sub_and_isBigO hTd he₀
  have hTO : (fun z ↦ T (z - z₀)) =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ := (T.isBigO_sub _ _).norm_right
  have htend : Tendsto e (𝓝 z₀) (𝓝 0) := he₀ ▸ hTd.continuousAt.tendsto
  set G := fderiv ℝ (fun w : ℂ ↦ (w ^ k • c).re)
  -- The chain rule on both sides.
  have hfP (z : ℂ) :
      fderiv ℝ (fun w ↦ ((T (w - z₀)) ^ k • c).re) z = (G (T (z - z₀))).comp T := by
    have hin : HasFDerivAt (fun w ↦ T (w - z₀)) T z :=
      (T.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const z₀)).congr_fderiv (by simp)
    exact ((by simpa using (hasFDerivAt_re_sub_pow_smul k c 0 _).differentiableAt :
      DifferentiableAt ℝ (fun w : ℂ ↦ (w ^ k • c).re) (T (z - z₀))).hasFDerivAt.comp z hin).fderiv
  have hfu : ∀ᶠ z in 𝓝 z₀, fderiv ℝ u z = (fderiv ℝ v (e z)).comp (fderiv ℝ e z) := by
    filter_upwards [huv.eventually_nhds, he, htend.eventually hv] with z hz hez hvz
    rw [EventuallyEq.fderiv_eq hz, fderiv_comp z hvz hez]
  have hDeO : (fun z ↦ fderiv ℝ e z) =O[𝓝 z₀] fun _ ↦ (1 : ℝ) := hDe.tendsto.isBigO_one ℝ
  -- A composite of linear maps is `o(g)` when the product of their norms is.
  have hcomp {A : ℂ → ℂ →L[ℝ] X} {B : ℂ → ℂ →L[ℝ] ℂ} {g : ℂ → ℝ}
      (h : (fun z ↦ ‖A z‖ * ‖B z‖) =o[𝓝 z₀] g) : (fun z ↦ (A z).comp (B z)) =o[𝓝 z₀] g :=
    (((ContinuousLinearMap.compL ℝ ℂ ℂ X).isBoundedBilinearMap.isBigO_comp (g := A) (h := B)
      (l := 𝓝 z₀)).congr_left fun z ↦ by simp).trans_isLittleO h
  -- The difference splits as `(Dv - G)(e z) ∘ De z + (G (e z) - G (T (z - z₀))) ∘ De z`
  -- `+ G (T (z - z₀)) ∘ (De z - T)`, and each term is `o(‖z - z₀‖ ^ (k - 1))`.
  have h1 : (fun z ↦ (fderiv ℝ v (e z) - G (e z)).comp (fderiv ℝ e z)) =o[𝓝 z₀]
      fun z ↦ ‖z - z₀‖ ^ (k - 1) :=
    hcomp <| (((h₁.comp_tendsto htend).trans_isBigO
      (heO.norm_left.pow (k - 1))).norm_left.mul_isBigO hDeO.norm_left).congr_right
        fun _ ↦ mul_one _
  have h2 : (fun z ↦ (G (e z) - G (T (z - z₀))).comp (fderiv ℝ e z)) =o[𝓝 z₀]
      fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
    refine hcomp <| (IsLittleO.mul_isBigO ?_
      hDeO.norm_left).congr_right fun _ ↦ mul_one _
    refine (IsBigO.of_bound (k * ‖c‖) (Eventually.of_forall fun z ↦ ?_)).trans_isLittleO
      (hlin.pow_sub_pow heO hTO (k - 1))
    rw [norm_norm]
    exact norm_fderiv_re_pow_smul_sub_le k c _ _
  have h3 : (fun z ↦ (G (T (z - z₀))).comp (fderiv ℝ e z - T)) =o[𝓝 z₀]
      fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
    refine hcomp <| (IsBigO.mul_isLittleO ?_
      ((isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr (hT ▸ hDe.tendsto))).norm_left
        ).congr_right fun _ ↦ mul_one _
    refine (IsBigO.of_bound (k * ‖c‖) (Eventually.of_forall fun z ↦ ?_)).trans
      (hTO.norm_left.pow (k - 1))
    rw [norm_norm, Real.norm_of_nonneg (by positivity), ← norm_pow]
    exact norm_fderiv_re_pow_smul_le k c _
  refine ((h1.add h2).add h3).congr' (hfu.mono fun z hz ↦ ?_) EventuallyEq.rfl
  dsimp only
  rw [hz, hfP]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  abel

end Pullback

/-! ### The expansion -/

section Expansion

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A map agrees near each point `z` of the source of `e` with its reading `u ∘ e⁻¹` in the chart,
composed with `e`. -/
private theorem eventuallyEq_comp_symm_comp {Y : Type*} {u : ℂ → Y}
    (e : OpenPartialHomeomorph ℂ ℂ) {z : ℂ} (hz : z ∈ e.source) : u =ᶠ[𝓝 z] (u ∘ e.symm) ∘ e :=
  (e.eventually_left_inverse hz).mono fun y hy ↦ by simp [hy]

/-- In an isothermal chart `e` of the principal part, `u` and `v = u ∘ e⁻¹` are related at each
point `z` of the source by `a u_ss + 2 b u_st + c u_tt = λ Δv(e z) + Dv(e z) (a e_ss + 2 b e_st +
c e_tt)` and `Du(z) = Dv(e z) ∘ De(z)`. -/
private theorem elliptic_eq_and_fderiv_eq_of_mem_source {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {a b c : ℂ → ℝ} {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω) {e : OpenPartialHomeomorph ℂ ℂ}
    (heΩ : e.source ⊆ Ω) (he2 : ContDiffOn ℝ 2 e e.source)
    (hes2 : ContDiffOn ℝ 2 e.symm e.target)
    (heJ : ∀ z ∈ e.source, 0 < a z * c z - b z ^ 2 ∧
      ∀ w, fderiv ℝ e z (ellipticStructure (a z) (b z) (c z) w) = I * fderiv ℝ e z w)
    {z : ℂ} (hz : z ∈ e.source) :
    a z • fderiv ℝ (fderiv ℝ u) z 1 1 + (2 * b z) • fderiv ℝ (fderiv ℝ u) z 1 I +
        c z • fderiv ℝ (fderiv ℝ u) z I I =
      (√(a z * c z - b z ^ 2) * LinearMap.det (fderiv ℝ e z : ℂ →ₗ[ℝ] ℂ)) •
          Δ (u ∘ e.symm) (e z) +
        fderiv ℝ (u ∘ e.symm) (e z) (a z • fderiv ℝ (fderiv ℝ e) z 1 1 +
          (2 * b z) • fderiv ℝ (fderiv ℝ e) z 1 I + c z • fderiv ℝ (fderiv ℝ e) z I I) ∧
      fderiv ℝ u z = (fderiv ℝ (u ∘ e.symm) (e z)).comp (fderiv ℝ e z) := by
  have hez : ContDiffAt ℝ 2 e z := he2.contDiffAt (e.open_source.mem_nhds hz)
  have hv : ContDiffAt ℝ 2 (u ∘ e.symm) (e z) := by
    refine ContDiffAt.comp (e z) ?_ (hes2.contDiffAt (e.open_target.mem_nhds (e.map_source hz)))
    rw [e.left_inv hz]
    exact hu.contDiffAt (hΩ.mem_nhds (heΩ hz))
  have hev := eventuallyEq_comp_symm_comp (u := u) e hz
  refine ⟨?_, ?_⟩
  · rw [hev.fderiv.fderiv_eq]
    exact elliptic_comp_eq_smul_laplacian_add hv hez (heJ z hz).1 (heJ z hz).2
  · rw [hev.fderiv_eq]
    exact fderiv_comp z (hv.differentiableAt two_ne_zero) (hez.differentiableAt two_ne_zero)

/-- The pointwise estimate behind `exists_laplacian_bound_comp_symm`: at a point `z` of the source
of an isothermal chart `e` at which `|λ z| ≥ m > 0`, `‖a e_ss + 2 b e_st + c e_tt‖ ≤ M₁` and
`‖De(z)‖ ≤ M₂`, the Laplacian of `v = u ∘ e⁻¹` at `e z` is bounded by
`(|K| (1 + M₂) + M₁) / m` times `‖v‖ + ‖Dv‖`. -/
private theorem norm_laplacian_comp_symm_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {a b c : ℂ → ℝ}
    {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω) {K : ℝ}
    (hK : ∀ z ∈ Ω, ‖a z • fderiv ℝ (fderiv ℝ u) z 1 1 + (2 * b z) • fderiv ℝ (fderiv ℝ u) z 1 I +
      c z • fderiv ℝ (fderiv ℝ u) z I I‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖))
    {e : OpenPartialHomeomorph ℂ ℂ} (heΩ : e.source ⊆ Ω) (he2 : ContDiffOn ℝ 2 e e.source)
    (hes2 : ContDiffOn ℝ 2 e.symm e.target)
    (heJ : ∀ z ∈ e.source, 0 < a z * c z - b z ^ 2 ∧
      ∀ w, fderiv ℝ e z (ellipticStructure (a z) (b z) (c z) w) = I * fderiv ℝ e z w)
    {z : ℂ} (hz : z ∈ e.source) {m M₁ M₂ : ℝ} (hm : 0 < m)
    (hΛ : m ≤ |√(a z * c z - b z ^ 2) * LinearMap.det (fderiv ℝ e z : ℂ →ₗ[ℝ] ℂ)|)
    (hL : ‖a z • fderiv ℝ (fderiv ℝ e) z 1 1 + (2 * b z) • fderiv ℝ (fderiv ℝ e) z 1 I +
      c z • fderiv ℝ (fderiv ℝ e) z I I‖ ≤ M₁) (hD : ‖fderiv ℝ e z‖ ≤ M₂) :
    ‖Δ (u ∘ e.symm) (e z)‖ ≤ (|K| * (1 + M₂) + M₁) / m *
      (‖(u ∘ e.symm) (e z)‖ + ‖fderiv ℝ (u ∘ e.symm) (e z)‖) := by
  obtain ⟨hid, hDu⟩ := elliptic_eq_and_fderiv_eq_of_mem_source hΩ hu heΩ he2 hes2 heJ hz
  set Dv := fderiv ℝ (u ∘ e.symm) (e z)
  have hvz : (u ∘ e.symm) (e z) = u z := by simp [e.left_inv hz]
  have hDuz : ‖fderiv ℝ u z‖ ≤ ‖Dv‖ * M₂ := by
    rw [hDu]
    exact (Dv.opNorm_comp_le _).trans (by gcongr)
  -- `λ z • Δv = (a u_ss + 2 b u_st + c u_tt)(z) - Dv (a e_ss + 2 b e_st + c e_tt)`.
  have hmain : m * ‖Δ (u ∘ e.symm) (e z)‖ ≤ |K| * (‖u z‖ + ‖fderiv ℝ u z‖) + ‖Dv‖ * M₁ := by
    have h := (hK z (heΩ hz)).trans (mul_le_mul_of_nonneg_right (le_abs_self K)
      (by positivity))
    rw [hid] at h
    refine (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _)).trans ?_
    rw [← Real.norm_eq_abs, ← norm_smul]
    exact (norm_le_add_norm_add _ _).trans (add_le_add h ((Dv.le_opNorm _).trans (by gcongr)))
  rw [hvz, div_mul_eq_mul_div, le_div_iff₀ hm]
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans hL
  have h1 := norm_nonneg (u z)
  have h2 := norm_nonneg Dv
  have h3 := abs_nonneg K
  nlinarith [mul_le_mul_of_nonneg_left hDuz h3, mul_nonneg h3 h1, mul_nonneg h3 h2,
    mul_nonneg (mul_nonneg h3 ((norm_nonneg _).trans hD)) h1, mul_nonneg hM₁ h1]

/-- In an isothermal chart `e` of the principal part, the differential inequality for `u` becomes
`‖Δv‖ ≤ K' (‖v‖ + ‖Dv‖)` for `v = u ∘ e⁻¹` on an open neighbourhood of `e z₀`. -/
private theorem exists_laplacian_bound_comp_symm {Ω : Set ℂ} (hΩ : IsOpen Ω) {a b c : ℂ → ℝ}
    (ha : ContinuousOn a Ω) (hb : ContinuousOn b Ω) (hc : ContinuousOn c Ω) {u : ℂ → X}
    (hu : ContDiffOn ℝ 2 u Ω) {K : ℝ}
    (hK : ∀ z ∈ Ω, ‖a z • fderiv ℝ (fderiv ℝ u) z 1 1 + (2 * b z) • fderiv ℝ (fderiv ℝ u) z 1 I +
      c z • fderiv ℝ (fderiv ℝ u) z I I‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖))
    {e : OpenPartialHomeomorph ℂ ℂ} {z₀ : ℂ} (hce : z₀ ∈ e.source) (heΩ : e.source ⊆ Ω)
    (he2 : ContDiffOn ℝ 2 e e.source) (hes2 : ContDiffOn ℝ 2 e.symm e.target)
    (heJ : ∀ z ∈ e.source, 0 < a z * c z - b z ^ 2 ∧
      ∀ w, fderiv ℝ e z (ellipticStructure (a z) (b z) (c z) w) = I * fderiv ℝ e z w) :
    ∃ Ω' : Set ℂ, IsOpen Ω' ∧ e z₀ ∈ Ω' ∧ Ω' ⊆ e.target ∧ ∃ K' : ℝ, ∀ w ∈ Ω',
      ‖Δ (u ∘ e.symm) w‖ ≤ K' * (‖(u ∘ e.symm) w‖ + ‖fderiv ℝ (u ∘ e.symm) w‖) := by
  set Λ : ℂ → ℝ := fun z ↦ √(a z * c z - b z ^ 2) * LinearMap.det (fderiv ℝ e z : ℂ →ₗ[ℝ] ℂ)
  set L : ℂ → ℂ := fun z ↦ a z • fderiv ℝ (fderiv ℝ e) z 1 1 +
    (2 * b z) • fderiv ℝ (fderiv ℝ e) z 1 I + c z • fderiv ℝ (fderiv ℝ e) z I I
  have hsrc : e.source ∈ 𝓝 z₀ := e.open_source.mem_nhds hce
  have hΩz : Ω ∈ 𝓝 z₀ := hΩ.mem_nhds (heΩ hce)
  -- `Λ` does not vanish at `z₀`, and `Λ`, `L` and `De` are continuous there.
  have hΛ0 : Λ z₀ ≠ 0 := by
    obtain ⟨T, hT⟩ := e.isInvertible_fderiv_of_contDiffOn he2 hes2 two_ne_zero hce
    refine mul_ne_zero (Real.sqrt_pos.mpr (heJ z₀ hce).1).ne' ?_
    rw [← hT]
    exact (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  have hDe : ContinuousAt (fderiv ℝ e) z₀ := (he2.contDiffAt hsrc).continuousAt_fderiv two_ne_zero
  have hD2 : ContinuousAt (fderiv ℝ (fderiv ℝ e)) z₀ :=
    (he2.contDiffAt hsrc).continuousAt_fderiv_fderiv le_rfl
  have ha' := ha.continuousAt hΩz
  have hb' := hb.continuousAt hΩz
  have hc' := hc.continuousAt hΩz
  have hΛc : ContinuousAt Λ z₀ :=
    (by fun_prop : ContinuousAt (fun z ↦ √(a z * c z - b z ^ 2)) z₀).mul
      (ContinuousLinearMap.continuous_det.continuousAt.comp hDe)
  have hLc : ContinuousAt L z₀ := by fun_prop
  have hm : 0 < |Λ z₀| / 2 := half_pos (abs_pos.mpr hΛ0)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.mp <| (eventually_mem_set.2 hsrc).and <|
    (hΛc.abs.eventually_const_lt (half_lt_self (abs_pos.mpr hΛ0))).and <|
      (hLc.norm.eventually_lt_const (lt_add_one _)).and
        (hDe.norm.eventually_lt_const (lt_add_one _))
  refine ⟨e.target ∩ e.symm ⁻¹' Metric.ball z₀ ρ, e.isOpen_inter_preimage_symm Metric.isOpen_ball,
    ⟨e.map_source hce, by simp [e.left_inv hce, hρ]⟩, inter_subset_left,
    (|K| * (1 + (‖fderiv ℝ e z₀‖ + 1)) + (‖L z₀‖ + 1)) / (|Λ z₀| / 2), fun w hw ↦ ?_⟩
  obtain ⟨hzs, hΛz, hLz, hDz⟩ := hρs _ hw.2
  rw [← e.right_inv hw.1]
  exact norm_laplacian_comp_symm_le hΩ hu hK heΩ he2 hes2 heJ hzs hm hΛz.le hLz.le hDz.le

variable [FiniteDimensional ℝ X]

/-- **The Hartman–Wintner expansion for a variable elliptic principal part.** Let `0 < α < 1`, let
`a, b, c : ℂ → ℝ` be `C¹` with `α`-Hölder derivatives on an open set `Ω`, and let `u : ℂ → X` be a
`C²` map into a finite-dimensional real normed space with

`‖a u_ss + 2 b u_st + c u_tt‖ ≤ K (‖u‖ + ‖Du‖)`

on `Ω`, where `u_ss`, `u_st` and `u_tt` are the second derivatives in the directions `1` and `i`.
At a zero `z₀ ∈ Ω` of `u` at which the principal part is elliptic, `a c - b² > 0`, either `u`
vanishes near `z₀`, or there are `k ≥ 1`, a nonzero `c'` in the complexification of `X` and a
real-linear automorphism `T` of the plane, carrying the complex structure
`ellipticStructure (a z₀) (b z₀) (c z₀)` of the frozen principal part to multiplication by `i`,
such that `u` is the nonzero homogeneous polynomial
`Re ((T (z - z₀)) ^ k • c')` of degree `k` up to `o(‖z - z₀‖ ^ k)`, and its derivative is the
derivative of that polynomial up to `o(‖z - z₀‖ ^ (k - 1))`. -/
theorem eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul_of_elliptic {Ω : Set ℂ}
    (hΩ : IsOpen Ω) {a b c : ℂ → ℝ} {α Ha Hb Hc : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (ha : ContDiffOn ℝ 1 a Ω) (haH : HolderOnWith Ha α (fderiv ℝ a) Ω)
    (hb : ContDiffOn ℝ 1 b Ω) (hbH : HolderOnWith Hb α (fderiv ℝ b) Ω)
    (hc : ContDiffOn ℝ 1 c Ω) (hcH : HolderOnWith Hc α (fderiv ℝ c) Ω)
    {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω) {K : ℝ}
    (hK : ∀ z ∈ Ω, ‖a z • fderiv ℝ (fderiv ℝ u) z 1 1 + (2 * b z) • fderiv ℝ (fderiv ℝ u) z 1 I +
      c z • fderiv ℝ (fderiv ℝ u) z I I‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hell : 0 < a z₀ * c z₀ - b z₀ ^ 2) (hu₀ : u z₀ = 0) :
    (∀ᶠ z in 𝓝 z₀, u z = 0) ∨ ∃ (k : ℕ) (c' : Complexification X) (T : ℂ ≃L[ℝ] ℂ),
      0 < k ∧ c' ≠ 0 ∧ (∀ w, T (ellipticStructure (a z₀) (b z₀) (c z₀) w) = I * T w) ∧
      (fun z ↦ u z - ((T (z - z₀)) ^ k • c').re) =o[𝓝 z₀] (fun z ↦ ‖z - z₀‖ ^ k) ∧
      (fun z ↦ fderiv ℝ u z - fderiv ℝ (fun w ↦ ((T (w - z₀)) ^ k • c').re) z) =o[𝓝 z₀]
        fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
  -- Read `u` in an isothermal chart `e` of the principal part, centred at `z₀`.
  obtain ⟨e, hce, he0, heΩ, he2, hes2, heJ⟩ :=
    exists_isothermal_chart_of_elliptic hΩ hα0 hα1 ha haH hb hbH hc hcH hz₀ hell
  obtain ⟨Ω', hΩ', h0Ω', hΩ't, K', hK'⟩ := exists_laplacian_bound_comp_symm hΩ ha.continuousOn
    hb.continuousOn hc.continuousOn hu hK hce heΩ he2 hes2 heJ
  have hv2 : ContDiffOn ℝ 2 (u ∘ e.symm) Ω' :=
    hu.comp (hes2.mono hΩ't) fun w hw ↦ heΩ (e.map_target (hΩ't hw))
  have huv := eventuallyEq_comp_symm_comp (u := u) e hce
  -- Apply the expansion for the Laplacian to `v = u ∘ e⁻¹` at `e z₀ = 0`.
  rcases eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul hΩ' hv2 hK' h0Ω'
      (by simp [e.left_inv hce, hu₀]) with h0 | ⟨k, c', hk, hc', h₀, h₁⟩
  · exact .inl (huv.trans ((e.continuousAt hce).eventually h0))
  obtain ⟨T, hT⟩ := e.isInvertible_fderiv_of_contDiffOn he2 hes2 two_ne_zero hce
  rw [he0] at h₀ h₁
  simp only [sub_zero] at h₀ h₁
  have hDe : ContinuousAt (fderiv ℝ e) z₀ :=
    (he2.contDiffAt (e.open_source.mem_nhds hce)).continuousAt_fderiv two_ne_zero
  have he : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ e z :=
    eventually_of_mem (e.open_source.mem_nhds hce) fun z hz ↦
      (he2.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt two_ne_zero
  refine .inr ⟨k, c', T, hk, hc', fun w ↦ by
    have h := (heJ z₀ hce).2 w
    rw [← hT] at h
    exact h,
    isLittleO_sub_re_pow_smul_of_eventuallyEq_comp (hT ▸ he.self_of_nhds.hasFDerivAt) he0 huv h₀,
    isLittleO_fderiv_sub_fderiv_re_pow_smul_of_eventuallyEq_comp he he0 hT.symm hDe
      (eventually_of_mem (hΩ'.mem_nhds (he0 ▸ h0Ω')) fun w hw ↦
        (hv2.contDiffAt (hΩ'.mem_nhds hw)).differentiableAt two_ne_zero) huv h₁⟩

end Expansion

end TauCeti
