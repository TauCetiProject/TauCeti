/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.Normed.Lp.DiscreteConvolution

/-!
# Products on the circle Sobolev spaces `H^s` for `s > 1/2`

For `s > 1/2` the Fourier-coefficient Sobolev space `H^s` of the circle is an algebra: the
product of two functions corresponds to the convolution of their Fourier coefficients, and
convolution maps `H^s × H^s` boundedly to `H^s`. More generally, a continuous bilinear map
`L : E →L[ℂ] E' →L[ℂ] F` induces a bounded bilinear map `H^s(E) × H^s(E') → H^s(F)`, which on
continuous representatives is `x ↦ L (a x) (b x)`.

The coefficient estimate is
`DiscreteConvolution.tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le`; this file transfers it
to the spaces `TauCeti.CircleSobolev s E` and identifies the result with pointwise products of the
continuous functions `CircleSobolev.toContinuousMap`.

## Main definitions

* `TauCeti.CircleSobolev.mkCoeffConvolution`: bundles discrete Fourier-coefficient convolution
  through a continuous `𝕜`-bilinear map `B : E →L[𝕜] E' →L[𝕜] F` as a continuous `𝕜`-bilinear
  operator `H^r(E) →L[𝕜] H^t(E') →L[𝕜] H^t(F)`.
* `TauCeti.CircleSobolev.convolution hs L`: for `s > 1/2`, the continuous bilinear map
  `H^s(E) → H^s(E') → H^s(F)` whose coefficients are the discrete convolution
  `a.coeff ⋆₊[L] b.coeff`.
* For a complete normed `ℂ`-algebra `A` and `[Fact (1 / 2 < s)]`, the ring structure on
  `CircleSobolev s A` with this product and unit `single 0 1` (commutative when `A` is), and the
  algebra structure over `ℂ`.
* `TauCeti.CircleSobolev.toContinuousMapAlgHom`: `toContinuousMap` as an algebra homomorphism
  `H^s(A) →ₐ[ℂ] C(AddCircle T, A)`.

## Main statements

* `TauCeti.CircleSobolev.addConvolutionExists_coeff`,
  `TauCeti.CircleSobolev.memℓp_weight_smul_addConvolution_coeff`,
  `TauCeti.CircleSobolev.norm_le_of_coeff_eq_addConvolution`, and
  `TauCeti.CircleSobolev.toContinuousMap_eq_of_coeff_eq_addConvolution`: scalar-generic existence,
  weighted `ℓ²` membership, norm estimates, and double-series pointwise evaluation for Fourier
  coefficient convolutions.
* `TauCeti.CircleSobolev.norm_convolution_le`: the product estimate
  `‖convolution hs L a b‖ ≤ 2 ^ (s + 1) √(∑ₙ (1 + |n|) ^ (-2 s)) ‖L‖ ‖a‖ ‖b‖`.
* `TauCeti.CircleSobolev.toContinuousMap_convolution_apply`: on continuous representatives the
  bilinear map is pointwise, `x ↦ L (a x) (b x)`.
* `TauCeti.CircleSobolev.toContinuousMap_mul` and `TauCeti.CircleSobolev.norm_mul_le`: the product
  of `H^s(A)` is the pointwise product, and
  `‖a * b‖ ≤ 2 ^ (s + 1) √(∑ₙ (1 + |n|) ^ (-2 s)) ‖a‖ ‖b‖`.
* `TauCeti.CircleSobolev.norm_list_prod_le` and `TauCeti.CircleSobolev.norm_pow_le`: the same
  estimate for finite products and powers, `‖a ^ k‖ ≤ mulConst s ^ (k - 1) ‖a‖ ^ k`, where
  `TauCeti.CircleSobolev.mulConst s` is the maximum of `1` and the constant above.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (Sobolev spaces as
  algebras).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (products of boundary maps in Hardy decompositions).
-/

public section

noncomputable section

open scoped DiscreteConvolution

open DiscreteConvolution (AddConvolutionExists AddConvolutionExistsAt
  addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
  summable_sq_one_add_abs_rpow_mul_norm_addConvolution
  tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le)

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem summable_sq_weight_mul_norm_coeff (a : CircleSobolev s E) :
    Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a.coeff n‖) ^ 2 := by
  simpa only [weight_def] using (hasSum_sq_weight_mul_norm_coeff a).summable

/-! ### Scalar-generic Fourier-coefficient convolution -/

section CoeffConvolution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜 F]

omit [NormedSpace ℂ F] in
/-- For `s > 1/2` and a complete target `F`, the discrete convolution of the Fourier coefficients
of `a ∈ H^s(E)` and `b ∈ H^s(E')` through a continuous `𝕜`-bilinear map `L` exists. -/
theorem addConvolutionExists_coeff [CompleteSpace F] (hs : 1 / 2 < s) (L : E →L[𝕜] E' →L[𝕜] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    AddConvolutionExists L.toLinearMap₁₂ a.coeff b.coeff :=
  (addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution L hs
    (summable_sq_weight_mul_norm_coeff a) (summable_sq_weight_mul_norm_coeff b)).1

/-- For `s > 1/2`, the discrete convolution `a.coeff ⋆₊[L] b.coeff` of the Fourier coefficients
of `a ∈ H^s(E)` and `b ∈ H^s(E')` through a continuous `𝕜`-bilinear map `L` is weighted
square-summable of order `s`. -/
theorem memℓp_weight_smul_addConvolution_coeff (hs : 1 / 2 < s) (L : E →L[𝕜] E' →L[𝕜] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    Memℓp (fun n ↦ weight s n • (a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff) n) 2 :=
  (memℓp_weight_smul_iff _).2 <| by
    simpa only [weight_def] using summable_sq_one_add_abs_rpow_mul_norm_addConvolution L hs
      (summable_sq_weight_mul_norm_coeff a) (summable_sq_weight_mul_norm_coeff b)

/-- For `s > 1/2`, any `c ∈ H^s(F)` whose Fourier coefficients are the discrete convolution
`a.coeff ⋆₊[L] b.coeff` for a continuous `𝕜`-bilinear map `L` satisfies
`‖c‖ ≤ 2 ^ (s + 1) √(∑ₙ (1 + |n|) ^ (-2 s)) ‖L‖ ‖a‖ ‖b‖`. -/
theorem norm_le_of_coeff_eq_addConvolution (hs : 1 / 2 < s) (L : E →L[𝕜] E' →L[𝕜] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') {c : CircleSobolev s F}
    (hc : c.coeff = a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff) :
    ‖c‖ ≤ 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
  have hK : 0 ≤ ∑' n, weight (-(2 * s)) n := tsum_nonneg fun n ↦ weight_nonneg _ n
  have h := tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le L hs
    (summable_sq_weight_mul_norm_coeff a) (summable_sq_weight_mul_norm_coeff b)
  simp only [neg_mul, ← weight_def, ← hc] at h
  rw [(hasSum_sq_weight_mul_norm_coeff c).tsum_eq, (hasSum_sq_weight_mul_norm_coeff a).tsum_eq,
    (hasSum_sq_weight_mul_norm_coeff b).tsum_eq] at h
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h.trans_eq ?_)
  have h4 : ((2 : ℝ) ^ (s + 1)) ^ 2 = 4 ^ (s + 1) := by
    rw [sq, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  simp only [mul_pow, Real.sq_sqrt hK, h4]
  ring

/-- Pointwise evaluation of a `CircleSobolev` element whose Fourier coefficients are the
discrete convolution `a.coeff ⋆₊[B] b.coeff` for a continuous `𝕜`-bilinear map `B`, when the
Fourier-weighted terms `e_{m + k}(x) • B (a_m) (b_k)` factor as `B (f₁ m) (f₂ k)` for convergent
series `∑ f₁ = u` and `∑ f₂ = v`. -/
theorem toContinuousMap_eq_of_coeff_eq_addConvolution [CompleteSpace F] (T : ℝ) [Fact (0 < T)]
    (hs : 1 / 2 < s) (B : E →L[𝕜] E' →L[𝕜] F) (a : CircleSobolev s E) (b : CircleSobolev s E')
    {c : CircleSobolev s F} (hc : c.coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) (x : AddCircle T)
    {f₁ : ℤ → E} {u : E} (ha : HasSum f₁ u) {f₂ : ℤ → E'} {v : E'} (hb : HasSum f₂ v)
    (hterm : ∀ m k, fourier (T := T) (m + k) x • B (a.coeff m) (b.coeff k) = B (f₁ m) (f₂ k)) :
    toContinuousMap T hs c x = B u v := by
  -- The double series `∑_{m, k} e_{m + k}(x) B (a_m) (b_k)` is absolutely summable.
  set g : ℤ × ℤ → F := fun p ↦ fourier (p.1 + p.2) x • B (a.coeff p.1) (b.coeff p.2) with hg
  have hgs : Summable g := Summable.of_norm_bounded
    (((summable_norm_coeff hs a).mul_of_nonneg (summable_norm_coeff hs b)
      (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _).mul_left ‖B‖) fun p ↦ by
      simpa [hg, norm_smul, fourier_apply, mul_assoc] using B.le_opNorm₂ (a.coeff p.1) (b.coeff p.2)
  -- Summing first over `k` and then over `m` gives `B u v`.
  have hrow (m : ℤ) : HasSum (fun k ↦ g (m, k)) (B (f₁ m) v) := by
    convert hb.mapL (B (f₁ m)) using 1
    exact funext fun k ↦ hterm m k
  have hgB : HasSum g (B u v) :=
    (ha.mapL (B.flip v)).unique (hgs.hasSum.prod_fiberwise hrow) ▸ hgs.hasSum
  -- Summing over the fibres of `(m, k) ↦ m + k` instead gives the Fourier series of `c`.
  let e : (Σ _ : ℤ, ℤ) ≃ ℤ × ℤ :=
    { toFun σ := (σ.1 - σ.2, σ.2)
      invFun p := ⟨p.1 + p.2, p.2⟩
      left_inv _ := by simp
      right_inv _ := by simp }
  have hfib (n : ℤ) : HasSum (fun m ↦ (g ∘ e) ⟨n, m⟩) (fourier n x • c.coeff n) := by
    rw [hc]
    convert ((addConvolutionExists_coeff hs B a b n).hasSum_sub).const_smul
      (fourier n x : ℂ) using 1
    ext m
    simp only [Function.comp_apply, hg, e, Equiv.coe_fn_mk, sub_add_cancel]
    rfl
  rw [toContinuousMap_apply]
  exact ((e.hasSum_iff.2 hgB).sigma hfib).tsum_eq

section MkCoeffConvolution

variable [SMul 𝕜 ℂ] {r t : ℝ}
  [IsScalarTower 𝕜 ℂ E] [IsScalarTower 𝕜 ℂ E'] [IsScalarTower 𝕜 ℂ F]
  [NormedSpace 𝕜 (CircleSobolev r E)] [IsScalarTower 𝕜 ℂ (CircleSobolev r E)]
  [NormedSpace 𝕜 (CircleSobolev t E')] [IsScalarTower 𝕜 ℂ (CircleSobolev t E')]
  [NormedSpace 𝕜 (CircleSobolev t F)] [IsScalarTower 𝕜 ℂ (CircleSobolev t F)]

omit [NontriviallyNormedField 𝕜] in
private theorem coeff_smul_of_tower {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul 𝕜 X] [IsScalarTower 𝕜 ℂ X] {u : ℝ} [SMul 𝕜 (CircleSobolev u X)]
    [IsScalarTower 𝕜 ℂ (CircleSobolev u X)] (c : 𝕜) (a : CircleSobolev u X) :
    (c • a).coeff = c • a.coeff := by
  rw [← smul_one_smul ℂ c a, coeff_smul]
  exact funext fun _ ↦ smul_one_smul ℂ c _

/-- Bundle discrete coefficient convolution through a continuous `𝕜`-bilinear map
`B : E →L[𝕜] E' →L[𝕜] F` as a continuous `𝕜`-bilinear operator
`H^r(E) →L[𝕜] H^t(E') →L[𝕜] H^t(F)` with norm bound `K * ‖B‖`. -/
def mkCoeffConvolution (K : ℝ) (B : E →L[𝕜] E' →L[𝕜] F)
    (hex : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff)
    (hmem : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2)
    (hnorm : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩ : CircleSobolev t F)‖ ≤
        K * ‖B‖ * ‖a‖ * ‖b‖) :
    CircleSobolev r E →L[𝕜] CircleSobolev t E' →L[𝕜] CircleSobolev t F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun a b ↦ ⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩)
      (fun a a' b ↦ CircleSobolev.ext <| (hex a b).add_distrib _ (hex a' b))
      (fun c a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        dsimp only
        rw [coeff_smul_of_tower, coeff_smul_of_tower, Pi.smul_apply]
        exact (hex a b n).vadd_convolution _)
      (fun a b b' ↦ CircleSobolev.ext <| (hex a b).distrib_add _ (hex a b'))
      (fun c a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        dsimp only
        rw [coeff_smul_of_tower, coeff_smul_of_tower, Pi.smul_apply]
        exact (hex a b n).convolution_vadd _))
    (K * ‖B‖) hnorm

/-- The Fourier coefficients of `mkCoeffConvolution` are `a.coeff ⋆₊[B] b.coeff`. -/
@[simp]
theorem coeff_mkCoeffConvolution (K : ℝ) (B : E →L[𝕜] E' →L[𝕜] F)
    (hex : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff)
    (hmem : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2)
    (hnorm : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩ : CircleSobolev t F)‖ ≤
        K * ‖B‖ * ‖a‖ * ‖b‖)
    (a : CircleSobolev r E) (b : CircleSobolev t E') :
    (mkCoeffConvolution K B hex hmem hnorm a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff :=
  (rfl)

/-- Pointwise norm bound for `mkCoeffConvolution`. -/
theorem norm_mkCoeffConvolution_le (K : ℝ) (B : E →L[𝕜] E' →L[𝕜] F)
    (hex : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff)
    (hmem : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2)
    (hnorm : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩ : CircleSobolev t F)‖ ≤
        K * ‖B‖ * ‖a‖ * ‖b‖)
    (a : CircleSobolev r E) (b : CircleSobolev t E') :
    ‖mkCoeffConvolution K B hex hmem hnorm a b‖ ≤ K * ‖B‖ * ‖a‖ * ‖b‖ :=
  hnorm a b

/-- Operator-norm bound for `mkCoeffConvolution`. -/
theorem opNorm_mkCoeffConvolution_le (K : ℝ) (B : E →L[𝕜] E' →L[𝕜] F)
    (hex : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff)
    (hmem : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2)
    (hnorm : ∀ (a : CircleSobolev r E) (b : CircleSobolev t E'),
      ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩ : CircleSobolev t F)‖ ≤
        K * ‖B‖ * ‖a‖ * ‖b‖) :
    ‖mkCoeffConvolution K B hex hmem hnorm‖ ≤ K * ‖B‖ := by
  have hKB : 0 ≤ K * ‖B‖ := by
    by_contra! hlt
    have hBne : B ≠ 0 := fun h0 ↦ hlt.ne (by rw [h0, ContinuousLinearMap.opNorm_zero, mul_zero])
    obtain ⟨x, hx⟩ := not_forall.1 (ContinuousLinearMap.ext_iff.not.1 hBne)
    obtain ⟨y, hy⟩ := not_forall.1 (ContinuousLinearMap.ext_iff.not.1 hx)
    rw [zero_apply] at hy
    have hpos : 0 < ‖(⟨(single (s := r) 0 x).coeff ⋆₊[B.toLinearMap₁₂]
        (single (s := t) 0 y).coeff, hmem _ _⟩ : CircleSobolev t F)‖ := by
      refine lt_of_lt_of_le (norm_pos_iff.2 hy) ?_
      simpa using norm_coeff_le
        (⟨(single (s := r) 0 x).coeff ⋆₊[B.toLinearMap₁₂] (single (s := t) 0 y).coeff,
          hmem _ _⟩ : CircleSobolev t F) 0
    have hle : K * ‖B‖ * ‖single (s := r) 0 x‖ * ‖single (s := t) 0 y‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hlt.le (norm_nonneg _)) (norm_nonneg _)
    linarith [hnorm (single 0 x) (single 0 y)]
  rw [mkCoeffConvolution]
  exact LinearMap.mkContinuous₂_norm_le _ hKB _

end MkCoeffConvolution

end CoeffConvolution

/-! ### The bilinear product -/

section Convolution

variable [CompleteSpace F]

/-- **The product on `H^s`, `s > 1/2`.** A continuous bilinear map `L : E →L[ℂ] E' →L[ℂ] F`
induces the continuous bilinear map `H^s(E) → H^s(E') → H^s(F)` sending `a` and `b` to the
element with coefficients `a.coeff ⋆₊[L] b.coeff`, the discrete convolution of their
coefficients. On continuous representatives it is the pointwise map `x ↦ L (a x) (b x)`
(`CircleSobolev.toContinuousMap_convolution_apply`). -/
def convolution (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F) :
    CircleSobolev s E →L[ℂ] CircleSobolev s E' →L[ℂ] CircleSobolev s F :=
  mkCoeffConvolution (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)) L
    (addConvolutionExists_coeff hs L) (memℓp_weight_smul_addConvolution_coeff hs L)
    fun a b ↦ norm_le_of_coeff_eq_addConvolution hs L a b rfl

@[simp]
theorem coeff_convolution (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F) (a : CircleSobolev s E)
    (b : CircleSobolev s E') :
    (convolution hs L a b).coeff = a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff :=
  (rfl)

/-- The coefficients of the product are the convolution sums
`∑ₘ L (a.coeff (n - m)) (b.coeff m)`. -/
theorem coeff_convolution_apply (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') (n : ℤ) :
    (convolution hs L a b).coeff n = ∑' m, L (a.coeff (n - m)) (b.coeff m) := by
  simp

/-- The convolution sums defining the coefficients of the product converge. -/
theorem hasSum_coeff_convolution (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') (n : ℤ) :
    HasSum (fun m ↦ L (a.coeff (n - m)) (b.coeff m)) ((convolution hs L a b).coeff n) :=
  (addConvolutionExists_coeff hs L a b n).hasSum_sub

/-- **The product estimate on `H^s`, `s > 1/2`:**
`‖convolution hs L a b‖ ≤ 2 ^ (s + 1) √(∑ₙ (1 + |n|) ^ (-2 s)) ‖L‖ ‖a‖ ‖b‖`. -/
theorem norm_convolution_le (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F) (a : CircleSobolev s E)
    (b : CircleSobolev s E') :
    ‖convolution hs L a b‖ ≤ 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ :=
  norm_mkCoeffConvolution_le _ _ _ _ _ a b

theorem opNorm_convolution_le (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F) :
    ‖(convolution hs L : CircleSobolev s E →L[ℂ] CircleSobolev s E' →L[ℂ] CircleSobolev s F)‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ :=
  opNorm_mkCoeffConvolution_le _ _ _ _ _

@[simp]
theorem convolution_single_single (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F) (m n : ℤ) (x : E)
    (y : E') : convolution hs L (single m x) (single n y) = single (m + n) (L x y) :=
  CircleSobolev.ext <| by simp

/-- The bilinear map `convolution hs L` commutes with the inclusions `H^s → H^t`, `1/2 < t ≤ s`. -/
@[simp]
theorem convolution_inclusion {t : ℝ} (ht : 1 / 2 < t) (h : t ≤ s) (L : E →L[ℂ] E' →L[ℂ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    convolution ht L (inclusion h a) (inclusion h b) =
      inclusion h (convolution (ht.trans_le h) L a b) :=
  CircleSobolev.ext <| by simp

variable (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace E']

/-- **On continuous representatives the product is pointwise:** for `s > 1/2`, the continuous
function attached to `convolution hs L a b` is `x ↦ L (a x) (b x)`. -/
@[simp]
theorem toContinuousMap_convolution_apply (hs : 1 / 2 < s) (L : E →L[ℂ] E' →L[ℂ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') (x : AddCircle T) :
    toContinuousMap T hs (convolution hs L a b) x =
      L (toContinuousMap T hs a x) (toContinuousMap T hs b x) := by
  have hA := (hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)
  have hB := (hasSum_toContinuousMap T hs b).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hA hB
  refine toContinuousMap_eq_of_coeff_eq_addConvolution T hs L a b rfl x hA hB fun m k ↦ ?_
  simp only [fourier_add, mul_smul, map_smul, smul_apply]
  exact smul_comm _ _ _

end Convolution

/-! ### The algebra `H^s(A)` -/

variable (s) in
/-- The constant of the product estimate for finite products in `H^s`: the maximum of `1` and the
constant `2 ^ (s + 1) √(∑ₙ (1 + |n|) ^ (-2 s))` of `norm_mul_le`. -/
def mulConst : ℝ :=
  max (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)) 1

theorem one_le_mulConst : 1 ≤ mulConst s :=
  le_max_right _ _

section Ring

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The unit of `H^s(A)`: the constant function `1`. -/
instance : One (CircleSobolev s A) :=
  ⟨single 0 1⟩

theorem one_def : (1 : CircleSobolev s A) = single 0 1 :=
  (rfl)

@[simp]
theorem coeff_one : (1 : CircleSobolev s A).coeff = Pi.single 0 1 :=
  coeff_single 0 1

variable [CompleteSpace A] [hs : Fact (1 / 2 < s)]

/-- For `s > 1/2`, the product on `H^s(A)`: the convolution of the coefficients. -/
instance : Mul (CircleSobolev s A) :=
  ⟨fun a b ↦ convolution hs.out (.mul ℂ A) a b⟩

theorem mul_def (a b : CircleSobolev s A) : a * b = convolution hs.out (.mul ℂ A) a b :=
  (rfl)

/-- The coefficients of a product are the convolution sums `∑ₘ a.coeff (n - m) * b.coeff m`. -/
@[simp]
theorem coeff_mul (a b : CircleSobolev s A) (n : ℤ) :
    (a * b).coeff n = ∑' m, a.coeff (n - m) * b.coeff m :=
  coeff_convolution_apply hs.out _ a b n

theorem hasSum_coeff_mul (a b : CircleSobolev s A) (n : ℤ) :
    HasSum (fun m ↦ a.coeff (n - m) * b.coeff m) ((a * b).coeff n) :=
  hasSum_coeff_convolution hs.out _ a b n

@[simp]
theorem single_mul_single (m n : ℤ) (x y : A) :
    (single m x * single n y : CircleSobolev s A) = single (m + n) (x * y) :=
  convolution_single_single hs.out _ m n x y

/-- **The product estimate in `H^s(A)`, `s > 1/2`.** -/
theorem norm_mul_le (a b : CircleSobolev s A) :
    ‖a * b‖ ≤ 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖a‖ * ‖b‖ :=
  calc ‖a * b‖
      ≤ 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖ContinuousLinearMap.mul ℂ A‖ * ‖a‖ * ‖b‖ :=
        norm_convolution_le hs.out _ a b
    _ ≤ 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * 1 * ‖a‖ * ‖b‖ := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℂ A
    _ = 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖a‖ * ‖b‖ := by rw [mul_one]

/-- On continuous representatives the product of `H^s(A)` is the pointwise product. -/
@[simp]
theorem toContinuousMap_mul (T : ℝ) [Fact (0 < T)] (a b : CircleSobolev s A) :
    toContinuousMap T hs.out (a * b) = toContinuousMap T hs.out a * toContinuousMap T hs.out b :=
  ContinuousMap.ext <| toContinuousMap_convolution_apply T hs.out _ a b

@[simp]
theorem toContinuousMap_one (T : ℝ) [Fact (0 < T)] :
    toContinuousMap T hs.out (1 : CircleSobolev s A) = 1 := by
  ext x
  simp [one_def]

/-- Elements of `H^s(A)` with the same continuous representatives on the unit circle are equal;
used to transfer ring identities from `C(AddCircle 1, A)`. -/
private theorem eq_of_toContinuousMap_one_eq {a b : CircleSobolev s A}
    (h : ∀ [Fact ((0 : ℝ) < 1)], toContinuousMap 1 hs.out a = toContinuousMap 1 hs.out b) :
    a = b :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  toContinuousMap_injective 1 hs.out h

/-- For `s > 1/2`, `H^s(A)` is a ring under the convolution product, with unit `single 0 1`. -/
instance : Ring (CircleSobolev s A) where
  mul_assoc a b c := by
    exact eq_of_toContinuousMap_one_eq <| by intro; simp only [toContinuousMap_mul, mul_assoc]
  one_mul a := by
    exact eq_of_toContinuousMap_one_eq <| by
      intro
      simp only [toContinuousMap_mul, toContinuousMap_one, one_mul]
  mul_one a := by
    exact eq_of_toContinuousMap_one_eq <| by
      intro
      simp only [toContinuousMap_mul, toContinuousMap_one, mul_one]
  left_distrib a b c := (convolution hs.out _ a).map_add b c
  right_distrib a b c := by simp only [mul_def, map_add, add_apply]
  zero_mul a := by simp only [mul_def, map_zero, zero_apply]
  mul_zero a := (convolution hs.out _ a).map_zero
  __ := (inferInstance : AddCommGroup (CircleSobolev s A))

/-- For `s > 1/2`, `H^s(A)` is a `ℂ`-algebra. -/
instance : Algebra ℂ (CircleSobolev s A) :=
  Algebra.ofModule
    (fun c a b ↦ by simp only [mul_def, map_smul, smul_apply])
    (fun c a b ↦ (convolution hs.out _ a).map_smul c b)

theorem algebraMap_eq_single (c : ℂ) :
    algebraMap ℂ (CircleSobolev s A) c = single 0 (algebraMap ℂ A c) := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, ← map_smul, Algebra.algebraMap_eq_smul_one]

/-- The product of `H^s(A)` is continuous, since it is a bounded bilinear map. -/
instance : IsTopologicalRing (CircleSobolev s A) where
  continuous_mul := (convolution hs.out (.mul ℂ A)).continuous₂

/-- The product estimate `norm_mul_le`, with the constant `mulConst s`. -/
theorem norm_mul_le_mulConst (a b : CircleSobolev s A) : ‖a * b‖ ≤ mulConst s * ‖a‖ * ‖b‖ :=
  (norm_mul_le a b).trans (by gcongr; exact le_max_left _ _)

/-- The product estimate for a finite product in `H^s(A)`:
`‖a₁ ⋯ aₖ‖ ≤ mulConst s ^ (k - 1) ‖a₁‖ ⋯ ‖aₖ‖`, with natural-number subtraction. -/
theorem norm_list_prod_le [NormOneClass A] (l : List (CircleSobolev s A)) :
    ‖l.prod‖ ≤ mulConst s ^ (l.length - 1) * (l.map norm).prod := by
  induction l with
  | nil => simp [one_def, weight_def]
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.prod_cons, List.length_cons, List.map_cons, List.prod_cons]
      calc ‖a * (b :: l).prod‖ ≤ mulConst s * ‖a‖ * ‖(b :: l).prod‖ :=
            norm_mul_le_mulConst a (b :: l).prod
        _ ≤ mulConst s * ‖a‖ *
            (mulConst s ^ ((b :: l).length - 1) * ((b :: l).map norm).prod) :=
          mul_le_mul_of_nonneg_left ih
            (mul_nonneg (zero_le_one.trans one_le_mulConst) (norm_nonneg a))
        _ = _ := by simp only [List.length_cons, Nat.add_sub_cancel, List.prod_cons, pow_succ]; ring

/-- The product estimate for powers in `H^s(A)`:
`‖a ^ k‖ ≤ mulConst s ^ (k - 1) ‖a‖ ^ k`, with natural-number subtraction. -/
theorem norm_pow_le [NormOneClass A] (a : CircleSobolev s A) (k : ℕ) :
    ‖a ^ k‖ ≤ mulConst s ^ (k - 1) * ‖a‖ ^ k := by
  simpa [List.prod_replicate] using norm_list_prod_le (List.replicate k a)

/-- For `s > 1/2`, `toContinuousMap` is an algebra homomorphism `H^s(A) → C(AddCircle T, A)`. -/
def toContinuousMapAlgHom (T : ℝ) [Fact (0 < T)] : CircleSobolev s A →ₐ[ℂ] C(AddCircle T, A) :=
  AlgHom.ofLinearMap (toContinuousMap T hs.out).toLinearMap (toContinuousMap_one T)
    (toContinuousMap_mul T)

@[simp]
theorem coe_toContinuousMapAlgHom (T : ℝ) [Fact (0 < T)] :
    ⇑(toContinuousMapAlgHom (s := s) (A := A) T) = toContinuousMap T hs.out :=
  (rfl)

/-- On continuous representatives the powers of `H^s(A)` are the pointwise powers. -/
@[simp]
theorem toContinuousMap_pow (T : ℝ) [Fact (0 < T)] (a : CircleSobolev s A) (k : ℕ) :
    toContinuousMap T hs.out (a ^ k) = toContinuousMap T hs.out a ^ k := by
  rw [← coe_toContinuousMapAlgHom T, map_pow]

end Ring

section CommRing

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [hs : Fact (1 / 2 < s)]

/-- For `s > 1/2` and a commutative `A`, `H^s(A)` is a commutative ring. -/
instance : CommRing (CircleSobolev s A) where
  mul_comm a b := by
    exact eq_of_toContinuousMap_one_eq <| by intro; simp only [toContinuousMap_mul, mul_comm]

end CommRing

end CircleSobolev

end TauCeti
