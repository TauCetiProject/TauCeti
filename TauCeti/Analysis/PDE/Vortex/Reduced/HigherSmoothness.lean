/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.SmoothDependence
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian.Power
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# Smooth dependence of the reduced vortex equation on the divisor in every Sobolev space

For coefficients `c ∈ ℂ^m`, `m ≥ 1`, let `P_c = TauCeti.Polynomial.monicOfCoeff c`, the monic
polynomial whose zero divisor has symmetric coordinates `c` in `Sym^m ℂ`, collisions of zeros
included. Taubes's plane vortex with this divisor is reconstructed from the solution `w_c` of the
reduced equation

`Δw = h_c (exp (2w) - 1) / 8 + k_c`,    `h_c = 1 - φ_c`,    `φ_c = (1 + ‖P_c‖²)⁻¹`.

The coefficient `φ_c`, the source `k_c` and the solution `w_c` lie in every Sobolev space `H^s(ℂ)`
(`TauCeti.Vortex.sobolevBackgroundDefect`, `TauCeti.Vortex.sobolevBackgroundSource`,
`TauCeti.Vortex.reducedSolution_mem_realSobolevFunctions`). This file shows that all three depend
smoothly on `c` in every `H^s(ℂ)`:

* `TauCeti.Vortex.contDiff_sobolevBackgroundDefect_monicOfCoeff`,
* `TauCeti.Vortex.contDiff_sobolevBackgroundSource_monicOfCoeff`,
* `TauCeti.Vortex.contDiff_ofRealSobolevFunction_reducedSolution`.

For `w_c` this extends `TauCeti.Vortex.contDiff_sobolevReducedSolution`, which is the case
`s = 2`. Composed with the derivatives `H^(s+1)(ℂ) → H^s(ℂ)` and the Sobolev embedding of `H^s(ℂ)`,
`s > 1`, into bounded continuous functions, both continuous linear, it makes `w_c` and each of its
derivatives depend smoothly on `c` uniformly on the plane. The connection of the plane vortex with
divisor `c` involves the first derivatives of `w_c`, so this is the input for smooth families of
vortex fields over compact windows of the divisor space.

**The coefficients.** Write `W_{n,i,j}(c) = φ_c ^ n conj z ^ i z ^ j`, the function
`Polynomial.conjMulDivOneAddNormSqPow P_c n (X ^ i) (X ^ j)`. When `i + j + 2 ≤ 2 m n` it is square
integrable, and it depends smoothly on `c` in `L²(ℂ)`: near `c₀`, `φ_c = φ_{c₀} ψ_c` for a family
`ψ` of bounded continuous functions that is smooth at `c₀`, so
`W_{n,i,j}(c) = ψ_c ^ n W_{n,i,j}(c₀)`
(`TauCeti.Vortex.contDiff_of_coeFn_eq_backgroundDefect_pow_mul`). Differentiating in `z` along
`v`, with `P_c = ∑ a_k X ^ k` and `P_c' = ∑ b_l X ^ l`,

`∂_v W_{n,i,j} = -n v ∑ conj a_k b_l W_{n+1,i+k,j+l} - n conj v ∑ a_k conj b_l W_{n+1,i+l,j+k}`
`              + i conj v W_{n,i-1,j} + j v W_{n,i,j-1}`,

a combination of functions of the same kind, with coefficients polynomial in `c` and `conj c`, and
the bound `i + j + 2 ≤ 2 m n` is preserved. So by induction on `k`, `W_{n,i,j}(c)` depends smoothly
on `c` in `H^k(ℂ)`: a family that is smooth in `H^k` together with its first derivatives is smooth
in `H^(k+1)` (`BesselPotentialSpace.exists_contDiff_inclusion_eq_of_lineDerivOp_eq`). Finally
`φ_c = W_{1,0,0}(c)` and `k_c = -φ_c / 8 + 2 ∑ conj b_k b_l W_{2,k,l}(c)`.

**The solution.** The reduced equation gives
`(1 - Δ) w_c = w_c - (1 - φ_c) (exp (2 w_c) - 1) / 8 - k_c`
(`TauCeti.Vortex.reducedEquationMap_eq_zero_of_laplacian_eq`). For `s > 1` the right side depends
smoothly on `c` in the algebra `H^s(ℂ)` as soon as `w_c` does, and `(1 - Δ)⁻¹` maps `H^s(ℂ)`
boundedly to `H^(s+2)(ℂ)`. Starting from `H²(ℂ)`, this bootstraps the smoothness of `c ↦ w_c` to
every `H^s(ℂ)`.

## Main results

* `TauCeti.Vortex.contDiff_sobolevBackgroundDefect_monicOfCoeff`: `c ↦ φ_c` is smooth into
  `H^s(ℂ)`.
* `TauCeti.Vortex.contDiff_sobolevBackgroundSource_monicOfCoeff`: `c ↦ k_c` is smooth into
  `H^s(ℂ)`.
* `TauCeti.Vortex.contDiff_ofRealSobolevFunction_reducedSolution`: `c ↦ w_c` is smooth into
  `H^s(ℂ)`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex _root_.MeasureTheory Filter Finset BesselPotentialSpace BoundedContinuousFunction
  TauCeti.Polynomial
open scoped BesselPotentialSpace ContDiff Topology ComplexConjugate ENNReal Laplacian LineDeriv

variable {m : ℕ}

/-! ### Defect monomials -/

/-- The defect monomial `φ_c ^ n conj z ^ i z ^ j`, with `φ_c = (1 + ‖P_c‖²)⁻¹`. -/
private def defectMonomial (c : Fin m → ℂ) (n i j : ℕ) : ℂ → ℂ :=
  _root_.Polynomial.conjMulDivOneAddNormSqPow (monicOfCoeff c) n (.X ^ i) (.X ^ j)

private theorem defectMonomial_apply (c : Fin m → ℂ) (n i j : ℕ) (z : ℂ) :
    defectMonomial c n i j z =
      backgroundDefect (monicOfCoeff c) z ^ n * (conj z ^ i * z ^ j) := by
  rw [defectMonomial, _root_.Polynomial.conjMulDivOneAddNormSqPow_apply, backgroundDefect_apply,
    Complex.ofReal_pow]
  simp only [_root_.Polynomial.eval_pow, _root_.Polynomial.eval_X, map_pow]

private theorem contDiff_defectMonomial (c : Fin m → ℂ) (n i j : ℕ) :
    ContDiff ℝ ∞ (defectMonomial c n i j) :=
  _root_.Polynomial.contDiff_conjMulDivOneAddNormSqPow _ _ _ _

/-- `φ_c ^ n conj z ^ i z ^ j` is square integrable when `i + j + 2 ≤ 2 m n`. -/
private theorem memLp_defectMonomial {n i j : ℕ} (h : i + j + 2 ≤ 2 * m * n) (c : Fin m → ℂ) :
    MemLp (defectMonomial c n i j) 2 :=
  _root_.Polynomial.memLp_conjMulDivOneAddNormSqPow (by
    rwa [_root_.Polynomial.natDegree_X_pow, _root_.Polynomial.natDegree_X_pow,
      natDegree_monicOfCoeff])

/-! ### Families smooth in the coefficients -/

/-- A family `f c` of functions on the plane is smooth in `H^k(ℂ)`: there is a smooth map `F`
into `H^k(ℂ)` whose `L²` function at `c` is `f c`. -/
private def IsSmoothFamily (k : ℕ) (f : (Fin m → ℂ) → ℂ → ℂ) : Prop :=
  ∃ F : (Fin m → ℂ) → H^{(k : ℝ)}(ℂ), ContDiff ℝ ∞ F ∧
    ∀ c, ⇑(inclusionLp k.cast_nonneg (F c)) =ᵐ[volume] f c

private theorem IsSmoothFamily.add {k : ℕ} {f g : (Fin m → ℂ) → ℂ → ℂ} (hf : IsSmoothFamily k f)
    (hg : IsSmoothFamily k g) : IsSmoothFamily k fun c z ↦ f c z + g c z := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  exact ⟨F + G, hF.add hG, fun c ↦ coeFn_inclusionLp_add_ae_eq _ (hFf c) (hGg c)⟩

private theorem IsSmoothFamily.mul_left {k : ℕ} {f : (Fin m → ℂ) → ℂ → ℂ}
    (hf : IsSmoothFamily k f) {γ : (Fin m → ℂ) → ℂ} (hγ : ContDiff ℝ ∞ γ) :
    IsSmoothFamily k fun c z ↦ γ c * f c z := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨fun c ↦ γ c • F c, hγ.smul hF, fun c ↦ coeFn_inclusionLp_smul_ae_eq _ _ (hFf c)⟩

private theorem isSmoothFamily_zero (k : ℕ) : IsSmoothFamily (m := m) k fun _ _ ↦ 0 :=
  ⟨0, contDiff_const, fun c ↦ by
    rw [Pi.zero_apply, map_zero]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)⟩

private theorem IsSmoothFamily.sum {k : ℕ} {ι : Type*} (t : Finset ι)
    {f : ι → (Fin m → ℂ) → ℂ → ℂ} (hf : ∀ a ∈ t, IsSmoothFamily k (f a)) :
    IsSmoothFamily k fun c z ↦ ∑ a ∈ t, f a c z := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isSmoothFamily_zero k
  | insert a t ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a t)).add (ih fun b hb ↦ hf b (mem_insert_of_mem hb))

private theorem IsSmoothFamily.sub {k : ℕ} {f g : (Fin m → ℂ) → ℂ → ℂ} (hf : IsSmoothFamily k f)
    (hg : IsSmoothFamily k g) : IsSmoothFamily k fun c z ↦ f c z - g c z := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  exact ⟨F - G, hF.sub hG, fun c ↦ coeFn_inclusionLp_sub_ae_eq _ (hFf c) (hGg c)⟩

/-- A smooth family in `H^k` is smooth in every `H^s`, `s ≤ k`. -/
private theorem IsSmoothFamily.contDiff {k : ℕ} {f : (Fin m → ℂ) → ℂ → ℂ}
    (hf : IsSmoothFamily k f) {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k) {G : (Fin m → ℂ) → H^{s}(ℂ)}
    (hG : ∀ c, ⇑(inclusionLp hs (G c)) =ᵐ[volume] f c) : ContDiff ℝ ∞ G := by
  obtain ⟨F, hF, hFf⟩ := hf
  have hGF : G = fun c ↦ inclusion hsk (F c) := funext fun c ↦
    ext_of_ae_eq_inclusionLp hs (by rw [inclusionLp_inclusion]; exact (hG c).trans (hFf c).symm)
  rw [hGF]
  exact ((inclusion hsk).restrictScalars ℝ).contDiff.comp hF

/-! ### Square integrability -/

/-- **The defect monomials depend smoothly on the coefficients in `L²`**, the case `k = 0`. -/
private theorem isSmoothFamily_zero_defectMonomial {n i j : ℕ} (h : i + j + 2 ≤ 2 * m * n) :
    IsSmoothFamily 0 fun c : Fin m → ℂ ↦ defectMonomial c n i j := by
  set g : (Fin m → ℂ) → Lp ℂ 2 (volume : Measure ℂ) := fun c ↦ (memLp_defectMonomial h c).toLp
  have hg : ContDiff ℝ ∞ g :=
    contDiff_of_coeFn_eq_backgroundDefect_pow_mul n (fun z ↦ conj z ^ i * z ^ j) fun c ↦
      (MemLp.coeFn_toLp (memLp_defectMonomial h c)).trans
        (.of_forall fun z ↦ defectMonomial_apply c n i j z)
  -- `L²` is `H⁰(ℂ)`.
  set J : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] H^{((0 : ℕ) : ℝ)}(ℂ) :=
    (inclusion (by simp)).comp (toLpₗᵢ ℂ ℂ 0 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨fun c ↦ J (g c), (J.restrictScalars ℝ).contDiff.comp hg, fun c ↦ ?_⟩
  have hJ : inclusionLp (Nat.cast_nonneg 0) (J (g c)) = g c := by
    simp only [J, ContinuousLinearMap.comp_apply, inclusionLp_inclusion, inclusionLp_zero]
    exact (toLpₗᵢ_apply _).symm.trans ((toLpₗᵢ ℂ ℂ 0 2).apply_symm_apply (g c))
  rw [hJ]
  exact MemLp.coeFn_toLp _

/-! ### The derivatives of the defect monomials -/

/-- The derivative of `φ_c ^ n conj z ^ i z ^ j` along the line `t ↦ z + t v`. -/
private theorem hasDerivAt_defectMonomial (c : Fin m → ℂ) (n i j : ℕ) (z v : ℂ) :
    HasDerivAt (fun t : ℝ ↦ defectMonomial c n i j (z + t • v))
      (-(n : ℂ) * (conj ((monicOfCoeff c).eval z) * ((monicOfCoeff c).derivative.eval z * v) +
          (monicOfCoeff c).eval z * conj ((monicOfCoeff c).derivative.eval z * v)) *
          defectMonomial c (n + 1) i j z +
        (i : ℂ) * conj v * defectMonomial c n (i - 1) j z +
        (j : ℂ) * v * defectMonomial c n i (j - 1) z) 0 := by
  refine (_root_.Polynomial.hasDerivAt_conjMulDivOneAddNormSqPow (monicOfCoeff c) n (.X ^ i)
    (.X ^ j) z v).congr_deriv ?_
  simp only [defectMonomial, _root_.Polynomial.conjMulDivOneAddNormSqPow_apply,
    _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_pow,
    _root_.Polynomial.eval_X, _root_.Polynomial.eval_neg, _root_.Polynomial.eval_natCast,
    _root_.Polynomial.derivative_X_pow, map_mul, map_neg, map_natCast, map_pow]
  ring

/-- **The derivatives of the defect monomials.** With `P_c = ∑ a_k X ^ k` and `P_c' = ∑ b_l X ^ l`,
the derivative of `W_{n,i,j} = φ_c ^ n conj z ^ i z ^ j` along `v` is
`-n v ∑ conj a_k b_l W_{n+1,i+k,j+l} - n conj v ∑ a_k conj b_l W_{n+1,i+l,j+k}`
`+ i conj v W_{n,i-1,j} + j v W_{n,i,j-1}`. -/
private theorem fderiv_defectMonomial (c : Fin m → ℂ) (n i j : ℕ) (z v : ℂ) :
    fderiv ℝ (defectMonomial c n i j) z v =
      ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
        (-(n : ℂ) * v * (conj ((monicOfCoeff c).coeff k) * (monicOfCoeff c).derivative.coeff l) *
            defectMonomial c (n + 1) (i + k) (j + l) z -
          (n : ℂ) * conj v *
            ((monicOfCoeff c).coeff k * conj ((monicOfCoeff c).derivative.coeff l)) *
            defectMonomial c (n + 1) (i + l) (j + k) z) +
        (i : ℂ) * conj v * defectMonomial c n (i - 1) j z +
        (j : ℂ) * v * defectMonomial c n i (j - 1) z := by
  set P := monicOfCoeff c
  have hD : DifferentiableAt ℝ (defectMonomial c n i j) z :=
    (contDiff_defectMonomial c n i j).differentiable (by simp) z
  rw [(hD.hasFDerivAt.hasLineDerivAt v).unique (hasDerivAt_defectMonomial c n i j z v)]
  have hdeg : P.natDegree < m + 1 := by
    rw [natDegree_monicOfCoeff]
    exact m.lt_succ_self
  have hP := _root_.Polynomial.eval_eq_sum_range' hdeg z
  have hP' := _root_.Polynomial.eval_eq_sum_range' (n := m + 1)
    ((_root_.Polynomial.natDegree_derivative_le P).trans_lt (by omega)) z
  have hW (a b : ℕ) : defectMonomial c (n + 1) (i + a) (j + b) z =
      defectMonomial c (n + 1) i j z * (conj z ^ a * z ^ b) := by
    simp only [defectMonomial_apply, pow_add]
    ring
  -- Expand `conj P P'` and `P conj P'` in the coefficients.
  have e₁ : conj (P.eval z) * P.derivative.eval z = ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
      conj (P.coeff k) * P.derivative.coeff l * (conj z ^ k * z ^ l) := by
    rw [hP, hP', map_sum, sum_mul_sum]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    simp only [map_mul, map_pow]
    ring
  have e₂ : P.eval z * conj (P.derivative.eval z) = ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
      P.coeff k * conj (P.derivative.coeff l) * (conj z ^ l * z ^ k) := by
    rw [hP, hP', map_sum, sum_mul_sum]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    simp only [map_mul, map_pow]
    ring
  have hS : ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
      (-(n : ℂ) * v * (conj (P.coeff k) * P.derivative.coeff l) *
          defectMonomial c (n + 1) (i + k) (j + l) z -
        (n : ℂ) * conj v * (P.coeff k * conj (P.derivative.coeff l)) *
          defectMonomial c (n + 1) (i + l) (j + k) z) =
      -(n : ℂ) * v * defectMonomial c (n + 1) i j z * (conj (P.eval z) * P.derivative.eval z) -
        (n : ℂ) * conj v * defectMonomial c (n + 1) i j z *
          (P.eval z * conj (P.derivative.eval z)) := by
    rw [e₁, e₂, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [hW, hW]
    ring
  rw [hS, map_mul]
  ring

/-! ### Every Sobolev order -/

/-- **The induction step.** If the defect monomials depend smoothly on `c` in `H^k`, then so do
their first derivatives, hence the defect monomials depend smoothly on `c` in `H^(k+1)`. -/
private theorem isSmoothFamily_succ_defectMonomial {k : ℕ}
    (ih : ∀ n i j, i + j + 2 ≤ 2 * m * n →
      IsSmoothFamily k fun c : Fin m → ℂ ↦ defectMonomial c n i j)
    {n i j : ℕ} (h : i + j + 2 ≤ 2 * m * n) :
    IsSmoothFamily (k + 1) fun c : Fin m → ℂ ↦ defectMonomial c n i j := by
  have hsucc : 2 * m * (n + 1) = 2 * m * n + 2 * m := by ring
  have ha (a : ℕ) : ContDiff ℝ ∞ fun c : Fin m → ℂ ↦ (monicOfCoeff c).coeff a :=
    (contDiff_coeff_monicOfCoeff a).restrict_scalars ℝ
  have hb (b : ℕ) : ContDiff ℝ ∞ fun c : Fin m → ℂ ↦ (monicOfCoeff c).derivative.coeff b :=
    (contDiff_coeff_derivative_monicOfCoeff b).restrict_scalars ℝ
  have hconj {f : (Fin m → ℂ) → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ fun c ↦ conj (f c) :=
    Complex.conjCLE.contDiff.comp hf
  -- The derivatives along every direction are smooth families in `H^k`.
  have hd (v : ℂ) : IsSmoothFamily k fun (c : Fin m → ℂ) z ↦
      fderiv ℝ (defectMonomial c n i j) z v := by
    simp_rw [fderiv_defectMonomial]
    refine ((IsSmoothFamily.sum _ fun a ha' ↦ IsSmoothFamily.sum _ fun b hb' ↦
      IsSmoothFamily.sub ?_ ?_).add ?_).add ?_
    · refine (ih _ _ _ ?_).mul_left (contDiff_const.mul ((hconj (ha a)).mul (hb b)))
      have := mem_range.1 ha'
      have := mem_range.1 hb'
      rw [hsucc]
      generalize 2 * m * n = M at h ⊢
      omega
    · refine (ih _ _ _ ?_).mul_left (contDiff_const.mul ((ha a).mul (hconj (hb b))))
      have := mem_range.1 ha'
      have := mem_range.1 hb'
      rw [hsucc]
      generalize 2 * m * n = M at h ⊢
      omega
    · exact (ih _ _ _ (by omega)).mul_left contDiff_const
    · exact (ih _ _ _ (by omega)).mul_left contDiff_const
  set b := Complex.orthonormalBasisOneI
  choose G hG hGd using fun e : Fin 2 ↦ hd (b e)
  obtain ⟨F, hF, hFd⟩ := ih n i j h
  obtain ⟨u, hu, huF⟩ := exists_contDiff_inclusion_eq_of_lineDerivOp_eq b hF hG fun c e ↦ by
    rw [← toTemperedDistribution_inclusionLp k.cast_nonneg,
      ← toTemperedDistribution_inclusionLp k.cast_nonneg]
    exact lineDerivOp_toTemperedDistribution_eq_of_contDiff
      ((contDiff_defectMonomial c n i j).of_le (by simp)) (hFd c) (hGd e c)
  have hle : ((k + 1 : ℕ) : ℝ) ≤ k + 1 := by push_cast; rfl
  refine ⟨fun c ↦ inclusion hle (u c), ((inclusion hle).restrictScalars ℝ).contDiff.comp hu,
    fun c ↦ ?_⟩
  rw [inclusionLp_inclusion, ← inclusionLp_inclusion (by linarith : (k : ℝ) ≤ k + 1)
    k.cast_nonneg, huF]
  exact hFd c

/-- **The defect monomials depend smoothly on the coefficients in every `H^k`.** -/
private theorem isSmoothFamily_defectMonomial (k : ℕ) {n i j : ℕ} (h : i + j + 2 ≤ 2 * m * n) :
    IsSmoothFamily k fun c : Fin m → ℂ ↦ defectMonomial c n i j := by
  induction k generalizing n i j with
  | zero => exact isSmoothFamily_zero_defectMonomial h
  | succ k ih => exact isSmoothFamily_succ_defectMonomial (fun _ _ _ h ↦ ih h) h

/-! ### The coefficients of the reduced equation -/

variable {s : ℝ}

/-- **The defect depends smoothly on the divisor in every Sobolev space.** For `m ≥ 1` and
`s ≥ 0`, the coefficient `φ_c = (1 + ‖P_c‖²)⁻¹` of the reduced equation, as an element of
`H^s(ℂ)`, depends smoothly on the coefficients `c ∈ ℂ^m` of `P_c`. -/
theorem contDiff_sobolevBackgroundDefect_monicOfCoeff (hm : 0 < m) (hs : 0 ≤ s) :
    ContDiff ℝ ∞ fun c : Fin m → ℂ ↦
      sobolevBackgroundDefect (P := monicOfCoeff c) (by rwa [natDegree_monicOfCoeff]) hs := by
  refine (isSmoothFamily_defectMonomial ⌈s⌉₊ (n := 1) (i := 0) (j := 0) (by omega)).contDiff hs
    (Nat.le_ceil s) fun c ↦ ?_
  filter_upwards [coeFn_inclusionLp_sobolevBackgroundDefect
    (P := monicOfCoeff c) (by rwa [natDegree_monicOfCoeff]) hs] with z hz
  rw [hz, defectMonomial_apply, backgroundDefect_apply]
  simp

/-- **The source depends smoothly on the divisor in every Sobolev space.** For `m ≥ 1` and
`s ≥ 0`, the source `k_c = (h_c - 1) / 8 + 2 ‖P_c'‖² / (1 + ‖P_c‖²)²` of the reduced equation, as
an element of `H^s(ℂ)`, depends smoothly on the coefficients `c ∈ ℂ^m` of `P_c`. -/
theorem contDiff_sobolevBackgroundSource_monicOfCoeff (hm : 0 < m) (hs : 0 ≤ s) :
    ContDiff ℝ ∞ fun c : Fin m → ℂ ↦
      sobolevBackgroundSource (P := monicOfCoeff c) (by rwa [natDegree_monicOfCoeff]) hs := by
  have hb (b : ℕ) : ContDiff ℝ ∞ fun c : Fin m → ℂ ↦ (monicOfCoeff c).derivative.coeff b :=
    (contDiff_coeff_derivative_monicOfCoeff b).restrict_scalars ℝ
  -- `k_c = -φ_c / 8 + 2 ∑ conj b_a b_b W_{2,a,b}(c)`.
  have hfam : IsSmoothFamily ⌈s⌉₊ fun (c : Fin m → ℂ) z ↦
      (-8⁻¹ : ℂ) * defectMonomial c 1 0 0 z + ∑ a ∈ range (m + 1), ∑ b ∈ range (m + 1),
        2 * (conj ((monicOfCoeff c).derivative.coeff a) * (monicOfCoeff c).derivative.coeff b) *
          defectMonomial c 2 a b z :=
    ((isSmoothFamily_defectMonomial _ (by omega)).mul_left contDiff_const).add
      (IsSmoothFamily.sum _ fun a ha ↦ IsSmoothFamily.sum _ fun b hb' ↦
        (isSmoothFamily_defectMonomial _ (by
          have := mem_range.1 ha
          have := mem_range.1 hb'
          omega)).mul_left
          (contDiff_const.mul ((Complex.conjCLE.contDiff.comp (hb a)).mul (hb b))))
  refine hfam.contDiff hs (Nat.le_ceil s) fun c ↦ ?_
  filter_upwards [coeFn_inclusionLp_sobolevBackgroundSource
    (P := monicOfCoeff c) (by rwa [natDegree_monicOfCoeff]) hs] with z hz
  set P := monicOfCoeff c
  have hP' := _root_.Polynomial.eval_eq_sum_range' (n := m + 1)
    ((_root_.Polynomial.natDegree_derivative_le P).trans_lt
      (by rw [natDegree_monicOfCoeff]; omega)) z
  have hn : ((‖P.derivative.eval z‖ ^ 2 : ℝ) : ℂ) =
      conj (P.derivative.eval z) * P.derivative.eval z := by
    rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [hz, backgroundSource_eq_backgroundDefect, hn, hP', map_sum, sum_mul_sum, mul_sum, sum_mul]
  simp only [defectMonomial_apply, pow_one, pow_zero, mul_one]
  congr 1
  refine sum_congr rfl fun a _ ↦ ?_
  rw [mul_sum, sum_mul]
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [map_mul, map_pow]
  ring

/-! ### The reduced solution -/

/-- The reduced solution `w_c` of `P_c` as an element of `H^s(ℂ)`. -/
private def reducedSolutionSobolev (hs : 0 ≤ s) (c : Fin m → ℂ) : H^{s}(ℂ) :=
  ofRealSobolevFunction hs (reducedSolution_mem_realSobolevFunctions (monicOfCoeff c) s)

private theorem coeFn_inclusionLp_reducedSolutionSobolev (hs : 0 ≤ s) (c : Fin m → ℂ) :
    ⇑(inclusionLp hs (reducedSolutionSobolev hs c)) =ᵐ[volume]
      fun z ↦ (reducedSolution (monicOfCoeff c) z : ℂ) :=
  coeFn_inclusionLp_ofRealSobolevFunction hs _

private theorem inclusion_reducedSolutionSobolev {t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (c : Fin m → ℂ) :
    inclusion hst (reducedSolutionSobolev (hs.trans hst) c) = reducedSolutionSobolev hs c :=
  ext_of_ae_eq_inclusionLp hs (by
    rw [inclusionLp_inclusion]
    exact (coeFn_inclusionLp_reducedSolutionSobolev _ c).trans
      (coeFn_inclusionLp_reducedSolutionSobolev hs c).symm)

/-- Smoothness of `c ↦ w_c` in `H^t(ℂ)` gives it in `H^s(ℂ)` for `s ≤ t`. -/
private theorem contDiff_reducedSolutionSobolev_of_le {t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : ContDiff ℝ ∞ (reducedSolutionSobolev (m := m) (hs.trans hst))) :
    ContDiff ℝ ∞ (reducedSolutionSobolev (m := m) hs) := by
  rw [show reducedSolutionSobolev (m := m) hs = fun c ↦
      inclusion hst (reducedSolutionSobolev (hs.trans hst) c) from
    funext fun c ↦ (inclusion_reducedSolutionSobolev hs hst c).symm]
  exact ((inclusion hst).restrictScalars ℝ).contDiff.comp h

/-- **The bootstrap step.** For `t > 1`, smoothness of `c ↦ w_c` in `H^t(ℂ)` gives it in
`H^(t+2)(ℂ)`, since `(1 - Δ) w_c = w_c - (1 - φ_c) (exp (2 w_c) - 1) / 8 - k_c` and the right
side depends smoothly on `c` in the algebra `H^t(ℂ)`. -/
private theorem contDiff_reducedSolutionSobolev_add_two (hm : 0 < m) {t : ℝ} (ht : 1 < t)
    (h : ContDiff ℝ ∞ (reducedSolutionSobolev (m := m) (by linarith : (0 : ℝ) ≤ t))) :
    ContDiff ℝ ∞ (reducedSolutionSobolev (m := m) (by linarith : (0 : ℝ) ≤ t + 2)) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hal := finrank_real_complex_lt_two_mul ht
  have hP (c : Fin m → ℂ) : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  set R : H^{t}(ℂ) →L[ℂ] H^{t + 2}(ℂ) :=
    mapCLM (TemperedDistribution.laplacianResolvent ℂ 1) fun v ↦
      v.memSobolev_toDistr.laplacianResolvent one_pos
  set E : (Fin m → ℂ) → H^{t}(ℂ) := fun c ↦ expSubOne hal ((2 : ℂ) • reducedSolutionSobolev ht0 c)
  have key (c : Fin m → ℂ) : reducedSolutionSobolev (by linarith : (0 : ℝ) ≤ t + 2) c =
      R (reducedSolutionSobolev ht0 c -
        ((8⁻¹ : ℂ) • (E c - mulCLM hal (sobolevBackgroundDefect (hP c) ht0) (E c)) +
          sobolevBackgroundSource (hP c) ht0)) := by
    set W := reducedSolutionSobolev (by linarith : (0 : ℝ) ≤ t + 2) c
    have hN := reducedEquationMap_eq_zero_of_laplacian_eq (hP c) ht
      ((contDiff_reducedSolution _).of_le (by simp)) (fun z ↦ by
        rw [laplacian_reducedSolution (hP c) z, reducedSource_def, backgroundSource_def]
        ring) (coeFn_inclusionLp_reducedSolutionSobolev _ c)
    rw [reducedEquationMap_def, sub_apply, ContinuousLinearMap.id_apply,
      inclusion_reducedSolutionSobolev ht0 (by linarith) c] at hN
    -- The reduced equation `N(W) = 0` says that the last term is `Δ W`.
    rw [show (8⁻¹ : ℂ) • (E c - mulCLM hal (sobolevBackgroundDefect (hP c) ht0) (E c)) +
        sobolevBackgroundSource (hP c) ht0 = laplacianCLM t W by
      rw [← sub_eq_zero, ← hN]
      abel, ← inclusion_reducedSolutionSobolev ht0 (by linarith : t ≤ t + 2) c]
    refine ext ?_
    simp only [R, toDistr_mapCLM, toDistr_sub, toDistr_inclusion, toDistr_laplacianCLM]
    exact (TemperedDistribution.laplacianResolvent_one_sub_laplacian W.toDistr).symm
  have hE : ContDiff ℝ ∞ E :=
    ((contDiff_expSubOne hal).restrict_scalars ℝ).comp (h.const_smul (2 : ℂ))
  have hmul : ContDiff ℝ ∞ fun c ↦ mulCLM hal (sobolevBackgroundDefect (hP c) ht0) (E c) :=
    ((mulCLM hal).isBoundedBilinearMap.contDiff.restrict_scalars ℝ).comp
      ((contDiff_sobolevBackgroundDefect_monicOfCoeff hm ht0).prodMk hE)
  rw [funext key]
  exact (R.restrictScalars ℝ).contDiff.comp (h.sub (((hE.sub hmul).const_smul (8⁻¹ : ℂ)).add
    (contDiff_sobolevBackgroundSource_monicOfCoeff hm ht0)))

/-- **The reduced solution depends smoothly on the divisor in every Sobolev space.** For `s ≥ 0`,
the solution `w_c` of the reduced equation for the monic polynomial `P_c` with coefficients
`c ∈ ℂ^m`, as an element of `H^s(ℂ)`, depends smoothly on `c`. For `s = 2` this element is
`TauCeti.Vortex.sobolevReducedSolution c`. -/
theorem contDiff_ofRealSobolevFunction_reducedSolution (hs : 0 ≤ s) :
    ContDiff ℝ ∞ fun c : Fin m → ℂ ↦
      ofRealSobolevFunction hs (reducedSolution_mem_realSobolevFunctions (monicOfCoeff c) s) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show (fun c : Fin 0 → ℂ ↦ ofRealSobolevFunction hs
        (reducedSolution_mem_realSobolevFunctions (monicOfCoeff c) s)) = fun _ ↦
        ofRealSobolevFunction hs (reducedSolution_mem_realSobolevFunctions (monicOfCoeff
          (default : Fin 0 → ℂ)) s) from funext fun c ↦ by rw [Subsingleton.elim c default]]
    exact contDiff_const
  -- `c ↦ w_c` is smooth in `H²(ℂ)`, and each bootstrap step gains two orders.
  have h₂ : ContDiff ℝ ∞ (reducedSolutionSobolev (m := m) zero_le_two) := by
    rw [show reducedSolutionSobolev (m := m) zero_le_two = sobolevReducedSolution from
      funext fun c ↦ eq_sobolevReducedSolution_of_ae
        (coeFn_inclusionLp_reducedSolutionSobolev zero_le_two c)]
    exact contDiff_sobolevReducedSolution
  have hj (j : ℕ) :
      ContDiff ℝ ∞ (reducedSolutionSobolev (m := m) (by positivity : (0 : ℝ) ≤ 2 + j)) := by
    induction j with
    | zero => exact contDiff_reducedSolutionSobolev_of_le _ (by simp) h₂
    | succ j ih =>
      exact contDiff_reducedSolutionSobolev_of_le _ (by push_cast; linarith)
        (contDiff_reducedSolutionSobolev_add_two hm
          (by have := j.cast_nonneg (α := ℝ); linarith) ih)
  exact contDiff_reducedSolutionSobolev_of_le hs (by linarith [Nat.le_ceil s]) (hj ⌈s⌉₊)

end TauCeti.Vortex
