/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Composition
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Strongly parameter-dependent symbols at a fixed spectral parameter

At a fixed spectral parameter `z ∈ Λ`, a strongly parameter-dependent symbol `a` of order `m`
(`TauCeti.ParameterSymbol`) is an ordinary symbol `(x, ξ) ↦ a((x, ξ), z)` of order `m`
(`TauCeti.ParameterSymbol.eval`), since the weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is comparable to
`⟨ξ⟩` for fixed `z`. Evaluation commutes with the operations of the calculus: the linear
operations, the pointwise composition, the derivatives and the terms of the composition expansion
(`TauCeti.ParameterSymbol.eval_sharpTerm`). The quantization `Op(a(·, ·, z))` is therefore a
family of pseudodifferential operators to which the calculus of `TauCeti.Symbol` applies at each
`z`, while the parameter-dependent class records the estimates uniform in `z`.

In particular the parametrices with parameter of
`TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Composition` are, at every spectral
parameter, parametrices in the ordinary symbol calculus whose remainders have order `-N` uniformly
in `z` (`TauCeti.ParameterSymbol.IsElliptic.exists_sub_sum_sharpTerm_eval_left`,
`TauCeti.ParameterSymbol.IsElliptic.exists_sub_sum_sharpTerm_eval_right`).

## Implementation notes

The ordinary symbol estimates bound the mixed derivatives `∂ₓ^α ∂_ξ^β`, which are iterated
derivatives of `a` along unit position and frequency directions. Writing a unit frequency direction
as the dilation by `t = parameterWeight ξ z` of a direction of norm `t⁻¹` bounds them by the
dilated derivatives `parameterIteratedFDeriv` times `t ^ (-|β|)`.
-/

public section

noncomputable section

open Set Finset
open scoped ContDiff

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U]
  [NormedSpace ℂ U] {m m' : ℝ} {z : ℂ}

/-! ### Estimates at a fixed spectral parameter -/

/-- At a fixed spectral parameter `z`, every power of the weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is
bounded by a multiple of the same power of `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)`. -/
private theorem exists_rpow_parameterWeight_le (z : ℂ) (e : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : CoordinateSpace n,
      parameterWeight ξ z ^ e ≤ C * (1 + ‖ξ‖ ^ 2) ^ (e / 2) := by
  set K := Real.sqrt 2 * (1 + Real.sqrt ‖z‖)
  refine ⟨max 1 (K ^ e), le_max_of_le_left zero_le_one, fun ξ => ?_⟩
  set u := Real.sqrt (1 + ‖ξ‖ ^ 2) with hu_def
  have hu : 0 < u := Real.sqrt_pos.2 (by positivity)
  have hbr : (1 + ‖ξ‖ ^ 2) ^ (e / 2) = u ^ e := by
    rw [hu_def, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    ring_nf
  -- The weight lies between `u` and `K u`.
  have hlow : u ≤ parameterWeight ξ z :=
    (sqrt_one_add_norm_sq_le ξ).trans (by
      rw [parameterWeight_def]
      linarith [Real.sqrt_nonneg ‖z‖])
  have hup : parameterWeight ξ z ≤ K * u := by
    have h := one_add_norm_le_sqrt_two_mul_sqrt ξ
    have hz := Real.sqrt_nonneg ‖z‖
    rw [parameterWeight_def]
    calc 1 + ‖ξ‖ + Real.sqrt ‖z‖ ≤ (1 + ‖ξ‖) * (1 + Real.sqrt ‖z‖) := by
          nlinarith [norm_nonneg ξ]
      _ ≤ (Real.sqrt 2 * u) * (1 + Real.sqrt ‖z‖) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = K * u := by ring
  rw [hbr]
  rcases le_or_gt 0 e with he | he
  · calc parameterWeight ξ z ^ e ≤ (K * u) ^ e :=
          Real.rpow_le_rpow (parameterWeight_pos ξ z).le hup he
      _ = K ^ e * u ^ e := Real.mul_rpow (by positivity) hu.le
      _ ≤ max 1 (K ^ e) * u ^ e :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu.le e)
  · calc parameterWeight ξ z ^ e ≤ u ^ e := Real.rpow_le_rpow_of_nonpos hu hlow he.le
      _ ≤ max 1 (K ^ e) * u ^ e :=
          le_mul_of_one_le_left (Real.rpow_nonneg hu.le e) (le_max_left _ _)

/-- A mixed derivative `∂ₓ^α ∂_ξ^β` of the slice `q ↦ a(q, z)` is bounded by the dilated
derivative of `a` of order `|α| + |β|` times `parameterWeight ξ z ^ (-|β|)`. -/
private theorem norm_mixedDeriv_slice_le (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ ≤
      ‖parameterIteratedFDeriv (α.length + β.length) a.coefficient ((x, ξ), z)‖ *
        parameterWeight ξ z ^ (-(β.length : ℝ)) := by
  set t := parameterWeight ξ z
  have ht : 0 < t := parameterWeight_pos ξ z
  have hcd : ContDiff ℝ ∞ fun q => a.coefficient (q, z) :=
    contDiff_iff_contDiffAt.2 fun q =>
      (a.contDiffAt_coefficient (p := (q, z)) hz).comp q (contDiffAt_id.prodMk contDiffAt_const)
  -- The directions of `∂ₓ^α ∂_ξ^β`, and their preimages under the dilation by `t`.
  set w : Fin (α.length + β.length) → CoordinateSpace n × CoordinateSpace n :=
    Fin.append (fun i => (EuclideanSpace.single (α.get i) 1, 0))
      fun i => (0, EuclideanSpace.single (β.get i) 1)
  set v : Fin (α.length + β.length) → (CoordinateSpace n × CoordinateSpace n) × ℂ :=
    fun i => parameterDilation n t⁻¹ (w i, 0)
  have hv : (fun i => (w i, (0 : ℂ))) = fun i => parameterDilation n t (v i) := by
    funext i
    simp [v, smul_smul, ht.ne']
  have hprod : ∏ i, ‖v i‖ = t ^ (-(β.length : ℝ)) := by
    rw [Fin.prod_univ_add, Real.rpow_neg ht.le, Real.rpow_natCast, ← inv_pow]
    simp only [v, w, Fin.append_left, Fin.append_right, parameterDilation_apply, Prod.norm_def,
      norm_smul, PiLp.norm_single, norm_zero, smul_zero, Real.norm_eq_abs, abs_of_pos ht,
      abs_inv, norm_one, mul_one, max_eq_left zero_le_one, max_eq_right (inv_pos.2 ht).le,
      max_eq_left (inv_pos.2 ht).le, prod_const_one, one_mul, prod_const, card_univ,
      Fintype.card_fin]
  rw [mixedDeriv_eq_iteratedFDeriv_append α β (hcd.of_le (by exact_mod_cast le_top)),
    (a.contDiffAt_coefficient (p := ((x, ξ), z)) hz).iteratedFDeriv_prod_left _ (by simp),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearMap.inl_apply]
  rw [hv, ← parameterIteratedFDeriv_apply, ← hprod]
  exact ContinuousMultilinearMap.le_opNorm _ _

/-! ### Evaluation at a spectral parameter -/

/-- The symbol `(x, ξ) ↦ a((x, ξ), z)` of order `m` of a strongly parameter-dependent symbol `a` of
order `m` at a spectral parameter `z ∈ Λ`. -/
def eval (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) : Symbol n V W m where
  coefficient q := a.coefficient (q, z)
  contDiff_coefficient := contDiff_iff_contDiffAt.2 fun q =>
    (a.contDiffAt_coefficient (p := (q, z)) hz).comp q (contDiffAt_id.prodMk contDiffAt_const)
  exists_bound K hK α β := by
    obtain ⟨C, hC, ha⟩ := a.exists_bound K hK (α.length + β.length)
    obtain ⟨D, hD, hw⟩ := exists_rpow_parameterWeight_le (n := n) z (m - β.length)
    refine ⟨C * D, mul_nonneg hC hD, fun x hx ξ => ?_⟩
    have ht := parameterWeight_pos ξ z
    calc ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖
        ≤ ‖parameterIteratedFDeriv (α.length + β.length) a.coefficient ((x, ξ), z)‖ *
            parameterWeight ξ z ^ (-(β.length : ℝ)) := norm_mixedDeriv_slice_le a hz α β x ξ
      _ ≤ C * parameterWeight ξ z ^ m * parameterWeight ξ z ^ (-(β.length : ℝ)) :=
          mul_le_mul_of_nonneg_right (ha x hx ξ z hz) (Real.rpow_nonneg ht.le _)
      _ = C * parameterWeight ξ z ^ (m - β.length) := by
          rw [mul_assoc, ← Real.rpow_add ht, ← sub_eq_add_neg]
      _ ≤ C * (D * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :=
          mul_le_mul_of_nonneg_left (hw ξ) hC
      _ = C * D * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by ring

@[simp]
theorem coefficient_eval (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    (a.eval hz).coefficient q = a.coefficient (q, z) := (rfl)

@[simp]
theorem eval_zero (hz : z ∈ Λ) : (0 : ParameterSymbol n Λ V W m).eval hz = 0 := by
  ext1
  rfl

@[simp]
theorem eval_add (a b : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (a + b).eval hz = a.eval hz + b.eval hz := by
  ext1
  rfl

@[simp]
theorem eval_smul (c : ℂ) (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (c • a).eval hz = c • a.eval hz := by
  ext1
  rfl

@[simp]
theorem eval_neg (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) : (-a).eval hz = -a.eval hz := by
  ext1
  funext q
  simp

@[simp]
theorem eval_sub (a b : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (a - b).eval hz = a.eval hz - b.eval hz := by
  ext1
  funext q
  simp

@[simp]
theorem eval_sum {ι : Type*} (s : Finset ι) (a : ι → ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (∑ i ∈ s, a i).eval hz = ∑ i ∈ s, (a i).eval hz := by
  ext1
  funext q
  simp [Symbol.coefficient_sum]

@[simp]
theorem eval_inclusion (h : m ≤ m') (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (inclusion h a).eval hz = Symbol.inclusion h (a.eval hz) := by
  ext1
  funext q
  rw [coefficient_eval, coefficient_inclusion, Symbol.coefficient_inclusion, coefficient_eval]

@[simp]
theorem eval_comp (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (b.comp a).eval hz = (b.eval hz).comp (a.eval hz) := by
  ext1
  funext q
  rw [coefficient_eval, coefficient_comp, Symbol.coefficient_comp, coefficient_eval,
    coefficient_eval]

@[simp]
theorem eval_const (T : V →L[ℂ] W) (hz : z ∈ Λ) :
    (const T : ParameterSymbol n Λ V W 0).eval hz = Symbol.const T := by
  ext1
  funext ⟨x, ξ⟩
  simp [coefficient_const T x ξ hz, Symbol.coefficient_const]

/-- The pointwise inverse of a parameter-elliptic symbol evaluates to the pointwise inverse. -/
theorem coefficient_eval_inverse [CompleteSpace V] {a : ParameterSymbol n Λ V W m}
    (ha : a.IsElliptic) (hz : z ∈ Λ) (q : CoordinateSpace n × CoordinateSpace n) :
    ((a.inverse ha).eval hz).coefficient q = ((a.eval hz).coefficient q).inverse := by
  rw [coefficient_eval, coefficient_inverse, coefficient_eval]

/-- At a spectral parameter in `Λ`, the position derivative of a parameter-dependent symbol is the
position derivative of the symbol at that parameter. -/
@[simp]
theorem eval_spatialDeriv (j : Fin n) (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (spatialDeriv j a).eval hz = Symbol.spatialDeriv j (a.eval hz) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_eval, coefficient_spatialDeriv j a x ξ hz, Symbol.coefficient_spatialDeriv,
    coordinateDeriv_cons, coordinateDeriv_nil]
  have hd : HasFDerivAt (fun y => a.coefficient ((y, ξ), z))
      ((fderiv ℝ a.coefficient ((x, ξ), z)).comp
        ((ContinuousLinearMap.inl ℝ _ _).comp (ContinuousLinearMap.inl ℝ _ _))) x :=
    (a.differentiableAt_coefficient (p := ((x, ξ), z)) hz).hasFDerivAt.comp x
      (((hasFDerivAt_prodMk_left x ξ).prodMk (hasFDerivAt_const z x)).congr_fderiv
        (by ext <;> simp))
  simp only [coefficient_eval]
  rw [hd.fderiv]
  simp

/-- At a spectral parameter in `Λ`, the frequency derivative of a parameter-dependent symbol is the
frequency derivative of the symbol at that parameter. -/
@[simp]
theorem eval_frequencyDeriv (j : Fin n) (a : ParameterSymbol n Λ V W m) (hz : z ∈ Λ) :
    (frequencyDeriv j a).eval hz = Symbol.frequencyDeriv j (a.eval hz) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_eval, coefficient_frequencyDeriv j a x ξ hz, Symbol.coefficient_frequencyDeriv,
    coordinateDeriv_cons, coordinateDeriv_nil]
  have hd : HasFDerivAt (fun η => a.coefficient ((x, η), z))
      ((fderiv ℝ a.coefficient ((x, ξ), z)).comp
        ((ContinuousLinearMap.inl ℝ _ _).comp (ContinuousLinearMap.inr ℝ _ _))) ξ :=
    (a.differentiableAt_coefficient (p := ((x, ξ), z)) hz).hasFDerivAt.comp ξ
      (((hasFDerivAt_prodMk_right x ξ).prodMk (hasFDerivAt_const z ξ)).congr_fderiv
        (by ext <;> simp))
  simp only [coefficient_eval]
  rw [hd.fderiv]
  simp

/-- **Evaluation commutes with the composition expansion.** At a spectral parameter in `Λ`, the
terms of the composition expansion of parameter-dependent symbols are those of the symbols at that
parameter. -/
@[simp]
theorem eval_sharpTerm (a : ParameterSymbol n Λ W U m') (b : ParameterSymbol n Λ V W m)
    (k : ℕ) (hz : z ∈ Λ) :
    (a.sharpTerm b k).eval hz = (a.eval hz).sharpTerm (b.eval hz) k := by
  induction k generalizing m m' with
  | zero => rw [sharpTerm_zero, Symbol.sharpTerm_zero, eval_inclusion, eval_comp]
  | succ k ih =>
    rw [sharpTerm_succ, Symbol.sharpTerm_succ, eval_inclusion, eval_smul, eval_sum]
    simp only [ih, eval_frequencyDeriv, eval_spatialDeriv]

/-! ### Parametrices at each spectral parameter -/

section Parametrix

variable [CompleteSpace V] {a : ParameterSymbol n Λ V W m}

/-- **Left parametrices with parameter, in the ordinary calculus.** If `a` has order `m` and is
elliptic with parameter, then for every `N` there are parameter-dependent symbols `b` of order `-m`,
equal to `a⁻¹` up to order `-m - 1`, and `r` of order `-N` such that at every spectral parameter
`z ∈ Λ`, `1 - ∑_{k < N} sharpTerm b_z a_z k = r_z` in the ordinary symbol calculus. The remainder
`r_z` is a symbol of order `-N` whose estimates are uniform in `z`. -/
theorem IsElliptic.exists_sub_sum_sharpTerm_eval_left (ha : a.IsElliptic) (N : ℕ) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      (∃ d : ParameterSymbol n Λ W V (-m - 1),
        b.coefficient = (a.inverse ha).coefficient + d.coefficient) ∧
      ∃ r : ParameterSymbol n Λ V V (-N), ∀ (z : ℂ) (hz : z ∈ Λ),
        (Symbol.const (.id ℂ V) : Symbol n V V 0).coefficient -
          ∑ k ∈ range N, ((b.eval hz).sharpTerm (a.eval hz) k).coefficient =
            (r.eval hz).coefficient := by
  obtain ⟨b, hd, r, hr⟩ := ha.exists_sub_sum_sharpTerm_left N
  refine ⟨b, hd, r, fun z hz => ?_⟩
  funext q
  have h := congrFun hr (q, z)
  simp only [Pi.sub_apply, Finset.sum_apply] at h
  simpa [← eval_sharpTerm, coefficient_const _ q.1 q.2 hz, Symbol.coefficient_const,
    Symbol.coefficient_sum] using h

/-- **Right parametrices with parameter, in the ordinary calculus.** If `a` has order `m` and is
elliptic with parameter, then for every `N` there are parameter-dependent symbols `b` of order `-m`,
equal to `a⁻¹` up to order `-m - 1`, and `r` of order `-N` such that at every spectral parameter
`z ∈ Λ`, `1 - ∑_{k < N} sharpTerm a_z b_z k = r_z` in the ordinary symbol calculus. The remainder
`r_z` is a symbol of order `-N` whose estimates are uniform in `z`. -/
theorem IsElliptic.exists_sub_sum_sharpTerm_eval_right (ha : a.IsElliptic) (N : ℕ) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      (∃ d : ParameterSymbol n Λ W V (-m - 1),
        b.coefficient = (a.inverse ha).coefficient + d.coefficient) ∧
      ∃ r : ParameterSymbol n Λ W W (-N), ∀ (z : ℂ) (hz : z ∈ Λ),
        (Symbol.const (.id ℂ W) : Symbol n W W 0).coefficient -
          ∑ k ∈ range N, ((a.eval hz).sharpTerm (b.eval hz) k).coefficient =
            (r.eval hz).coefficient := by
  obtain ⟨b, hd, r, hr⟩ := ha.exists_sub_sum_sharpTerm_right N
  refine ⟨b, hd, r, fun z hz => ?_⟩
  funext q
  have h := congrFun hr (q, z)
  simp only [Pi.sub_apply, Finset.sum_apply] at h
  simpa [← eval_sharpTerm, coefficient_const _ q.1 q.2 hz, Symbol.coefficient_const,
    Symbol.coefficient_sum] using h

end Parametrix

end ParameterSymbol

end TauCeti
