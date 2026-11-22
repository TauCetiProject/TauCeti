/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Measure.Moments
import Mathlib.Algebra.CharZero.Infinite

/-!
# Multiplication by the coordinate on locally analytic functions and distributions

On the disc `a + pʰℤ_p` the coordinate is `x = a + pʰ w`, so multiplying the power series
`∑ₙ c(a, n) wⁿ` by `x` gives the power series with coefficients

`a • c(a, n) + pʰ • c(a, n - 1)`,

the second term being absent for `n = 0`. This is `TauCeti.AnalyticStage.mulCoord`, a continuous
linear endomorphism of the analytic stage `LA_h(E)` which does not increase norms
(`norm_mulCoord_le`). It evaluates to `x ↦ x • f(x)` (`eval_mulCoord`) and commutes with
re-expansion to the smaller discs (`transition_mulCoord`): on the disc of `a' = a + pʰ b` the
coordinate is `x = a' + p^(h+1) v`, and Pascal's rule matches the two re-expansions. Both
identities are proved on coefficients, so no torsion-freeness of `E` is needed.

The stage operators therefore induce `TauCeti.LocallyAnalytic.mulCoord` on the algebraic direct
limit `LA(ℤ_p, E)`. On the locally analytic Mahler terms it is the Mahler recurrence

`x (x choose n) = (n + 1) (x choose (n + 1)) + n (x choose n)`

(`mulCoord_mahlerTerm`), proved on the stage of level `n + 1`, where Amice's vectors of degree
`n` and `n + 1` are the Mahler terms themselves.

The transpose is multiplication of a distribution by the coordinate,
`TauCeti.LocallyAnalyticDistribution.mulCoord`, with `(x μ)(f) = μ(x f)`. It does not increase
the stage seminorms, and by the Mahler recurrence it acts on the Amice transform as the Mahler
derivation `∂ = (1 + T) d/dT` (`amiceTransform_mulCoord`). On the distribution of a measure it is
the measure weighted by the coordinate (`mulCoord_ofMeasure`), for which the corresponding
identity is `AbstractMeasure.amiceTransform_weight_id_smul_one`.

## Main definitions

* `TauCeti.AnalyticStage.mulCoord S`: multiplication by `x` on the analytic stage `LA_h(E)`.
* `TauCeti.LocallyAnalytic.mulCoord S`: multiplication by `x` on `LA(ℤ_p, E)`.
* `TauCeti.LocallyAnalyticDistribution.mulCoord`: multiplication of a distribution by `x`.

## Main results

* `TauCeti.AnalyticStage.eval_mulCoord`, `TauCeti.LocallyAnalytic.eval_mulCoord`: multiplication
  by `x` evaluates to `x ↦ x • f(x)`.
* `TauCeti.AnalyticStage.transition_mulCoord`: multiplication by `x` commutes with re-expansion.
* `TauCeti.LocallyAnalytic.mulCoord_mahlerTerm`: the Mahler recurrence for locally analytic
  Mahler terms.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mulCoord_le`: multiplication by `x` does not
  increase the stage seminorms.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mulCoord`: `A_{xμ} = ∂ A_μ`.
* `TauCeti.LocallyAnalyticDistribution.mulCoord_ofMeasure`: on measures, multiplication by `x`
  is the weighted measure.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.1,
  Lemma 3.29.
-/

public section

open Filter Topology
open scoped ZeroAtInfty Polynomial

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E]

/-- The coefficients of `x f` on the disc of `a`, where `x = a + pʰ w`. -/
private noncomputable def mulCoordCoeff (c : AnalyticStage p h E) : ZMod (p ^ h) × ℕ → E
  | (a, 0) => (a.val : ℤ_[p]) • c (a, 0)
  | (a, n + 1) => (a.val : ℤ_[p]) • c (a, n + 1) + (p : ℤ_[p]) ^ h • c (a, n)

private theorem norm_mulCoordCoeff_le (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) :
    ‖mulCoordCoeff c i‖ ≤ max ‖c i‖ ‖c (i.1, i.2 - 1)‖ := by
  obtain ⟨a, _ | n⟩ := i
  · exact (PadicInt.norm_smul_le_norm _ _).trans (le_max_left _ _)
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (PadicInt.norm_smul_le_norm _ _) (PadicInt.norm_smul_le_norm _ _))

private theorem norm_mulCoordCoeff_le_norm (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) :
    ‖mulCoordCoeff c i‖ ≤ ‖c‖ :=
  (norm_mulCoordCoeff_le c i).trans (max_le (c.norm_coe_le_norm _) (c.norm_coe_le_norm _))

private theorem tendsto_mulCoordCoeff (c : AnalyticStage p h E) :
    Tendsto (mulCoordCoeff c) cofinite (𝓝 0) := by
  -- Lowering the degree by one has fibres of at most two elements.
  have hφ : Tendsto (fun i : ZMod (p ^ h) × ℕ ↦ (i.1, i.2 - 1)) cofinite cofinite :=
    Tendsto.cofinite_of_finite_preimage_singleton fun j ↦ Set.finite_coe_iff.mpr <|
      (Set.toFinite ({j, (j.1, j.2 + 1)} : Set (ZMod (p ^ h) × ℕ))).subset fun i hi ↦ by
        obtain ⟨a, n⟩ := i
        obtain ⟨b, m⟩ := j
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases n with _ | n <;> simp
  have hc := tendsto_zero_iff_norm_tendsto_zero.mp c.tendsto_cofinite
  refine squeeze_zero_norm (norm_mulCoordCoeff_le c) ?_
  simpa using hc.max (hc.comp hφ)

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Multiplication by the coordinate `x` on the analytic stage `LA_h(E)`. On the disc of `a`,
where `x = a.val + pʰ w`, the coefficient of `wⁿ` in `x ∑ₖ c(a, k) wᵏ` is
`a.val • c(a, n) + pʰ • c(a, n - 1)`, the second term being absent for `n = 0`. -/
noncomputable def mulCoord : AnalyticStage p h E →L[S] AnalyticStage p h E :=
  let L : AnalyticStage p h E →ₗ[S] AnalyticStage p h E :=
    { toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete (mulCoordCoeff c) (tendsto_mulCoordCoeff c)
      map_add' c d := by
        ext ⟨a, _ | n⟩
        · simp [mulCoordCoeff, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, smul_add]
        · simp only [mulCoordCoeff, ZeroAtInftyContinuousMap.coe_mkOfDiscrete,
            FunLike.coe_add, Pi.add_apply, smul_add]
          abel
      map_smul' s c := by
        ext ⟨a, _ | n⟩ <;>
          simp [mulCoordCoeff, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, smul_comm _ s] }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦ ?_
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact norm_mulCoordCoeff_le_norm c i }

private theorem coe_mulCoord (c : AnalyticStage p h E) : ⇑(mulCoord S c) = mulCoordCoeff c :=
  ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _

/-- The constant coefficient of `x f` on the disc of `a` is `a.val` times that of `f`. -/
@[simp]
theorem mulCoord_apply_zero (c : AnalyticStage p h E) (a : ZMod (p ^ h)) :
    mulCoord S c (a, 0) = (a.val : ℤ_[p]) • c (a, 0) := by
  rw [coe_mulCoord, mulCoordCoeff]

/-- The coefficient of `w^(n+1)` in `x f` on the disc of `a` is
`a.val • c(a, n + 1) + pʰ • c(a, n)`. -/
@[simp]
theorem mulCoord_apply_succ (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (n : ℕ) :
    mulCoord S c (a, n + 1) =
      (a.val : ℤ_[p]) • c (a, n + 1) + (p : ℤ_[p]) ^ h • c (a, n) := by
  rw [coe_mulCoord, mulCoordCoeff]

/-- Multiplication by the coordinate does not increase norms. -/
theorem norm_mulCoord_le (c : AnalyticStage p h E) : ‖mulCoord S c‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦
    coe_mulCoord S c ▸ norm_mulCoordCoeff_le_norm c i

/-- Multiplication by the coordinate has operator norm at most `1`. -/
theorem opNorm_mulCoord_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] : ‖mulCoord (p := p) (h := h) (E := E) 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_mulCoord_le 𝕜 c

variable [CompleteSpace E]

/-- Multiplication by the coordinate evaluates to `x ↦ x • f(x)`. -/
@[simp]
theorem eval_mulCoord (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S (mulCoord S c) x = x • eval S c x := by
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  rw [PadicInt.discHomeomorph_apply]
  have hc := hasSum_eval_natCast_val_add_mul S c a w
  -- The terms of positive degree split into `a.val` times the shifted series of `f` and
  -- `pʰ w` times the series of `f`.
  have hsucc : HasSum (fun n ↦ w ^ (n + 1) • mulCoord S c (a, n + 1)) _ :=
    (((hasSum_nat_add_iff' 1).mpr hc).const_smul (a.val : ℤ_[p])).add
      (hc.const_smul ((p : ℤ_[p]) ^ h * w)) |>.congr_fun fun n ↦ by
      rw [mulCoord_apply_succ]
      module
  have hsum := (hasSum_nat_add_iff (f := fun n ↦ w ^ n • mulCoord S c (a, n)) 1).mp hsucc
  rw [(hasSum_eval_natCast_val_add_mul S (mulCoord S c) a w).unique hsum]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_smul, mulCoord_apply_zero]
  module

omit [CompleteSpace E] in
/-- Re-expanding `x f` on a disc `a + pʰ(b + p v)`: if the coefficient of `vʲ` (resp. `v^(j-1)`)
in the re-expansion of `f` is `D` (resp. `Y`, or `0` when `j = 0`), then that of `x f` is
`(a + pʰ b) D + p^(h+1) Y`. -/
private theorem hasSum_choose_smul_mulCoord (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (b : ℤ_[p]) (j : ℕ) {D Y : E}
    (hD : HasSum (fun k ↦ reexpandScalar b p k j • c (a, k)) D)
    (hY : HasSum (fun k ↦ (if j = 0 then 0 else reexpandScalar b p k (j - 1)) • c (a, k)) Y) :
    HasSum (fun k ↦ reexpandScalar b p k j • mulCoord S c (a, k))
      (((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * b) • D + (p : ℤ_[p]) ^ (h + 1) • Y) := by
  -- Split the terms of positive degree by Pascal's rule `reexpandScalar_succ_succ`.
  have hsucc : HasSum (fun k ↦ reexpandScalar b p (k + 1) j • mulCoord S c (a, k + 1)) _ :=
    ((((hasSum_nat_add_iff' 1).mpr hD).const_smul (a.val : ℤ_[p])).add
      (hD.const_smul ((p : ℤ_[p]) ^ h * b))).add (hY.const_smul ((p : ℤ_[p]) ^ (h + 1)))
      |>.congr_fun fun k ↦ by
      rw [mulCoord_apply_succ]
      rcases j with _ | j
      · simp only [reexpandScalar_zero_right, ↓reduceIte, pow_succ]
        module
      · simp only [reexpandScalar_succ_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        module
  have hsum := (hasSum_nat_add_iff
    (f := fun k ↦ reexpandScalar b p k j • mulCoord S c (a, k)) 1).mp hsucc
  simp only [Finset.range_one, Finset.sum_singleton, mulCoord_apply_zero] at hsum
  convert hsum using 1
  module

/-- Multiplication by the coordinate commutes with re-expansion to the discs of the next level. -/
theorem transition_mulCoord (c : AnalyticStage p h E) :
    transition S (mulCoord S c) = mulCoord S (transition S c) := by
  ext ⟨a', j⟩
  have hD (j : ℕ) := hasSum_transition_apply S c a' j
  rw [← (hasSum_transition_apply S (mulCoord S c) a' j).tsum_eq]
  rcases j with _ | j
  · rw [(hasSum_choose_smul_mulCoord S c _ _ 0 (hD 0) (Y := 0) (by simp)).tsum_eq,
      ← PadicInt.natCast_val_eq_add, mulCoord_apply_zero, smul_zero, add_zero]
  · rw [(hasSum_choose_smul_mulCoord S c _ _ (j + 1) (hD (j + 1)) (by simpa using hD j)).tsum_eq,
      ← PadicInt.natCast_val_eq_add, mulCoord_apply_succ]

/-- Multiplication by the coordinate commutes with re-expansion between any two levels. -/
theorem transitionLE_mulCoord {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transitionLE S hhk (mulCoord S c) = mulCoord S (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ih, transition_mulCoord,
      ContinuousLinearMap.comp_apply]

/-- The Mahler recurrence for Amice's polynomials of degrees `n` and `n + 1 < pʰ` on the disc of
`a`: these are `(a + pʰ w choose n)` and its successor, so multiplying by the coordinate
`a + pʰ w` gives `(n + 1) (a + pʰ w choose (n + 1)) + n (a + pʰ w choose n)`. -/
private theorem coord_mul_amicePolynomial {n : ℕ} (hn : n + 1 < p ^ h) (a : ℤ_[p]) :
    (Polynomial.C a + Polynomial.C ((p : ℤ_[p]) ^ h) * Polynomial.X) *
        amicePolynomial p h n a =
      ((n + 1 : ℕ) : ℤ_[p][X]) * amicePolynomial p h (n + 1) a +
        (n : ℤ_[p][X]) * amicePolynomial p h n a := by
  refine Polynomial.funext fun w ↦ ?_
  have hrec := DFunLike.congr_fun (id_mul_mahler (p := p) n) (a + (p : ℤ_[p]) ^ h * w)
  simp only [ContinuousMap.mul_apply, ContinuousMap.id_apply, ContinuousMap.add_apply,
    mahler_apply, nsmul_eq_mul] at hrec
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_natCast, eval_amicePolynomial, Nat.div_eq_of_lt hn,
    Nat.div_eq_of_lt (Nat.lt_succ_self n |>.trans hn), Nat.factorial_zero, Nat.cast_one,
    one_mul]
  push_cast at hrec ⊢
  exact hrec

omit [CompleteSpace E] in
/-- On the stage of a level `h` with `n + 1 < pʰ`, multiplication by the coordinate sends Amice's
vector `e_{h,n} • e = (x choose n) • e` to
`(x choose (n + 1)) • (n + 1) e + (x choose n) • n e`: for such `h` the factors `⌊n / pʰ⌋!` and
`⌊(n + 1) / pʰ⌋!` of Amice's vectors are `1`. -/
private theorem mulCoord_amiceTerm {n : ℕ} (hn : n + 1 < p ^ h) (e : E) :
    mulCoord S (amiceTerm p h n e) =
      amiceTerm p h (n + 1) ((n + 1) • e) + amiceTerm p h n (n • e) := by
  -- Compare the coefficients of both sides of `coord_mul_amicePolynomial`.
  ext ⟨a, k⟩
  have hk := congrArg (fun P : ℤ_[p][X] ↦ P.coeff k) (coord_mul_amicePolynomial hn (a.val : ℤ_[p]))
  rcases k with _ | k <;>
  · simp only [add_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, Polynomial.coeff_natCast_mul, mul_zero,
      add_zero] at hk
    simp only [mulCoord_apply_zero, mulCoord_apply_succ, FunLike.coe_add, Pi.add_apply,
      amiceTerm_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, ← add_smul]
    congr 1
    push_cast at hk ⊢
    linear_combination hk

end AnalyticStage

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Multiplication by the coordinate `x` on the locally analytic functions `LA(ℤ_p, E)`, induced
by `AnalyticStage.mulCoord` on each stage. -/
noncomputable def mulCoord : LocallyAnalytic p S E →ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.map (fun _ ↦ (AnalyticStage.mulCoord S).toLinearMap)
    fun _ _ hhk ↦ LinearMap.ext fun c ↦ (transitionLE_mulCoord S hhk c).symm

/-- Multiplication by the coordinate is computed on any stage. -/
@[simp]
theorem mulCoord_ofStage (h : ℕ) (c : AnalyticStage p h E) :
    mulCoord S (ofStage S h c) = ofStage S h (AnalyticStage.mulCoord S c) := by
  rw [mulCoord, ofStage_def, Module.DirectLimit.map_apply_of, ContinuousLinearMap.coe_coe]

/-- Multiplication by the coordinate evaluates to `x ↦ x • f(x)`. -/
@[simp]
theorem eval_mulCoord (f : LocallyAnalytic p S E) (x : ℤ_[p]) :
    eval S (mulCoord S f) x = x • eval S f x := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, mulCoord_ofStage, eval_ofStage, eval_ofStage, AnalyticStage.eval_mulCoord]

/-- **The Mahler recurrence.** Multiplication by the coordinate sends the Mahler term
`x ↦ (x choose n) • e` to `(x choose (n + 1)) • (n + 1) e + (x choose n) • n e`. -/
theorem mulCoord_mahlerTerm (e : E) (n : ℕ) :
    mulCoord S (mahlerTerm p S e n) =
      mahlerTerm p S ((n + 1) • e) (n + 1) + mahlerTerm p S (n • e) n := by
  have hn : n + 1 < p ^ (n + 1) := Nat.lt_pow_self hp.out.one_lt
  have hterm (m : ℕ) (hm : m < p ^ (n + 1)) (e' : E) :
      ofStage S (n + 1) (amiceTerm p (n + 1) m e') = mahlerTerm p S e' m := by
    rw [ofStage_amiceTerm, Nat.div_eq_of_lt hm, Nat.factorial_zero, one_smul]
  rw [← hterm n ((Nat.lt_succ_self n).trans hn), mulCoord_ofStage, mulCoord_amiceTerm S hn,
    map_add, hterm _ hn, hterm _ ((Nat.lt_succ_self n).trans hn)]

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- Multiplication of a locally analytic distribution by the coordinate `x`:
`(x μ)(f) = μ(x f)`. -/
noncomputable def mulCoord :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K where
  toFun μ := ⟨(μ : Module.Dual K (LocallyAnalytic p K K)) ∘ₗ LocallyAnalytic.mulCoord K,
    mem_iff.mpr fun h ↦ by
      convert (stage h μ ∘L AnalyticStage.mulCoord K).continuous using 1
      ext c
      simp⟩
  map_add' μ ν := rfl
  map_smul' a μ := rfl

/-- The distribution `x μ` takes the value `μ(x f)` on `f`. -/
@[simp]
theorem coe_mulCoord_apply (μ : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    (mulCoord μ : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.mulCoord K f) :=
  (rfl)

/-- The restriction of `x μ` to a stage is the restriction of `μ` composed with multiplication by
the coordinate on that stage. -/
@[simp]
theorem stage_mulCoord (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stage h (mulCoord μ) = stage h μ ∘L AnalyticStage.mulCoord K := by
  ext c
  simp

/-- Multiplication by the coordinate does not increase the stage seminorms. -/
theorem stageSeminorm_mulCoord_le (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h (mulCoord μ) ≤ stageSeminorm h μ := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stage_mulCoord]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) opNorm_mulCoord_le_one)

/-- **The Amice transform of `x μ`** is the Mahler derivation `∂ = (1 + T) d/dT` of the Amice
transform of `μ`. -/
@[simp]
theorem amiceTransform_mulCoord (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (mulCoord μ) = PowerSeries.mahlerDerivation K (amiceTransform μ) := by
  ext n
  simp only [coeff_amiceTransform, PowerSeries.coeff_mahlerDerivation, coe_mulCoord_apply,
    mulCoord_mahlerTerm, map_add, ← Nat.cast_smul_eq_nsmul K, mahlerTerm_smul, map_smul]
  push_cast [smul_eq_mul]
  ring

/-- Iterating, multiplication by `x ^ k` acts on the Amice transform as `∂ ^ k`. -/
theorem amiceTransform_iterate_mulCoord (μ : LocallyAnalyticDistribution p K) (k : ℕ) :
    amiceTransform (mulCoord^[k] μ) =
      (PowerSeries.mahlerDerivation K)^[k] (amiceTransform μ) :=
  Function.Semiconj.iterate_right (f := amiceTransform) amiceTransform_mulCoord k μ

/-- On the distribution of a measure, multiplication by the coordinate is the measure weighted by
the coordinate function. -/
@[simp]
theorem mulCoord_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) :
    mulCoord (ofMeasure μ) =
      ofMeasure (AbstractMeasure.weight (ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], K)) μ) := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  rw [coe_mulCoord_apply, coe_ofMeasure_apply, coe_ofMeasure_apply, AbstractMeasure.weight_apply]
  congr 1
  ext x
  simp [Algebra.smul_def]

end LocallyAnalyticDistribution

end TauCeti
