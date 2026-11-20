/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Measure.Dilation

/-!
# Dilation of locally analytic distributions on `ℤ_p`

For `a ∈ ℤ_p`, multiplication by `a` is an analytic self-map of `ℤ_p`, so a function analytic
on the discs of level `h` stays analytic on them after composition with it. This file constructs
the pullback `f ↦ (x ↦ f(a x))` on the analytic stages and on the locally analytic functions, and
its transpose, the pushforward `a_*` of locally analytic distributions, and computes the effect
of `a_*` on Amice transforms:

`A_{a_* μ}(T) = A_μ((1 + T) ^ a - 1)`.

For `a = p` this is the Frobenius operator `φ`, for a unit `a` it is the operator `σ_a`, and for
`a = 0` it sends `μ` to its total mass at `0`. On measures these are the pushforwards of
`TauCeti.NumberTheory.Padics.Measure.Dilation` and `TauCeti.NumberTheory.Padics.Measure.PhiPsi`.

On the analytic stage `LA_h(E)`, multiplication by `a` maps the disc of `b` into the disc of `d`,
where `a b.val = d.val + pʰ s` is the disc decomposition of `PadicInt.discHomeomorph`. In the disc
coordinates, `a (b.val + pʰ w) = d.val + pʰ (s + a w)`, so a series `∑ₙ c(d, n) vⁿ` on the disc of
`d` becomes `∑ₙ c(d, n) (s + a w)ⁿ`, whose coefficient of `wʲ` is
`∑ₙ (n choose j) sⁿ⁻ʲ aʲ • c(d, n)`. This is the affine re-expansion
`TauCeti.AnalyticStage.reexpand` that also defines the transitions between levels, so the
resulting map `TauCeti.AnalyticStage.compMulLeft` is, like the transition, an instance of
`TauCeti.AnalyticStage.reexpandMap` and does not increase norms. Re-expanding twice along affine
substitutions is re-expanding once along their composite
(`TauCeti.AnalyticStage.reexpand_reexpand`); this gives compatibility with the transitions
between levels and the composition law
`(a a')^* = a'^* ∘ a^*`, all on coefficients, so that no torsion-freeness of `E` is needed.

The Amice formula rests on the dilation formula for Mahler functions, `PadicInt.mahler_mul` of
`TauCeti.NumberTheory.Padics.Measure.Dilation`: `(a x choose n) = ∑_{m ≤ n} c_{n,m} (x choose m)`,
where `c_{n,m}` is the coefficient of `Tⁿ` in `((1 + T) ^ a - 1) ^ m`. On the stage of a level `h`
with `n < pʰ`, Amice's polynomials on each disc are binomial polynomials, and the Mahler identity
becomes a polynomial identity in the disc coordinate.

## Main definitions

* `TauCeti.AnalyticStage.compMulLeft S a`: dilation `LA_h(E) →L[S] LA_h(E)`.
* `TauCeti.LocallyAnalytic.compMulLeft S a`: dilation of locally analytic functions.
* `TauCeti.LocallyAnalyticDistribution.mapMulLeft a`: the pushforward `a_*`,
  `(a_* μ)(f) = μ(x ↦ f(a x))`.
* `TauCeti.LocallyAnalyticDistribution.phi p K`: the Frobenius operator `φ = p_*`.

## Main results

* `TauCeti.AnalyticStage.eval_compMulLeft`, `TauCeti.LocallyAnalytic.eval_compMulLeft`: dilation
  evaluates to `x ↦ f(a x)`.
* `TauCeti.AnalyticStage.transition_compMulLeft`: dilation commutes with raising the level.
* `TauCeti.LocallyAnalytic.compMulLeft_mahlerTerm`: dilation of the Mahler terms.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mapMulLeft_le`: `a_*` does not increase the
  stage seminorms.
* `TauCeti.LocallyAnalyticDistribution.mapMulLeft_mul`: `(a a')_* = a_* ∘ a'_*`.
* `TauCeti.LocallyAnalyticDistribution.mapMulLeft_ofMeasure`: on measures, `a_*` is the
  pushforward of measures.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mapMulLeft`:
  `A_{a_* μ}(T) = A_μ((1 + T) ^ a - 1)`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_phi`: `A_{φ μ}(T) = A_μ((1 + T) ^ p - 1)`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mapMulLeft_zero`: `A_{0_* μ}` is the
  constant series `μ(1)`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.5.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.5.
-/

public section

open Filter Topology
open scoped ZeroAtInfty Polynomial

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace AnalyticStage

/-! ### Dilation on an analytic stage -/

section Stage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E]

/-- The disc label and the disc coordinate of `a b.val`, for the centre `b.val` of a disc of
level `h`. -/
private noncomputable def mulDisc (a : ℤ_[p]) (b : ZMod (p ^ h)) : ZMod (p ^ h) × ℤ_[p] :=
  (PadicInt.discHomeomorph p h).symm (a * b.val)

private theorem natCast_val_mulDisc_add (a : ℤ_[p]) (b : ZMod (p ^ h)) :
    ((mulDisc a b).1.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (mulDisc a b).2 = a * b.val := by
  rw [← PadicInt.discHomeomorph_apply, mulDisc, Homeomorph.apply_symm_apply]

variable [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Dilation on the analytic stage `LA_h(E)`**: the coefficient vector of `x ↦ f(a x)`, for
`a ∈ ℤ_p`. Multiplication by `a` maps the disc of `b` into the disc of `d`, where
`a b.val = d.val + pʰ s`; in the disc coordinates, `a (b.val + pʰ w) = d.val + pʰ (s + a w)`, so
the coefficient of `wʲ` is `∑ₙ (n choose j) sⁿ⁻ʲ aʲ • c(d, n)`. -/
noncomputable def compMulLeft (a : ℤ_[p]) : AnalyticStage p h E →L[S] AnalyticStage p h E :=
  reexpandMap S (fun b ↦ (mulDisc a b).1) (fun b ↦ (mulDisc a b).2) fun _ ↦ a

private theorem coe_compMulLeft (a : ℤ_[p]) (c : AnalyticStage p h E) :
    ⇑(compMulLeft S a c) =
      fun i ↦ reexpand (mulDisc a i.1).2 a (fun n ↦ c ((mulDisc a i.1).1, n)) i.2 :=
  funext fun ⟨b, j⟩ ↦ by rw [compMulLeft, reexpandMap_apply]

/-- The re-expansion formula for dilation: if `a b.val = d.val + pʰ s`, where `(d, s)` is the disc
decomposition of `a b.val`, the coefficients on the disc of `b` re-expand those on the disc of `d`
along `s + a w`. -/
theorem compMulLeft_apply (a : ℤ_[p]) (c : AnalyticStage p h E) (b : ZMod (p ^ h)) (j : ℕ) :
    compMulLeft S a c (b, j) = reexpand ((PadicInt.discHomeomorph p h).symm (a * b.val)).2 a
      (fun n ↦ c (((PadicInt.discHomeomorph p h).symm (a * b.val)).1, n)) j := by
  simp only [coe_compMulLeft, mulDisc]

/-- Dilation does not increase norms. -/
theorem norm_compMulLeft_le (a : ℤ_[p]) (c : AnalyticStage p h E) :
    ‖compMulLeft S a c‖ ≤ ‖c‖ :=
  norm_reexpandMap_le S _ _ _ c

/-- Dilation has operator norm at most `1`. -/
theorem opNorm_compMulLeft_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] (a : ℤ_[p]) :
    ‖compMulLeft (p := p) (h := h) (E := E) 𝕜 a‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_compMulLeft_le 𝕜 a c

/-- Dilation evaluates to `x ↦ f(a x)`. -/
@[simp]
theorem eval_compMulLeft (a : ℤ_[p]) (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S (compMulLeft S a c) x = eval S c (a * x) := by
  obtain ⟨⟨b, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  have hx : a * ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) =
      ((mulDisc a b).1.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * ((mulDisc a b).2 + a * w) := by
    rw [mul_add, ← natCast_val_mulDisc_add]
    ring
  rw [PadicInt.discHomeomorph_apply, compMulLeft, eval_reexpandMap_natCast_val_add_mul, hx]

/-- Dilation commutes with re-expansion to the discs of the next level. -/
theorem transition_compMulLeft (a : ℤ_[p]) (c : AnalyticStage p h E) :
    transition S (compMulLeft S a c) = compMulLeft S a (transition S c) := by
  ext ⟨b', j⟩
  -- Both sides re-expand `c` on the disc of level `h` containing `a b'.val`, at the
  -- disc coordinate of `a b'.val`.
  have hy : (((mulDisc a b').1.val : ZMod (p ^ h)),
      ((((mulDisc a b').1.val / p ^ h : ℕ) : ℤ_[p]) + p * (mulDisc a b').2)) =
      ((mulDisc a (b'.val : ZMod (p ^ h))).1,
        (mulDisc a (b'.val : ZMod (p ^ h))).2 + a * ((b'.val / p ^ h : ℕ) : ℤ_[p])) := by
    have h₁ := natCast_val_mulDisc_add a b'
    have h₂ := natCast_val_mulDisc_add a (b'.val : ZMod (p ^ h))
    -- A centre of level `h + 1` is the centre of level `h` below it plus `pʰ` times a digit.
    rw [PadicInt.natCast_eq_natCast_val_add_mul h (mulDisc a b').1.val,
      PadicInt.natCast_eq_natCast_val_add_mul h b'.val] at h₁
    rw [← PadicInt.discHomeomorph_symm_natCast_val_add_mul h,
      ← PadicInt.discHomeomorph_symm_natCast_val_add_mul h]
    congr 1
    linear_combination h₁ - h₂
  obtain ⟨hd, hs⟩ := Prod.mk.inj hy
  rw [transition_apply, coe_compMulLeft, coe_compMulLeft]
  simp only [transition_apply]
  rw [reexpand_reexpand (tendsto_apply_mk c _), reexpand_reexpand (tendsto_apply_mk c _), hd, hs,
    mul_comm (p : ℤ_[p]) a]

/-- Dilation commutes with re-expansion between any two levels. -/
theorem transitionLE_compMulLeft (a : ℤ_[p]) {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transitionLE S hhk (compMulLeft S a c) = compMulLeft S a (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ih, transition_compMulLeft,
      ContinuousLinearMap.comp_apply]

private theorem mulDisc_eq (a : ℤ_[p]) (b : ZMod (p ^ h)) {y : ZMod (p ^ h) × ℤ_[p]}
    (hy : (y.1.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * y.2 = a * b.val) : mulDisc a b = y := by
  rw [mulDisc, ← hy, PadicInt.discHomeomorph_symm_natCast_val_add_mul]

/-- Dilation by `1` is the identity. -/
@[simp]
theorem compMulLeft_one (c : AnalyticStage p h E) : compMulLeft S 1 c = c := by
  ext ⟨b, j⟩
  rw [coe_compMulLeft]
  simp [mulDisc_eq 1 b (y := (b, 0)) (by simp)]

/-- Dilations compose: `x ↦ f(a a' x)` is `x ↦ f(a x)` dilated by `a'`. -/
theorem compMulLeft_mul (a a' : ℤ_[p]) (c : AnalyticStage p h E) :
    compMulLeft S (a * a') c = compMulLeft S a' (compMulLeft S a c) := by
  ext ⟨b, j⟩
  have hy : mulDisc (a * a') b = ((mulDisc a (mulDisc a' b).1).1,
      (mulDisc a (mulDisc a' b).1).2 + a * (mulDisc a' b).2) :=
    mulDisc_eq _ _ <| by
      linear_combination natCast_val_mulDisc_add a (mulDisc a' b).1 +
        a * natCast_val_mulDisc_add a' b
  simp only [coe_compMulLeft]
  rw [reexpand_reexpand (tendsto_apply_mk c _), hy]

/-- On the stage of a level `h` with `n < pʰ`, dilation by `a` sends Amice's vector
`e_{h,n} • e = (x choose n) • e` to `∑_{m ≤ n} (x choose m) • c_{n,m} e`, where `c_{n,m}` is the
coefficient of `Tⁿ` in `((1 + T) ^ a - 1) ^ m`: for such `h` the factors `⌊m / pʰ⌋!` of Amice's
vectors are `1`. -/
private theorem compMulLeft_amiceTerm (a : ℤ_[p]) {n : ℕ} (hn : n < p ^ h) (e : E) :
    compMulLeft S a (amiceTerm p h n e) = ∑ m ∈ Finset.range (n + 1), amiceTerm p h m
      (PowerSeries.coeff n ((PowerSeries.binomialSeries ℤ_[p] a - 1) ^ m) • e) := by
  ext ⟨b, j⟩
  -- On the disc of `b`, both sides are polynomials in the disc coordinate.
  have hpoly : (amicePolynomial p h n ((mulDisc a b).1.val : ℤ_[p])).comp
      (Polynomial.C (mulDisc a b).2 + Polynomial.C a * Polynomial.X) =
      ∑ m ∈ Finset.range (n + 1), Polynomial.C
        (PowerSeries.coeff n ((PowerSeries.binomialSeries ℤ_[p] a - 1) ^ m)) *
          amicePolynomial p h m (b.val : ℤ_[p]) := by
    have : Infinite ℤ_[p] := Infinite.of_injective _ Nat.cast_injective
    refine Polynomial.funext fun w ↦ ?_
    have hx : ((mulDisc a b).1.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * ((mulDisc a b).2 + a * w) =
        a * ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) := by
      linear_combination natCast_val_mulDisc_add a b
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_finsetSum, eval_amicePolynomial, hx,
      Nat.div_eq_of_lt hn, Nat.factorial_zero, Nat.cast_one, one_mul, ← mahler_apply,
      PadicInt.mahler_mul]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Nat.div_eq_of_lt ((Finset.mem_range_succ_iff.mp hm).trans_lt hn)]
    simp
  have hcoeff := congrArg (fun P ↦ P.coeff j) hpoly
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at hcoeff
  rw [coe_compMulLeft]
  simp only [amiceTerm_apply, reexpand_coeff_smul, hcoeff, Finset.sum_smul]
  simp [amiceTerm_apply, smul_smul, mul_comm]

end Stage

end AnalyticStage

/-! ### Dilation of locally analytic functions -/

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Dilation `f ↦ (x ↦ f(a x))` on the locally analytic functions `LA(ℤ_p, E)`, induced by
`AnalyticStage.compMulLeft` on each stage. -/
noncomputable def compMulLeft (a : ℤ_[p]) : LocallyAnalytic p S E →ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.map (fun _ ↦ (AnalyticStage.compMulLeft S a).toLinearMap)
    fun _ _ hhk ↦ LinearMap.ext fun c ↦ (transitionLE_compMulLeft S a hhk c).symm

/-- Dilation is computed on any stage. -/
@[simp]
theorem compMulLeft_ofStage (a : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h E) :
    compMulLeft S a (ofStage S h c) = ofStage S h (AnalyticStage.compMulLeft S a c) := by
  rw [compMulLeft, ofStage_def, Module.DirectLimit.map_apply_of, ContinuousLinearMap.coe_coe]

/-- Dilation evaluates to `x ↦ f(a x)`. -/
@[simp]
theorem eval_compMulLeft (a : ℤ_[p]) (f : LocallyAnalytic p S E) (x : ℤ_[p]) :
    eval S (compMulLeft S a f) x = eval S f (a * x) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, compMulLeft_ofStage, eval_ofStage, eval_ofStage,
    AnalyticStage.eval_compMulLeft]

/-- Dilation by `1` is the identity. -/
@[simp]
theorem compMulLeft_one (f : LocallyAnalytic p S E) : compMulLeft S 1 f = f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, compMulLeft_ofStage, AnalyticStage.compMulLeft_one]

/-- Dilations compose: `x ↦ f(a a' x)` is `x ↦ f(a x)` dilated by `a'`. -/
theorem compMulLeft_mul (a a' : ℤ_[p]) (f : LocallyAnalytic p S E) :
    compMulLeft S (a * a') f = compMulLeft S a' (compMulLeft S a f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, compMulLeft_ofStage, compMulLeft_ofStage, compMulLeft_ofStage,
    AnalyticStage.compMulLeft_mul]

/-- **Mahler terms of a dilation.** Dilation by `a` sends the Mahler term `x ↦ (x choose n) • e`
to `∑_{m ≤ n} (x choose m) • c_{n,m} e`, where `c_{n,m}` is the coefficient of `Tⁿ` in
`((1 + T) ^ a - 1) ^ m`. -/
theorem compMulLeft_mahlerTerm (a : ℤ_[p]) (e : E) (n : ℕ) :
    compMulLeft S a (mahlerTerm p S e n) = ∑ m ∈ Finset.range (n + 1), mahlerTerm p S
      (PowerSeries.coeff n ((PowerSeries.binomialSeries ℤ_[p] a - 1) ^ m) • e) m := by
  have hn : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  rw [mahlerTerm_def, compMulLeft_ofStage, compMulLeft_amiceTerm S a hn, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [ofStage_amiceTerm, Nat.div_eq_of_lt ((Finset.mem_range_succ_iff.mp hm).trans_lt hn),
    Nat.factorial_zero, one_smul]

end LocallyAnalytic

/-! ### Pushforward of distributions along dilations -/

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- The pushforward of a locally analytic distribution along multiplication by `a ∈ ℤ_p`:
`(a_* μ)(f) = μ(x ↦ f(a x))`. -/
noncomputable def mapMulLeft (a : ℤ_[p]) :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K where
  toFun μ := ⟨(μ : Module.Dual K (LocallyAnalytic p K K)) ∘ₗ LocallyAnalytic.compMulLeft K a,
    mem_iff.mpr fun h ↦ by
      convert (stage h μ ∘L AnalyticStage.compMulLeft K a).continuous using 1
      ext c
      simp⟩
  map_add' μ ν := rfl
  map_smul' b μ := rfl

/-- The distribution `a_* μ` takes the value `μ(x ↦ f(a x))` on `f`. -/
@[simp]
theorem coe_mapMulLeft_apply (a : ℤ_[p]) (μ : LocallyAnalyticDistribution p K)
    (f : LocallyAnalytic p K K) :
    (mapMulLeft a μ : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.compMulLeft K a f) :=
  (rfl)

/-- The restriction of `a_* μ` to a stage is the restriction of `μ` composed with dilation on that
stage. -/
@[simp]
theorem stage_mapMulLeft (a : ℤ_[p]) (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stage h (mapMulLeft a μ) = stage h μ ∘L AnalyticStage.compMulLeft K a := by
  ext c
  simp

/-- Pushforward along a dilation does not increase the stage seminorms. -/
theorem stageSeminorm_mapMulLeft_le (a : ℤ_[p]) (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h (mapMulLeft a μ) ≤ stageSeminorm h μ := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stage_mapMulLeft]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (opNorm_compMulLeft_le_one a))

/-- Pushforward along multiplication by `1` is the identity. -/
@[simp]
theorem mapMulLeft_one (μ : LocallyAnalyticDistribution p K) : mapMulLeft 1 μ = μ :=
  Subtype.ext <| LinearMap.ext fun f ↦ by simp

/-- Pushforwards along dilations compose: `(a a')_* = a_* ∘ a'_*`. -/
theorem mapMulLeft_mul (a a' : ℤ_[p]) (μ : LocallyAnalyticDistribution p K) :
    mapMulLeft (a * a') μ = mapMulLeft a (mapMulLeft a' μ) :=
  Subtype.ext <| LinearMap.ext fun f ↦ by simp [LocallyAnalytic.compMulLeft_mul]

/-- On the distribution of a measure, pushforward along a dilation is the pushforward of the
measure. -/
@[simp]
theorem mapMulLeft_ofMeasure (a : ℤ_[p]) (μ : AbstractMeasure ℤ_[p] K K) :
    mapMulLeft a (ofMeasure μ) = ofMeasure (AbstractMeasure.map (ContinuousMap.mulLeft a) μ) := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  rw [coe_mapMulLeft_apply, coe_ofMeasure_apply, coe_ofMeasure_apply, AbstractMeasure.map_apply]
  congr 1
  ext x
  simp

/-- **The Amice transform of a dilation.** Pushforward along multiplication by `a ∈ ℤ_p` substitutes
`(1 + T) ^ a - 1` into the Amice transform: `A_{a_* μ}(T) = A_μ((1 + T) ^ a - 1)`. -/
theorem amiceTransform_mapMulLeft (a : ℤ_[p]) (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (mapMulLeft a μ) =
      (amiceTransform μ).subst (PowerSeries.binomialSeries K a - 1) := by
  have hmap : PowerSeries.binomialSeries K a - 1 = PowerSeries.map (algebraMap ℤ_[p] K)
      (PowerSeries.binomialSeries ℤ_[p] a - 1) := by
    ext n
    simp [Algebra.smul_def]
  ext n
  rw [coeff_amiceTransform, coe_mapMulLeft_apply, compMulLeft_mahlerTerm, map_sum,
    PowerSeries.coeff_subst_eq_sum_range _ (by simp) n]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  -- Make the `ℤ_p`-coefficient a `K`-scalar and pull it out of the Mahler term and of `μ`.
  rw [hmap, ← map_pow, PowerSeries.coeff_map, coeff_amiceTransform, algebra_compatible_smul K,
    mahlerTerm_smul, map_smul]
  exact mul_comm _ _

/-- Pushforwards along dilations commute. -/
theorem mapMulLeft_comm (a a' : ℤ_[p]) (μ : LocallyAnalyticDistribution p K) :
    mapMulLeft a (mapMulLeft a' μ) = mapMulLeft a' (mapMulLeft a μ) := by
  rw [← mapMulLeft_mul, ← mapMulLeft_mul, mul_comm]

variable (p K) in
/-- The Frobenius operator `φ` on locally analytic distributions on `ℤ_p`: pushforward along
`x ↦ p x`, so that `(φ μ)(f) = μ(x ↦ f(p x))`. -/
noncomputable def phi : LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K :=
  mapMulLeft (p : ℤ_[p])

/-- `φ` is pushforward along multiplication by `p`. -/
theorem phi_eq_mapMulLeft : phi p K = mapMulLeft (p : ℤ_[p]) :=
  (rfl)

/-- **The Amice transform of `φ μ`** is the Amice transform of `μ` composed with
`T ↦ (1 + T) ^ p - 1`: `A_{φ μ}(T) = A_μ((1 + T) ^ p - 1)`. -/
theorem amiceTransform_phi (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (phi p K μ) =
      (amiceTransform μ).subst ((1 + PowerSeries.X : PowerSeries K) ^ p - 1) := by
  rw [phi_eq_mapMulLeft, amiceTransform_mapMulLeft, PowerSeries.binomialSeries_nat]

/-- On the distribution of a measure, `φ` is Frobenius on measures. -/
@[simp]
theorem phi_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) :
    phi p K (ofMeasure μ) = ofMeasure (AbstractMeasure.phiMeasure μ) := by
  rw [phi_eq_mapMulLeft, mapMulLeft_ofMeasure, AbstractMeasure.phiMeasure_eq_map]

/-- `φ` commutes with pushforward along every dilation; in particular with `σ_a` for
`a ∈ ℤ_pˣ`. -/
theorem phi_mapMulLeft (a : ℤ_[p]) (μ : LocallyAnalyticDistribution p K) :
    phi p K (mapMulLeft a μ) = mapMulLeft a (phi p K μ) := by
  rw [phi_eq_mapMulLeft, mapMulLeft_comm]

/-- Dilation by zero sends a distribution to its total mass at zero: its Amice transform is the
constant series `μ(1)`. -/
@[simp]
theorem amiceTransform_mapMulLeft_zero (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (mapMulLeft 0 μ) =
      PowerSeries.C (PowerSeries.constantCoeff (amiceTransform μ)) := by
  rw [amiceTransform_mapMulLeft]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.C_apply]

end LocallyAnalyticDistribution

end TauCeti
