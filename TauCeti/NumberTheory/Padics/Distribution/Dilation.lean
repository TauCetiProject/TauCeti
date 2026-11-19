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
`∑ₙ (n choose j) sⁿ⁻ʲ aʲ • c(d, n)`. These coefficients are again a null family, and the
resulting map `TauCeti.AnalyticStage.compMulLeft` does not increase norms. Re-expanding twice
along affine substitutions is re-expanding once along their composite; this gives the evaluation
formula, compatibility with the transitions between levels, and the composition law
`(a a')^* = a'^* ∘ a^*`, all on coefficients, so that no torsion-freeness of `E` is needed.

The Amice formula rests on the dilation formula for Mahler functions, `PadicInt.mahler_mul`:
`(a x choose n) = ∑_{m ≤ n} c_{n,m} (x choose m)`, where `c_{n,m}` is the coefficient of `Tⁿ` in
`((1 + T) ^ a - 1) ^ m`. It is the coefficientwise form of the corresponding identity for the
Dirac measure at `x`. On the stage of a level `h` with `n < pʰ`, Amice's polynomials on each disc
are binomial polynomials, and the Mahler identity becomes a polynomial identity in the disc
coordinate.

## Main definitions

* `TauCeti.AnalyticStage.compMulLeft S a`: dilation `LA_h(E) →L[S] LA_h(E)`.
* `TauCeti.LocallyAnalytic.compMulLeft S a`: dilation of locally analytic functions.
* `TauCeti.LocallyAnalyticDistribution.mapMulLeft a`: the pushforward `a_*`,
  `(a_* μ)(f) = μ(x ↦ f(a x))`.
* `TauCeti.LocallyAnalyticDistribution.phi p K`: the Frobenius operator `φ = p_*`.

## Main results

* `PadicInt.mahler_mul`: the Mahler expansion of `x ↦ (a x choose n)`.
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

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.5.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.5.
-/

public section

open Filter Topology
open scoped ZeroAtInfty Polynomial

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Mahler functions of a dilation.** For `a ∈ ℤ_p`, the function `x ↦ (a x choose n)` is the
integral combination `∑_{k ≤ n} c_{n,k} (x choose k)`, where `c_{n,k}` is the coefficient of `Tⁿ`
in `((1 + T) ^ a - 1) ^ k`. This is the coefficientwise form of
`(1 + T) ^ (a x) = ((1 + T) ^ a) ^ x = ∑ₖ (x choose k) ((1 + T) ^ a - 1) ^ k`. -/
theorem mahler_mul (a x : ℤ_[p]) (n : ℕ) :
    mahler n (a * x) = ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff n ((PowerSeries.binomialSeries ℤ_[p] a - 1) ^ k) * mahler k x := by
  have h := congrArg (PowerSeries.coeff n)
    (AbstractMeasure.amiceTransform_map_mulLeft (AbstractMeasure.dirac ℤ_[p] x) a)
  rw [PowerSeries.coeff_subst_eq_sum_range _ (by simp) n] at h
  simpa [AbstractMeasure.coeff_amiceTransform, mahler_apply, mul_comm] using h

end PadicInt

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace AnalyticStage

/-! ### Affine re-expansion of coefficient sequences -/

section Reexpansion

open Polynomial

/-- The coefficient `(n choose j) sⁿ⁻ʲ tʲ` of `vʲ` in `(s + t v)ⁿ`. -/
private noncomputable def reexpandScalar (s t : ℤ_[p]) (n j : ℕ) : ℤ_[p] :=
  (n.choose j : ℤ_[p]) * s ^ (n - j) * t ^ j

private theorem reexpandScalar_of_lt (s t : ℤ_[p]) {n j : ℕ} (hnj : n < j) :
    reexpandScalar s t n j = 0 := by
  simp [reexpandScalar, Nat.choose_eq_zero_of_lt hnj]

/-- The coefficients of `(C s + C t X)ⁿ` are the re-expansion scalars. -/
private theorem coeff_C_add_C_mul_X_pow (s t : ℤ_[p]) (n j : ℕ) :
    ((C s + C t * X) ^ n).coeff j = reexpandScalar s t n j := by
  have hcomp : (C s + C t * X) ^ n = ((X + C s) ^ n).comp (C t * X) := by
    rw [pow_comp, add_comp, X_comp, C_comp, add_comm]
  rw [hcomp, comp_C_mul_X_coeff, coeff_X_add_C_pow, reexpandScalar]
  ring

/-- Substituting `s + t X` into a polynomial of degree below `N` re-expands its coefficients. -/
private theorem coeff_comp_C_add_C_mul_X (P : ℤ_[p][X]) {N : ℕ} (hP : P.natDegree < N)
    (s t : ℤ_[p]) (j : ℕ) :
    (P.comp (C s + C t * X)).coeff j =
      ∑ k ∈ Finset.range N, P.coeff k * reexpandScalar s t k j := by
  conv_lhs => rw [P.as_sum_range' N hP]
  simp [sum_comp, coeff_C_add_C_mul_X_pow]

/-- Re-expanding twice is re-expanding once: `s₁ + t₁ (s₂ + t₂ u) = (s₁ + t₁ s₂) + t₁ t₂ u`. -/
private theorem sum_reexpandScalar_mul (s₁ t₁ s₂ t₂ : ℤ_[p]) (n j : ℕ) :
    ∑ m ∈ Finset.range (n + 1), reexpandScalar s₂ t₂ m j * reexpandScalar s₁ t₁ n m =
      reexpandScalar (s₁ + t₁ * s₂) (t₁ * t₂) n j := by
  have hdeg : ((C s₁ + C t₁ * X) ^ n).natDegree < n + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_pow_le_of_le n ?_).trans (mul_one n).le)
    rw [add_comm]
    exact natDegree_linear_le
  have hcomp : ((C s₁ + C t₁ * X) ^ n).comp (C s₂ + C t₂ * X) =
      (C (s₁ + t₁ * s₂) + C (t₁ * t₂) * X) ^ n := by
    simp only [pow_comp, add_comp, mul_comp, C_comp, X_comp, map_add, map_mul]
    ring
  have h := coeff_comp_C_add_C_mul_X _ hdeg s₂ t₂ j
  rw [hcomp, coeff_C_add_C_mul_X_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [coeff_C_add_C_mul_X_pow, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]

/-- The coefficients of `∑ₙ (s + t v)ⁿ • cₙ` in powers of `v`. -/
private noncomputable def reexpand (s t : ℤ_[p]) (c : ℕ → E) (j : ℕ) : E :=
  ∑' n, reexpandScalar s t n j • c n

omit [IsBoundedSMul ℤ_[p] E] in
/-- Re-expanding the coefficients of a polynomial is substituting `s + t X` into it. -/
private theorem reexpand_coeff_smul (P : ℤ_[p][X]) (s t : ℤ_[p]) (e : E) (j : ℕ) :
    reexpand s t (fun k ↦ P.coeff k • e) j = (P.comp (C s + C t * X)).coeff j • e := by
  rw [coeff_comp_C_add_C_mul_X P (Nat.lt_succ_self _) s t j, Finset.sum_smul, reexpand]
  refine (tsum_eq_sum fun k hk ↦ ?_).trans
    (Finset.sum_congr rfl fun k _ ↦ by rw [smul_smul, mul_comm])
  rw [Finset.mem_range, not_lt] at hk
  simp [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hk)]

private theorem norm_smul_le_norm (r : ℤ_[p]) (e : E) : ‖r • e‖ ≤ ‖e‖ :=
  (norm_smul_le r e).trans (mul_le_of_le_one_left (norm_nonneg e) (PadicInt.norm_le_one r))

/-- A coefficient of a re-expansion is bounded by the coefficients of the same or higher degree. -/
private theorem norm_reexpand_le [IsUltrametricDist E] (s t : ℤ_[p]) {c : ℕ → E} {C : ℝ}
    (hC : 0 ≤ C) {j : ℕ} (hc : ∀ n, j ≤ n → ‖c n‖ ≤ C) : ‖reexpand s t c j‖ ≤ C :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun n ↦ by
    rcases lt_or_ge n j with hn | hn
    · simpa [reexpandScalar_of_lt s t hn] using hC
    · exact (norm_smul_le_norm _ _).trans (hc n hn)

variable [IsUltrametricDist E] [CompleteSpace E]

private theorem summable_smul_of_tendsto {c : ℕ → E} (hc : Tendsto c cofinite (𝓝 0))
    (r : ℕ → ℤ_[p]) : Summable fun n ↦ r n • c n :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    squeeze_zero_norm (fun _ ↦ norm_smul_le_norm _ _) (tendsto_zero_iff_norm_tendsto_zero.mp hc)

/-- **Composition of re-expansions.** Re-expanding `∑ₙ (s₁ + t₁ v)ⁿ • cₙ` along
`v = s₂ + t₂ u` is the re-expansion along `s₁ + t₁ (s₂ + t₂ u)`. -/
private theorem reexpand_reexpand {c : ℕ → E} (hc : Tendsto c cofinite (𝓝 0))
    (s₁ t₁ s₂ t₂ : ℤ_[p]) (j : ℕ) :
    reexpand s₂ t₂ (reexpand s₁ t₁ c) j = reexpand (s₁ + t₁ * s₂) (t₁ * t₂) c j := by
  set f : ℕ → ℕ → E := fun m n ↦ (reexpandScalar s₂ t₂ m j * reexpandScalar s₁ t₁ n m) • c n
  -- The term `(m, n)` vanishes unless `m ≤ n`, so it is bounded by `‖c (max m n)‖`.
  have hmax : Tendsto (fun x : ℕ × ℕ ↦ max x.1 x.2) cofinite cofinite :=
    Tendsto.cofinite_of_finite_preimage_singleton fun k ↦
      ((Set.finite_Iic k).prod (Set.finite_Iic k)).subset fun x hx ↦ by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨Set.mem_Iic.mpr (le_max_left _ _), Set.mem_Iic.mpr (le_max_right _ _)⟩
  have hf : Summable (Function.uncurry f) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| squeeze_zero_norm
      (a := fun x ↦ ‖c (max x.1 x.2)‖) (fun x ↦ ?_)
      ((tendsto_zero_iff_norm_tendsto_zero.mp hc).comp hmax)
    rcases le_or_gt x.1 x.2 with hx | hx
    · simpa [f, Function.uncurry, max_eq_right hx] using norm_smul_le_norm _ (c x.2)
    · simp [f, Function.uncurry, reexpandScalar_of_lt s₁ t₁ hx]
  calc reexpand s₂ t₂ (reexpand s₁ t₁ c) j = ∑' m, ∑' n, f m n := by
        refine tsum_congr fun m ↦ ?_
        simp only [reexpand, f, mul_smul]
        exact ((summable_smul_of_tendsto hc _).tsum_const_smul _).symm
    _ = ∑' n, ∑' m, f m n := hf.tsum_comm.symm
    _ = reexpand (s₁ + t₁ * s₂) (t₁ * t₂) c j := by
        refine tsum_congr fun n ↦ ?_
        rw [← sum_reexpandScalar_mul, Finset.sum_smul]
        refine tsum_eq_sum fun m hm ↦ ?_
        rw [Finset.mem_range, not_lt] at hm
        simp [f, reexpandScalar_of_lt s₁ t₁ (Nat.lt_of_succ_le hm)]

/-- Summing a re-expansion against the powers of `w` evaluates the original series at
`s + t w`. -/
private theorem tsum_pow_smul_reexpand {c : ℕ → E} (hc : Tendsto c cofinite (𝓝 0))
    (s t w : ℤ_[p]) :
    ∑' j, w ^ j • reexpand s t c j = ∑' n, (s + t * w) ^ n • c n := by
  have h := reexpand_reexpand hc s t w 0 0
  simpa [reexpand, reexpandScalar] using h

end Reexpansion

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

/-- The coefficients of `w ↦ f(a (b.val + pʰ w))` on the disc of `b`, where `f` has coefficient
vector `c`: writing `a b.val = d.val + pʰ s`, they re-expand the series of `f` on the disc of
`d` along `s + a w`. -/
private noncomputable def compMulLeftCoeff (a : ℤ_[p]) (c : AnalyticStage p h E)
    (i : ZMod (p ^ h) × ℕ) : E :=
  reexpand (mulDisc a i.1).2 a (fun n ↦ c ((mulDisc a i.1).1, n)) i.2

omit hp [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] in
private theorem tendsto_apply_mk (c : AnalyticStage p h E) (b : ZMod (p ^ h)) :
    Tendsto (fun n ↦ c (b, n)) cofinite (𝓝 0) :=
  c.tendsto_cofinite.comp (Prod.mk_right_injective b).tendsto_cofinite

private theorem norm_compMulLeftCoeff_le (a : ℤ_[p]) (c : AnalyticStage p h E)
    (i : ZMod (p ^ h) × ℕ) : ‖compMulLeftCoeff a c i‖ ≤ ‖c‖ :=
  norm_reexpand_le _ _ (norm_nonneg c) fun _ _ ↦ c.norm_coe_le_norm _

private theorem tendsto_compMulLeftCoeff (a : ℤ_[p]) (c : AnalyticStage p h E) :
    Tendsto (compMulLeftCoeff a c) cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  have hc := NormedAddGroup.tendsto_nhds_zero.mp c.tendsto_cofinite (ε / 2) (half_pos hε)
  rw [eventually_cofinite] at hc ⊢
  -- Beyond the degrees of the finitely many large coefficients of `c`, every re-expanded
  -- coefficient is small, uniformly in the disc.
  obtain ⟨N, hN⟩ := (hc.image Prod.snd).bddAbove
  refine (Set.finite_univ.prod (Set.finite_Iic N)).subset fun i hi ↦ ⟨trivial, ?_⟩
  by_contra hiN
  rw [Set.mem_Iic, not_le] at hiN
  refine hi ((norm_reexpand_le _ _ (half_pos hε).le fun n hn ↦ ?_).trans_lt (half_lt_self hε))
  by_contra hcn
  have hmem : ((mulDisc a i.1).1, n) ∈ {x | ¬‖c x‖ < ε / 2} := not_lt.mpr (not_le.mp hcn).le
  have := hN ⟨_, hmem, rfl⟩
  omega

variable [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Dilation on the analytic stage `LA_h(E)`**: the coefficient vector of `x ↦ f(a x)`, for
`a ∈ ℤ_p`. Multiplication by `a` maps the disc of `b` into the disc of `d`, where
`a b.val = d.val + pʰ s`; in the disc coordinates, `a (b.val + pʰ w) = d.val + pʰ (s + a w)`, so
the coefficient of `wʲ` is `∑ₙ (n choose j) sⁿ⁻ʲ aʲ • c(d, n)`. -/
noncomputable def compMulLeft (a : ℤ_[p]) : AnalyticStage p h E →L[S] AnalyticStage p h E :=
  let L : AnalyticStage p h E →ₗ[S] AnalyticStage p h E :=
    { toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete (compMulLeftCoeff a c)
        (tendsto_compMulLeftCoeff a c)
      map_add' c d := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, compMulLeftCoeff, reexpand,
          FunLike.coe_add, Pi.add_apply, smul_add]
        exact (summable_smul_of_tendsto (tendsto_apply_mk c _) _).tsum_add
          (summable_smul_of_tendsto (tendsto_apply_mk d _) _)
      map_smul' s c := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, compMulLeftCoeff, reexpand,
          FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_comm _ s]
        exact (summable_smul_of_tendsto (tendsto_apply_mk c _) _).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦ ?_
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact norm_compMulLeftCoeff_le a c i }

private theorem coe_compMulLeft (a : ℤ_[p]) (c : AnalyticStage p h E) :
    ⇑(compMulLeft S a c) = compMulLeftCoeff a c :=
  ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _

/-- The re-expansion formula for dilation: if `a b.val = d.val + pʰ s`, where `(d, s)` is the disc
decomposition of `a b.val`, the coefficient of `wʲ` on the disc of `b` is
`∑ₙ (n choose j) sⁿ⁻ʲ aʲ • c(d, n)`. -/
theorem compMulLeft_apply (a : ℤ_[p]) (c : AnalyticStage p h E) (b : ZMod (p ^ h)) (j : ℕ) :
    compMulLeft S a c (b, j) = ∑' n, ((n.choose j : ℤ_[p]) *
      ((PadicInt.discHomeomorph p h).symm (a * b.val)).2 ^ (n - j) * a ^ j) •
        c (((PadicInt.discHomeomorph p h).symm (a * b.val)).1, n) := by
  rw [coe_compMulLeft]
  rfl

/-- Dilation does not increase norms. -/
theorem norm_compMulLeft_le (a : ℤ_[p]) (c : AnalyticStage p h E) :
    ‖compMulLeft S a c‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦
    coe_compMulLeft S a c ▸ norm_compMulLeftCoeff_le a c i

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
  rw [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul, hx, eval_natCast_val_add_mul,
    coe_compMulLeft]
  simp only [compMulLeftCoeff]
  exact tsum_pow_smul_reexpand (tendsto_apply_mk c _) _ _ w

/-- On the discs of the next level, the transition is the re-expansion along `β + p v`, where
`β` is the digit of the smaller disc. -/
private theorem transition_apply_eq_reexpand (c : AnalyticStage p h E) (b' : ZMod (p ^ (h + 1)))
    (j : ℕ) :
    transition S c (b', j) =
      reexpand ((b'.val / p ^ h : ℕ) : ℤ_[p]) p (fun k ↦ c ((b'.val : ZMod (p ^ h)), k)) j :=
  transition_apply S c b' j

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
    -- A centre of level `h + 1` is the centre of level `h` below it plus `pʰ` times a digit.
    have hval (b' : ZMod (p ^ (h + 1))) : (b'.val : ℤ_[p]) =
        (((b'.val : ZMod (p ^ h)).val : ℕ) : ℤ_[p]) +
          (p : ℤ_[p]) ^ h * ((b'.val / p ^ h : ℕ) : ℤ_[p]) := by
      rw [ZMod.val_natCast]
      exact_mod_cast (Nat.mod_add_div b'.val (p ^ h)).symm
    have h₁ := natCast_val_mulDisc_add a b'
    have h₂ := natCast_val_mulDisc_add a (b'.val : ZMod (p ^ h))
    rw [hval, hval b'] at h₁
    rw [← PadicInt.discHomeomorph_symm_natCast_val_add_mul h,
      ← PadicInt.discHomeomorph_symm_natCast_val_add_mul h]
    congr 1
    linear_combination h₁ - h₂
  obtain ⟨hd, hs⟩ := Prod.mk.inj hy
  rw [transition_apply_eq_reexpand, coe_compMulLeft, coe_compMulLeft]
  simp only [compMulLeftCoeff, transition_apply_eq_reexpand]
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
  simp only [compMulLeftCoeff, mulDisc_eq 1 b (y := (b, 0)) (by simp), reexpand]
  rw [tsum_eq_single j fun n hn ↦ ?_]
  · simp [reexpandScalar]
  · rcases lt_or_gt_of_ne hn with hnj | hnj
    · simp [reexpandScalar_of_lt _ _ hnj]
    · simp [reexpandScalar, Nat.sub_ne_zero_of_lt hnj]

/-- Dilations compose: `x ↦ f(a a' x)` is `x ↦ f(a x)` dilated by `a'`. -/
theorem compMulLeft_mul (a a' : ℤ_[p]) (c : AnalyticStage p h E) :
    compMulLeft S (a * a') c = compMulLeft S a' (compMulLeft S a c) := by
  ext ⟨b, j⟩
  have hy : mulDisc (a * a') b = ((mulDisc a (mulDisc a' b).1).1,
      (mulDisc a (mulDisc a' b).1).2 + a * (mulDisc a' b).2) :=
    mulDisc_eq _ _ <| by
      linear_combination natCast_val_mulDisc_add a (mulDisc a' b).1 +
        a * natCast_val_mulDisc_add a' b
  simp only [coe_compMulLeft, compMulLeftCoeff]
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
  simp only [compMulLeftCoeff, amiceTerm_apply, reexpand_coeff_smul, hcoeff, Finset.sum_smul]
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
  rw [hmap, ← map_pow, PowerSeries.coeff_map, coeff_amiceTransform, Algebra.smul_def,
    ← smul_eq_mul, mahlerTerm_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

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

-- Dilation by zero sends a distribution to its total mass at zero: its Amice transform is the
-- constant series `μ(1)`.
example (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (mapMulLeft 0 μ) =
      PowerSeries.C (PowerSeries.constantCoeff (amiceTransform μ)) := by
  rw [amiceTransform_mapMulLeft]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.C_apply]

end LocallyAnalyticDistribution

end TauCeti
