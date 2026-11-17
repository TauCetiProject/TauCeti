/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Distribution.Translation
import Mathlib.Algebra.Module.Torsion.Free
import TauCeti.NumberTheory.Padics.Measure.Pushforward

/-!
# Additive convolution of locally analytic distributions on `ℤ_p`

This file equips `TauCeti.LocallyAnalyticDistribution p K` with its additive convolution ring and
`K`-algebra structure, building on analytic-stage comultiplication and translation
(`TauCeti.NumberTheory.Padics.Distribution.Translation`), Dirac distributions
(`TauCeti.NumberTheory.Padics.Distribution.Dual`), and the Amice transform
(`TauCeti.NumberTheory.Padics.Distribution.Amice.Transform`).

## Main definitions and results

* `TauCeti.AnalyticStage.comul_amiceTerm`: Vandermonde comultiplication formula on Amice's vectors
  `amiceTerm p h n e` at arbitrary stage level `h` and degree `n`, without torsion-freeness on `E`.
* `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage`: given a continuous functional
  `φ : LA_h(K) →L[K] K`, coordinatewise postcomposition of `AnalyticStage.comul K` with `φ` defines
  a bounded operator `LA_h(K) →L[K] LA_h(K)` of norm at most `‖φ‖`
  (`opNorm_convolveFunRightStage_le`), compatible with evaluation (`eval_convolveFunRightStage`),
  stage transitions (`convolveFunRightStage_transition`, `convolveFunRightStage_transitionLE`),
  composition (`convolveFunRightStage_comp`), and Dirac distributions
  (`convolveFunRightStage_stage_dirac_apply`).
* `TauCeti.LocallyAnalyticDistribution.convolveFunRight`: for a distribution `ν`, the stage-level
  operators descend via `Module.DirectLimit.map` to `LA(ℤ_p, K) →ₗ[K] LA(ℤ_p, K)`, sending `f` to
  `x ↦ ν (y ↦ f (x + y))` (`eval_convolveFunRight`, `convolveFunRight_dirac`,
  `convolveFunRight_mahlerTerm`).
* Additive convolution `(μ * ν)(f) = μ (convolveFunRight ν f)` with identity `1 = dirac K 0`
  (`dirac_zero`, `one_def`) equips `LocallyAnalyticDistribution p K` with `CommRing` and
  `Algebra K` instances extending the existing submodule addition and scalar multiplication without
  typeclass diamonds.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: same-stage submultiplicativity
  `stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_one`,
  `TauCeti.LocallyAnalyticDistribution.amiceTransform_mul`,
  `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom`, and (under `[NormedAlgebra ℚ_[p] K]`)
  `TauCeti.LocallyAnalyticDistribution.amiceTransformRingEquiv`: the Amice transform is a
  `K`-algebra homomorphism and a ring isomorphism onto `PowerSeries.OnOpenDisc.subring K 1`.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure`: embeds Mathlib's convolution algebra
  `D(Multiplicative ℤ_[p], K)` of continuous measures into `LocallyAnalyticDistribution p K` as an
  injective `K`-algebra homomorphism intertwining Dirac elements (`ofMulMeasure_dirac`) and Amice
  transforms (`amiceTransform_ofMulMeasure`), with `stageSeminorm_ofMulMeasure_le`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
* The right-handed convolution interface (`convolveFunRight`, `convolveFunRight_dirac`,
  `convolveFunRight_one`, `convolveFunRight_mul`, `dirac_mul_dirac`) is modeled on Mathlib's
  `Mathlib.NumberTheory.Padics.Measure.Monoid` (`AbstractMeasure.convolveFunRight`,
  `AbstractMeasure.dirac_mul_dirac`, `AbstractMeasure.convolveFunRight_one`,
  `AbstractMeasure.convolveFunRight_mul`).
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Comultiplication on Amice's vectors -/

namespace AnalyticStage

section Amice

open scoped Nat

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private theorem factorial_div_mul_factorial_div_dvd (h : ℕ) {i j n : ℕ} (hij : i + j = n) :
    (i / p ^ h)! * (j / p ^ h)! ∣ (n / p ^ h)! := by
  have hle : i / p ^ h + j / p ^ h ≤ n / p ^ h := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp.out.pos h), add_mul, ← hij]
    exact add_le_add (Nat.div_mul_le_self i (p ^ h)) (Nat.div_mul_le_self j (p ^ h))
  exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial hle)

private theorem comul_amiceTerm_padicInt (h n : ℕ) :
    comul (p := p) (h := h) ℤ_[p] (amiceTerm p h n (1 : ℤ_[p])) =
      ∑ ij ∈ Finset.antidiagonal n,
        ((n / p ^ h)! / ((ij.1 / p ^ h)! * (ij.2 / p ^ h)!)) •
          amiceTerm p h ij.1 (amiceTerm p h ij.2 (1 : ℤ_[p])) := by
  have hpReg : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    smul_right_injective ℤ_[p] (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply eval_injective ℤ_[p] (ZeroAtInftyContinuousMap.isSMulRegular hpReg)
  ext x : 1
  apply eval_injective ℤ_[p] hpReg
  ext y : 1
  simp only [eval_eval_comul, eval_amiceTerm, map_sum, ContinuousMap.coe_sum, Finset.sum_apply,
    PadicInt.mahlerTerm_apply, mahler_apply, Ring.add_choose_eq n (Commute.all x y),
    nsmul_eq_mul, smul_eq_mul, mul_one, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hdvd := factorial_div_mul_factorial_div_dvd (p := p) h (Finset.mem_antidiagonal.mp hij)
  have hfac : (((n / p ^ h)! / ((ij.1 / p ^ h)! * (ij.2 / p ^ h)!)) : ℤ_[p]) *
      ((ij.1 / p ^ h)! : ℤ_[p]) * ((ij.2 / p ^ h)! : ℤ_[p]) = ((n / p ^ h)! : ℤ_[p]) := by
    rw [mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  simp only [map_nsmul, eval_amiceTerm, PadicInt.mahlerTerm_apply, mahler_apply, map_smul,
    ContinuousMap.smul_apply]
  simp only [nsmul_eq_mul, smul_eq_mul, mul_one]
  rw [← hfac]
  ring

/-- **Binomial comultiplication on Amice's vectors.** At any level `h`, comultiplying Amice's
vector `e_{h,n} • e` splits it according to Vandermonde's identity into
`∑_{i + j = n} (⌊n / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)) • e_{h,i} • (e_{h,j} • e)`. No
torsion-freeness of `E` is needed. -/
theorem comul_amiceTerm (n : ℕ) (e : E) :
    comul S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n,
        ((n / p ^ h)! / ((ij.1 / p ^ h)! * (ij.2 / p ^ h)!)) •
          amiceTerm p h ij.1 (amiceTerm p h ij.2 e) := by
  let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
  have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ :=
    ⟨‖e‖, ContinuousLinearMap.norm_toSpanSingleton_apply_le e⟩
  have he : amiceTerm p h n e =
      ZeroAtInftyContinuousMap.compLeft u hu (amiceTerm p h n (1 : ℤ_[p])) := by
    simp [u]
  rw [he, comul_compLeft ℤ_[p] S, comul_amiceTerm_padicInt,
    map_sum (ZeroAtInftyContinuousMap.compLeft _ _)]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [u]

end Amice

end AnalyticStage

/-! ### Additive convolution on locally analytic distributions -/

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-! #### Bounded two-variable test-function pairing -/

/-- The stage-level right convolution operator of a continuous functional `φ : LA_h(K) →L[K] K`:
postcomposing `AnalyticStage.comul K` coordinatewise with `φ` sends `c` to the coefficient vector
of `x ↦ φ (y ↦ c(x + y))`. -/
noncomputable def convolveFunRightStage {h : ℕ} :
    (AnalyticStage p h K →L[K] K) →ₗ[K] (AnalyticStage p h K →L[K] AnalyticStage p h K) where
  toFun φ :=
    (ZeroAtInftyContinuousMap.compLeft φ ⟨‖φ‖, φ.le_opNorm⟩).comp
      (AnalyticStage.comul (p := p) (h := h) (E := K) K).toContinuousLinearMap
  map_add' φ ψ := by ext c i; simp
  map_smul' a φ := by ext c i; simp

/-- Coordinatewise formula for `convolveFunRightStage φ`. -/
@[simp]
theorem convolveFunRightStage_apply {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) (i : ZMod (p ^ h) × ℕ) :
    convolveFunRightStage φ c i = φ (AnalyticStage.comul K c i) := by
  simp [convolveFunRightStage]

private theorem convolveFunRightStage_eq_compLeft {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) :
    convolveFunRightStage φ c =
      ZeroAtInftyContinuousMap.compLeft φ ⟨‖φ‖, φ.le_opNorm⟩ (AnalyticStage.comul K c) := by
  ext i
  simp

/-- `convolveFunRightStage φ` is bounded by `‖φ‖`. -/
theorem norm_convolveFunRightStage_apply_le {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) :
    ‖convolveFunRightStage φ c‖ ≤ ‖φ‖ * ‖c‖ := by
  rw [convolveFunRightStage_eq_compLeft]
  calc
    ‖ZeroAtInftyContinuousMap.compLeft φ ⟨‖φ‖, φ.le_opNorm⟩ (AnalyticStage.comul K c)‖
        ≤ ‖φ‖ * ‖AnalyticStage.comul K c‖ :=
      ZeroAtInftyContinuousMap.norm_compLeft_apply_le φ φ.le_opNorm (AnalyticStage.comul K c)
    _ = ‖φ‖ * ‖c‖ := by rw [(AnalyticStage.comul (p := p) (h := h) (E := K) K).norm_map]

/-- The operator norm of `convolveFunRightStage φ` is at most `‖φ‖`. -/
theorem opNorm_convolveFunRightStage_le {h : ℕ} (φ : AnalyticStage p h K →L[K] K) :
    ‖convolveFunRightStage φ‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ) (norm_convolveFunRightStage_apply_le φ)

/-- Evaluating `convolveFunRightStage φ c` at `x` applies `φ` to the translate of `c` by `x`. -/
@[simp]
theorem eval_convolveFunRightStage {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) (x : ℤ_[p]) :
    AnalyticStage.eval K (convolveFunRightStage φ c) x = φ (AnalyticStage.translate K x c) := by
  rw [convolveFunRightStage_eq_compLeft, AnalyticStage.eval_compLeft K K,
    AnalyticStage.translate_eq_eval_comul]

/-- Stage-level right convolution commutes with adjacent stage transitions: applying `ψ` after
refining equals refining after applying `ψ ∘ transition`. -/
theorem convolveFunRightStage_transition {h : ℕ} (ψ : AnalyticStage p (h + 1) K →L[K] K)
    (c : AnalyticStage p h K) :
    convolveFunRightStage ψ (transition K c) =
      transition K (convolveFunRightStage (ψ.comp (transition K)) c) := by
  rw [convolveFunRightStage_eq_compLeft, convolveFunRightStage_eq_compLeft,
    comul_transition, transition_compLeft K K]
  ext i
  simp

/-- Stage-level right convolution commutes with multi-level stage transitions. -/
theorem convolveFunRightStage_transitionLE {h k : ℕ} (hhk : h ≤ k)
    (ψ : AnalyticStage p k K →L[K] K) (c : AnalyticStage p h K) :
    convolveFunRightStage ψ (transitionLE K hhk c) =
      transitionLE K hhk (convolveFunRightStage (ψ.comp (transitionLE K hhk)) c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ K hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      convolveFunRightStage_transition, ih, ← ContinuousLinearMap.comp_assoc]

/-- For a distribution `ν`, the stage-level right convolution operators commute with adjacent
transitions. -/
theorem convolveFunRightStage_stage_transition (ν : LocallyAnalyticDistribution p K) {h : ℕ}
    (c : AnalyticStage p h K) :
    convolveFunRightStage (stage (h + 1) ν) (transition K c) =
      transition K (convolveFunRightStage (stage h ν) c) := by
  rw [convolveFunRightStage_transition, stage_comp_transition]

/-- For a distribution `ν`, the stage-level right convolution operators commute with multi-level
transitions. -/
theorem convolveFunRightStage_stage_transitionLE (ν : LocallyAnalyticDistribution p K) {h k : ℕ}
    (hhk : h ≤ k) (c : AnalyticStage p h K) :
    convolveFunRightStage (stage k ν) (transitionLE K hhk c) =
      transitionLE K hhk (convolveFunRightStage (stage h ν) c) := by
  rw [convolveFunRightStage_transitionLE, stage_comp_transitionLE]

/-- Stage-level right convolution is associative with respect to composition of stage
functionals. -/
theorem convolveFunRightStage_comp {h : ℕ} (φ ψ : AnalyticStage p h K →L[K] K) :
    convolveFunRightStage (φ.comp (convolveFunRightStage ψ)) =
      (convolveFunRightStage φ).comp (convolveFunRightStage ψ) := by
  ext c i
  simp only [convolveFunRightStage_apply, ContinuousLinearMap.comp_apply]
  rw [convolveFunRightStage_eq_compLeft, convolveFunRightStage_eq_compLeft,
    comul_compLeft K K ψ ⟨‖ψ‖, ψ.le_opNorm⟩, ZeroAtInftyContinuousMap.compLeft_apply]
  congr 2
  have hcoassoc := congrArg (fun d ↦ d i) (comul_comul K c)
  simpa only [ZeroAtInftyContinuousMap.compLeft_apply,
    LinearIsometry.coe_toContinuousLinearMap] using hcoassoc.symm

/-- Stage-level right convolution with a Dirac distribution at `x` is translation by `x`. -/
@[simp]
theorem convolveFunRightStage_stage_dirac_apply (x : ℤ_[p]) {h : ℕ} (c : AnalyticStage p h K) :
    convolveFunRightStage (stage h (dirac K x)) c = AnalyticStage.translate K x c := by
  ext i
  simp [AnalyticStage.eval_comul_apply]

/-- Right convolution of a locally analytic function with a distribution: sends `f` to the locally
analytic function `x ↦ ν (y ↦ f (x + y))`. -/
noncomputable def convolveFunRight :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalytic p K K →ₗ[K] LocallyAnalytic p K K where
  toFun ν := Module.DirectLimit.map
    (fun h ↦ (convolveFunRightStage (stage h ν)).toLinearMap)
    (fun _ _ hhk ↦ LinearMap.ext (convolveFunRightStage_stage_transitionLE ν hhk))
  map_add' ν₁ ν₂ := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.DirectLimit.map_apply_of,
      ContinuousLinearMap.coe_coe, map_add, add_apply]
  map_smul' a ν := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply,
      Module.DirectLimit.map_apply_of, ContinuousLinearMap.coe_coe, map_smul, smul_apply]

/-- Right convolution restricts to `convolveFunRightStage (stage h ν)` on stage `h`. -/
@[simp]
theorem convolveFunRight_ofStage (ν : LocallyAnalyticDistribution p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    convolveFunRight ν (ofStage K h c) =
      ofStage K h (convolveFunRightStage (stage h ν) c) := by
  rw [ofStage_def]
  exact Module.DirectLimit.map_apply_of
    (fun h ↦ (convolveFunRightStage (stage h ν)).toLinearMap)
    (fun _ _ hhk ↦ LinearMap.ext (convolveFunRightStage_stage_transitionLE ν hhk)) c

/-- Evaluating `convolveFunRight ν f` at `x` applies `ν` to the translate of `f` by `x`. -/
@[simp]
theorem eval_convolveFunRight (ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K)
    (x : ℤ_[p]) :
    LocallyAnalytic.eval K (convolveFunRight ν f) x =
      (ν : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.translate K x f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, eval_ofStage, eval_convolveFunRightStage,
    LocallyAnalytic.translate_ofStage, stage_apply]

/-- Right convolution with a Dirac distribution at `x` is translation by `x`. -/
@[simp]
theorem convolveFunRight_dirac (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    convolveFunRight (dirac K x) f = LocallyAnalytic.translate K x f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, convolveFunRightStage_stage_dirac_apply,
    LocallyAnalytic.translate_ofStage]

/-- Right convolution acts on locally analytic Mahler terms via the Vandermonde formula with the
moments of `ν`. -/
theorem convolveFunRight_mahlerTerm (ν : LocallyAnalyticDistribution p K) (n : ℕ) :
    convolveFunRight ν (mahlerTerm p K 1 n) =
      ∑ ij ∈ Finset.antidiagonal n, (amiceTransform ν).coeff ij.2 • mahlerTerm p K 1 ij.1 := by
  have hlt : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  rw [mahlerTerm_def, convolveFunRight_ofStage]
  have hstage : convolveFunRightStage (stage n ν) (amiceTerm p n n (1 : K)) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p n ij.1 ((amiceTransform ν).coeff ij.2) := by
    ext i
    simp only [convolveFunRightStage_apply, comul_amiceTerm, ZeroAtInftyContinuousMap.coe_sum,
      Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    have hij' := Finset.mem_antidiagonal.mp hij
    have hn : n / p ^ n = 0 := Nat.div_eq_of_lt hlt
    have hi : ij.1 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
    have hj : ij.2 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
    have hcoeff : stage n ν (amiceTerm p n ij.2 (1 : K)) = (amiceTransform ν).coeff ij.2 := by
      simp [hj]
    simp [hn, hi, hj, hcoeff]
  rw [hstage, map_sum]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hij' := Finset.mem_antidiagonal.mp hij
  have hi : ij.1 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
  simp [hi, ← mahlerTerm_smul]

/-! #### Convolution ring and `K`-algebra structure -/

/-- The multiplicative identity for additive convolution is the Dirac distribution at `0`. -/
noncomputable instance : One (LocallyAnalyticDistribution p K) where
  one := dirac K 0

/-- The convolution identity is the Dirac distribution at `0`. -/
theorem one_def : (1 : LocallyAnalyticDistribution p K) = dirac K 0 :=
  (rfl)

/-- The Dirac distribution at `0` is the convolution identity `1`. -/
@[simp]
theorem dirac_zero : dirac K (0 : ℤ_[p]) = (1 : LocallyAnalyticDistribution p K) :=
  (rfl)

/-- Applying the convolution identity evaluates the function at `0`. -/
@[simp]
theorem coe_one_apply (f : LocallyAnalytic p K K) :
    ((1 : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f 0 :=
  coe_dirac_apply 0 f

/-- Stage-level right convolution with the identity distribution `1` is the identity operator. -/
@[simp]
theorem convolveFunRightStage_stage_one (h : ℕ) :
    convolveFunRightStage (stage h (1 : LocallyAnalyticDistribution p K)) =
      ContinuousLinearMap.id K _ := by
  ext c
  rw [one_def, convolveFunRightStage_stage_dirac_apply, AnalyticStage.translate_zero,
    ContinuousLinearMap.id_apply]

/-- **Additive convolution of locally analytic distributions**:
`(μ * ν)(f) = μ (x ↦ ν (y ↦ f (x + y)))`. -/
noncomputable instance : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν :=
    ⟨(μ : Module.Dual K (LocallyAnalytic p K K)).comp (convolveFunRight ν), mem_iff.mpr fun h ↦ by
      convert ((stage h μ).comp (convolveFunRightStage (stage h ν))).continuous using 1
      ext c
      simp⟩

/-- Applying the convolution `μ * ν` to `f` applies `μ` to `convolveFunRight ν f`. -/
@[simp]
theorem coe_mul_apply (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    ((μ * ν : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (convolveFunRight ν f) :=
  (rfl)

/-- Restricting the convolution `μ * ν` to stage `h` composes `stage h μ` with the stage-level
right convolution operator of `stage h ν`. -/
@[simp]
theorem stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stage h (μ * ν) = (stage h μ).comp (convolveFunRightStage (stage h ν)) := by
  ext c
  simp

/-- The operator norm of the convolution identity on stage `h` equals `1`. -/
@[simp]
theorem norm_stage_one (h : ℕ) :
    ‖stage h (1 : LocallyAnalyticDistribution p K)‖ = 1 :=
  norm_stage_dirac (K := K) 0 h

/-- Every stage seminorm of the convolution identity equals `1`. -/
theorem stageSeminorm_one (h : ℕ) :
    stageSeminorm h (1 : LocallyAnalyticDistribution p K) = 1 :=
  stageSeminorm_dirac (K := K) 0 h

/-- **Stage seminorm submultiplicativity for additive convolution.** At every fixed analytic level
`h`, the stage seminorm of `μ * ν` is at most the product of the stage seminorms of `μ` and `ν`,
with no loss of level or extra constant. -/
theorem stageSeminorm_mul_le (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stageSeminorm_apply, stage_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (opNorm_convolveFunRightStage_le _) (norm_nonneg _))

/-- The Amice transform sends the convolution identity to `1`. -/
@[simp]
theorem amiceTransform_one : amiceTransform (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [one_def, amiceTransform_dirac, PowerSeries.binomialSeries_zero]

/-- **The Amice transform is multiplicative for additive convolution.** -/
@[simp]
theorem amiceTransform_mul (μ ν : LocallyAnalyticDistribution p K) :
    amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν := by
  ext n
  rw [coeff_amiceTransform, coe_mul_apply, convolveFunRight_mahlerTerm, map_sum,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [map_smul, coeff_amiceTransform, coeff_amiceTransform, smul_eq_mul, mul_comm]

/-- Locally analytic distributions form a commutative ring under additive convolution, extending
the existing submodule additive group structure. -/
noncomputable instance : CommRing (LocallyAnalyticDistribution p K) where
  left_distrib μ ν₁ ν₂ := amiceTransform_injective <| by simp [map_add, mul_add]
  right_distrib μ₁ μ₂ ν := amiceTransform_injective <| by simp [map_add, add_mul]
  zero_mul μ := amiceTransform_injective <| by simp
  mul_zero μ := amiceTransform_injective <| by simp
  mul_assoc μ ν ρ := amiceTransform_injective <| by simp [mul_assoc]
  one_mul μ := amiceTransform_injective <| by simp
  mul_one μ := amiceTransform_injective <| by simp
  mul_comm μ ν := amiceTransform_injective <| by simp [mul_comm]

/-- Locally analytic distributions form a `K`-algebra under additive convolution, extending the
existing submodule scalar multiplication. -/
noncomputable instance : Algebra K (LocallyAnalyticDistribution p K) :=
  Algebra.ofModule
    (fun r μ ν ↦ amiceTransform_injective <| by
      rw [amiceTransform_mul, map_smul, map_smul, amiceTransform_mul, smul_mul_assoc])
    (fun r μ ν ↦ amiceTransform_injective <| by
      rw [amiceTransform_mul, map_smul, map_smul, amiceTransform_mul, mul_smul_comm])

/-- Convolution of Dirac distributions corresponds to addition in `ℤ_p`. -/
@[simp]
theorem dirac_mul_dirac (x y : ℤ_[p]) :
    dirac K x * dirac K y = dirac K (x + y) :=
  amiceTransform_injective <| by simp [PowerSeries.binomialSeries_add]

/-- Right convolution with `1` is the identity on locally analytic functions. -/
@[simp]
theorem convolveFunRight_one (f : LocallyAnalytic p K K) :
    convolveFunRight (1 : LocallyAnalyticDistribution p K) f = f := by
  rw [one_def, convolveFunRight_dirac, LocallyAnalytic.translate_zero]

/-- Stage-level right convolution is associative with respect to distribution convolution. -/
theorem convolveFunRightStage_stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    convolveFunRightStage (stage h (μ * ν)) =
      (convolveFunRightStage (stage h μ)).comp (convolveFunRightStage (stage h ν)) := by
  rw [stage_mul, convolveFunRightStage_comp]

/-- Right convolution turns `LocallyAnalytic p K K` into a module action of the convolution
algebra: `convolveFunRight (μ * ν) = convolveFunRight μ ∘ convolveFunRight ν`. -/
theorem convolveFunRight_mul (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    convolveFunRight (μ * ν) f = convolveFunRight μ (convolveFunRight ν f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, convolveFunRight_ofStage, convolveFunRight_ofStage,
    convolveFunRightStage_stage_mul, ContinuousLinearMap.comp_apply]

/-! #### Algebra and ring homomorphisms for the Amice transform -/

/-- The Amice transform bundled as a `K`-algebra homomorphism into formal power series. -/
noncomputable def amiceTransformAlgHom :
    LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K :=
  AlgHom.ofLinearMap amiceTransform amiceTransform_one amiceTransform_mul

/-- Applying `amiceTransformAlgHom` to `μ` gives `amiceTransform μ`. -/
@[simp]
theorem amiceTransformAlgHom_apply (μ : LocallyAnalyticDistribution p K) :
    amiceTransformAlgHom μ = amiceTransform μ :=
  (rfl)

/-- The linear map underlying `amiceTransformAlgHom` is `amiceTransform`. -/
@[simp]
theorem toLinearMap_amiceTransformAlgHom :
    (amiceTransformAlgHom (p := p) (K := K)).toLinearMap = amiceTransform :=
  (rfl)

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- **Amice's theorem as a ring isomorphism.** When `K` is a normed `ℚ_p`-algebra, the Amice
transform is a ring isomorphism from the convolution ring `LocallyAnalyticDistribution p K` onto
the ring `PowerSeries.OnOpenDisc.subring K 1` of power series converging on the open unit disc. -/
noncomputable def amiceTransformRingEquiv :
    LocallyAnalyticDistribution p K ≃+* PowerSeries.OnOpenDisc.subring K 1 :=
  AddEquiv.toRingEquiv (amiceTransformEquiv (p := p) (K := K)) fun μ ν ↦ Subtype.ext <| by
    simp only [Subring.coe_mul, coe_amiceTransformEquiv, amiceTransform_mul]

/-- The underlying power series of `amiceTransformRingEquiv μ` is `amiceTransform μ`. -/
@[simp]
theorem coe_amiceTransformRingEquiv (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformRingEquiv μ : PowerSeries K) = amiceTransform μ :=
  coe_amiceTransformEquiv μ

/-- The inverse of `amiceTransformRingEquiv` is `ofOnOpenDisc`. -/
@[simp]
theorem amiceTransformRingEquiv_symm_apply (F : PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformRingEquiv.symm F =
      ofOnOpenDisc p (PowerSeries.OnOpenDisc.mem_subring.mp F.2) :=
  amiceTransformEquiv_symm_apply F

end NormedAlgebra

/-! #### Compatibility with native measure convolution -/

private theorem amiceTransform_ofMeasure_arrowCongrLeft
    (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) :
    amiceTransform (ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ)) =
      AbstractMeasure.amiceTransformₐ μ := by
  ext n
  rw [amiceTransform_ofMeasure, AbstractMeasure.coeff_amiceTransform,
    AbstractMeasure.coeff_amiceTransformₐ, AbstractMeasure.arrowCongrLeft_apply]
  refine congrArg μ ?_
  ext x
  simp [AbstractMeasure.mulMahler_apply]

/-- The canonical embedding of Mathlib's convolution algebra `D(Multiplicative ℤ_p, K)` of
continuous measures into `LocallyAnalyticDistribution p K`, as an injective `K`-algebra
homomorphism. -/
noncomputable def ofMulMeasure :
    AbstractMeasure (Multiplicative ℤ_[p]) K K →ₐ[K] LocallyAnalyticDistribution p K :=
  AlgHom.ofLinearMap
    (ofMeasure.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).toLinearMap)
    (amiceTransform_injective <| by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        amiceTransform_ofMeasure_arrowCongrLeft, map_one, amiceTransform_one])
    (fun μ ν ↦ amiceTransform_injective <| by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        amiceTransform_ofMeasure_arrowCongrLeft, map_mul, amiceTransform_mul])

/-- `ofMulMeasure` transports a measure along `Homeomorph.ofAdd.symm` and applies `ofMeasure`. -/
theorem ofMulMeasure_apply (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) :
    ofMulMeasure μ = ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ) :=
  (rfl)

/-- Applying `ofMulMeasure μ` to a locally analytic function integrates its evaluation transported
to `Multiplicative ℤ_p`. -/
@[simp]
theorem coe_ofMulMeasure_apply (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K)
    (f : LocallyAnalytic p K K) :
    (ofMulMeasure μ : Module.Dual K (LocallyAnalytic p K K)) f =
      μ ((LocallyAnalytic.eval K f).comp
        (Homeomorph.ofAdd.symm : Multiplicative ℤ_[p] ≃ₜ ℤ_[p])) := by
  simp [ofMulMeasure_apply]

/-- `ofMulMeasure` sends the Dirac measure at `x : Multiplicative ℤ_p` to
`dirac K (Multiplicative.toAdd x)`. -/
@[simp]
theorem ofMulMeasure_dirac (x : Multiplicative ℤ_[p]) :
    ofMulMeasure (AbstractMeasure.dirac K x) = dirac K (Multiplicative.toAdd x) := by
  ext f
  simp [coe_ofMulMeasure_apply, AbstractMeasure.dirac_apply]

/-- The Amice transform on distributions agrees with Mathlib's multiplicative-measure Amice
transform `AbstractMeasure.amiceTransformₐ` along `ofMulMeasure`. -/
@[simp]
theorem amiceTransform_ofMulMeasure (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) :
    amiceTransform (ofMulMeasure μ) = AbstractMeasure.amiceTransformₐ μ :=
  amiceTransform_ofMeasure_arrowCongrLeft μ

/-- `ofMulMeasure` is injective. -/
theorem ofMulMeasure_injective : Function.Injective (ofMulMeasure (p := p) (K := K)) :=
  ofMeasure_injective.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).injective

/-- The stage seminorms of `ofMulMeasure μ` are bounded by the operator norm of `μ`. -/
theorem stageSeminorm_ofMulMeasure_le (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) (h : ℕ) :
    stageSeminorm h (ofMulMeasure μ) ≤ ‖AbstractMeasure.toCLMEquiv μ‖ := by
  rw [ofMulMeasure_apply]
  refine (stageSeminorm_ofMeasure_le _ h).trans ?_
  rw [congrFun (AbstractMeasure.coe_arrowCongrLeft Homeomorph.ofAdd.symm) μ]
  exact AbstractMeasure.norm_toCLMEquiv_map_le μ _

end LocallyAnalyticDistribution

end TauCeti
