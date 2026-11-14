/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.AddChar
public import Mathlib.NumberTheory.Padics.Measure.Monoid
public import TauCeti.NumberTheory.Padics.Distribution.Comul
public import TauCeti.NumberTheory.Padics.Distribution.Dual

/-!
# Point masses and additive convolution of locally analytic distributions on `ℤ_p`

Let `K` be a complete nontrivially normed field with contractive `ℤ_p`-action. Using the
two-variable addition re-expansion `TauCeti.AnalyticStage.comul` and the bounded two-variable
pairing `ZeroAtInftyContinuousMap.prodFunctional`, this file equips the space
`TauCeti.LocallyAnalyticDistribution p K` with point masses and its genuine additive convolution
`K`-algebra structure directly across the analytic stages:

* `TauCeti.LocallyAnalyticDistribution.dirac`: the point-mass distribution `δ_x` at `x ∈ ℤ_p`,
  evaluating locally analytic functions at `x`, with `stageSeminorm h (dirac x) = 1` at every
  analytic level `h`;
* `One (LocallyAnalyticDistribution p K)` and `Mul (LocallyAnalyticDistribution p K)`: the unit
  `1 = dirac 0` and the additive convolution `μ * ν`, defined on each analytic stage `LA_h(K)` by
  `(stage h μ ⊗ stage h ν) ∘ comul`;
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: submultiplicativity of every stage
  seminorm, `stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν`;
* `CommRing (LocallyAnalyticDistribution p K)` and `Algebra K (LocallyAnalyticDistribution p K)`:
  the commutative convolution `K`-algebra structure, proved from the counit, cocommutativity,
  transition compatibility, and coassociativity of `comul` without appealing to the Amice
  transform or assuming characteristic zero;
* `TauCeti.LocallyAnalyticDistribution.ofMeasure_map_add_prodMk'` and
  `TauCeti.LocallyAnalyticDistribution.ofMulMeasure`: compatibility of `ofMeasure` with native
  additive measure convolution on `ℤ_p`, bundled as an injective `K`-algebra homomorphism
  `D(Multiplicative ℤ_p, K) →ₐ[K] LocallyAnalyticDistribution p K`.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.dirac`: point-mass distribution at `x ∈ ℤ_p`.
* `TauCeti.LocallyAnalyticDistribution.diracHom`: the multiplicative group homomorphism
  `Multiplicative ℤ_p →* LocallyAnalyticDistribution p K` sending `ofAdd x` to `dirac x`.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure`: the convolution `K`-algebra embedding
  `D(Multiplicative ℤ_p, K) →ₐ[K] LocallyAnalyticDistribution p K`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_dirac`: every point mass has stage seminorm
  `1` at every level.
* `TauCeti.LocallyAnalyticDistribution.dirac_injective`: `dirac` is injective.
* `TauCeti.LocallyAnalyticDistribution.stage_mul`: stage restriction of `μ * ν` is
  `prodFunctional (stage h μ) (stage h ν) _ ∘L comul K`.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: stage seminorms are submultiplicative.
* `TauCeti.LocallyAnalyticDistribution.dirac_add`: `dirac (x + y) = dirac x * dirac y`.
* `TauCeti.LocallyAnalyticDistribution.ofMeasure_map_add_prodMk'`: `ofMeasure` intertwines
  pushforward product-measure convolution along `+ : ℤ_p × ℤ_p → ℤ_p` with distribution
  convolution.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure_injective`: `ofMulMeasure` is injective.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open scoped AbstractMeasure ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace TauCeti.LocallyAnalyticDistribution

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

open AnalyticStage LocallyAnalytic

/-! ### Point-mass distributions -/

/-- **Point-mass locally analytic distribution** `δ_x` at `x ∈ ℤ_p`, induced by the Dirac measure
at `x`. -/
noncomputable def dirac (x : ℤ_[p]) : LocallyAnalyticDistribution p K :=
  ofMeasure (AbstractMeasure.dirac K x)

/-- The image of a Dirac measure under `ofMeasure` is `dirac`. -/
@[simp]
theorem ofMeasure_dirac (x : ℤ_[p]) :
    ofMeasure (p := p) (K := K) (AbstractMeasure.dirac K x) = dirac x :=
  (rfl)

/-- `dirac x` evaluates a locally analytic function at `x`. -/
@[simp]
theorem coe_dirac_apply (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    (dirac (K := K) x : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f x := by
  rw [dirac, coe_ofMeasure_apply, AbstractMeasure.dirac_apply]

/-- On the analytic stage `LA_h(K)`, `dirac x` evaluates the series of `c` at `x`. -/
theorem stage_dirac_apply (h : ℕ) (x : ℤ_[p]) (c : AnalyticStage p h K) :
    stage h (dirac (K := K) x) c = AnalyticStage.eval K c x := by
  simp

/-- On the analytic stage `LA_h(K)`, `dirac 0` reads off the `(0, 0)`-coordinate. -/
theorem stage_dirac_zero (h : ℕ) :
    stage h (dirac (p := p) (K := K) 0) = evalCLM K (0, 0) := by
  ext c
  rw [stage_dirac_apply, eval_apply_zero, evalCLM_apply]

private theorem eval_single_zero_one (h : ℕ) (a : ZMod (p ^ h)) (z : ℤ_[p]) :
    AnalyticStage.eval K (single (a, 0) (1 : K)) z =
      if PadicInt.toZModPow h z = a then 1 else 0 := by
  conv_lhs => rw [← PadicInt.natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm h z]
  rw [eval_natCast_val_add_mul, tsum_eq_single 0]
  · by_cases ha : PadicInt.toZModPow h z = a <;> simp [single_apply, ha]
  · intro n hn
    simp [single_apply, hn]

/-- On every analytic stage `LA_h(K)`, the point mass `dirac x` has operator norm `1`. -/
@[simp]
theorem norm_stage_dirac (h : ℕ) (x : ℤ_[p]) :
    ‖stage h (dirac (p := p) (K := K) x)‖ = 1 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ ?_
    rw [stage_dirac_apply, one_mul]
    exact (ContinuousMap.norm_coe_le_norm (AnalyticStage.eval K c) x).trans (norm_eval_le K c)
  · let c : AnalyticStage p h K := single (PadicInt.toZModPow h x, 0) 1
    have hc_norm : ‖c‖ = 1 := by simp [c]
    have hc_eval : stage h (dirac (p := p) (K := K) x) c = 1 := by
      rw [stage_dirac_apply]
      simp [c, eval_single_zero_one]
    have hle := (stage h (dirac (p := p) (K := K) x)).le_opNorm c
    rw [hc_eval, hc_norm, norm_one, mul_one] at hle
    exact hle

/-- Every point mass `dirac x` has stage seminorm equal to `1` at every analytic level `h`. -/
theorem stageSeminorm_dirac (h : ℕ) (x : ℤ_[p]) :
    stageSeminorm h (dirac (p := p) (K := K) x) = 1 := by
  simp

/-- Every point-mass distribution is nonzero. -/
theorem dirac_ne_zero (x : ℤ_[p]) : dirac (p := p) (K := K) x ≠ 0 := by
  intro hx
  have h1 := stageSeminorm_dirac (p := p) (K := K) 0 x
  rw [hx, map_zero] at h1
  exact zero_ne_one h1

/-- Distinct points of `ℤ_p` define distinct point-mass distributions, separated by locally
constant indicator functions of residue discs. -/
theorem dirac_injective : Function.Injective (dirac (p := p) (K := K)) := by
  intro x y hxy
  refine PadicInt.ext_of_toZModPow.mp fun h ↦ ?_
  have heval := DFunLike.congr_fun (congrArg (stage h) hxy)
    (single (PadicInt.toZModPow h x, 0) (1 : K))
  rw [stage_dirac_apply, stage_dirac_apply, eval_single_zero_one, eval_single_zero_one] at heval
  by_contra hne
  simp [Ne.symm hne] at heval

/-! ### Stage-by-stage additive convolution and `CommRing` / `Algebra` structure -/

/-- The convolution unit of `LocallyAnalyticDistribution p K` is the point mass `dirac 0`. -/
noncomputable instance : One (LocallyAnalyticDistribution p K) where
  one := dirac 0

/-- The convolution unit `1` is the point mass at `0`. -/
theorem one_def : (1 : LocallyAnalyticDistribution p K) = dirac 0 := (rfl)

/-- The point mass at `0` is the convolution unit `1`. -/
@[simp]
theorem dirac_zero : dirac (p := p) (K := K) 0 = 1 := (rfl)

/-- **Additive convolution of locally analytic distributions**, defined on each analytic stage
`LA_h(K)` by pairing `prodFunctional (stage h μ) (stage h ν)` against `AnalyticStage.comul K`. -/
noncomputable instance : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν := stagesEquiv.symm
    ⟨fun h ↦ (prodFunctional (stage h μ) (stage h ν)
      ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩).comp (comul K),
      mem_compatibleStageFunctionals_iff.mpr fun h ↦ by
        ext c
        simp only [ContinuousLinearMap.comp_apply, prodFunctional_apply, curryEquiv_comul]
        rw [← transition_compLeft_transition_comulCurried K c]
        have hrow : compLeft (stage (h + 1) ν) ⟨‖stage (h + 1) ν‖, (stage (h + 1) ν).le_opNorm⟩
              (transition K (compLeft (transition K)
                ⟨1, fun y ↦ by simpa only [one_mul] using norm_transition_le K y⟩
                (comulCurried K c))) =
            transition K (compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
              (comulCurried K c)) := by
          rw [← transition_compLeft K]
          refine congrArg (transition (p := p) (h := h) (E := K) K) ?_
          ext u
          simp [← stage_comp_transition ν h]
        rw [hrow, ← ContinuousLinearMap.comp_apply (stage (h + 1) μ) (transition K),
          stage_comp_transition μ h]⟩

/-- On the stage `LA_h(K)`, the convolution unit `1` evaluates the `(0, 0)`-coordinate. -/
@[simp]
theorem stage_one (h : ℕ) :
    stage h (1 : LocallyAnalyticDistribution p K) = evalCLM K (0, 0) :=
  stage_dirac_zero h

/-- On the stage `LA_h(K)`, `μ * ν` is the two-variable product functional of `stage h μ` and
`stage h ν` composed with `comul K`. -/
theorem stage_mul (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stage h (μ * ν) =
      (prodFunctional (stage h μ) (stage h ν)
        ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩).comp (comul K) :=
  stage_stagesEquiv_symm _ h

/-- Pointwise form of `stage_mul` in terms of `comulCurried`: `μ * ν` applies `stage h ν` to each
row of `comulCurried K c` and `stage h μ` to the resulting column. -/
theorem stage_mul_apply (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) (c : AnalyticStage p h K) :
    stage h (μ * ν) c =
      stage h μ (compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩ (comulCurried K c)) := by
  rw [stage_mul, ContinuousLinearMap.comp_apply, prodFunctional_apply, curryEquiv_comul]

/-- **Submultiplicativity of the stage seminorms** under additive convolution. -/
theorem stageSeminorm_mul_le (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stageSeminorm_apply, stage_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [opNorm_prodFunctional]
  exact mul_le_of_le_one_right (by positivity) opNorm_comul_le_one

/-- Every stage seminorm of the convolution unit `1` equals `1`. -/
theorem stageSeminorm_one (h : ℕ) :
    stageSeminorm h (1 : LocallyAnalyticDistribution p K) = 1 :=
  stageSeminorm_dirac h 0

noncomputable instance : MulZeroClass (LocallyAnalyticDistribution p K) where
  zero_mul ν := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦
    let st := stage (p := p) (K := K) h
    let z : LocallyAnalyticDistribution p K := 0
    let d := compLeft (st ν) ⟨‖st ν‖, (st ν).le_opNorm⟩ (comulCurried K c)
    calc
      st (z * ν) c = st z d := stage_mul_apply h z ν c
      _ = (0 : AnalyticStage p h K →L[K] K) d := congrArg (· d) (map_zero st)
      _ = 0 := _root_.zero_apply (F := AnalyticStage p h K →L[K] K) d
      _ = (0 : AnalyticStage p h K →L[K] K) c :=
        (_root_.zero_apply (F := AnalyticStage p h K →L[K] K) c).symm
      _ = st z c := congrArg (· c) (map_zero st).symm
  mul_zero μ := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦
    let st := stage (p := p) (K := K) h
    let z : LocallyAnalyticDistribution p K := 0
    have hd : compLeft (st z) ⟨‖st z‖, (st z).le_opNorm⟩ (comulCurried K c) = 0 :=
      ZeroAtInftyContinuousMap.ext fun u ↦ calc
        compLeft (st z) ⟨‖st z‖, (st z).le_opNorm⟩ (comulCurried K c) u
          = st z (comulCurried K c u) := compLeft_apply _ _ _ u
        _ = (0 : AnalyticStage p h K →L[K] K) (comulCurried K c u) :=
          congrArg (· (comulCurried K c u)) (map_zero st)
        _ = 0 := _root_.zero_apply (F := AnalyticStage p h K →L[K] K) _
        _ = (0 : AnalyticStage p h K) u := (_root_.zero_apply (F := AnalyticStage p h K) u).symm
    calc
      st (μ * z) c =
          st μ (compLeft (st z) ⟨‖st z‖, (st z).le_opNorm⟩
            (comulCurried K c)) := stage_mul_apply h μ z c
      _ = st μ 0 := congrArg (st μ) hd
      _ = 0 := map_zero (st μ)
      _ = (0 : AnalyticStage p h K →L[K] K) c :=
        (_root_.zero_apply (F := AnalyticStage p h K →L[K] K) c).symm
      _ = st z c := congrArg (· c) (map_zero st).symm

noncomputable instance : Distrib (LocallyAnalyticDistribution p K) where
  left_distrib μ ν₁ ν₂ := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦
    let st := stage (p := p) (K := K) h
    let b₁ : ∃ C, ∀ y, ‖st ν₁ y‖ ≤ C * ‖y‖ := ⟨‖st ν₁‖, (st ν₁).le_opNorm⟩
    let b₂ : ∃ C, ∀ y, ‖st ν₂ y‖ ≤ C * ‖y‖ := ⟨‖st ν₂‖, (st ν₂).le_opNorm⟩
    let b₁₂ : ∃ C, ∀ y, ‖st (ν₁ + ν₂) y‖ ≤ C * ‖y‖ :=
      ⟨‖st (ν₁ + ν₂)‖, (st (ν₁ + ν₂)).le_opNorm⟩
    have hd : compLeft (st (ν₁ + ν₂)) b₁₂ (comulCurried K c) =
        compLeft (st ν₁) b₁ (comulCurried K c) +
          compLeft (st ν₂) b₂ (comulCurried K c) :=
      ZeroAtInftyContinuousMap.ext fun u ↦ calc
        compLeft (st (ν₁ + ν₂)) b₁₂ (comulCurried K c) u
          = st (ν₁ + ν₂) (comulCurried K c u) := compLeft_apply _ _ _ u
        _ = (st ν₁ + st ν₂) (comulCurried K c u) :=
          congrArg (· (comulCurried K c u)) (map_add st ν₁ ν₂)
        _ = st ν₁ (comulCurried K c u) + st ν₂ (comulCurried K c u) :=
          _root_.add_apply (st ν₁) (st ν₂) _
        _ = compLeft (st ν₁) b₁ (comulCurried K c) u +
              compLeft (st ν₂) b₂ (comulCurried K c) u :=
          congrArg₂ (· + ·) (compLeft_apply _ _ _ u).symm (compLeft_apply _ _ _ u).symm
        _ = (compLeft (st ν₁) b₁ (comulCurried K c) +
              compLeft (st ν₂) b₂ (comulCurried K c)) u :=
          (_root_.add_apply _ _ u).symm
    calc
      st (μ * (ν₁ + ν₂)) c
        = st μ (compLeft (st (ν₁ + ν₂)) b₁₂ (comulCurried K c)) :=
          stage_mul_apply h μ (ν₁ + ν₂) c
      _ = st μ (compLeft (st ν₁) b₁ (comulCurried K c) +
            compLeft (st ν₂) b₂ (comulCurried K c)) := congrArg (st μ) hd
      _ = st μ (compLeft (st ν₁) b₁ (comulCurried K c)) +
            st μ (compLeft (st ν₂) b₂ (comulCurried K c)) :=
          map_add (st μ) _ _
      _ = st (μ * ν₁) c + st (μ * ν₂) c :=
          congrArg₂ (· + ·) (stage_mul_apply h μ ν₁ c).symm (stage_mul_apply h μ ν₂ c).symm
      _ = (st (μ * ν₁) + st (μ * ν₂)) c :=
          (_root_.add_apply (st (μ * ν₁)) (st (μ * ν₂)) c).symm
      _ = st (μ * ν₁ + μ * ν₂) c :=
          congrArg (· c) (map_add st (μ * ν₁) (μ * ν₂)).symm
  right_distrib μ₁ μ₂ ν :=
    LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦
      let st := stage (p := p) (K := K) h
      let d := compLeft (st ν) ⟨‖st ν‖, (st ν).le_opNorm⟩ (comulCurried K c)
      calc
        st ((μ₁ + μ₂) * ν) c = st (μ₁ + μ₂) d := stage_mul_apply h (μ₁ + μ₂) ν c
        _ = (st μ₁ + st μ₂) d := congrArg (· d) (map_add st μ₁ μ₂)
        _ = st μ₁ d + st μ₂ d := _root_.add_apply (st μ₁) (st μ₂) d
        _ = st (μ₁ * ν) c + st (μ₂ * ν) c :=
          congrArg₂ (· + ·) (stage_mul_apply h μ₁ ν c).symm (stage_mul_apply h μ₂ ν c).symm
        _ = (st (μ₁ * ν) + st (μ₂ * ν)) c :=
          (_root_.add_apply (st (μ₁ * ν)) (st (μ₂ * ν)) c).symm
        _ = st (μ₁ * ν + μ₂ * ν) c :=
          congrArg (· c) (map_add st (μ₁ * ν) (μ₂ * ν)).symm

noncomputable instance : NonUnitalNonAssocRing (LocallyAnalyticDistribution p K) where
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero

noncomputable instance : Ring (LocallyAnalyticDistribution p K) where
  mul_assoc μ ν ρ := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
    rw [stage_mul_apply, stage_mul_apply, stage_mul_apply, comulCurried_compLeft K,
      comulCurried_comulCurried K]
    refine congrArg (stage h μ) (ZeroAtInftyContinuousMap.ext fun u ↦ ?_)
    simp only [compLeft_apply, stage_mul_apply]
  one_mul ν := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
    rw [stage_mul_apply, stage_one, evalCLM_apply, compLeft_apply]
    refine congrArg (stage h ν) (ZeroAtInftyContinuousMap.ext fun ⟨b, j⟩ ↦ ?_)
    rw [comulCurried_apply_apply, comul_apply_zero_left K]
  mul_one μ := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
    rw [stage_mul_apply]
    refine congrArg (stage h μ) (ZeroAtInftyContinuousMap.ext fun ⟨a, i⟩ ↦ ?_)
    rw [compLeft_apply, stage_one, evalCLM_apply, comulCurried_apply_apply,
      comul_apply_zero_right K]

/-- Locally analytic distributions form a commutative ring under additive convolution, with unit
`1 = dirac 0`. -/
noncomputable instance : CommRing (LocallyAnalyticDistribution p K) where
  mul_comm μ ν := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
    rw [stage_mul, stage_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← prodFunctional_comp_congrLeft_prodComm (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
        (stage h μ) ⟨‖stage h μ‖, (stage h μ).le_opNorm⟩,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, comul_swap K]

/-- Locally analytic distributions form a commutative `K`-algebra under additive convolution, with
scalar action inherited without diamond from the defining `Submodule K`. -/
noncomputable instance : Algebra K (LocallyAnalyticDistribution p K) :=
  have hsmul_mul (r : K) (μ ν : LocallyAnalyticDistribution p K) : (r • μ) * ν = r • (μ * ν) :=
    LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
      rw [(stage h).map_smul, _root_.smul_apply, stage_mul_apply, stage_mul_apply,
        (stage h).map_smul, _root_.smul_apply]
  Algebra.ofModule hsmul_mul fun r μ ν ↦ by
    rw [mul_comm, hsmul_mul, mul_comm]

-- Defeq sanity checks against `Submodule` additive and module structures.
example : (inferInstance : CommRing (LocallyAnalyticDistribution p K)).toAddCommGroup =
    Submodule.addCommGroup (LocallyAnalyticDistribution p K) := rfl

example : (inferInstance : Algebra K (LocallyAnalyticDistribution p K)).toModule =
    Submodule.module (LocallyAnalyticDistribution p K) := rfl

/-- Convolution of point-mass distributions corresponds to addition in `ℤ_p`. -/
theorem dirac_add (x y : ℤ_[p]) :
    dirac (p := p) (K := K) (x + y) = dirac x * dirac y := by
  refine LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ ?_
  rw [stage_mul_apply, stage_dirac_apply, stage_dirac_apply, eval_compLeft K, stage_dirac_apply,
    eval_eval_comulCurried K]

/-- Point-mass distributions as a multiplicative group homomorphism from `Multiplicative ℤ_p`. -/
noncomputable def diracHom : Multiplicative ℤ_[p] →* LocallyAnalyticDistribution p K where
  toFun x := dirac x.toAdd
  map_one' := dirac_zero
  map_mul' x y := dirac_add x.toAdd y.toAdd

/-- `diracHom` sends `x : Multiplicative ℤ_p` to `dirac x.toAdd`. -/
@[simp]
theorem diracHom_apply (x : Multiplicative ℤ_[p]) :
    diracHom (p := p) (K := K) x = dirac x.toAdd := (rfl)

/-! ### Comparison with native convolution of measures -/

/-- **Compatibility of `ofMeasure` with additive convolution of measures on `ℤ_p`.** Pushing the
product measure `μ.prodMk' ν` forward along `+ : ℤ_p × ℤ_p → ℤ_p` and viewing the result as a
locally analytic distribution gives the stage-wise convolution `ofMeasure μ * ofMeasure ν`. -/
theorem ofMeasure_map_add_prodMk' (μ ν : D(ℤ_[p], K)) :
    ofMeasure (p := p) (K := K)
        (AbstractMeasure.map ⟨fun q : ℤ_[p] × ℤ_[p] ↦ q.1 + q.2, continuous_add⟩ (μ.prodMk' ν)) =
      ofMeasure μ * ofMeasure ν := by
  refine LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ ?_
  rw [stage_ofMeasure, ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv,
    AbstractMeasure.map_apply, AbstractMeasure.prodMk'_apply, stage_mul_apply, stage_ofMeasure,
    ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv]
  refine congrArg μ (ContinuousMap.ext fun x ↦ ?_)
  rw [eval_compLeft K, stage_ofMeasure, ContinuousLinearMap.comp_apply,
    AbstractMeasure.coe_toCLMEquiv, AbstractMeasure.contractSnd_apply]
  refine congrArg ν (ContinuousMap.ext fun y ↦ ?_)
  exact (eval_eval_comulCurried K c x y).symm

/-- **Embedding of multiplicative `ℤ_p`-measures as a `K`-algebra homomorphism.** Transports a
measure on `Multiplicative ℤ_p` along `Homeomorph.ofAdd.symm` and views it as a locally analytic
distribution on `ℤ_p`, intertwining Mathlib's measure convolution with distribution convolution. -/
noncomputable def ofMulMeasure :
    D(Multiplicative ℤ_[p], K) →ₐ[K] LocallyAnalyticDistribution p K :=
  AlgHom.ofLinearMap
    (ofMeasure.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).toLinearMap)
    (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        AbstractMeasure.coe_arrowCongrLeft, AbstractMeasure.one_def, AbstractMeasure.map_dirac]
      rfl)
    (fun μ ν ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      have hpush : AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm (μ * ν) =
          AbstractMeasure.map ⟨fun q : ℤ_[p] × ℤ_[p] ↦ q.1 + q.2, continuous_add⟩
            ((AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ).prodMk'
              (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm ν)) := by
        ext g
        simp only [AbstractMeasure.mul_def, AbstractMeasure.arrowCongrLeft_apply,
          AbstractMeasure.map_apply, AbstractMeasure.prodMk'_apply]
        refine congrArg μ (ContinuousMap.ext fun x ↦ ?_)
        simp only [ContinuousMap.comp_apply, AbstractMeasure.contractSnd_apply,
          AbstractMeasure.arrowCongrLeft_apply]
        refine congrArg ν (ContinuousMap.ext fun y ↦ ?_)
        simp [ContinuousMap.comp_apply, toAdd_mul]
      rw [hpush, ofMeasure_map_add_prodMk'])

/-- `ofMulMeasure` applies `ofMeasure` after transporting along `Homeomorph.ofAdd.symm`. -/
theorem ofMulMeasure_apply (μ : D(Multiplicative ℤ_[p], K)) :
    ofMulMeasure (p := p) (K := K) μ =
      ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ) :=
  (rfl)

/-- Transporting an additive `ℤ_p`-measure along `Homeomorph.ofAdd` and applying `ofMulMeasure`
recovers `ofMeasure`. -/
@[simp]
theorem ofMulMeasure_ofAdd (μ : D(ℤ_[p], K)) :
    ofMulMeasure (p := p) (K := K) (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd μ) =
      ofMeasure μ := by
  rw [ofMulMeasure_apply, ← AbstractMeasure.arrowCongrLeft_symm, LinearEquiv.symm_apply_apply]

/-- `ofMulMeasure` sends the Dirac measure at `x : Multiplicative ℤ_p` to `dirac x.toAdd`. -/
@[simp]
theorem ofMulMeasure_dirac (x : Multiplicative ℤ_[p]) :
    ofMulMeasure (p := p) (K := K) (AbstractMeasure.dirac K x) = dirac x.toAdd := by
  rw [ofMulMeasure_apply, AbstractMeasure.coe_arrowCongrLeft, AbstractMeasure.map_dirac]
  rfl

/-- The `K`-algebra homomorphism `ofMulMeasure` is injective. -/
theorem ofMulMeasure_injective :
    Function.Injective (ofMulMeasure (p := p) (K := K)) :=
  ofMeasure_injective.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).injective

/-- Every stage seminorm of `ofMulMeasure μ` is bounded by the measure norm of `μ`. -/
theorem stageSeminorm_ofMulMeasure_le (μ : D(Multiplicative ℤ_[p], K)) (h : ℕ) :
    stageSeminorm h (ofMulMeasure (p := p) (K := K) μ) ≤ ‖AbstractMeasure.toCLMEquiv μ‖ := by
  rw [ofMulMeasure_apply]
  refine (stageSeminorm_ofMeasure_le _ h).trans ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (AbstractMeasure.toCLMEquiv μ))
    fun g ↦ ?_
  let φ : C(Multiplicative ℤ_[p], ℤ_[p]) :=
    ⟨Homeomorph.ofAdd.symm, Homeomorph.ofAdd.symm.continuous⟩
  have hcomp : ‖g.comp φ‖ ≤ ‖g‖ :=
    (ContinuousMap.norm_le (g.comp φ) (norm_nonneg g)).mpr fun x ↦ g.norm_coe_le_norm (φ x)
  calc
    ‖AbstractMeasure.toCLMEquiv (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ) g‖
      = ‖AbstractMeasure.toCLMEquiv μ (g.comp φ)‖ := by
        rw [AbstractMeasure.coe_toCLMEquiv, AbstractMeasure.arrowCongrLeft_apply,
          AbstractMeasure.coe_toCLMEquiv]
    _ ≤ ‖AbstractMeasure.toCLMEquiv μ‖ * ‖g.comp φ‖ :=
        (AbstractMeasure.toCLMEquiv μ).le_opNorm _
    _ ≤ ‖AbstractMeasure.toCLMEquiv μ‖ * ‖g‖ :=
        mul_le_mul_of_nonneg_left hcomp (norm_nonneg (AbstractMeasure.toCLMEquiv μ))

end TauCeti.LocallyAnalyticDistribution
