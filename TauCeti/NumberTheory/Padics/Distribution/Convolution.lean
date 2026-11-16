/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.NumberTheory.Padics.Measure.Monoid
public import TauCeti.NumberTheory.Padics.Distribution.Comul
public import TauCeti.NumberTheory.Padics.Distribution.Dual
public import TauCeti.NumberTheory.Padics.Measure.Dirac
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Dirac distributions and additive convolution on `ℤ_p`

Let `K` be a complete ultrametric nontrivially normed field which is a `ℤ_p`-algebra with
contractive `ℤ_p`-action. This file equips `TauCeti.LocallyAnalyticDistribution p K` with its
Dirac distributions and its additive convolution algebra structure:

* **Dirac distributions** (`LocallyAnalyticDistribution.dirac K x`): evaluation at `x ∈ ℤ_p` on
  locally analytic functions, obtained as `ofMeasure (AbstractMeasure.dirac K x)`. Every Dirac
  distribution has exact stage seminorm `1` at every level (`stageSeminorm_dirac`), and `dirac K`
  is injective (`dirac_injective`). Unlike the operator norm on `C(ℤ_p, K)*`, where distinct Dirac
  measures lie at distance `1`, the `h`-th stage seminorm makes `x ↦ dirac K x` Lipschitz on each
  disc modulo `pʰ` (`stageSeminorm_dirac_sub_le`), hence continuous at every point
  (`tendsto_stageSeminorm_dirac_sub`).
* **Additive convolution**: `1 = dirac K 0`, and `μ * ν` restricts on the analytic stage `LA_h(K)`
  to `prodPairing (stage h μ) (stage h ν) ∘L AnalyticStage.addComul K`. Compatibility of
  `addComul` with stage transitions (`prodMapCLM_transition_addComul`), together with its counit,
  cocommutativity, and coassociativity laws, makes `LocallyAnalyticDistribution p K` a commutative
  `K`-algebra in which every stage seminorm is submultiplicative (`stageSeminorm_mul_le`).
* **Compatibility with measures and group multiplication**:
  `dirac K (x + y) = dirac K x * dirac K y` (`dirac_add`), giving a monoid homomorphism
  `diracMonoidHom : Multiplicative ℤ_[p] →* LocallyAnalyticDistribution p K`, and embedding
  Mathlib's convolution algebra of measures `D(Multiplicative ℤ_[p], K)` faithfully as a
  `K`-subalgebra via `ofMulMeasure`.

None of the constructions in this file uses the Amice transform or requires `K` to have
characteristic zero; compatibility with the Amice transform is proved in
`TauCeti.NumberTheory.Padics.Distribution.Amice.Convolution`.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.dirac K x`: the Dirac distribution at `x ∈ ℤ_p`.
* `CommRing (TauCeti.LocallyAnalyticDistribution p K)` and
  `Algebra K (TauCeti.LocallyAnalyticDistribution p K)`: additive convolution of distributions.
* `TauCeti.LocallyAnalyticDistribution.diracMonoidHom`: `x ↦ dirac K x.toAdd` as a monoid
  homomorphism from `Multiplicative ℤ_[p]`.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure`: the injective `K`-algebra homomorphism
  `D(Multiplicative ℤ_[p], K) →ₐ[K] LocallyAnalyticDistribution p K`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_dirac`: `stageSeminorm h (dirac K x) = 1`.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_dirac_sub_le`: discwise Lipschitz continuity
  of `dirac K` in the `h`-th stage seminorm.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: submultiplicativity of every stage
  seminorm under convolution.
* `TauCeti.LocallyAnalyticDistribution.dirac_add`: `dirac K (x + y) = dirac K x * dirac K y`.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure_injective`: measures embed faithfully as a
  convolution `K`-subalgebra of locally analytic distributions.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped AbstractMeasure ZeroAtInfty

namespace TauCeti.LocallyAnalyticDistribution

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Dirac distributions -/

section Dirac

variable (K) in
/-- The **Dirac distribution** at `x ∈ ℤ_p`: evaluation of locally analytic functions at `x`,
defined as the distribution associated to the Dirac measure `AbstractMeasure.dirac K x`. -/
noncomputable def dirac (x : ℤ_[p]) : LocallyAnalyticDistribution p K :=
  ofMeasure (AbstractMeasure.dirac K x)

/-- `dirac K x` is the distribution induced by `AbstractMeasure.dirac K x`. -/
theorem dirac_def (x : ℤ_[p]) : dirac K x = ofMeasure (AbstractMeasure.dirac K x) :=
  (rfl)

/-- `ofMeasure` sends the Dirac measure at `x` to `dirac K x`. -/
theorem ofMeasure_dirac (x : ℤ_[p]) : ofMeasure (AbstractMeasure.dirac K x) = dirac K x :=
  (rfl)

/-- Applying `dirac K x` to a locally analytic function evaluates it at `x`. -/
@[simp]
theorem coe_dirac_apply (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    (dirac K x : Module.Dual K (LocallyAnalytic p K K)) f = LocallyAnalytic.eval K f x := by
  simp [dirac_def]

/-- On the analytic stage `LA_h(K)`, `dirac K x` restricts to point evaluation at `x` composed with
stage evaluation. -/
theorem stage_dirac (x : ℤ_[p]) (h : ℕ) :
    stage h (dirac K x) = ContinuousMap.evalCLM K x ∘L AnalyticStage.eval K := by
  ext c
  simp [dirac_def]

/-- Applying `stage h (dirac K x)` to a stage vector evaluates it at `x`. -/
theorem stage_dirac_apply (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h K) :
    stage h (dirac K x) c = AnalyticStage.eval K c x := by
  simp

/-- On the disc `a + pʰℤ_p`, `stage h (dirac K (a.val + pʰ w))` evaluates the power series of `c`
on the disc of `a` at `w`. -/
theorem stage_dirac_natCast_val_add_mul (h : ℕ) (a : ZMod (p ^ h)) (w : ℤ_[p])
    (c : AnalyticStage p h K) :
    stage h (dirac K ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w)) c = ∑' n, w ^ n • c (a, n) := by
  rw [stage_dirac_apply, AnalyticStage.eval_natCast_val_add_mul]

/-- At `0 ∈ ℤ_p`, `stage h (dirac K 0)` reads off the constant coefficient on the disc of `0`. -/
theorem stage_dirac_zero_apply (h : ℕ) (c : AnalyticStage p h K) :
    stage h (dirac K 0) c = c (0, 0) := by
  simp [dirac_def]

/-- **Every Dirac distribution has stage seminorm `1`** at every analytic level `h`. -/
theorem stageSeminorm_dirac (h : ℕ) (x : ℤ_[p]) : stageSeminorm h (dirac K x) = 1 := by
  classical
  refine le_antisymm ?_ ?_
  · exact (stageSeminorm_ofMeasure_le (AbstractMeasure.dirac K x) h).trans_eq
      (TauCeti.AbstractMeasure.norm_dirac x)
  · let c : AnalyticStage p h K := single (PadicInt.toZModPow h x, 0) 1
    have hc : ‖c‖ ≤ 1 := by simp [c]
    have hval : AnalyticStage.eval K c x = 1 := by
      rw [AnalyticStage.eval_apply, tsum_eq_single 0]
      · simp [c]
      · intro n hn
        simp [c, single_apply, hn]
    have hle := (stage h (dirac K x)).unit_le_opNorm c hc
    rwa [stage_apply, coe_dirac_apply, LocallyAnalytic.eval_ofStage, hval, norm_one,
      ← stageSeminorm_apply] at hle

/-- The operator norm of `stage h (dirac K x)` is `1`. -/
@[simp]
theorem norm_stage_dirac (h : ℕ) (x : ℤ_[p]) : ‖stage h (dirac K x)‖ = 1 := by
  rw [← stageSeminorm_apply, stageSeminorm_dirac]

/-- `dirac K` is injective: distinct points of `ℤ_p` define distinct locally analytic
distributions. -/
theorem dirac_injective : Function.Injective (dirac (p := p) K) := by
  intro x y hxy
  by_contra hne
  have hmeas : AbstractMeasure.dirac K x = AbstractMeasure.dirac K y := ofMeasure_injective hxy
  have h1 := TauCeti.AbstractMeasure.one_le_norm_dirac_sub (K := K) hne
  simp only [hmeas, sub_self, map_zero, norm_zero] at h1
  linarith

private theorem norm_pow_sub_pow_le (u v : ℤ_[p]) (n : ℕ) : ‖u ^ n - v ^ n‖ ≤ ‖u - v‖ := by
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow u v n
  rw [hq, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one q)

/-- On a single disc `a + pʰℤ_p`, `stage h (dirac K ·)` is `1`-Lipschitz in the disc coordinate. -/
theorem stageSeminorm_dirac_natCast_val_add_mul_sub_le (h : ℕ) (a : ZMod (p ^ h)) (u v : ℤ_[p]) :
    stageSeminorm h
      (dirac K ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) -
        dirac K ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v)) ≤ ‖u - v‖ := by
  rw [stageSeminorm_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c ↦ ?_
  have hu := AnalyticStage.hasSum_eval_natCast_val_add_mul K c a u
  have hv := AnalyticStage.hasSum_eval_natCast_val_add_mul K c a v
  rw [stage_apply, Submodule.coe_sub, LinearMap.sub_apply, coe_dirac_apply, coe_dirac_apply,
    LocallyAnalytic.eval_ofStage, ← (hu.sub hv).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun n ↦ ?_
  rw [← sub_smul]
  exact (norm_smul_le _ _).trans
    (mul_le_mul (norm_pow_sub_pow_le u v n) (c.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))

/-- **Discwise Lipschitz continuity of `dirac` in the `h`-th stage seminorm.** When `x` and `y` lie
in the same residue disc modulo `pʰ`, the `h`-th stage seminorm of `dirac K x - dirac K y` is at
most `‖x - y‖ / ‖(p : ℤ_[p])‖ ^ h`. -/
theorem stageSeminorm_dirac_sub_le {h : ℕ} {x y : ℤ_[p]}
    (hxy : PadicInt.toZModPow h x = PadicInt.toZModPow h y) :
    stageSeminorm h (dirac K x - dirac K y) ≤ ‖x - y‖ / ‖(p : ℤ_[p])‖ ^ h := by
  set a := PadicInt.toZModPow h x
  set u := ((PadicInt.discHomeomorph p h).symm x).2
  set v := ((PadicInt.discHomeomorph p h).symm y).2
  have hx := PadicInt.natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm h x
  have hy := PadicInt.natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm h y
  rw [← hxy] at hy
  have hsub : x - y = (p : ℤ_[p]) ^ h * (u - v) := by
    calc x - y = ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) -
          ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) := by rw [hx, hy]
      _ = (p : ℤ_[p]) ^ h * (u - v) := by ring
  have hp0 : 0 < ‖(p : ℤ_[p])‖ ^ h :=
    pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)) h
  have huv : ‖u - v‖ = ‖x - y‖ / ‖(p : ℤ_[p])‖ ^ h := by
    rw [hsub, norm_mul, norm_pow, mul_div_cancel_left₀ _ hp0.ne']
  rw [← huv]
  conv_lhs => rw [← hx, ← hy]
  exact stageSeminorm_dirac_natCast_val_add_mul_sub_le h a u v

/-- At every analytic level `h`, the map `y ↦ dirac K y` is continuous at `x` with respect to
`stageSeminorm h`. -/
theorem tendsto_stageSeminorm_dirac_sub (h : ℕ) (x : ℤ_[p]) :
    Tendsto (fun y ↦ stageSeminorm h (dirac K y - dirac K x)) (𝓝 x) (𝓝 0) := by
  have hopen : IsOpen {y : ℤ_[p] | PadicInt.toZModPow h y = PadicInt.toZModPow h x} :=
    (isOpen_discrete {PadicInt.toZModPow h x}).preimage (PadicInt.continuous_toZModPow h)
  have hnhds : {y : ℤ_[p] | PadicInt.toZModPow h y = PadicInt.toZModPow h x} ∈ 𝓝 x :=
    hopen.mem_nhds rfl
  have hcont : Continuous (fun y : ℤ_[p] ↦ ‖y - x‖ / ‖(p : ℤ_[p])‖ ^ h) :=
    ((continuous_id.sub continuous_const).norm).div_const _
  have hlim : Tendsto (fun y : ℤ_[p] ↦ ‖y - x‖ / ‖(p : ℤ_[p])‖ ^ h) (𝓝 x) (𝓝 0) := by
    simpa [sub_self, zero_div] using hcont.tendsto x
  refine squeeze_zero' (Eventually.of_forall fun y ↦ apply_nonneg (stageSeminorm h) _) ?_ hlim
  filter_upwards [hnhds] with y hy
  exact stageSeminorm_dirac_sub_le hy

end Dirac

/-! ### Additive convolution and `K`-algebra structure -/

section Convolution

/-- The multiplicative identity of `LocallyAnalyticDistribution p K` is the Dirac distribution at
`0 ∈ ℤ_p`. -/
noncomputable instance instOne : One (LocallyAnalyticDistribution p K) where
  one := dirac K 0

/-- `1` is the Dirac distribution at `0`. -/
theorem one_def : (1 : LocallyAnalyticDistribution p K) = dirac K 0 :=
  (rfl)

/-- The Dirac distribution at `0` is `1`. -/
@[simp]
theorem dirac_zero : dirac K (0 : ℤ_[p]) = 1 :=
  (rfl)

/-- Applying `1` to a locally analytic function evaluates it at `0`. -/
@[simp]
theorem coe_one_apply (f : LocallyAnalytic p K K) :
    ((1 : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f 0 :=
  coe_dirac_apply 0 f

/-- On stage `LA_h(K)`, the unit distribution `1` evaluates the `(0, 0)`-coefficient. -/
theorem stage_one_apply (h : ℕ) (c : AnalyticStage p h K) :
    stage h (1 : LocallyAnalyticDistribution p K) c = c (0, 0) :=
  stage_dirac_zero_apply h c

/-- Every stage seminorm of `1` is `1`. -/
theorem stageSeminorm_one (h : ℕ) : stageSeminorm h (1 : LocallyAnalyticDistribution p K) = 1 :=
  stageSeminorm_dirac h 0

/-- The operator norm of `stage h 1` is `1`. -/
@[simp]
theorem norm_stage_one (h : ℕ) : ‖stage h (1 : LocallyAnalyticDistribution p K)‖ = 1 := by
  rw [← stageSeminorm_apply, stageSeminorm_one]

private theorem mulStage_comp_transition (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    (prodPairing (stage (h + 1) μ) (stage (h + 1) ν) ∘L
        AnalyticStage.addComul (p := p) (h := h + 1) (E := K) K) ∘L
      AnalyticStage.transition K =
      prodPairing (stage h μ) (stage h ν) ∘L
        AnalyticStage.addComul (p := p) (h := h) (E := K) K := by
  let tK := AnalyticStage.transition (p := p) (h := h) (E := K) K
  have btK : ∃ C, ∀ f : AnalyticStage p h K, ‖tK f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simpa [tK] using AnalyticStage.norm_transition_le K f⟩
  have hcomul : prodMapCLM tK btK tK btK ∘L
      AnalyticStage.addComul (p := p) (h := h) (E := K) K =
      AnalyticStage.addComul (p := p) (h := h + 1) (E := K) K ∘L tK :=
    ContinuousLinearMap.ext (AnalyticStage.prodMapCLM_transition_addComul K btK btK)
  calc (prodPairing (stage (h + 1) μ) (stage (h + 1) ν) ∘L
          AnalyticStage.addComul (p := p) (h := h + 1) (E := K) K) ∘L tK
      = prodPairing (stage (h + 1) μ) (stage (h + 1) ν) ∘L
          (AnalyticStage.addComul (p := p) (h := h + 1) (E := K) K ∘L tK) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (prodPairing (stage (h + 1) μ) (stage (h + 1) ν) ∘L prodMapCLM tK btK tK btK) ∘L
          AnalyticStage.addComul (p := p) (h := h) (E := K) K := by
        rw [← hcomul, ContinuousLinearMap.comp_assoc]
    _ = prodPairing (stage h μ) (stage h ν) ∘L
          AnalyticStage.addComul (p := p) (h := h) (E := K) K := by
        rw [prodPairing_comp_prodMapCLM, stage_comp_transition, stage_comp_transition]

/-- **Additive convolution** of locally analytic distributions on `ℤ_p`. -/
noncomputable instance instMul : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν := stagesEquiv.symm
    ⟨fun h ↦ prodPairing (stage h μ) (stage h ν) ∘L
      AnalyticStage.addComul (p := p) (h := h) (E := K) K,
      by exact mem_compatibleStageFunctionals_iff.mpr (mulStage_comp_transition μ ν)⟩

/-- On the analytic stage `LA_h(K)`, `μ * ν` restricts to `prodPairing (stage h μ) (stage h ν)`
composed with `AnalyticStage.addComul K`. -/
@[simp]
theorem stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stage h (μ * ν) =
      prodPairing (stage h μ) (stage h ν) ∘L
        AnalyticStage.addComul (p := p) (h := h) (E := K) K := by
  change stage h (stagesEquiv.symm _) = _
  exact stage_stagesEquiv_symm _ h

/-- Pointwise stage formula for the convolution `μ * ν`. -/
theorem stage_mul_apply (μ ν : LocallyAnalyticDistribution p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    stage h (μ * ν) c =
      prodPairing (stage h μ) (stage h ν) (AnalyticStage.addComul K c) :=
  congr($(stage_mul μ ν h) c)

/-- **Submultiplicativity of the stage seminorms** under convolution. -/
theorem stageSeminorm_mul_le (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  have hcomul : ‖AnalyticStage.addComul (p := p) (h := h) (E := K) K‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by simp
  rw [stageSeminorm_apply, stageSeminorm_apply, stageSeminorm_apply, stage_mul]
  calc ‖prodPairing (stage h μ) (stage h ν) ∘L
          AnalyticStage.addComul (p := p) (h := h) (E := K) K‖
      ≤ ‖prodPairing (stage h μ) (stage h ν)‖ *
          ‖AnalyticStage.addComul (p := p) (h := h) (E := K) K‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖prodPairing (stage h μ) (stage h ν)‖ * 1 :=
        mul_le_mul_of_nonneg_left hcomul (ContinuousLinearMap.opNorm_nonneg _)
    _ = ‖stage h μ‖ * ‖stage h ν‖ := by rw [mul_one, norm_prodPairing]

private theorem mul_comm_aux (μ ν : LocallyAnalyticDistribution p K) : μ * ν = ν * μ := by
  ext h c
  rw [stage_mul_apply, stage_mul_apply, ← prodPairing_congrLeft_prodComm,
    AnalyticStage.congrLeft_prodComm_addComul]

private theorem mul_one_aux (μ : LocallyAnalyticDistribution p K) : μ * 1 = μ := by
  ext h c
  rw [stage_mul_apply, prodPairing_apply]
  refine congrArg (stage h μ) (ZeroAtInftyContinuousMap.ext fun ⟨a, i⟩ ↦ ?_)
  simp

private theorem mul_assoc_aux (μ ν ρ : LocallyAnalyticDistribution p K) :
    μ * ν * ρ = μ * (ν * ρ) := by
  ext h c
  let cK := AnalyticStage.addComul (p := p) (h := h) (E := K) K
  have bcK : ∃ C, ∀ f : AnalyticStage p h K, ‖cK f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simp [cK]⟩
  have hlhs : prodPairing (stage h (μ * ν)) (stage h ρ) =
      prodPairing (stage h μ) (prodPairing (stage h ν) (stage h ρ)) ∘L
        (congrLeft K K (Homeomorph.prodAssoc _ _ _)).toLinearIsometry.toContinuousLinearMap ∘L
          fstMapCLM (ZMod (p ^ h) × ℕ) cK bcK := by
    rw [stage_mul, ← prodPairing_comp_fstMapCLM _ _ cK bcK,
      ← prodPairing_comp_congrLeft_prodAssoc, ContinuousLinearMap.comp_assoc]
  have hrhs : prodPairing (stage h μ) (stage h (ν * ρ)) =
      prodPairing (stage h μ) (prodPairing (stage h ν) (stage h ρ)) ∘L
        sndMapCLM (ZMod (p ^ h) × ℕ) cK bcK := by
    rw [stage_mul, ← prodPairing_comp_sndMapCLM _ _ cK bcK]
  rw [stage_mul_apply, stage_mul_apply, hlhs, hrhs]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  exact congrArg (prodPairing (stage h μ) (prodPairing (stage h ν) (stage h ρ)))
    (AnalyticStage.coassoc_addComul K bcK bcK c)

/-- Locally analytic distributions on `ℤ_p` form a commutative ring under additive convolution. -/
noncomputable instance instCommRing : CommRing (LocallyAnalyticDistribution p K) where
  zero_mul ν := by ext h c; simp
  mul_zero μ := by ext h c; simp
  left_distrib μ ν₁ ν₂ := by ext h c; simp [prodPairing_add_right]
  right_distrib μ₁ μ₂ ν := by ext h c; simp [prodPairing_add_left]
  mul_assoc μ ν ρ := by exact mul_assoc_aux μ ν ρ
  mul_comm μ ν := by exact mul_comm_aux μ ν
  mul_one μ := by exact mul_one_aux μ
  one_mul μ := by rw [mul_comm_aux, mul_one_aux]

/-- Locally analytic distributions on `ℤ_p` form a commutative `K`-algebra under additive
convolution. -/
noncomputable instance instAlgebra : Algebra K (LocallyAnalyticDistribution p K) :=
  Algebra.ofModule
    (fun r μ ν ↦ by ext h c; simp [prodPairing_smul_left])
    (fun r μ ν ↦ by ext h c; simp [prodPairing_smul_right])

end Convolution

/-! ### Compatibility with measures and group multiplication -/

section Measures

private theorem eval₂_prodSMul_mul (h k : ℕ) (f : AnalyticStage p h K) (g : AnalyticStage p k K) :
    AnalyticStage.eval₂ K (prodSMul f g) =
      (AnalyticStage.eval K f).comp ContinuousMap.fst *
        (AnalyticStage.eval K g).comp ContinuousMap.snd := by
  ext ⟨x, y⟩
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, rfl⟩ := (PadicInt.discHomeomorph p k).surjective y
  simp only [PadicInt.discHomeomorph_apply, ContinuousMap.mul_apply, ContinuousMap.comp_apply]
  change AnalyticStage.eval₂ K (prodSMul f g)
      ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u, (b.val : ℤ_[p]) + (p : ℤ_[p]) ^ k * v) =
    AnalyticStage.eval K f ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) *
      AnalyticStage.eval K g ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ k * v)
  rw [AnalyticStage.eval₂_natCast_val_add_mul, AnalyticStage.eval_natCast_val_add_mul,
    AnalyticStage.eval_natCast_val_add_mul]
  have hf := (AnalyticStage.hasSum_eval_natCast_val_add_mul K f a u).summable
  have hg := (AnalyticStage.hasSum_eval_natCast_val_add_mul K g b v).summable
  rw [← hf.tsum_mul_right]
  refine tsum_congr fun i ↦ ?_
  rw [← hg.tsum_mul_left]
  refine tsum_congr fun j ↦ ?_
  simp only [prodSMul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- On two-variable stage families, pairing the stage functionals of two measures agrees with
integrating their two-variable evaluation against the product measure `μ.prodMk' ν`. -/
theorem prodPairing_stage_ofMeasure (μ ν : AbstractMeasure ℤ_[p] K K) (h k : ℕ)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), K)) :
    prodPairing (stage h (ofMeasure μ)) (stage k (ofMeasure ν)) F =
      (μ.prodMk' ν) (AnalyticStage.eval₂ K F) := by
  classical
  have hL : prodPairing (stage h (ofMeasure μ)) (stage k (ofMeasure ν)) =
      AbstractMeasure.toCLMEquiv (μ.prodMk' ν) ∘L
        AnalyticStage.eval₂ (p := p) (h := h) (k := k) (E := K) K := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext_single_one fun ij ↦ ?_
    rcases ij with ⟨i, j⟩
    have h1 : single (i, j) (1 : K) = prodSMul (single i (1 : K)) (single j (1 : K)) := by simp
    rw [h1, prodPairing_prodSMul, ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv,
      eval₂_prodSMul_mul, AbstractMeasure.prodMk'_prod_apply]
    simp
  simpa using congr($hL F)

/-- Convolving two measures as distributions integrates the evaluated stage function pulled back
along addition `(x, y) ↦ x + y`. -/
theorem stage_ofMeasure_mul_apply (μ ν : AbstractMeasure ℤ_[p] K K) (h : ℕ)
    (c : AnalyticStage p h K) :
    stage h (ofMeasure μ * ofMeasure ν) c =
      (μ.prodMk' ν) ((AnalyticStage.eval K c).comp ⟨fun q : ℤ_[p] × ℤ_[p] ↦ q.1 + q.2,
        continuous_add⟩) := by
  rw [stage_mul_apply, prodPairing_stage_ofMeasure]
  congr 1
  ext ⟨x, y⟩
  exact AnalyticStage.eval₂_addComul K c x y

/-- **Convolution of Dirac distributions** adds their support points:
`dirac K (x + y) = dirac K x * dirac K y`. -/
@[simp]
theorem dirac_add (x y : ℤ_[p]) : dirac K (x + y) = dirac K x * dirac K y := by
  ext h c
  rw [dirac_def x, dirac_def y, stage_ofMeasure_mul_apply]
  simp [AbstractMeasure.prodMk'_apply]

/-- `dirac K` sends `n • x` to `(dirac K x) ^ n`. -/
theorem dirac_nsmul (n : ℕ) (x : ℤ_[p]) : dirac K (n • x) = dirac K x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, dirac_add, ih, pow_succ]

/-- `dirac K` sends a natural number `n : ℤ_p` to `(dirac K 1) ^ n`. -/
theorem dirac_natCast (n : ℕ) : dirac K (n : ℤ_[p]) = dirac K 1 ^ n := by
  simpa using dirac_nsmul (K := K) n 1

variable (K) in
/-- `x ↦ dirac K x.toAdd` as a monoid homomorphism from `Multiplicative ℤ_[p]` into the convolution
algebra of locally analytic distributions. -/
noncomputable def diracMonoidHom : Multiplicative ℤ_[p] →* LocallyAnalyticDistribution p K where
  toFun x := dirac K x.toAdd
  map_one' := by simp
  map_mul' x y := by simp [toAdd_mul, dirac_add]

/-- `diracMonoidHom K` evaluates at `x : Multiplicative ℤ_[p]` to `dirac K x.toAdd`. -/
@[simp]
theorem diracMonoidHom_apply (x : Multiplicative ℤ_[p]) :
    diracMonoidHom K x = dirac K x.toAdd :=
  (rfl)

/-- `diracMonoidHom K` sends `Multiplicative.ofAdd x` to `dirac K x`. -/
theorem diracMonoidHom_ofAdd (x : ℤ_[p]) :
    diracMonoidHom K (Multiplicative.ofAdd x) = dirac K x :=
  (rfl)

/-- **Embedding the measure algebra into locally analytic distributions.** Pushing a measure on
`Multiplicative ℤ_[p]` along `Homeomorph.ofAdd.symm : Multiplicative ℤ_[p] ≃ₜ ℤ_[p]` and
restricting to locally analytic functions defines a `K`-algebra homomorphism from Mathlib's measure
convolution algebra `D(Multiplicative ℤ_[p], K)` into `LocallyAnalyticDistribution p K`. -/
noncomputable def ofMulMeasure :
    D(Multiplicative ℤ_[p], K) →ₐ[K] LocallyAnalyticDistribution p K :=
  AlgHom.ofLinearMap
    (ofMeasure.comp
      (AbstractMeasure.arrowCongrLeft (Homeomorph.ofAdd (X := ℤ_[p])).symm).toLinearMap)
    (by
      ext h c
      simp [AbstractMeasure.one_def, AbstractMeasure.coe_arrowCongrLeft])
    (fun μ ν ↦ by
      ext h c
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [stage_ofMeasure_mul_apply, stage_ofMeasure, ContinuousLinearMap.comp_apply,
        AbstractMeasure.coe_toCLMEquiv, AbstractMeasure.arrowCongrLeft_apply,
        AbstractMeasure.mul_apply, AbstractMeasure.prodMk'_apply,
        AbstractMeasure.arrowCongrLeft_apply]
      congr 1
      ext x
      simp only [AbstractMeasure.convolveFunRight_apply, ContinuousMap.comp_apply,
        AbstractMeasure.contractSnd_apply, AbstractMeasure.arrowCongrLeft_apply]
      congr 1)

/-- `ofMulMeasure` pushes forward along `Homeomorph.ofAdd.symm` and applies `ofMeasure`. -/
theorem ofMulMeasure_def (μ : D(Multiplicative ℤ_[p], K)) :
    ofMulMeasure μ =
      ofMeasure (AbstractMeasure.arrowCongrLeft (Homeomorph.ofAdd (X := ℤ_[p])).symm μ) :=
  (rfl)

/-- `ofMulMeasure` sends the Dirac measure at `x : Multiplicative ℤ_[p]` to `dirac K x.toAdd`. -/
@[simp]
theorem ofMulMeasure_dirac (x : Multiplicative ℤ_[p]) :
    ofMulMeasure (AbstractMeasure.dirac K x) = dirac K x.toAdd := by
  ext h c
  simp [ofMulMeasure_def]

/-- `ofMulMeasure` is injective: `D(Multiplicative ℤ_[p], K)` embeds faithfully as a `K`-subalgebra
of `LocallyAnalyticDistribution p K`. -/
theorem ofMulMeasure_injective : Function.Injective (ofMulMeasure (p := p) (K := K)) :=
  ofMeasure_injective.comp (AbstractMeasure.arrowCongrLeft _).injective

end Measures

end TauCeti.LocallyAnalyticDistribution
