/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.Data.Comparison
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# The continued uncompleted L-function of an analytic L-function record

Given an analytic L-function record `d : AnalyticLFunctionData`, the completed function is related
to the uncompleted L-function on `Re s > 1` by `Λ(s) = N^(s/2) γ(s) L(s)`. Away from the poles of
`Λ`, multiplying `Λ(s)` by `N^(-s/2)` and the entire reciprocal `d.invGammaFactor s = (γ(s))⁻¹`
recovers `L(s)`, including at the trivial zeros where `γ` has poles and `invGammaFactor` vanishes.

At a recorded pole `s` of `Λ`, however, a zero of `invGammaFactor` of multiplicity at least
`d.polarOrder s` cancels the pole of `Λ` as a meromorphic germ, while the raw pointwise product
multiplies `Λ(s)` by `0` (for instance at `s = 0` for the Riemann zeta function, where
`(Gammaℝ 0)⁻¹ = 0` whereas `ζ(0) = -1/2`). Conversely, at an uncancelled pole of `L` (such as
`s = 1` for `ζ`), Mathlib's uncompleted function retains the raw quotient value
`completedRiemannZeta 1 / Gammaℝ 1` rather than `0`.

`AnalyticLFunctionData.continuedL` therefore defines the continued uncompleted L-function by
replacing the raw product `N^(-s/2) Λ(s) d.invGammaFactor s` with its local meromorphic normal-form
value `toMeromorphicNFAt _ s s` selectively at the finitely many points of `d.polarOrder.support`
where `(d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s`, leaving all other
values unchanged.

## Main definitions

* `TauCeti.LFunctions.AnalyticLFunctionData.continuedL`: the continued uncompleted L-function of
  an analytic L-function record.

## Main results

* `continuedL_of_polarOrder_ne_zero`, `continuedL_of_polarOrder_eq_zero`,
  `continuedL_eventuallyEq`, `completed_eventuallyEq_mul_continuedL`, `completed_eq_mul_continuedL`:
  branch characterizations, punctured-germ identities at every point, and pointwise recovery of `Λ`
  wherever `γ(s) ≠ 0`.
* `EqOffZero.continuedL_eq`, `dual_continuedL`: invariance under changing `coeff 0` and reflection
  compatibility with `AnalyticLFunctionData.dual`.
* `meromorphicOrderAt_continuedL`, `divisor_continuedL`,
  `HasMeromorphicContinuation.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt`,
  `HasMeromorphicContinuation.analyticAt_continuedL_iff`,
  `HasMeromorphicContinuation.continuedL_eq_toMeromorphicNFAt`: meromorphic order, divisor,
  characterizations of analytic points, and normal-form representation there.
* `HasMeromorphicContinuation.completed_eq_zero_of_eventuallyEq_zero`,
  `HasDirichletAgreement.continuedL_eq_LSeries`,
  `HasDirichletAgreement.toMeromorphicNFOn_continuedL_eq_meromorphicContinuation`: identity
  principle for `completed`, agreement with `LSeries d.coeff` on `Re s > 1` (including across any
  poles of `γ` in that half-plane), and identification of the normal form with
  `TauCeti.meromorphicContinuation`.
* `HasFunctionalEquation.gammaFactor_mul_continuedL_eventuallyEq`,
  `HasFunctionalEquation.gammaFactor_mul_continuedL`,
  `HasFunctionalEquation.continuedL_eq_mul_dual`: the functional equation against `d.dual` as germs
  everywhere and pointwise off the excluded loci.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer, 2000, §12.
-/

public section

open Complex ComplexConjugate Filter Set Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

private noncomputable def rawContinuedL (d : AnalyticLFunctionData) (s : ℂ) : ℂ :=
  ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s

private theorem rawContinuedL_eq (d : AnalyticLFunctionData) :
    (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) =
      rawContinuedL d :=
  rfl

private theorem analyticAt_conductor_cpow_neg_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s := by
  have hbase : ((d.conductor : ℕ) : ℂ) ∈ slitPlane :=
    natCast_mem_slitPlane.mpr d.conductor.ne_zero
  fun_prop (disch := assumption)

private theorem analyticAt_conductor_cpow_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2)) s := by
  have hbase : ((d.conductor : ℕ) : ℂ) ∈ slitPlane :=
    natCast_mem_slitPlane.mpr d.conductor.ne_zero
  fun_prop (disch := assumption)

section Basic

variable (d : AnalyticLFunctionData)

open Classical in
/-- **The continued uncompleted L-function** of an analytic L-function record `d`. Away from the
finitely many recorded poles of `d.completed` that are cancelled by zeros of `d.invGammaFactor`, it
equals `N ^ (-s / 2) * d.completed s * d.invGammaFactor s`; at those removable poles it takes the
analytic value extracted by `toMeromorphicNFAt`. Uncancelled poles keep their raw product value. -/
noncomputable def continuedL (s : ℂ) : ℂ :=
  if d.polarOrder s ≠ 0 ∧ (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s then
    toMeromorphicNFAt
      (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s
  else
    ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s

open Classical in
/-- The defining formula of `AnalyticLFunctionData.continuedL`. -/
theorem continuedL_def (s : ℂ) :
    d.continuedL s =
      if d.polarOrder s ≠ 0 ∧
          (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s then
        toMeromorphicNFAt
          (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s
      else
        ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s :=
  (rfl)

/-- At a recorded pole of `Λ` cancelled by a zero of `invGammaFactor` of at least the same order,
`continuedL` takes the local meromorphic normal-form value. -/
theorem continuedL_of_polarOrder_ne_zero {s : ℂ} (hp : d.polarOrder s ≠ 0)
    (hle : (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s) :
    d.continuedL s =
      toMeromorphicNFAt
        (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s := by
  simp only [continuedL_def, hp, ne_eq, not_false_eq_true, hle, and_self, ↓reduceIte]

/-- Away from the recorded poles of `Λ`, `continuedL` is the raw product with `invGammaFactor`. -/
theorem continuedL_of_polarOrder_eq_zero {s : ℂ} (hp : d.polarOrder s = 0) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := by
  rw [continuedL_def, ite_eq_right]
  exact fun h ↦ (h.1 hp).elim

/-- At a recorded pole whose order exceeds the zero multiplicity of `invGammaFactor`, `continuedL`
retains the raw product value. -/
theorem continuedL_of_meromorphicOrderAt_invGammaFactor_lt {s : ℂ}
    (h : meromorphicOrderAt d.invGammaFactor s < (d.polarOrder s : WithTop ℤ)) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := by
  rw [continuedL_def, ite_eq_right]
  exact fun hle ↦ (hle.2.not_gt h).elim

/-- Wherever the gamma factor is regular (`γ(s) ≠ 0`), `continuedL` is the raw product: no pole of
`Λ` can be cancelled there. -/
theorem continuedL_of_gammaFactor_ne_zero {s : ℂ} (hγ : d.gammaFactor s ≠ 0) :
    d.continuedL s =
      ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * (d.gammaFactor s)⁻¹ := by
  have hord : meromorphicOrderAt d.invGammaFactor s = 0 := by
    rw [d.meromorphicOrderAt_invGammaFactor,
      (d.meromorphicOrderAt_gammaFactor_eq_zero_iff s).mpr hγ, neg_zero]
  rw [← d.invGammaFactor_def, continuedL_def, ite_eq_right]
  rintro ⟨hp, hle⟩
  rw [hord] at hle
  exact hp (Nat.le_zero.mp (by exact_mod_cast hle))

/-- At a pole of `γ` that is not a recorded pole of `Λ`, `continuedL` vanishes. -/
theorem continuedL_eq_zero_of_polarOrder_eq_zero {s : ℂ} (hp : d.polarOrder s = 0)
    (hγ : d.gammaFactor s = 0) : d.continuedL s = 0 := by
  rw [d.continuedL_of_polarOrder_eq_zero hp, (d.invGammaFactor_eq_zero_iff s).mpr hγ, mul_zero]

/-- At every point of `ℂ`, `continuedL` agrees on a punctured neighbourhood with the raw product
`N ^ (-z / 2) * Λ(z) * invGammaFactor d z`. -/
theorem continuedL_eventuallyEq (s : ℂ) :
    d.continuedL =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z := by
  have hfin := d.polarOrder.support.finite_toSet
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite (x := s) univ_mem hfin.to_subtype] with z hz
  exact d.continuedL_of_polarOrder_eq_zero (by simpa using hz.2)

/-- Pointwise recovery of the completed function wherever `γ(s) ≠ 0`. At a pole of `γ` the right
hand side multiplies by the junk value `0`, so the hypothesis cannot be dropped. -/
theorem completed_eq_mul_continuedL {s : ℂ} (hγ : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s := by
  have hpow : ((d.conductor : ℕ) : ℂ) ^ (s / 2) * ((d.conductor : ℕ) : ℂ) ^ (-s / 2) = 1 := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr d.conductor.ne_zero),
      (by ring : s / 2 + -s / 2 = 0), cpow_zero]
  rw [d.continuedL_of_gammaFactor_ne_zero hγ]
  calc
    d.completed s =
        (((d.conductor : ℕ) : ℂ) ^ (s / 2) * ((d.conductor : ℕ) : ℂ) ^ (-s / 2)) *
          (d.gammaFactor s * (d.gammaFactor s)⁻¹) * d.completed s := by
      rw [hpow, mul_inv_cancel₀ hγ, one_mul, one_mul]
    _ = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s *
        (((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * (d.gammaFactor s)⁻¹) := by ring

/-- At every point `s`, `Λ(z) = N ^ (z / 2) * γ(z) * continuedL d z` holds as an equality of
punctured germs, poles of `Λ` and `γ` included. -/
theorem completed_eventuallyEq_mul_continuedL (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z := by
  have hγ : ∀ᶠ z in 𝓝[≠] s, d.gammaFactor z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (d.meromorphic_gammaFactor s)).mp
      (d.meromorphicOrderAt_gammaFactor_ne_top s)
  filter_upwards [hγ] with z hz using d.completed_eq_mul_continuedL hz

/-- The continued function of the dual card is the reflection of `continuedL` across the real
axis. -/
theorem dual_continuedL_apply (s : ℂ) :
    d.dual.continuedL s = conj (d.continuedL (conj s)) := by
  have hraw : rawContinuedL d.dual = conj ∘ rawContinuedL d ∘ conj := by
    ext z
    have hN := TauCeti.ofReal_cpow_conj (d.conductor : ℕ).cast_nonneg (-z / 2)
    rw [Complex.ofReal_natCast, map_div₀, map_neg, map_ofNat] at hN
    simp only [rawContinuedL, Function.comp_apply, dual_conductor, dual_completed_apply,
      d.invGammaFactor_dual, Complex.star_def, map_mul, hN, Complex.conj_conj]
  have hord : meromorphicOrderAt d.dual.invGammaFactor s =
      meromorphicOrderAt d.invGammaFactor (conj s) := by
    have heq : d.dual.invGammaFactor = conj ∘ d.invGammaFactor ∘ conj := by
      ext z
      simpa only [Complex.star_def, Function.comp_apply] using d.invGammaFactor_dual z
    rw [heq, TauCeti.meromorphicOrderAt_conj_conj]
  simp only [continuedL_def, dual_polarOrder_apply, hord, rawContinuedL_eq]
  split_ifs with h
  · rw [hraw]
    exact congrFun (TauCeti.toMeromorphicNFAt_conj_conj (rawContinuedL d) s) s
  · exact congrFun hraw s

@[simp]
theorem dual_continuedL : d.dual.continuedL = conj ∘ d.continuedL ∘ conj :=
  funext d.dual_continuedL_apply

/-! ### Meromorphy, orders, divisors, and analyticity -/

/-- `continuedL` is meromorphic at `z` if and only if `completed` is meromorphic at `z`. -/
@[simp]
theorem meromorphicAt_continuedL_iff {z : ℂ} :
    MeromorphicAt d.continuedL z ↔ MeromorphicAt d.completed z := by
  constructor
  · intro hm
    have hmul : MeromorphicAt
        (fun w ↦ ((d.conductor : ℕ) : ℂ) ^ (w / 2) * d.gammaFactor w * d.continuedL w) z :=
      ((analyticAt_conductor_cpow_div_two d z).meromorphicAt.mul
        (d.meromorphic_gammaFactor z)).mul hm
    exact hmul.congr (d.completed_eventuallyEq_mul_continuedL z).symm
  · intro hm
    have hmul : MeromorphicAt
        (fun w ↦ ((d.conductor : ℕ) : ℂ) ^ (-w / 2) * d.completed w * d.invGammaFactor w) z :=
      ((analyticAt_conductor_cpow_neg_div_two d z).meromorphicAt.mul hm).mul
        (d.analyticAt_invGammaFactor z).meromorphicAt
    exact hmul.congr (d.continuedL_eventuallyEq z).symm

/-- `continuedL` is meromorphic on `U` if and only if `completed` is meromorphic on `U`. -/
@[simp]
theorem meromorphicOn_continuedL_iff {U : Set ℂ} :
    MeromorphicOn d.continuedL U ↔ MeromorphicOn d.completed U :=
  forall₂_congr fun _ _ ↦ d.meromorphicAt_continuedL_iff

/-- `continuedL` is globally meromorphic if and only if `completed` is globally meromorphic. -/
@[simp]
theorem meromorphic_continuedL_iff : Meromorphic d.continuedL ↔ Meromorphic d.completed :=
  forall_congr' fun _ ↦ d.meromorphicAt_continuedL_iff

/-- The meromorphic order of `continuedL` is that of `Λ` minus that of `γ`, whenever `Λ` is
meromorphic at `z` (including when `Λ` vanishes identically near `z`). -/
theorem meromorphicOrderAt_continuedL {z : ℂ} (hm : MeromorphicAt d.completed z) :
    meromorphicOrderAt d.continuedL z =
      meromorphicOrderAt d.completed z - meromorphicOrderAt d.gammaFactor z := by
  have hN := analyticAt_conductor_cpow_neg_div_two d z
  have hN0 : meromorphicOrderAt (fun w : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (-w / 2)) z = 0 :=
    hN.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero)))
  rw [meromorphicOrderAt_congr (d.continuedL_eventuallyEq z),
    fun_meromorphicOrderAt_mul (hN.meromorphicAt.fun_mul hm)
      (d.analyticAt_invGammaFactor z).meromorphicAt,
    fun_meromorphicOrderAt_mul hN.meromorphicAt hm, hN0, zero_add,
    d.meromorphicOrderAt_invGammaFactor, sub_eq_add_neg]

/-- On any domain where `Λ` is meromorphic with finite order, the divisor of `continuedL` is the
divisor of `Λ` minus the divisor of `γ`. -/
theorem divisor_continuedL {U : Set ℂ} (hm : MeromorphicOn d.completed U)
    (htop : ∀ z ∈ U, meromorphicOrderAt d.completed z ≠ ⊤) :
    MeromorphicOn.divisor d.continuedL U =
      MeromorphicOn.divisor d.completed U - MeromorphicOn.divisor d.gammaFactor U := by
  ext z
  by_cases hz : z ∈ U
  · lift meromorphicOrderAt d.completed z to ℤ using htop z hz with a ha
    lift meromorphicOrderAt d.gammaFactor z to ℤ using d.meromorphicOrderAt_gammaFactor_ne_top z
      with b hb
    simp [hm, d.meromorphicOn_continuedL_iff.mpr hm, d.meromorphicOn_gammaFactor, hz,
      d.meromorphicOrderAt_continuedL (hm z hz), ← ha, ← hb,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  · simp [hz]

/-- At an analytic point, `continuedL` vanishes if and only if its meromorphic order is strictly
positive. -/
theorem continuedL_eq_zero_iff_meromorphicOrderAt_pos {z : ℂ} (ha : AnalyticAt ℂ d.continuedL z) :
    d.continuedL z = 0 ↔ 0 < meromorphicOrderAt d.continuedL z := by
  rw [lt_iff_le_and_ne, and_iff_right ha.meromorphicOrderAt_nonneg, ne_comm, ← not_iff_not,
    not_ne_iff]
  exact ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.symm

end Basic

section Predicates

variable {d e : AnalyticLFunctionData}

/-- Comparing two cards away from index zero preserves `continuedL`. -/
theorem EqOffZero.continuedL_eq (h : d.EqOffZero e) : d.continuedL = e.continuedL := by
  have hinv : d.invGammaFactor = e.invGammaFactor := by
    rw [d.invGammaFactor_eq_inv, e.invGammaFactor_eq_inv, h.gammaFactor_eq]
  ext s
  simp only [continuedL_def, h.polarOrder_eq, h.conductor_eq, h.completed_eq, hinv]

/-- Under `HasMeromorphicContinuation`, `continuedL` is meromorphic on `ℂ`. -/
@[fun_prop]
theorem HasMeromorphicContinuation.meromorphic_continuedL (hm : d.HasMeromorphicContinuation) :
    Meromorphic d.continuedL :=
  d.meromorphic_continuedL_iff.mpr hm.meromorphic

/-- Under `HasMeromorphicContinuation`, `continuedL` is meromorphic on every set. -/
@[fun_prop]
theorem HasMeromorphicContinuation.meromorphicOn_continuedL (hm : d.HasMeromorphicContinuation)
    {U : Set ℂ} : MeromorphicOn d.continuedL U :=
  hm.meromorphic_continuedL.meromorphicOn

/-- If a meromorphically continued completed function vanishes on a neighbourhood of a single
point, then it vanishes everywhere on `ℂ` (including at any candidate pole points, since exactness
of `polarOrder` rules out poles of infinite meromorphic order). -/
theorem HasMeromorphicContinuation.completed_eq_zero_of_eventuallyEq_zero
    (hm : d.HasMeromorphicContinuation) {z₀ : ℂ} (h0 : d.completed =ᶠ[𝓝 z₀] 0) :
    d.completed = 0 := by
  have htop_z₀ : meromorphicOrderAt d.completed z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (h0.filter_mono nhdsWithin_le_nhds)
  have htop : ∀ w : ℂ, meromorphicOrderAt d.completed w = ⊤ := fun w ↦
    (meromorphicOn_univ.mpr hm.meromorphic).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ z₀) (mem_univ w) htop_z₀
  ext w
  have hp : d.polarOrder w = 0 := by
    by_contra hp
    exact WithTop.top_ne_coe (htop w ▸ hm.meromorphicOrderAt_eq w hp)
  exact (((hm.analyticAt w hp).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    continuousAt_const).mp (meromorphicOrderAt_eq_top_iff.mp (htop w))).eq_of_nhds

/-- At a recorded pole of `Λ`, the meromorphic order of `continuedL` is `-polarOrder z` minus the
order of `γ`. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL_of_polarOrder_ne_zero
    (hm : d.HasMeromorphicContinuation) {z : ℂ} (hp : d.polarOrder z ≠ 0) :
    meromorphicOrderAt d.continuedL z =
      -(d.polarOrder z : ℤ) - meromorphicOrderAt d.gammaFactor z := by
  rw [d.meromorphicOrderAt_continuedL (hm.meromorphic z), hm.meromorphicOrderAt_eq z hp]

/-- Away from the recorded poles of `Λ`, `continuedL` is analytic. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_of_polarOrder_eq_zero
    (hm : d.HasMeromorphicContinuation) {z : ℂ} (hp : d.polarOrder z = 0) :
    AnalyticAt ℂ d.continuedL z := by
  have hraw : AnalyticAt ℂ (rawContinuedL d) z :=
    ((analyticAt_conductor_cpow_neg_div_two d z).mul (hm.analyticAt z hp)).mul
      (d.analyticAt_invGammaFactor z)
  refine hraw.congr ?_
  have hfin := d.polarOrder.support.finite_toSet
  have hopen : IsOpen ((d.polarOrder.support : Set ℂ)ᶜ) := hfin.isClosed.isOpen_compl
  filter_upwards [hopen.mem_nhds (by simpa using hp)] with w hw
  exact (d.continuedL_of_polarOrder_eq_zero (by simpa using hw)).symm

/-- If `Λ` has no poles (`d.polarOrder = 0`), then `continuedL` is entire. -/
theorem HasMeromorphicContinuation.differentiable_continuedL_of_polarOrder_eq_zero
    (hm : d.HasMeromorphicContinuation) (hp : d.polarOrder = 0) :
    Differentiable ℂ d.continuedL :=
  fun z ↦ (hm.analyticAt_continuedL_of_polarOrder_eq_zero (by simp [hp])).differentiableAt

/-- Under `HasMeromorphicContinuation`, `continuedL` is analytic at `z` if and only if its
meromorphic order at `z` is nonnegative. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt
    (hm : d.HasMeromorphicContinuation) {z : ℂ} :
    0 ≤ meromorphicOrderAt d.continuedL z ↔ AnalyticAt ℂ d.continuedL z := by
  classical
  refine ⟨fun hord ↦ ?_, AnalyticAt.meromorphicOrderAt_nonneg⟩
  by_cases hp : d.polarOrder z = 0
  · exact hm.analyticAt_continuedL_of_polarOrder_eq_zero hp
  · have hraw_mero : MeromorphicAt (rawContinuedL d) z :=
      ((analyticAt_conductor_cpow_neg_div_two d z).meromorphicAt.mul
        (hm.meromorphic z)).mul (d.analyticAt_invGammaFactor z).meromorphicAt
    have hraw_ord : 0 ≤ meromorphicOrderAt (rawContinuedL d) z := by
      rw [← rawContinuedL_eq, ← meromorphicOrderAt_congr (d.continuedL_eventuallyEq z)]
      exact hord
    have hle : (d.polarOrder z : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor z := by
      rw [hm.meromorphicOrderAt_continuedL_of_polarOrder_ne_zero hp, sub_eq_add_neg,
        ← d.meromorphicOrderAt_invGammaFactor] at hord
      rw [d.meromorphicOrderAt_invGammaFactor_eq_count] at hord ⊢
      have hk : 0 ≤ -(d.polarOrder z : ℤ) +
          (((d.gammaR.countP fun μ ↦ ∃ n : ℕ, z + μ = -(2 * (n : ℂ))) +
            (d.gammaC.countP fun ν ↦ ∃ n : ℕ, z + ν = -(n : ℂ))) : ℕ) := by
        exact_mod_cast hord
      exact WithTop.coe_le_coe.mpr (by omega)
    have han : AnalyticAt ℂ (toMeromorphicNFAt (rawContinuedL d) z) z :=
      hraw_mero.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hraw_ord
    refine han.congr ?_
    have hfin : ((d.polarOrder.support : Set ℂ) \ {z}).Finite :=
      d.polarOrder.support.finite_toSet.sdiff
    have hopen : IsOpen (((d.polarOrder.support : Set ℂ) \ {z})ᶜ) := hfin.isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds (by simp)] with w hw
    by_cases hwz : w = z
    · subst hwz
      rw [d.continuedL_of_polarOrder_ne_zero hp hle, rawContinuedL_eq]
    · have hwp : d.polarOrder w = 0 := by
        by_contra hne
        exact hw ⟨Finsupp.mem_support_iff.mpr hne, hwz⟩
      rw [d.continuedL_of_polarOrder_eq_zero hwp,
        ← hraw_mero.eqOn_compl_singleton_toMeromorphicNFAt hwz]
      rfl

/-- Under `HasMeromorphicContinuation`, `continuedL` is analytic at `z` if and only if the zero
multiplicity of `invGammaFactor` at `z` is at least `d.polarOrder z`. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_iff
    (hm : d.HasMeromorphicContinuation) {z : ℂ} :
    AnalyticAt ℂ d.continuedL z ↔
      (d.polarOrder z : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor z := by
  classical
  by_cases hp : d.polarOrder z = 0
  · rw [hp, Nat.cast_zero]
    exact iff_of_true (hm.analyticAt_continuedL_of_polarOrder_eq_zero hp)
      (d.analyticAt_invGammaFactor z).meromorphicOrderAt_nonneg
  · rw [← hm.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt,
      hm.meromorphicOrderAt_continuedL_of_polarOrder_ne_zero hp, sub_eq_add_neg,
      ← d.meromorphicOrderAt_invGammaFactor, d.meromorphicOrderAt_invGammaFactor_eq_count]
    set k : ℕ := (d.gammaR.countP fun μ ↦ ∃ n : ℕ, z + μ = -(2 * (n : ℂ))) +
      (d.gammaC.countP fun ν ↦ ∃ n : ℕ, z + ν = -(n : ℂ))
    have hk : ((k : ℕ) : WithTop ℤ) = ((k : ℤ) : WithTop ℤ) := rfl
    have hp' : ((d.polarOrder z : ℕ) : WithTop ℤ) = ((d.polarOrder z : ℤ) : WithTop ℤ) := rfl
    have h0 : (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := rfl
    rw [hk, hp', h0, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
      WithTop.coe_le_coe, WithTop.coe_le_coe]
    omega

/-- Under `HasMeromorphicContinuation`, at every point where the zero multiplicity of
`invGammaFactor` is at least `d.polarOrder s`, `continuedL` equals the local meromorphic normal-form
value of `N ^ (-z / 2) * Λ(z) * invGammaFactor d z`. -/
theorem HasMeromorphicContinuation.continuedL_eq_toMeromorphicNFAt
    (hm : d.HasMeromorphicContinuation) {s : ℂ}
    (hle : (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s) :
    d.continuedL s =
      toMeromorphicNFAt
        (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s :=
  ((hm.analyticAt_continuedL_iff.mpr hle).toMeromorphicNFAt_apply_of_eventuallyEq
    (d.continuedL_eventuallyEq s).symm).symm

/-! ### Agreement with the Dirichlet series -/

/-- On `Re s > 1`, `continuedL` agrees with `LSeries d.coeff` at every point where `γ(s) ≠ 0`,
without requiring meromorphic continuation. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries_of_gammaFactor_ne_zero
    (hd : d.HasDirichletAgreement) {s : ℂ} (hs : 1 < s.re) (hγ : d.gammaFactor s ≠ 0) :
    d.continuedL s = LSeries d.coeff s := by
  have hpow : ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ (s / 2) = 1 := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr d.conductor.ne_zero), neg_div, neg_add_cancel,
      cpow_zero]
  rw [d.continuedL_of_gammaFactor_ne_zero hγ, hd.completed_eq s hs]
  calc
    ((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
        (((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * LSeries d.coeff s) *
        (d.gammaFactor s)⁻¹ =
      (((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ (s / 2)) *
        (d.gammaFactor s * (d.gammaFactor s)⁻¹) * LSeries d.coeff s := by ring
    _ = LSeries d.coeff s := by rw [hpow, mul_inv_cancel₀ hγ, one_mul, one_mul]

private theorem gammaFactor_ne_zero_of_norm_sum_lt (d : AnalyticLFunctionData) {x : ℝ}
    (hx : (d.gammaR.map (‖·‖)).sum + (d.gammaC.map (‖·‖)).sum < x) :
    d.gammaFactor (x : ℂ) ≠ 0 := by
  intro h0
  have hnn : ∀ s : Multiset ℂ, ∀ r ∈ s.map (‖·‖), 0 ≤ r := fun s _ hr ↦ by
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp hr
    positivity
  have hR_nonneg : 0 ≤ (d.gammaR.map (‖·‖)).sum := Multiset.sum_nonneg (hnn _)
  have hC_nonneg : 0 ≤ (d.gammaC.map (‖·‖)).sum := Multiset.sum_nonneg (hnn _)
  rcases (d.gammaFactor_eq_zero_iff (x : ℂ)).mp h0 with ⟨μ, hμ, n, hn⟩ | ⟨ν, hν, n, hn⟩
  · have hre := congrArg Complex.re hn
    simp only [add_re, ofReal_re, neg_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im,
      mul_zero, sub_zero] at hre
    have hle : ‖μ‖ ≤ (d.gammaR.map (‖·‖)).sum :=
      Multiset.single_le_sum (hnn _) _ (Multiset.mem_map_of_mem _ hμ)
    have hμre : -‖μ‖ ≤ μ.re :=
      neg_le.mp (neg_re μ ▸ (Complex.re_le_norm (-μ)).trans_eq (norm_neg μ))
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · have hre := congrArg Complex.re hn
    simp only [add_re, ofReal_re, neg_re, natCast_re] at hre
    have hle : ‖ν‖ ≤ (d.gammaC.map (‖·‖)).sum :=
      Multiset.single_le_sum (hnn _) _ (Multiset.mem_map_of_mem _ hν)
    have hνre : -‖ν‖ ≤ ν.re :=
      neg_le.mp (neg_re ν ▸ (Complex.re_le_norm (-ν)).trans_eq (norm_neg ν))
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith

/-- If a card agrees with its Dirichlet series on `Re s > 1` and continues meromorphically to `ℂ`,
then its Dirichlet series either converges absolutely on `Re s > 1` or converges nowhere. -/
theorem HasDirichletAgreement.abscissaOfAbsConv_le_one_or_eq_top
    (hd : d.HasDirichletAgreement) (hm : d.HasMeromorphicContinuation) :
    LSeries.abscissaOfAbsConv d.coeff ≤ 1 ∨ LSeries.abscissaOfAbsConv d.coeff = ⊤ := by
  by_contra! h
  rcases h with ⟨hgt, hne_top⟩
  cases hσ : LSeries.abscissaOfAbsConv d.coeff with
  | bot => simp [hσ] at hgt
  | top => exact hne_top hσ
  | coe r =>
    have hr1 : 1 < r := by exact_mod_cast hσ ▸ hgt
    let z₀ : ℂ := ((1 + r) / 2 : ℝ)
    have hz₀_open : IsOpen {z : ℂ | 1 < z.re ∧ z.re < r} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hz₀_mem : z₀ ∈ {z : ℂ | 1 < z.re ∧ z.re < r} := by
      simp only [z₀, Set.mem_ofPred_eq, ofReal_re]
      constructor <;> linarith
    have hzero_nhds : d.completed =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hz₀_open.mem_nhds hz₀_mem] with z hz
      have hns : ¬LSeriesSummable d.coeff z := fun hsum ↦
        hz.2.not_ge (by exact_mod_cast hσ ▸ hsum.abscissaOfAbsConv_le)
      simp only [Pi.zero_apply, hd.completed_eq z hz.1,
        LSeries.eq_zero_of_not_LSeriesSummable d.coeff z hns, mul_zero]
    have hcomp_zero := congrFun (hm.completed_eq_zero_of_eventuallyEq_zero hzero_nhds)
    let B : ℝ := max 1 ((d.gammaR.map (‖·‖)).sum + (d.gammaC.map (‖·‖)).sum)
    have hL_ne : ∀ᶠ x : ℝ in atTop, LSeries d.coeff x ≠ 0 :=
      (LSeries.tendsto_atTop hne_top.lt_top).eventually_ne (hd.coeff_one.symm ▸ one_ne_zero)
    obtain ⟨x, hxB, hxL⟩ := ((eventually_gt_atTop B).and hL_ne).exists
    have hx1 : 1 < ((x : ℂ)).re := by
      simpa only [ofReal_re] using (le_max_left _ _).trans_lt hxB
    have hne : d.completed (x : ℂ) ≠ 0 := by
      rw [hd.completed_eq (x : ℂ) hx1]
      exact mul_ne_zero (mul_ne_zero
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero)))
        (gammaFactor_ne_zero_of_norm_sum_lt d ((le_max_right _ _).trans_lt hxB))) hxL
    exact hne (hcomp_zero (x : ℂ))

/-- Under Dirichlet agreement and meromorphic continuation, `LSeries d.coeff` is analytic on the
half-plane `Re s > 1`. -/
theorem HasDirichletAgreement.analyticOnNhd_LSeries
    (hd : d.HasDirichletAgreement) (hm : d.HasMeromorphicContinuation) :
    AnalyticOnNhd ℂ (LSeries d.coeff) {s | 1 < s.re} := by
  rcases hd.abscissaOfAbsConv_le_one_or_eq_top hm with hle | htop
  · exact (LSeries_analyticOnNhd d.coeff).mono fun s hs ↦ hle.trans_lt (by exact_mod_cast hs)
  · rw [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top htop]
    exact analyticOnNhd_const

/-- Under Dirichlet agreement and meromorphic continuation, `continuedL` agrees with
`LSeries d.coeff` on the entire half-plane `Re s > 1`, including at any poles of `γ` there. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries
    (hd : d.HasDirichletAgreement) (hm : d.HasMeromorphicContinuation) {s : ℂ} (hs : 1 < s.re) :
    d.continuedL s = LSeries d.coeff s := by
  have ha : AnalyticAt ℂ (LSeries d.coeff) s := hd.analyticOnNhd_LSeries hm s hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hγ : ∀ᶠ z in 𝓝[≠] s, d.gammaFactor z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (d.meromorphic_gammaFactor s)).mp
      (d.meromorphicOrderAt_gammaFactor_ne_top s)
  have heq : d.continuedL =ᶠ[𝓝[≠] s] LSeries d.coeff := by
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hs), hγ] with z hz1 hzγ
    exact hd.continuedL_eq_LSeries_of_gammaFactor_ne_zero hz1 hzγ
  have hord : 0 ≤ meromorphicOrderAt d.continuedL s := by
    rw [meromorphicOrderAt_congr heq]
    exact ha.meromorphicOrderAt_nonneg
  have hc : AnalyticAt ℂ d.continuedL s :=
    hm.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt.mp hord
  exact ((hc.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ha.continuousAt).mp
    heq).eq_of_nhds

/-- Converting `continuedL` to meromorphic normal form on `ℂ` recovers the canonical half-plane
continuation `meromorphicContinuation 1 (LSeries d.coeff)`. -/
theorem HasDirichletAgreement.toMeromorphicNFOn_continuedL_eq_meromorphicContinuation
    (hd : d.HasDirichletAgreement) (hm : d.HasMeromorphicContinuation) :
    toMeromorphicNFOn d.continuedL univ = meromorphicContinuation 1 (LSeries d.coeff) := by
  symm
  refine meromorphicContinuation_eq_toMeromorphicNFOn hm.meromorphic_continuedL ?_
    fun s hs ↦ hd.continuedL_eq_LSeries hm hs
  intro s hs
  have hEq : EqOn d.continuedL (LSeries d.coeff) {z | 1 < z.re} :=
    fun z hz ↦ hd.continuedL_eq_LSeries hm hz
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hd.analyticOnNhd_LSeries hm s hs).congr ?_
  filter_upwards [hopen.mem_nhds hs] with z hz using (hEq hz).symm

/-! ### Functional equation -/

/-- **The functional equation for `continuedL` as germs.** At every point `s`,
`γ(z) * continuedL d z = ε * N ^ (1 / 2 - z) * γ_dual(1 - z) * continuedL d.dual (1 - z)` holds on
a punctured neighbourhood of `s`. -/
theorem HasFunctionalEquation.gammaFactor_mul_continuedL_eventuallyEq
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    (fun z ↦ d.gammaFactor z * d.continuedL z) =ᶠ[𝓝[≠] s]
      fun z ↦ d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - z) *
        d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z) := by
  have hsub : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) :=
    (continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin fun z hz ↦
      sub_right_injective.ne hz
  filter_upwards [d.completed_eventuallyEq_mul_continuedL s, hfe.eventuallyEq s,
    hsub.eventually (d.dual.completed_eventuallyEq_mul_continuedL (1 - s))] with z h1 h2 h3
  rw [dual_conductor] at h3
  have hpow : ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * ((d.conductor : ℕ) : ℂ) ^ (z / 2) = 1 := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr d.conductor.ne_zero), neg_div, neg_add_cancel,
      cpow_zero]
  have hpow' : ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * ((d.conductor : ℕ) : ℂ) ^ ((1 - z) / 2) =
      ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - z) := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr d.conductor.ne_zero)]
    congr 1
    ring
  have hmul := congrArg (((d.conductor : ℕ) : ℂ) ^ (-z / 2) * ·)
    (h1.symm.trans (h2.trans (congrArg (d.rootNumber * ·) h3)))
  calc
    d.gammaFactor z * d.continuedL z =
        (((d.conductor : ℕ) : ℂ) ^ (-z / 2) * ((d.conductor : ℕ) : ℂ) ^ (z / 2)) *
          (d.gammaFactor z * d.continuedL z) := by rw [hpow, one_mul]
    _ = ((d.conductor : ℕ) : ℂ) ^ (-z / 2) *
          (((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z) := by ring
    _ = ((d.conductor : ℕ) : ℂ) ^ (-z / 2) *
          (d.rootNumber * (((d.conductor : ℕ) : ℂ) ^ ((1 - z) / 2) *
            d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z))) := hmul
    _ = d.rootNumber * (((d.conductor : ℕ) : ℂ) ^ (-z / 2) *
          ((d.conductor : ℕ) : ℂ) ^ ((1 - z) / 2)) *
          d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z) := by ring
    _ = d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - z) *
          d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z) := by rw [hpow']

/-- **Pointwise functional equation for `continuedL` in solved form.** Wherever `s` is not a
recorded pole of `Λ` and `γ_dual(1 - s) ≠ 0`, `continuedL d s` equals the dual expression with
`invGammaFactor d s`; this holds at trivial zeros (`γ(s) = 0`) as well, where both sides vanish. -/
theorem HasFunctionalEquation.continuedL_eq_mul_dual
    (hfe : d.HasFunctionalEquation) {s : ℂ} (hp : d.polarOrder s = 0)
    (hγ' : d.dual.gammaFactor (1 - s) ≠ 0) :
    d.continuedL s =
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
        d.invGammaFactor s * d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by
  have hp' : d.polarOrder (1 - conj s) = 0 := by rw [hfe.polarOrder_one_sub_conj, hp]
  have hpow' : ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ ((1 - s) / 2) =
      ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr d.conductor.ne_zero)]
    congr 1
    ring
  rw [d.continuedL_of_polarOrder_eq_zero hp, hfe.completed_eq s hp hp',
    d.dual.completed_eq_mul_continuedL hγ', dual_conductor]
  calc
    ((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
        (d.rootNumber * (((d.conductor : ℕ) : ℂ) ^ ((1 - s) / 2) *
          d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s))) * d.invGammaFactor s =
      d.rootNumber * (((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
        ((d.conductor : ℕ) : ℂ) ^ ((1 - s) / 2)) *
        d.invGammaFactor s * d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by ring
    _ = d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
        d.invGammaFactor s * d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by
      rw [hpow']

/-- **Symmetric pointwise functional equation for `continuedL`.** Holds when `s` is not a recorded
pole of `Λ` (which by polar symmetry also excludes `1 - conj s`) and both `γ(s)` and
`γ_dual(1 - s)` are nonzero. -/
theorem HasFunctionalEquation.gammaFactor_mul_continuedL
    (hfe : d.HasFunctionalEquation) {s : ℂ} (hp : d.polarOrder s = 0)
    (hγ : d.gammaFactor s ≠ 0) (hγ' : d.dual.gammaFactor (1 - s) ≠ 0) :
    d.gammaFactor s * d.continuedL s =
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
        d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by
  rw [hfe.continuedL_eq_mul_dual hp hγ']
  calc
    d.gammaFactor s * (d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
        d.invGammaFactor s * d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s)) =
      (d.invGammaFactor s * d.gammaFactor s) *
        (d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
          d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s)) := by ring
    _ = d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
        d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by
      rw [d.invGammaFactor_mul_gammaFactor hγ, one_mul]

end Predicates

section Counterexample

open Classical in
private noncomputable def polarCounterexampleData : AnalyticLFunctionData where
  coeff := 0
  conductor := 1
  gammaR := 0
  gammaC := 0
  rootNumber := 1
  completed s := if s = 2 then 1 else if s = -1 then 0 else ((s - 2) * (s + 1))⁻¹
  polarOrder := Finsupp.single 2 1 + Finsupp.single (-1) 1

open Classical in
private theorem polarCounterexampleData_polarOrder (s : ℂ) :
    polarCounterexampleData.polarOrder s =
      (if s = 2 then 1 else 0) + (if s = -1 then 1 else 0) := by
  simp [polarCounterexampleData, Finsupp.single_apply, eq_comm]

private theorem polarCounterexampleData_completed_eventuallyEq (s : ℂ) :
    polarCounterexampleData.completed =ᶠ[𝓝[≠] s] fun z ↦ ((z - 2) * (z + 1))⁻¹ := by
  have hfin : ({(2 : ℂ), -1} : Set ℂ).Finite := by simp
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite (x := s) univ_mem hfin.to_subtype] with z hz
  have hz2 : z ≠ 2 := fun h ↦ hz.2 (by simp [h])
  have hzm1 : z ≠ -1 := fun h ↦ hz.2 (by simp [h])
  simp [polarCounterexampleData, hz2, hzm1]

private theorem polarCounterexampleData_hasMeromorphicContinuation :
    polarCounterexampleData.HasMeromorphicContinuation where
  meromorphic z :=
    (((analyticAt_id.fun_sub analyticAt_const).fun_mul
      (analyticAt_id.fun_add analyticAt_const)).meromorphicAt.inv).congr
      (polarCounterexampleData_completed_eventuallyEq z).symm
  meromorphicOrderAt_eq p hp := by
    classical
    rw [meromorphicOrderAt_congr (polarCounterexampleData_completed_eventuallyEq p)]
    have ha1 : AnalyticAt ℂ (fun z : ℂ ↦ z - 2) p := analyticAt_id.fun_sub analyticAt_const
    have ha2 : AnalyticAt ℂ (fun z : ℂ ↦ z + 1) p := analyticAt_id.fun_add analyticAt_const
    rw [fun_meromorphicOrderAt_inv,
      fun_meromorphicOrderAt_mul ha1.meromorphicAt ha2.meromorphicAt,
      polarCounterexampleData_polarOrder]
    by_cases hp2 : p = 2
    · subst hp2
      have ho2 : meromorphicOrderAt (fun z : ℂ ↦ z + 1) 2 = 0 :=
        ha2.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by norm_num)
      rw [meromorphicOrderAt_id_sub_const, ho2]
      norm_num
    by_cases hpm1 : p = -1
    · subst hpm1
      have ho1 : meromorphicOrderAt (fun z : ℂ ↦ z - 2) (-1) = 0 :=
        ha1.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by norm_num)
      have hsub : (fun z : ℂ ↦ z + 1) = fun z : ℂ ↦ z - (-1) := by ext z; ring
      rw [ho1, hsub, meromorphicOrderAt_id_sub_const]
      norm_num
    exfalso
    apply hp
    rw [polarCounterexampleData_polarOrder]
    simp [hp2, hpm1]
  analyticAt p hp := by
    classical
    rw [polarCounterexampleData_polarOrder] at hp
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp
    have hpm1 : p ≠ -1 := by rintro rfl; norm_num at hp
    have hp1 : p + 1 ≠ 0 := fun h ↦ hpm1 (by linear_combination h)
    have hga : AnalyticAt ℂ (fun z : ℂ ↦ ((z - 2) * (z + 1))⁻¹) p :=
      ((analyticAt_id.fun_sub analyticAt_const).fun_mul
        (analyticAt_id.fun_add analyticAt_const)).inv
        (mul_ne_zero (sub_ne_zero.mpr hp2) hp1)
    refine hga.congr ?_
    have hfin : ({(2 : ℂ), -1} : Set ℂ).Finite := by simp
    filter_upwards [hfin.isClosed.isOpen_compl.mem_nhds (by simp [hp2, hpm1])] with z hz
    have hz2 : z ≠ 2 := fun h ↦ hz (by simp [h])
    have hzm1 : z ≠ -1 := fun h ↦ hz (by simp [h])
    simp [polarCounterexampleData, hz2, hzm1]

private theorem polarCounterexampleData_hasFunctionalEquation :
    polarCounterexampleData.HasFunctionalEquation where
  norm_rootNumber := by simp [polarCounterexampleData]
  polarOrder_one_sub_conj s := by
    classical
    have e2 : 1 - conj s = (2 : ℂ) ↔ s = (-1 : ℂ) := by
      constructor <;> intro h
      · apply (starRingEnd ℂ).injective
        rw [map_neg, map_one]
        linear_combination -h
      · subst h
        rw [map_neg, map_one]
        norm_num
    have em1 : 1 - conj s = (-1 : ℂ) ↔ s = (2 : ℂ) := by
      constructor <;> intro h
      · apply (starRingEnd ℂ).injective
        rw [map_ofNat]
        linear_combination -h
      · subst h
        rw [map_ofNat]
        norm_num
    rw [polarCounterexampleData_polarOrder, polarCounterexampleData_polarOrder, add_comm]
    simp only [e2, em1]
  completed_eq s hs hs' := by
    classical
    rw [polarCounterexampleData_polarOrder] at hs hs'
    have hs2 : s ≠ 2 := by rintro rfl; norm_num at hs
    have hsm1 : s ≠ -1 := by rintro rfl; norm_num at hs
    have hcs2 : 1 - conj s ≠ 2 := fun h ↦ by rw [h] at hs'; norm_num at hs'
    have hcsm1 : 1 - conj s ≠ -1 := fun h ↦ by rw [h] at hs'; norm_num at hs'
    rw [polarCounterexampleData.dual_completed_apply, map_sub, map_one]
    simp only [polarCounterexampleData, one_mul, hs2, hsm1, hcs2, hcsm1, ↓reduceIte,
      map_inv₀, map_mul, map_sub, map_add, map_one, map_ofNat, Complex.conj_conj]
    congr 1
    ring

-- Polar-exclusion counterexample: a degree-0, conductor-1, root-number-1 record with simple poles
-- at `2` and `-1` (off `{0, 1}`) and assigned pole values `F(2) = 1`, `F(-1) = 0` satisfies both
-- `HasMeromorphicContinuation` and `HasFunctionalEquation` and has regular gamma factors
-- everywhere, yet fails the pointwise functional equation at `s = 2` (`1 ≠ 0`).
example : ∃ d : AnalyticLFunctionData,
    d.degree = 0 ∧ d.conductor = 1 ∧ d.rootNumber = 1 ∧
    d.HasMeromorphicContinuation ∧ d.HasFunctionalEquation ∧
    d.polarOrder 0 = 0 ∧ d.polarOrder 1 = 0 ∧
    d.gammaFactor 2 ≠ 0 ∧ d.dual.gammaFactor (1 - 2) ≠ 0 ∧
    d.gammaFactor 2 * d.continuedL 2 ≠
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - 2) *
        d.dual.gammaFactor (1 - 2) * d.dual.continuedL (1 - 2) := by
  classical
  have hdeg : polarCounterexampleData.degree = 0 := by simp [polarCounterexampleData, degree_def]
  have hγ (s : ℂ) : polarCounterexampleData.gammaFactor s = 1 := by
    simp [polarCounterexampleData, gammaFactor_def]
  have hγ' (s : ℂ) : polarCounterexampleData.dual.gammaFactor s = 1 := by
    simp [polarCounterexampleData, gammaFactor_def]
  refine ⟨polarCounterexampleData, hdeg, rfl, rfl,
    polarCounterexampleData_hasMeromorphicContinuation,
    polarCounterexampleData_hasFunctionalEquation,
    by rw [polarCounterexampleData_polarOrder]; norm_num,
    by rw [polarCounterexampleData_polarOrder]; norm_num,
    by rw [hγ]; exact one_ne_zero, by rw [hγ']; exact one_ne_zero, ?_⟩
  rw [polarCounterexampleData.continuedL_of_gammaFactor_ne_zero (by rw [hγ]; exact one_ne_zero),
    (by norm_num : (1 : ℂ) - 2 = -1), polarCounterexampleData.dual_continuedL_apply, map_neg,
    map_one,
    polarCounterexampleData.continuedL_of_gammaFactor_ne_zero (by rw [hγ]; exact one_ne_zero),
    hγ, hγ']
  norm_num [polarCounterexampleData]

end Counterexample

end TauCeti.LFunctions.AnalyticLFunctionData
