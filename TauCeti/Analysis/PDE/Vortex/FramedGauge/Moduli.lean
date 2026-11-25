/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Divisor
public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.Data.Fintype.Order
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.PDE.Vortex.Coupling
import TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay

/-!
# Smooth framed vortices in the affine Sobolev field spaces

A smooth framed degree-`m` plane vortex is a smooth field `x` on `ℂ` solving the vortex
equations whose section satisfies `α(z) (z / |z|)⁻ᵐ → 1` at infinity
(`TauCeti.Vortex.framedVortexSubMulAction 1 m`). Its framed gauge orbits are classified by their
zero divisors (`TauCeti.Vortex.framedVortexModuliEquiv`). The Fredholm and slice theory of the
vortex equations is set up on the affine Sobolev space `A_m^k = x_m + H^k`
(`TauCeti.Vortex.framedFieldSpace`) with its gauge group `G_(k+1)`. This file compares the two
models: every smooth framed vortex orbit has a representative lying in `A_m^k` for every `k`.

A smooth framed vortex need not itself lie in `A_m^k`: the phase of its section may approach the
winding phase `(z / |z|)^m` only like `1 / |z|`, which is not square integrable on the plane.
A smooth framed gauge normalizes the phase, so that outside a compact set the section is `|α|`
times the winding phase (`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). In the
winding end trivialization such a vortex tends to the vacuum together with all its derivatives,
at every exponential rate `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField`). Outside the cutoff
disc, `x - x_ref` is the rotation of the section part of that difference by the winding phase,
which equals the reference section `x_ref` uses there and has bounded derivatives, so the
derivatives of `x - x_ref` there are bounded by those of the end trivialization
(`exists_norm_iteratedFDeriv_sub_referenceField_le_mul`). Hence every derivative of
`x - x_ref` decays exponentially (`isBigO_iteratedFDeriv_sub_referenceField`). A
smooth field with this decay lies in every `A_m^k`
(`TauCeti.Vortex.mem_framedFieldSpace_of_isBigO_iteratedFDeriv_sub_referenceField`).

With Taubes's existence theorem (`TauCeti.Vortex.framedVortexDivisor_surjective`) this shows that
every effective divisor of degree `m` is the divisor of a `C²` vortex of `A_m^k`
(`sobolevVortexDivisor_surjective`). For `k ≥ 4`, where `G_(k+1)` preserves the `C²` vortices of
`A_m^k`, the divisor therefore identifies the Sobolev moduli of framed vortices with `Sym ℂ m`
(`sobolevVortexModuliEquiv`), the Sobolev counterpart of `TauCeti.Vortex.framedVortexModuliEquiv`.
Conversely, a smooth framed gauge relating two fields of `A_m^k` lies in `G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`).

## Main results

All in the namespace `TauCeti.Vortex`:

* `exists_norm_iteratedFDeriv_sub_referenceField_le_mul`: outside the cutoff disc, the
  derivatives of `x - x_ref` of order `n` are bounded by a constant, depending only on `n`, times
  a bound for the derivatives of order at most `n` of the end trivialization of `x`.
* `isBigO_iteratedFDeriv_sub_referenceField`: for a smooth vortex normalized at its end, every
  derivative of `x - x_ref` is `O(exp (-c |z|))` for every `c < 1 / 2`.
* `gaugeTransform_mem_framedFieldSpace_of_eventually_sectionValue_eq`: a smooth framed vortex
  whose section is `|α|` times the winding phase near infinity lies in `A_m^s` for every `s`, with
  this decay.
* `exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex has a smooth
  framed gauge representative lying in `A_m^s` for every `s`, with this decay.
* `exists_contDiff_sobolevVortexDivisor_eq`: every point of `Sym ℂ m` is the divisor of a smooth
  vortex of `A_m^k` lying in every `A_m^s`, with this decay.
* `sobolevVortexDivisor_surjective`: every point of `Sym ℂ m` is the divisor of a `C²` vortex of
  `A_m^k`.
* `sobolevVortexModuliEquiv`: for `k ≥ 4`, the Sobolev moduli of framed vortices are `Sym ℂ m`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology Asymptotics
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Exponential decay of all derivatives of `x - x_ref` -/

/-- **`x - x_ref` from the end trivialization, pointwise.** For every order `n` there is a
constant `C ≥ 0` with the following property. Let `z` be a point outside the cutoff disc of the
reference field, and let `x` be a field whose end trivialization `u⁻¹ · x - (0, 1)`, `u` the
winding phase, is `C^n` at `z`. If the derivatives of order at most `n` of the end trivialization
at `z` have norm at most `E`, then the derivative of order `n` of `x - x_ref` at `z` has norm at
most `C E`. -/
theorem exists_norm_iteratedFDeriv_sub_referenceField_le_mul (f : ContDiffBump (0 : ℝ))
    (m n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ), f.rOut < ‖z‖ ^ 2 →
      ContDiffAt ℝ n (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w) z →
      ∀ E : ℝ, (∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w -
        vacuumField w) z‖ ≤ E) →
      ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ ≤ C * E := by
  -- One bound for the derivatives of order at most `n` of the reference section.
  choose Cs hCs using fun i : Fin (n + 1) ↦ exists_norm_iteratedFDeriv_referenceSection_le f m i
  obtain ⟨M, hM⟩ := Finite.exists_le Cs
  have hsM : ∀ i ≤ n, ∀ w, ‖iteratedFDeriv ℝ i (referenceSection f m) w‖ ≤ M := fun i hi w ↦
    (hCs ⟨i, Nat.lt_succ_iff.2 hi⟩ w).trans (hM _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hsM 0 (Nat.zero_le n) 0)
  -- The linear maps `P` (connection coordinates), `Q` (section coordinates as a complex number)
  -- and `J` (a complex number as section coordinates) of `sub_referenceField_apply_eq`.
  set P : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1) +
      (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 1 1)
  set Q : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℂ :=
    (EuclideanSpace.proj 2).smulRight (1 : ℂ) + (EuclideanSpace.proj 3).smulRight I
  set J : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    reCLM.smulRight (EuclideanSpace.single 2 1) + imCLM.smulRight (EuclideanSpace.single 3 1)
  set B := ContinuousLinearMap.mul ℝ ℂ
  refine ⟨‖P‖ + ‖J‖ * (‖B‖ * 2 ^ n * M * ‖Q‖), by positivity, fun x z hz hG E hE ↦ ?_⟩
  set G : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w -
    vacuumField w
  have hs : ContDiffAt ℝ n (referenceSection f m) z :=
    (contDiff_referenceSection f m).contDiffAt.of_le (by exact_mod_cast le_top)
  have hQG : ContDiffAt ℝ n (fun w ↦ Q (G w)) z := Q.contDiff.contDiffAt.comp z hG
  -- Near `z`, `x - x_ref = P G + J (s Q G)`.
  have heq : (x - referenceField f m) =ᶠ[𝓝 z]
      fun w ↦ P (G w) + J (B (referenceSection f m w) (Q (G w))) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.pow 2)).mem_nhds hz] with w hw
    rw [sub_referenceField_apply_eq f hw.le (g := G w) rfl]
    generalize referenceSection f m w = σ
    generalize G w = v
    ext i
    fin_cases i <;> simp [P, Q, J, B, add_comm]
  -- The Leibniz rule for the product of the reference section with the section part.
  have hprod : ‖iteratedFDeriv ℝ n (fun w ↦ B (referenceSection f m w) (Q (G w))) z‖ ≤
      ‖B‖ * 2 ^ n * M * (‖Q‖ * E) :=
    B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le hs hQG (fun i hi ↦ hsM i hi z) fun i hi ↦
        (Q.norm_iteratedFDeriv_comp_left hG (by exact_mod_cast hi)).trans
          (mul_le_mul_of_nonneg_left (hE i hi) (norm_nonneg _))
  have hPG : ContDiffAt ℝ n (fun w ↦ P (G w)) z := P.contDiff.contDiffAt.comp z hG
  have hBQG : ContDiffAt ℝ n (fun w ↦ B (referenceSection f m w) (Q (G w))) z :=
    (B.contDiff.contDiffAt.comp z hs).clm_apply hQG
  have hJ : ContDiffAt ℝ n (fun w ↦ J (B (referenceSection f m w) (Q (G w)))) z :=
    J.contDiff.contDiffAt.comp z hBQG
  rw [(heq.iteratedFDeriv ℝ n).self_of_nhds, fun_iteratedFDeriv_add_apply hPG hJ]
  have hP := (P.norm_iteratedFDeriv_comp_left hG le_rfl).trans
    (mul_le_mul_of_nonneg_left (hE n le_rfl) (norm_nonneg _))
  have hJ' := (J.norm_iteratedFDeriv_comp_left
    (f := fun w ↦ B (referenceSection f m w) (Q (G w))) hBQG le_rfl).trans
    (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
  calc _ ≤ ‖P‖ * E + ‖J‖ * (‖B‖ * 2 ^ n * M * (‖Q‖ * E)) :=
        (norm_add_le _ _).trans (add_le_add hP hJ')
    _ = _ := by ring

/-- **Exponential decay of all derivatives of `x - x_ref`.** Let `x` be a plane vortex with smooth
section and `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then for every order `n` and every rate `c < 1 / 2`, the `n`-th derivative
of `x - x_ref` is `O(exp (-c |z|))` at infinity. This extends the first-order estimate
`TauCeti.Vortex.exists_eventually_norm_fderiv_sub_referenceField_le_mul_exp` to every order. -/
theorem isBigO_iteratedFDeriv_sub_referenceField (f : ContDiffBump (0 : ℝ))
    (hp : ContDiff ℝ ∞ (fun z ↦ x z 2)) (hq : ContDiff ℝ ∞ (fun z ↦ x z 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (x - referenceField f m) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  -- A smooth decaying `g` agreeing with the end trivialization minus the vacuum near infinity.
  obtain ⟨g, hg, hgdec, hgx⟩ :=
    exists_contDiff_isBigO_eventuallyEq_gaugeTransform_inv_sub_vacuumField hp hq hsol hlim hphase
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_sub_referenceField_le_mul f m n
  -- One eventual bound `K exp (-c |z|)` for the derivatives of `g` of order at most `n`.
  choose K hK using fun i : Fin (n + 1) ↦ (hgdec c hc i).bound
  obtain ⟨K₁, hK₁⟩ := Finite.exists_le K
  have hout : ∀ᶠ z in cocompact ℂ, f.rOut < ‖z‖ ^ 2 :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).eventually_gt_atTop f.rOut
  refine IsBigO.of_bound (C * K₁) ?_
  filter_upwards [hgx, hout, eventually_all.2 hK] with z hz hzr hKz
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, mul_assoc]
  refine hC x z hzr ((hg.contDiffAt.congr_of_eventuallyEq hz).of_le (by exact_mod_cast le_top))
    _ fun i hi ↦ ?_
  rw [(hz.iteratedFDeriv ℝ i).eq_of_nhds]
  refine (hKz ⟨i, Nat.lt_succ_iff.2 hi⟩).trans ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (hK₁ _) (Real.exp_pos _).le

/-! ### Smooth framed vortices have representatives in `A_m^s` -/

/-- **A smooth framed vortex normalized at its end lies in every `A_m^s`.** Let `x` be a smooth
framed degree-`m` vortex and `u` a smooth framed gauge such that the section of `u · x` is `|α|`
times the winding phase `(z / |z|)^m` outside a compact set. Then `u · x` lies in the affine
Sobolev space `A_m^s` for every real `s`, and every derivative of `u · x - x_ref` is
`O(exp (-c |z|))` at infinity for every rate `c < 1 / 2`. -/
theorem gaugeTransform_mem_framedFieldSpace_of_eventually_sectionValue_eq
    (f : ContDiffBump (0 : ℝ)) {u : ℂ → Circle} (hu : u ∈ framedGaugeGroup)
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue (gaugeTransform u x) z =
      ‖sectionValue (gaugeTransform u x) z‖ * windingPhase m z) :
    (∀ s : ℝ, gaugeTransform u x ∈ framedFieldSpace f m s) ∧
      ∀ c < 1 / 2, ∀ n : ℕ, iteratedFDeriv ℝ n (gaugeTransform u x - referenceField f m)
        =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨-, hu1⟩ := (mem_framedGaugeGroup _).1 hu
  have hy : ContDiff ℝ ∞ (gaugeTransform u x) := by
    simpa using contDiff_framedGaugeGroup_smul ⟨u, hu⟩ hx
  have hsol' (z : ℂ) : equation (gaugeTransform u x) z = 0 := by
    simpa using (equation_framedGaugeGroup_smul_eq_zero_iff ⟨u, hu⟩
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow
    (tendsto_sectionValue_gaugeTransform hu1 hframe)
  have hdec := fun c (hc : c < 1 / 2) n ↦
    isBigO_iteratedFDeriv_sub_referenceField f (contDiff_euclidean.1 hy 2)
      (contDiff_euclidean.1 hy 3) hsol' hlim hphase hc n
  exact ⟨mem_framedFieldSpace_of_isBigO_iteratedFDeriv_sub_referenceField hy (c := 1 / 4)
    (by norm_num) (hdec (1 / 4) (by norm_num)), hdec⟩

/-- **Every smooth framed vortex orbit meets every `A_m^s`.** A smooth framed degree-`m` vortex
`x` is carried by a smooth framed gauge `u` to a field `u · x` lying in the affine Sobolev space
`A_m^s` for every real `s`, such that every derivative of `u · x - x_ref` is `O(exp (-c |z|))`
at infinity for every rate `c < 1 / 2`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, (∀ s : ℝ, u • x ∈ framedFieldSpace f m s) ∧
      ∀ c < 1 / 2, ∀ n : ℕ, iteratedFDeriv ℝ n (u • x - referenceField f m) =O[cocompact ℂ]
        fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  exact ⟨u, gaugeTransform_mem_framedFieldSpace_of_eventually_sectionValue_eq f u.property hx hsol
    hframe hu⟩

/-! ### The Sobolev moduli of framed vortices -/

variable {k : ℕ} [Fact (1 < k)]

/-- **Smooth existence on the Sobolev scale.** For `k ≥ 2`, every effective divisor of degree `m`,
repeated points included, is the divisor of a smooth vortex of `A_m^k` lying in the affine Sobolev
space `A_m^s` for every real `s`, such that every derivative of its difference with the reference
field is `O(exp (-c |z|))` at infinity for every rate `c < 1 / 2`. -/
theorem exists_contDiff_sobolevVortexDivisor_eq (D : Sym ℂ m) :
    ∃ x : sobolevVortices f m k, sobolevVortexDivisor x = D ∧
      ContDiff ℝ ∞ (x : ℂ → EuclideanSpace ℝ (Fin 4)) ∧
      (∀ s : ℝ, (x : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedFieldSpace f m s) ∧
      ∀ c < 1 / 2, ∀ n : ℕ,
        iteratedFDeriv ℝ n ((x : ℂ → EuclideanSpace ℝ (Fin 4)) - referenceField f m)
          =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨x, hx⟩ := framedVortexDivisor_surjective one_pos m D
  obtain ⟨hxc, hxsol, hxfr⟩ := mem_framedVortexSubMulAction.1 x.property
  simp only [coupledEquation_one] at hxsol
  obtain ⟨u, hu, hdec⟩ := exists_framedGaugeGroup_smul_mem_framedFieldSpace f hxc hxsol hxfr
  obtain ⟨hyc, hysol, -⟩ := mem_framedVortexSubMulAction.1 (u • x).property
  rw [SubMulAction.val_smul] at hyc hysol
  refine ⟨⟨⟨u • (x : ℂ → EuclideanSpace ℝ (Fin 4)), hu k⟩,
    mem_sobolevVortices.2 ⟨hyc.of_le (by simp), by simpa using hysol⟩⟩, ?_, hyc, hu, hdec⟩
  rw [sobolevVortexDivisor_eq_framedVortexDivisor _ (u • x) (SubMulAction.val_smul u x).symm,
    framedVortexDivisor_smul, hx]

/-- **Existence on the Sobolev scale.** For `k ≥ 2`, every effective divisor of degree `m`,
repeated points included, is the divisor of a `C²` vortex of `A_m^k`. -/
theorem sobolevVortexDivisor_surjective :
    Function.Surjective (sobolevVortexDivisor (f := f) (m := m) (k := k)) := fun D ↦
  (exists_contDiff_sobolevVortexDivisor_eq D).imp fun _ hx ↦ hx.left

/-- For `k ≥ 4`, every point of `Sym ℂ m` is the divisor of a `G_(k+1)`-orbit of `C²` vortices of
`A_m^k`. -/
theorem sobolevVortexModuliDivisor_surjective {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    Function.Surjective (sobolevVortexModuliDivisor (f := f) (m := m) (hs := hs) hk) := fun D ↦
  (sobolevVortexDivisor_surjective D).elim fun x hx ↦
    ⟨Quotient.mk'' ⟨x.val, mem_sobolevVortexSubMulAction.2 x.property⟩, by
      rw [sobolevVortexModuliDivisor_mk]
      exact hx⟩

/-- **The Sobolev moduli of framed vortices are `Sym ℂ m`** (Taubes). For `k ≥ 4`, the divisor
identifies the orbits of `G_(k+1)` on the `C²` vortices of `A_m^k` with the effective divisors of
degree `m`. -/
def sobolevVortexModuliEquiv {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) ≃ Sym ℂ m :=
  Equiv.ofBijective (sobolevVortexModuliDivisor hk)
    ⟨sobolevVortexModuliDivisor_injective hk, sobolevVortexModuliDivisor_surjective hk⟩

/-- The equivalence sends an orbit to the divisor of its vortices. -/
@[simp]
theorem sobolevVortexModuliEquiv_apply {hs : 1 < (k : ℝ) + 1} (hk : 3 < k)
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)) :
    sobolevVortexModuliEquiv hk q = sobolevVortexModuliDivisor hk q :=
  (rfl)

end TauCeti.Vortex
