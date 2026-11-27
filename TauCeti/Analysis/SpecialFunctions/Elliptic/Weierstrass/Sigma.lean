/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Weierstrass.Zeta
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Group.Int.Even
import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct

/-!
# The Weierstrass `σ` function

For a pair of periods `L` with lattice `Λ`, the Weierstrass `σ` function is the canonical product
`σ(z) = z ∏_{l ∈ Λ, l ≠ 0} (1 - z / l) exp(z / l + z² / (2 l²))`
(`PeriodPair.weierstrassSigma`), whose factors are the genus-two Weierstrass elementary factors
`Complex.weierstrassFactor 2 (z / l)`. Since `‖E₂(w) - 1‖ ≤ ‖w‖³` on the unit disc and
`∑_{l ≠ 0} ‖l‖⁻³` converges, the product converges locally uniformly on `ℂ`, so `σ` is entire.
It is odd, `σ'(0) = 1`, and its zeros are the points of `Λ`, all simple.

The logarithmic derivative of `σ` is the Weierstrass `ζ` function
(`PeriodPair.logDeriv_weierstrassSigma`), so `-(σ' / σ)' = ℘` away from `Λ`. The quasi-periodicity
`ζ(z + l) = ζ(z) + η(l)` of `ζ` then integrates to the quasi-periodicity of `σ`: for `l ∈ Λ`,

  `σ(z + l) = ± exp(η(l) (z + l / 2)) σ(z)`,

with the sign `-1` exactly when `l / 2 ∉ Λ`. In terms of the periods, for `l = a ω₁ + b ω₂` the
sign is `(-1)^(a + b + a b)`. These are the functional equations behind the classical functions
`σ(N z - t) / σ(N z)` with divisor `[N]^*(t) - [N]^*(0)`, which compute the Weil pairing of a
complex torus.

## Main definitions

* `PeriodPair.weierstrassSigma`: the Weierstrass `σ` function of `L`.

## Main results

* `PeriodPair.hasProdLocallyUniformlyOn_weierstrassFactor_two_div`: the canonical product
  converges locally uniformly on `ℂ`.
* `PeriodPair.differentiable_weierstrassSigma`: `σ` is entire.
* `PeriodPair.weierstrassSigma_eq_zero_iff`: `σ(z) = 0` exactly when `z ∈ Λ`.
* `PeriodPair.analyticOrderAt_weierstrassSigma_coe`: these zeros are simple.
* `PeriodPair.weierstrassSigma_neg`, `PeriodPair.hasDerivAt_weierstrassSigma_zero`: `σ` is odd
  and `σ'(0) = 1`.
* `PeriodPair.logDeriv_weierstrassSigma`, `PeriodPair.hasDerivAt_weierstrassSigma`: `σ' / σ = ζ`
  away from `Λ`.
* `PeriodPair.weierstrassSigma_add_coe_of_div_two_notMem`,
  `PeriodPair.weierstrassSigma_add_coe_of_div_two_mem`, `PeriodPair.weierstrassSigma_add_coe`:
  the quasi-periodicity of `σ`.
* `PeriodPair.weierstrassSigma_eq_of_lattice_eq`: `σ` depends only on the lattice, not on the
  chosen basis.

## References

* *NIST Digital Library of Mathematical Functions*, §23.2, (23.2.6)–(23.2.7) and (23.2.17).
* M. Abramowitz and I. A. Stegun, *Handbook of mathematical functions*, Chapter 18.
-/

public section

noncomputable section

open Complex Filter
open scoped Topology PeriodPair

namespace PeriodPair

variable (L : PeriodPair)

/-- The **Weierstrass `σ` function** of the lattice `Λ` of `L`,
`σ(z) = z ∏_{l ∈ Λ, l ≠ 0} (1 - z / l) exp(z / l + z² / (2 l²))`. With the convention
`z / 0 = 0`, the factor `l = 0` of the product below is `Complex.weierstrassFactor 2 0 = 1`. -/
def weierstrassSigma (z : ℂ) : ℂ := z * ∏' l : L.lattice, weierstrassFactor 2 (z / l)

/-- The defining canonical product of `σ`. -/
theorem weierstrassSigma_def (z : ℂ) :
    L.weierstrassSigma z = z * ∏' l : L.lattice, weierstrassFactor 2 (z / l) :=
  (rfl)

private theorem weierstrassSigma_eq :
    L.weierstrassSigma = fun z ↦ z * ∏' l : L.lattice, weierstrassFactor 2 (z / l) :=
  funext L.weierstrassSigma_def

/-- The genus-two canonical-product summability hypothesis for the lattice `Λ`. -/
private theorem summable_div_pow_three (R : ℝ) (_hR : 0 < R) :
    Summable fun l : L.lattice ↦ (R / ‖(l : ℂ)‖) ^ (2 + 1) := by
  simpa only [div_eq_mul_inv, mul_pow, Nat.reduceAdd, Submodule.norm_coe] using
    (ZLattice.summable_norm_pow_inv L.lattice 3 (by simp)).mul_left (R ^ 3)

/-- The canonical product of `σ` converges uniformly on every compact set. -/
theorem hasProdUniformlyOn_weierstrassFactor_two_div {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun (l : L.lattice) z ↦ weierstrassFactor 2 (z / l))
      (fun z ↦ ∏' l : L.lattice, weierstrassFactor 2 (z / l)) K :=
  hasProdUniformlyOn_weierstrassFactor_div L.summable_div_pow_three hK

/-- The canonical product of `σ` converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_two_div :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) z ↦ weierstrassFactor 2 (z / l))
      (fun z ↦ ∏' l : L.lattice, weierstrassFactor 2 (z / l)) Set.univ :=
  hasProdLocallyUniformlyOn_weierstrassFactor_div L.summable_div_pow_three

private theorem differentiable_tprod_weierstrassFactor_two_div :
    Differentiable ℂ fun z ↦ ∏' l : L.lattice, weierstrassFactor 2 (z / l) :=
  differentiable_tprod_weierstrassFactor_div L.summable_div_pow_three

/-- **`σ` is entire.** -/
@[fun_prop]
theorem differentiable_weierstrassSigma : Differentiable ℂ L.weierstrassSigma := by
  rw [weierstrassSigma_eq]
  exact differentiable_id.mul L.differentiable_tprod_weierstrassFactor_two_div

private theorem weierstrassFactor_two_div_ne_zero {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) :
    weierstrassFactor 2 (z / l) ≠ 0 := by
  rw [ne_eq, weierstrassFactor_div_eq_zero_iff]
  rintro ⟨_, hlz⟩
  exact hz (hlz ▸ l.property)

/-- **The zeros of `σ` are the lattice points.** -/
theorem weierstrassSigma_eq_zero_iff {z : ℂ} : L.weierstrassSigma z = 0 ↔ z ∈ L.lattice := by
  rw [weierstrassSigma_def, mul_eq_zero,
    Complex.tprod_weierstrassFactor_div_eq_zero_iff L.summable_div_pow_three]
  constructor
  · rintro (rfl | ⟨l, -, rfl⟩)
    · exact zero_mem _
    · exact l.property
  · intro hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨z, hz⟩, by simpa using hz0, rfl⟩

/-- `σ` does not vanish off the lattice. -/
theorem weierstrassSigma_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : L.weierstrassSigma z ≠ 0 :=
  fun h ↦ hz (L.weierstrassSigma_eq_zero_iff.mp h)

private theorem tprod_weierstrassFactor_two_div_ne_zero {z : ℂ} (hz : z ∉ L.lattice) :
    ∏' l : L.lattice, weierstrassFactor 2 (z / l) ≠ 0 := by
  have hs := L.weierstrassSigma_ne_zero hz
  rw [weierstrassSigma_def] at hs
  exact right_ne_zero_of_mul hs

@[simp]
theorem weierstrassSigma_coe (l : L.lattice) : L.weierstrassSigma l = 0 :=
  L.weierstrassSigma_eq_zero_iff.mpr l.property

@[simp]
theorem weierstrassSigma_zero : L.weierstrassSigma 0 = 0 :=
  L.weierstrassSigma_eq_zero_iff.mpr (zero_mem _)

/-- **`σ` is odd.** -/
@[simp]
theorem weierstrassSigma_neg (z : ℂ) : L.weierstrassSigma (-z) = -L.weierstrassSigma z := by
  have h : ∏' l : L.lattice, weierstrassFactor 2 (-z / l) =
      ∏' l : L.lattice, weierstrassFactor 2 (z / l) := by
    refine Eq.trans ?_ ((Equiv.neg L.lattice).tprod_eq fun l ↦ weierstrassFactor 2 (z / l))
    congr 1 with l
    simp [div_neg, neg_div]
  rw [weierstrassSigma_def, weierstrassSigma_def, h, neg_mul]

/-- **`σ'(0) = 1`.** -/
theorem hasDerivAt_weierstrassSigma_zero : HasDerivAt L.weierstrassSigma 1 0 := by
  have h := (hasDerivAt_id' (0 : ℂ)).fun_mul
    (L.differentiable_tprod_weierstrassFactor_two_div 0).hasDerivAt
  rw [weierstrassSigma_eq]
  convert h using 1
  simp [weierstrassFactor_zero]

/-- `σ'(0) = 1`, in terms of `deriv`. -/
theorem deriv_weierstrassSigma_zero : deriv L.weierstrassSigma 0 = 1 :=
  L.hasDerivAt_weierstrassSigma_zero.deriv

/-- The logarithmic derivative of the factor of `σ` at `l` is the term of the series of `ζ` at `l`,
except for `l = 0`, where the factor is constant and the term is `1 / z`. -/
private theorem logDeriv_weierstrassFactor_two_div [DecidableEq L.lattice] {z : ℂ}
    (hz : z ∉ L.lattice) (l : L.lattice) :
    logDeriv (fun w ↦ weierstrassFactor 2 (w / l)) z =
      Function.update (fun l : L.lattice ↦ 1 / (z - l) + 1 / l + z / l ^ 2) 0 0 l := by
  rcases eq_or_ne l 0 with rfl | hl
  · simp [weierstrassFactor_zero, logDeriv_const]
  rw [Function.update_of_ne hl]
  have hl' : (l : ℂ) ≠ 0 := by simpa using hl
  have hzl : z - l ≠ 0 := sub_ne_zero.mpr fun h ↦ hz (h ▸ l.property)
  have hlz : (l : ℂ) - z ≠ 0 := fun h ↦ hzl (by linear_combination -h)
  rw [← Function.comp_def (weierstrassFactor 2) (· / (l : ℂ)),
    logDeriv_comp (differentiable_weierstrassFactor 2 _) (by fun_prop), logDeriv_weierstrassFactor,
    deriv_div_const, deriv_id'']
  field_simp
  ring

/-- **The logarithmic derivative of `σ` is `ζ`** away from the lattice. -/
theorem logDeriv_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    logDeriv L.weierstrassSigma z = L.weierstrassZeta z := by
  classical
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ zero_mem _)
  have hsum : HasSum (fun l : L.lattice ↦ logDeriv (fun w ↦ weierstrassFactor 2 (w / l)) z)
      (L.weierstrassZeta z - 1 / z) := by
    rw [funext (L.logDeriv_weierstrassFactor_two_div hz)]
    convert (L.hasSum_weierstrassZeta z).update 0 0 using 1
    simp only [ZeroMemClass.coe_zero, sub_zero, div_zero, add_zero]
    ring
  have hP := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    (L.weierstrassFactor_two_div_ne_zero hz)
    (fun l ↦ (by fun_prop : Differentiable ℂ _).differentiableOn) hsum.summable
    L.hasProdLocallyUniformlyOn_weierstrassFactor_two_div.multipliableLocallyUniformlyOn
    (L.tprod_weierstrassFactor_two_div_ne_zero hz)
  rw [weierstrassSigma_eq, logDeriv_fun_mul z hz0 (L.tprod_weierstrassFactor_two_div_ne_zero hz)
    differentiableAt_fun_id (L.differentiable_tprod_weierstrassFactor_two_div z), hP, hsum.tsum_eq,
    logDeriv_id']
  ring

/-- **`-(σ' / σ)' = ℘`** away from the lattice. -/
theorem hasDerivAt_logDeriv_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (logDeriv L.weierstrassSigma) (-℘[L] z) z := by
  refine (L.hasDerivAt_weierstrassZeta hz).congr_of_eventuallyEq ?_
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  exact L.logDeriv_weierstrassSigma hw

/-- **`σ' = ζ σ`** away from the lattice. -/
theorem hasDerivAt_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassSigma (L.weierstrassZeta z * L.weierstrassSigma z) z := by
  have h := L.logDeriv_weierstrassSigma hz
  rw [logDeriv_apply, div_eq_iff (L.weierstrassSigma_ne_zero hz)] at h
  exact h ▸ (L.differentiable_weierstrassSigma z).hasDerivAt

/-- For `l ∈ Λ`, the functions `σ(z + l)` and `exp(η(l) z) σ(z)` have the same logarithmic
derivative `ζ(z) + η(l)` on the connected set `ℂ ∖ Λ`, so they are proportional there. -/
private theorem exists_eqOn_weierstrassSigma_add_coe (l : L.lattice) :
    ∃ c : ℂ, Set.EqOn (fun z ↦ L.weierstrassSigma (z + l))
      (fun z ↦ c * (cexp (L.quasiPeriod l * z) * L.weierstrassSigma z)) (L.lattice : Set ℂ)ᶜ := by
  have hshift {z : ℂ} (hz : z ∉ L.lattice) : z + l ∉ L.lattice :=
    fun h ↦ hz (by simpa using sub_mem h l.property)
  have hexp (z : ℂ) : HasDerivAt (fun w ↦ cexp (L.quasiPeriod l * w))
      (cexp (L.quasiPeriod l * z) * L.quasiPeriod l) z := by
    simpa using ((hasDerivAt_id z).const_mul (L.quasiPeriod l)).cexp
  obtain ⟨c, -, hc⟩ := (logDeriv_eqOn_iff (𝕜 := ℂ) (f := L.weierstrassSigma ∘ (· + (l : ℂ)))
    (g := (fun w ↦ cexp (L.quasiPeriod l * w)) * L.weierstrassSigma)
    (L.differentiable_weierstrassSigma.comp (by fun_prop)).differentiableOn
    ((Differentiable.mul (fun z ↦ (hexp z).differentiableAt)
      L.differentiable_weierstrassSigma).differentiableOn)
    L.isClosed_lattice.isOpen_compl
    (L.countable_lattice.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
    (fun z hz ↦ mul_ne_zero (exp_ne_zero _) (L.weierstrassSigma_ne_zero hz))
    (fun z hz ↦ L.weierstrassSigma_ne_zero (hshift hz))).mp fun z hz ↦ by
      have h1 : logDeriv (L.weierstrassSigma ∘ (· + (l : ℂ))) z =
          L.weierstrassZeta z + L.quasiPeriod l := by
        rw [logDeriv_comp (L.differentiable_weierstrassSigma _) (by fun_prop), deriv_add_const,
          deriv_id'', mul_one, L.logDeriv_weierstrassSigma (hshift hz), weierstrassZeta_add_coe]
      rw [h1, logDeriv_mul (f := fun w ↦ cexp (L.quasiPeriod l * w)) z (exp_ne_zero _)
        (L.weierstrassSigma_ne_zero hz)
        (hexp z).differentiableAt (L.differentiable_weierstrassSigma z),
        L.logDeriv_weierstrassSigma hz, logDeriv_apply, (hexp z).deriv,
        mul_div_cancel_left₀ _ (exp_ne_zero _), add_comm]
  exact ⟨c, fun z hz ↦ by simpa [smul_eq_mul] using hc hz⟩

/-- For `l ∈ Λ` there is a sign `ε` with `σ(z + l) = ε exp(η(l) (z + l / 2)) σ(z)` for all `z`:
evaluating the proportionality at `z₀` and at `-z₀ - l`, and using that `σ` is odd, shows that the
square of the constant is `exp(η(l) l)`. -/
private theorem exists_weierstrassSigma_add_coe (l : L.lattice) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ z, L.weierstrassSigma (z + l) =
      ε * cexp (L.quasiPeriod l * (z + l / 2)) * L.weierstrassSigma z := by
  obtain ⟨c, hc⟩ := L.exists_eqOn_weierstrassSigma_add_coe l
  set η := L.quasiPeriod l
  set z₀ := L.ω₁ / 2
  have hz₀ : z₀ ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hz₁ : -z₀ - l ∉ L.lattice := fun h ↦ hz₀ (by simpa using neg_mem (add_mem h l.property))
  have h₀ := hc hz₀
  have h₁ := hc hz₁
  simp only at h₀ h₁
  rw [sub_add_cancel, show -z₀ - l = -(z₀ + l) by ring, weierstrassSigma_neg, weierstrassSigma_neg,
    h₀] at h₁
  -- `h₁` now says `σ(z₀) = c² exp(-η l) σ(z₀)`, and `σ(z₀) ≠ 0`.
  have hc2 : c ^ 2 * cexp (-(η * l)) = 1 := by
    have hs := L.weierstrassSigma_ne_zero hz₀
    have : (c ^ 2 * cexp (-(η * l)) - 1) * L.weierstrassSigma z₀ = 0 := by
      rw [show -(η * l) = η * -(z₀ + l) + η * z₀ by ring, exp_add]
      linear_combination h₁
    simpa [sub_eq_zero] using (mul_eq_zero.mp this).resolve_right hs
  refine ⟨c * cexp (-(η * l / 2)), ?_, fun z ↦ ?_⟩
  · have he : cexp (-(η * l / 2)) ^ 2 = cexp (-(η * l)) := by
      rw [← exp_natCast_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, he, hc2]
  by_cases hz : z ∈ L.lattice
  · simp [L.weierstrassSigma_eq_zero_iff.mpr hz,
      L.weierstrassSigma_eq_zero_iff.mpr (add_mem hz l.property)]
  have hcz : L.weierstrassSigma (z + l) = c * (cexp (η * z) * L.weierstrassSigma z) := hc hz
  rw [hcz, show cexp (η * z) = cexp (-(η * l / 2)) * cexp (η * (z + l / 2)) by
    rw [← exp_add]; congr 1; ring]
  ring

/-- **Quasi-periodicity of `σ`** for `l ∈ Λ` with `l / 2 ∉ Λ`:
`σ(z + l) = -exp(η(l) (z + l / 2)) σ(z)`. -/
theorem weierstrassSigma_add_coe_of_div_two_notMem (z : ℂ) {l : L.lattice}
    (hl : (l : ℂ) / 2 ∉ L.lattice) :
    L.weierstrassSigma (z + l) = -cexp (L.quasiPeriod l * (z + l / 2)) * L.weierstrassSigma z := by
  obtain ⟨ε, -, h⟩ := L.exists_weierstrassSigma_add_coe l
  have h₀ := h (-(l / 2))
  rw [show -((l : ℂ) / 2) + l = l / 2 by ring, show -((l : ℂ) / 2) + l / 2 = 0 by ring, mul_zero,
    exp_zero, mul_one, weierstrassSigma_neg] at h₀
  have hε : ε = -1 := by
    have : (1 + ε) * L.weierstrassSigma (l / 2) = 0 := by linear_combination h₀
    linear_combination (mul_eq_zero.mp this).resolve_right (L.weierstrassSigma_ne_zero hl)
  rw [h, hε, neg_one_mul]

/-- **Quasi-periodicity of `σ`** for `l ∈ 2Λ`: `σ(z + l) = exp(η(l) (z + l / 2)) σ(z)`. -/
theorem weierstrassSigma_add_coe_of_div_two_mem (z : ℂ) {l : L.lattice}
    (hl : (l : ℂ) / 2 ∈ L.lattice) :
    L.weierstrassSigma (z + l) = cexp (L.quasiPeriod l * (z + l / 2)) * L.weierstrassSigma z := by
  set m : L.lattice := ⟨l / 2, hl⟩
  have hlm : l = m + m := Subtype.ext (by simp [m])
  obtain ⟨ε, hε, h⟩ := L.exists_weierstrassSigma_add_coe m
  rw [hlm, map_add, Submodule.coe_add, ← add_assoc, h, h,
    show ∀ a b s : ℂ, ε * a * (ε * b * s) = ε ^ 2 * (a * b) * s by intros; ring, hε, one_mul,
    ← exp_add]
  congr 2
  ring

/-- **Quasi-periodicity of `σ`** in terms of the periods: if `l = a ω₁ + b ω₂`, then
`σ(z + l) = (-1)^(a + b + a b) exp(η(l) (z + l / 2)) σ(z)`. -/
theorem weierstrassSigma_add_coe (z : ℂ) (l : L.lattice) {a b : ℤ}
    (h : a * L.ω₁ + b * L.ω₂ = l) :
    L.weierstrassSigma (z + l) =
      (-1) ^ (a + b + a * b) * cexp (L.quasiPeriod l * (z + l / 2)) * L.weierstrassSigma z := by
  -- `a + b + a b = (a + 1) (b + 1) - 1` is even exactly when `a` and `b` are.
  have hsign : Even (a + b + a * b) ↔ Even a ∧ Even b := by
    rw [← not_iff_not, ← Int.even_add_one, show a + b + a * b + 1 = (a + 1) * (b + 1) by ring,
      Int.even_mul, Int.even_add_one, Int.even_add_one]
    tauto
  have hdiv : (l : ℂ) / 2 ∈ L.lattice ↔ Even a ∧ Even b := by
    rw [show (l : ℂ) / 2 = ((a / 2 : ℚ) : ℂ) * L.ω₁ + ((b / 2 : ℚ) : ℂ) * L.ω₂ by
        rw [← h]; push_cast; ring,
      mul_ω₁_add_mul_ω₂_mem_lattice, even_iff_two_dvd, even_iff_two_dvd,
      ← Rat.den_div_intCast_eq_one_iff a 2 two_ne_zero,
      ← Rat.den_div_intCast_eq_one_iff b 2 two_ne_zero, Int.cast_ofNat]
  by_cases hab : Even a ∧ Even b
  · rw [L.weierstrassSigma_add_coe_of_div_two_mem z (hdiv.mpr hab),
      Even.neg_one_zpow (hsign.mpr hab), one_mul]
  · rw [L.weierstrassSigma_add_coe_of_div_two_notMem z
      (mt hdiv.mp hab),
      Odd.neg_one_zpow (Int.not_even_iff_odd.mp (mt hsign.mp hab)), neg_one_mul]

/-- **The zeros of `σ` are simple.** -/
theorem analyticOrderAt_weierstrassSigma_coe (l : L.lattice) :
    analyticOrderAt L.weierstrassSigma l = 1 := by
  obtain ⟨ε, hε, h⟩ := L.exists_weierstrassSigma_add_coe l
  set η := L.quasiPeriod l
  have hd : HasDerivAt (fun z ↦ L.weierstrassSigma (z + l)) (ε * cexp (η * (l / 2))) 0 := by
    have hexp : HasDerivAt (fun z ↦ cexp (η * (z + l / 2)))
        (cexp (η * (0 + l / 2)) * (η * 1)) 0 :=
      (((hasDerivAt_id (0 : ℂ)).add_const _).const_mul η).cexp
    convert (hexp.const_mul ε).mul L.hasDerivAt_weierstrassSigma_zero using 1
    · exact funext fun z ↦ by rw [h, Pi.mul_apply, mul_assoc]
    · simp
  have hderiv : deriv L.weierstrassSigma l = ε * cexp (η * (l / 2)) := by
    have := hd.deriv
    rwa [deriv_comp_add_const, zero_add] at this
  refine (L.differentiable_weierstrassSigma.analyticAt _)
    |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (L.weierstrassSigma_coe l) ?_
  rw [hderiv]
  refine mul_ne_zero ?_ (exp_ne_zero _)
  rintro rfl
  simp at hε

/-- **`σ` depends only on the lattice**, not on the chosen pair of periods. -/
theorem weierstrassSigma_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.weierstrassSigma = L'.weierstrassSigma := by
  ext z
  rw [weierstrassSigma_def, weierstrassSigma_def, h]

end PeriodPair
