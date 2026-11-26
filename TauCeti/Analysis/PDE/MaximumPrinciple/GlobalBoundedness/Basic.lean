/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
public import TauCeti.Analysis.Sobolev.FiniteMeasure
public import TauCeti.Analysis.SpecificLimits.Stampacchia
public import TauCeti.MeasureTheory.Integral.Bochner.Holder
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Global boundedness of weak subsolutions (Stampacchia)

Let `Ω ⊆ ℝⁿ` be open with finite measure, let `a` be measurable and uniformly elliptic on `Ω`
with constants `0 < λ ≤ Λ`, and let `c` be bounded, measurable and nonnegative. This file proves
the weak maximum principle with a right-hand side: if `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ f` in `Ω`, with `f ∈ Lʳ(Ω)`, `r > 1` and `r > n/2`,

meaning `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a level
`k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then

`u ≤ k + C ‖f‖_{Lʳ(Ω)} / λ · |Ω| ^ (2/n - 1/r)` almost everywhere in `Ω`,

with `C` depending only on `n`, `r` and the normalization of the Haar measure. In particular the
weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f` with
`f ∈ Lʳ(Ω)`, meaning `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, is bounded, with
`|u| ≤ C ‖f‖_{Lʳ} / λ · |Ω| ^ (2/n - 1/r)`. No regularity of `∂Ω` and no regularity of the
coefficients beyond measurability is used, and the power of `|Ω|` makes the estimate invariant
under dilations.

This is the bound that lets De Giorgi's interior estimates absorb a right-hand side: on a ball
`B ⊆ Ω`, a solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` differs from a solution of the homogeneous equation by
the solution of the Dirichlet problem on `B` with data `f`, and the bound above controls that
difference by `R ^ (2 - n/r) ‖f‖_{Lʳ}`.

## Stampacchia's method

For a level `l ≥ k`, the truncation `w = (u - l)⁺` lies in `H¹₀(Ω)` and is a nonnegative test
function, and its gradient is `∇u` on `{u > l}` and zero elsewhere. Testing the subsolution
inequality against it, ellipticity and `c ≥ 0` give `λ ‖∇w‖² ≤ ∫ f w`. A Sobolev inequality
`‖w‖_{Lˢ} ≤ S ‖∇w‖_{L²}` on `H¹₀(Ω)` and Hölder's inequality on the superlevel set `{u > l}`,
off which `w` vanishes, turn this into

`‖(u - l)⁺‖_{Lˢ} ≤ S² ‖f‖_{Lʳ} / λ · |{u > l}| ^ (1 - 1/r - 1/s)`.

Chebyshev's inequality on `{u > h}`, where `(u - l)⁺ ≥ h - l`, then gives, for `φ l = |{u > l}|`
and `M = S² ‖f‖_{Lʳ} / λ`,

`φ h ≤ (M / (h - l)) ^ s φ l ^ β` for `k ≤ l < h`, where `β = s (1 - 1/r - 1/s)`.

When `s (1 - 1/r) > 2`, the exponent `β` exceeds `1`, and Stampacchia's lemma
(`TauCeti.apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow`) shows that `φ` vanishes at a finite
level above `k`. In every dimension the Sobolev inequality on sets of finite measure
(`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`) provides such an
exponent `s` whenever `r > 1` and `r > n/2`, with `S` a multiple of `|Ω| ^ (1/n - 1/2 + 1/s)`.
Only the energy estimate for `‖(u - l)⁺‖_{Lˢ}` depends on the right-hand side; the passage from it
to the bound on `u` is shared by both kinds of data below.

## A right-hand side in divergence form

The same holds for weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` with `F ∈ L^q(Ω; ℝⁿ)`,
`q > n` and `q > 2`, meaning `a(u, v) ≤ -∫_Ω F · ∇v` for every nonnegative `v ∈ H¹₀(Ω)`:

`u ≤ k + C ‖F‖_{L^q(Ω)} / λ · |Ω| ^ (1/n - 1/q)` almost everywhere in `Ω`.

Testing against `w = (u - l)⁺` now gives `λ ‖∇w‖² ≤ ∫ ‖F‖ ‖∇w‖`, and since `∇w` vanishes off
`{u > l}`, Hölder's inequality bounds the right side by
`‖F‖_{L^q} ‖∇w‖_{L²} |{u > l}| ^ (1/2 - 1/q)`. After cancelling one factor of `‖∇w‖_{L²}`, the
Sobolev inequality gives `‖(u - l)⁺‖_{Lˢ} ≤ S ‖F‖_{L^q} / λ · |{u > l}| ^ (1/2 - 1/q)`, and
Stampacchia's lemma applies once `s (1/2 - 1/q) > 1`. On a ball `B` of radius `ρ` this bounds the
solution of the Dirichlet problem on `B` with datum `∂ᵢFⁱ` by a multiple of
`ρ ^ (1 - n/q) ‖F‖_{L^q}`. That is the divergence-form counterpart of the bound above, needed when
De Giorgi's interior estimates absorb a divergence-form right-hand side.

## A small drift

Only the coercivity of the energy form on `H¹₀(Ω)` enters the energy estimate: testing against
`w = (u - l)⁺` gives `κ ‖∇w‖² ≤ ∫ f w` as soon as `κ ‖∇v‖² ≤ a(v, v)` on `H¹₀(Ω)`. A drift `b` with
`‖b‖ ≤ β` keeps this coercivity, with `κ = λ/4`, when it is small against the Poincaré constant of
`Ω`, `2β ‖v‖_{L²} ≤ λ ‖∇v‖_{L²}`; on a ball `B(x₀, ρ)` this is `2βρ ≤ λ`. So the bounds for a
datum `f ∈ Lʳ` hold for weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ f`, and the Dirichlet
problem with a small drift on a ball is solvable with the same bound. The bounds for a datum in
divergence form are stated without a drift. This is what De Giorgi's interior estimates need
to absorb a right-hand side in the presence of a drift: on balls small enough that `2βρ ≤ λ`.

## Main declarations

* `TauCeti.PDE.ae_value_le_add_of_forall_eLpNorm_le_of_coercive`: the bound with an explicit
  constant for a coercive energy form, under a Sobolev inequality on `H¹₀(Ω)` with exponent `s`
  and constant `S`. Without a drift the coercivity constant is `λ`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow_drift`: the scale-invariant bound in every
  dimension, for `r > max 1 (n/2)`, with a small drift; without a drift, `b = 0` and `β = 0`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_drift`: the two-sided bound for weak
  solutions of the Dirichlet problem, with a small drift or none.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_ae_abs_le_drift` and
  `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_ae_abs_le`: on a ball `B(x₀, ρ)` with
  `2βρ ≤ λ`, the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼw) + bⁱ ∂ᵢw = f`, `w ∈ H¹₀`, has a solution with
  `|w| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ} / λ`; without a drift on every ball.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le_divergence`: the bound
  with an explicit constant for a right-hand side `∂ᵢFⁱ` in divergence form, `F ∈ L^q` with
  `q ≥ 2`, under a Sobolev inequality on `H¹₀(Ω)` with exponent `s` and constant `S`, where
  `s (1/2 - 1/q) > 1`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow_divergence`: the scale-invariant bound for
  a right-hand side in divergence form in every dimension, for `q > max 2 n`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`: the two-sided bound for weak
  solutions of the Dirichlet problem with a right-hand side in divergence form, `q > max 2 n`.
* `TauCeti.PDE.ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le` and
  `TauCeti.PDE.exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le`: the bound
  for any `u` whose truncations satisfy `λ ‖∇(u - l)⁺‖² ≤ ∫ g (u - l)⁺ - ∫ ⟪F, ∇(u - l)⁺⟫`, with a
  scalar datum `g ∈ L^{q/2}` and a datum `F ∈ L^q` in divergence form at once; with a drift this
  energy inequality holds only above some level.
* `TauCeti.PDE.ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le`: Stampacchia's iteration,
  from `‖(u - l)⁺‖_{Lˢ} ≤ M |{u > l}| ^ θ` at every level `l ≥ k`, `s θ > 1`, to a bound on `u`.
* `TauCeti.PDE.exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow` and
  `TauCeti.PDE.exists_sobolev_exponent`: the Sobolev inequality and exponents behind the
  scale-invariant bounds.
* `TauCeti.PDE.exists_inv_add_inv_eq_and_forall_eLpNorm_value_le_of_measure_ne_top`: for
  `max(2, n) < r`, the Sobolev inequality `‖v‖_{L^q} ≤ S ‖∇v‖₂` on `W^{1,2}_0(Ω)` at the exponent
  `q` with `1/r + 1/q = 1/2`.

The case of an operator with a drift that need not be small is
`TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.LowerOrder`.

## References

* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.15 and Theorem 8.16.
* D. Kinderlehrer, G. Stampacchia, *An Introduction to Variational Inequalities and Their
  Applications*, Chapter II, Appendix B.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}

omit [DecidableEq ι] in
/-- The step of Stampacchia's energy estimate that does not depend on the right-hand side. Let
`u ∈ H¹(Ω)` satisfy `a(u, v) ≤ R v` for every nonnegative `v ∈ H¹₀(Ω)`, and let
`(u - k)⁺ ∈ H¹₀(Ω)` for a level `k ≥ 0`. At a level `l ≥ k`, the truncation `w = (u - l)⁺` is such
a test function, and the coercivity `κ ‖∇v‖² ≤ a(v, v)` on `H¹₀(Ω)` together with `c ≥ 0` gives
`κ ‖∇w‖² ≤ a(w, w) ≤ a(u, w) ≤ R w`. Without a drift, ellipticity gives the coercivity with
`κ = λ`. -/
private theorem mul_norm_gradient_posPartAbove_sq_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {κ : ℝ}
    (hκ : ∀ v ∈ w1p0Submodule mu Omega 2, κ * ‖W1p.gradient v‖ ^ 2 ≤ energyFormH1 a b c v v)
    {u : W1p mu Omega 2} {R : W1p0 mu Omega 2 → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ R v)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l) :
    κ * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
      R ⟨_, W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary⟩ := by
  have hl : 0 ≤ l := hk.trans hkl
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.posPartAbove (by norm_num) hl u) x :=
    (W1p.value_posPartAbove_ae (by norm_num) hl u).mono fun x hx => hx ▸ le_max_right _ _
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hw0 := W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  exact (hκ _ hw0).trans ((energyFormH1_posPartAbove_self_le hcoeff (hmem.mono hc_nonneg) hl
    u).trans (hu ⟨_, hw0⟩ hnonneg))

omit [DecidableEq ι] in
/-- The energy estimate behind Stampacchia's method. For a weak subsolution `u` of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ f` with `(u - k)⁺ ∈ H¹₀(Ω)`, whose energy form is coercive on
`H¹₀(Ω)` with constant `κ > 0`, testing against `w = (u - l)⁺` at a level `l ≥ k` and combining
coercivity, the Sobolev inequality and Hölder's inequality on the superlevel set `{u > l}` gives

`‖(u - l)⁺‖_{Lˢ} ≤ S² ‖f‖_{Lʳ} / κ · |{u > l}| ^ (1 - 1/r - 1/s)`. -/
private theorem toReal_eLpNorm_posPartAbove_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ v ∈ w1p0Submodule mu Omega 2, κ * ‖W1p.gradient v‖ ^ 2 ≤ energyFormH1 a b c v v)
    (hOmega : mu Omega ≠ ∞) {r s S : ℝ≥0} (hr : 0 < r) (hs : 0 < s)
    (hrs : (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1)
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f r (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l) :
    (eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s
        (mu.restrict Omega)).toReal ≤
      S ^ 2 * (eLpNorm f r (mu.restrict Omega)).toReal / κ *
        (mu.restrict Omega).real {x | l < W1p.value u x} ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  set ν := mu.restrict Omega
  have hl : 0 ≤ l := hk.trans hkl
  set w := W1p.posPartAbove (by norm_num) hl u
  have hw0 : w ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hval : ∀ᵐ x ∂ν, W1p.value w x = max (W1p.value u x - l) 0 :=
    W1p.value_posPartAbove_ae (by norm_num) hl u
  -- Coercivity and the subsolution inequality tested against `w`.
  have henergy : κ * ‖W1p.gradient w‖ ^ 2 ≤ ∫ x in Omega, f x * W1p.value w x ∂mu :=
    mul_norm_gradient_posPartAbove_sq_le hcoeff hc_nonneg hκ hu hk hboundary hkl
  -- The Sobolev inequality, in real form.
  have hsob := hS w hw0
  have hwLp : MemLp (W1p.value w) s ν := lt_of_le_of_lt hsob (by finiteness)
  have hsobR : (eLpNorm (W1p.value w) s ν).toReal ≤ S * ‖W1p.gradient w‖ :=
    W1p.toReal_eLpNorm_value_le_mul_norm_gradient hsob
  -- Hölder's inequality on the superlevel set `{u > l}`, off which `w` vanishes.
  set A := {x | l < W1p.value u x}
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  have hwA : ∀ᵐ x ∂ν, x ∉ A → W1p.value w x = 0 := by
    filter_upwards [hval] with x hx hxA
    rw [hx, max_eq_right (sub_nonpos.2 (not_lt.1 hxA))]
  have hholder := (Real.le_norm_self _).trans <|
    MeasureTheory.norm_integral_smul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow hr hs hrs hf hwLp
      (measure_ne_top ν A) hwA
  simp only [smul_eq_mul] at hholder
  -- Absorb one factor of `‖w‖_{Lˢ}`.
  set W := (eLpNorm (W1p.value w) s ν).toReal
  set F := (eLpNorm f r ν).toReal
  set m := ν.real A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹)
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  have hkey : κ * W ^ 2 ≤ S ^ 2 * F * m * W := by
    calc κ * W ^ 2 ≤ κ * ((S : ℝ) * ‖W1p.gradient w‖) ^ 2 := by gcongr
      _ = S ^ 2 * (κ * ‖W1p.gradient w‖ ^ 2) := by ring
      _ ≤ S ^ 2 * (F * W * m) :=
          mul_le_mul_of_nonneg_left (henergy.trans hholder) (by positivity)
      _ = S ^ 2 * F * m * W := by ring
  rcases hW.eq_or_lt with hW0 | hWpos
  · rw [← hW0]
    positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hκ0]
    nlinarith

omit [DecidableEq ι] in
/-- **Stampacchia's iteration.** Let `Ω` have finite measure, let `u ∈ W^{1,2}(Ω)` and `k ≥ 0`,
and suppose that for every level `l ≥ k` the truncation `(u - l)⁺` lies in `Lˢ(Ω)` with

`‖(u - l)⁺‖_{Lˢ} ≤ M |{u > l}| ^ θ`,

where `M ≥ 0` and `s θ > 1`. Then almost everywhere in `Ω`

`u ≤ k + 2 ^ (s θ / (s θ - 1)) M |Ω| ^ (θ - 1/s)`.

Chebyshev's inequality for `(u - l)⁺ ≥ h - l` on `{u > h}` turns the hypothesis into the
recursion `φ h ≤ (M / (h - l)) ^ s φ l ^ (s θ)` for the measures `φ l = |{u > l}|`, and
Stampacchia's lemma `TauCeti.apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow` makes `φ` vanish at a
finite level. The energy estimate supplying the hypothesis depends on the right-hand side of the
equation; this step does not. -/
theorem ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le (hOmega : mu Omega ≠ ∞)
    {s : ℝ≥0} (hs : 0 < s) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 1 < (s : ℝ) * θ)
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hfin : ∀ l (hkl : k ≤ l), eLpNorm (W1p.value
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s (mu.restrict Omega) ≠ ∞)
    (hbound : ∀ l (hkl : k ≤ l), (eLpNorm (W1p.value
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s (mu.restrict Omega)).toReal ≤
        M * (mu.restrict Omega).real {x | l < W1p.value u x} ^ θ) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ ((s : ℝ) * θ / ((s : ℝ) * θ - 1)) * M * mu.real Omega ^ (θ - (s : ℝ)⁻¹) := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  have hs0 : (0 : ℝ) < s := hs
  set β : ℝ := s * θ
  have hβ : 1 < β := hθ
  set φ : ℝ → ℝ := fun t => ν.real {x | t < W1p.value u x}
  -- Chebyshev's inequality: `(u - l)⁺ ≥ t - l` on `{u > t}`.
  have hrec : ∀ l t, k ≤ l → l < t → φ t ≤ (M / (t - l)) ^ (s : ℝ) * φ l ^ β := by
    intro l t hkl hlt
    set w := W1p.posPartAbove (by norm_num) (hk.trans hkl) u
    set W := (eLpNorm (W1p.value w) s ν).toReal
    have htl : 0 < t - l := sub_pos.2 hlt
    have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := ν) (f := W1p.value w)
      (by exact_mod_cast hs.ne') ENNReal.coe_ne_top (ENNReal.ofReal (t - l))
    have hsub : ν {x | t < W1p.value u x} ≤
        ν {x | ENNReal.ofReal (t - l) ≤ ‖W1p.value w x‖ₑ} := by
      refine measure_mono_ae ?_
      filter_upwards [W1p.value_posPartAbove_ae (by norm_num) (hk.trans hkl) u] with x hx hxt
      rw [hx, Real.eNorm_of_nonneg (le_max_right _ _)]
      exact ENNReal.ofReal_le_ofReal (le_max_of_le_left (by linarith))
    have hfin' : eLpNorm (W1p.value w) s ν ^ ((s : ℝ≥0∞).toReal) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (hfin l hkl)
    have hreal : (t - l) ^ (s : ℝ) * φ t ≤ W ^ (s : ℝ) := by
      have := ENNReal.toReal_mono hfin' ((mul_le_mul_right hsub _).trans hcheb)
      rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal htl.le, ENNReal.coe_toReal, ← measureReal_def] at this
    have hpow : W ^ (s : ℝ) ≤ M ^ (s : ℝ) * φ l ^ β := by
      calc W ^ (s : ℝ)
          ≤ (M * φ l ^ θ) ^ (s : ℝ) :=
            Real.rpow_le_rpow ENNReal.toReal_nonneg (hbound l hkl) hs0.le
        _ = _ := by
            rw [Real.mul_rpow hM (by positivity), ← Real.rpow_mul measureReal_nonneg,
              mul_comm θ]
    rw [Real.div_rpow hM htl.le, div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
    exact hreal.trans hpow
  -- It suffices to bound `u` by the level `k + M φ(k) ^ ((β - 1)/s) 2 ^ (β/(β - 1))`.
  suffices hmain : ∀ᵐ x ∂ν, W1p.value u x ≤ k + M * φ k ^ ((β - 1) / s) * 2 ^ (β / (β - 1)) by
    have hexp : (β - 1) / s = θ - (s : ℝ)⁻¹ := by
      simp only [β]
      field_simp
    have hφk : φ k ≤ mu.real Omega := by
      refine (measureReal_mono (subset_univ _)).trans_eq ?_
      simp [ν, measureReal_def]
    have hθs : 0 ≤ θ - (s : ℝ)⁻¹ := by
      rw [← hexp]
      exact div_nonneg (by linarith) hs0.le
    filter_upwards [hmain] with x hx
    refine hx.trans ?_
    rw [hexp]
    calc k + M * φ k ^ (θ - (s : ℝ)⁻¹) * 2 ^ (β / (β - 1))
        ≤ k + M * mu.real Omega ^ (θ - (s : ℝ)⁻¹) * 2 ^ (β / (β - 1)) := by
          gcongr
      _ = _ := by ring
  rcases hM.eq_or_lt with hM0 | hMpos
  · -- If `M = 0`, the truncation `(u - k)⁺` has zero `Lˢ` norm, so `u ≤ k`.
    have hW := hbound k le_rfl
    rw [← hM0, zero_mul] at hW
    have hzero : eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hk u)) s ν = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hW ENNReal.toReal_nonneg)).resolve_right
        (hfin k le_rfl)
    rw [eLpNorm_eq_zero_iff (by exact_mod_cast hs.ne')] at hzero
    filter_upwards [hzero, W1p.value_posPartAbove_ae (by norm_num) hk u] with x hx hx'
    rw [← hM0, zero_mul, zero_mul, add_zero]
    have : max (W1p.value u x - k) 0 = 0 := hx'.symm.trans hx
    linarith [le_max_left (W1p.value u x - k) 0]
  · -- If `M > 0`, Stampacchia's lemma applies to the measures of the superlevel sets.
    have hanti : AntitoneOn φ (Ici k) := fun t₁ _ t₂ _ ht =>
      measureReal_mono (fun x hx => lt_of_le_of_lt ht hx) (measure_ne_top _ _)
    have hstamp := apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow hMpos hs0 hβ
      (fun _ _ => measureReal_nonneg) hanti hrec
    have hnull := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hstamp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    exact not_lt.1 hx

/-- The exponent facts behind Stampacchia's method: if `s (1 - 1/r) > 2` then `s > 0`,
`2/s < 1 - 1/r`, `1/r + 1/s ≤ 1` and `β = s (1 - 1/r - 1/s) = s (1 - 1/r) - 1 > 1`. -/
private theorem exponent_facts {r s : ℝ≥0} (hrs : 2 < (s : ℝ) * (1 - (r : ℝ)⁻¹)) :
    0 < (s : ℝ) ∧ 2 / (s : ℝ) < 1 - (r : ℝ)⁻¹ ∧ (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1 ∧
      (s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) = (s : ℝ) * (1 - (r : ℝ)⁻¹) - 1 ∧
      1 < (s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  have hs0 : (0 : ℝ) < s := by
    rcases (NNReal.coe_nonneg s).eq_or_lt with hs | hs
    · rw [← hs, zero_mul] at hrs
      norm_num at hrs
    · exact hs
  have h2s : 2 / (s : ℝ) < 1 - (r : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hs0]
    linarith
  have hβ_eq : (s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) = (s : ℝ) * (1 - (r : ℝ)⁻¹) - 1 := by
    field_simp
  refine ⟨hs0, h2s, ?_, hβ_eq, by linarith⟩
  have : (s : ℝ)⁻¹ ≤ 2 / s := by
    rw [div_eq_mul_inv]
    linarith [inv_pos.2 hs0]
  linarith

omit [DecidableEq ι] in
/-- **Stampacchia's global bound for a coercive energy form.** Let `Ω` have finite measure, and
let the coefficients `a, b, c` be bounded with `c ≥ 0`, and such that the energy form is coercive
on `H¹₀(Ω)`, `κ ‖∇v‖² ≤ a(v, v)` with `κ > 0`. Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev
inequality `‖v‖_{Lˢ} ≤ S ‖∇v‖_{L²}`, and let `f ∈ Lʳ(Ω)` with `s (1 - 1/r) > 2`. If `u ∈ H¹(Ω)` is
a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ f` in `Ω`,

that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a level
`k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + 2 ^ (β / (β - 1)) S² ‖f‖_{Lʳ} / κ · |Ω| ^ (1 - 1/r - 2/s)`, where `β = s (1 - 1/r) - 1`.

Without a drift, ellipticity gives the coercivity with `κ = λ`
(`TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift`); a
small drift gives it
with `κ = λ/4`
(`TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sq_le_energyFormH1_self_of_small_drift`). -/
theorem ae_value_le_add_of_forall_eLpNorm_le_of_coercive
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ v ∈ w1p0Submodule mu Omega 2, κ * ‖W1p.gradient v‖ ^ 2 ≤ energyFormH1 a b c v v)
    (hOmega : mu Omega ≠ ∞) {r s S : ℝ≥0} (hr : 0 < r) (hrs : 2 < (s : ℝ) * (1 - (r : ℝ)⁻¹))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f r (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ (((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) / ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2)) * S ^ 2 *
        (eLpNorm f r (mu.restrict Omega)).toReal / κ *
          mu.real Omega ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ)) := by
  obtain ⟨hs0, -, hrs', hβ_eq, hβ⟩ := exponent_facts hrs
  have hs : 0 < s := by exact_mod_cast hs0
  have hbound := ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le hOmega hs
    (div_nonneg (by positivity) hκ0.le) hβ hk
    (fun l hkl => ((hS _ (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl
      hboundary)).trans_lt (by finiteness)).ne)
    (fun l hkl => toReal_eLpNorm_posPartAbove_le hcoeff hc_nonneg hκ0 hκ hOmega hr hs hrs' hS
      hf hu hk hboundary hkl)
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  have hexp : 1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹ - (s : ℝ)⁻¹ = 1 - (r : ℝ)⁻¹ - 2 / s := by ring
  rw [hβ_eq, hexp, show (s : ℝ) * (1 - (r : ℝ)⁻¹) - 1 - 1 = s * (1 - (r : ℝ)⁻¹) - 2 by ring]
  ring

omit [DecidableEq ι] in
/-- The Sobolev inequality behind the scale-invariant bounds: for `0 < δ < min (1/n) (1/2)`,
every `v ∈ W^{1,2}_0(Ω)` lies in `Lˢ(Ω)` with `s = (1/2 - δ)⁻¹`, and

`‖v‖_{Lˢ} ≤ K |Ω| ^ (1/n - δ) ‖∇v‖_{L²}`,

with `K > 0` depending only on `n`, `δ` and the normalization of `mu`. This is
`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt` at `p = 2`. -/
theorem exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow [Nonempty ι] {δ : ℝ}
    (hδ0 : 0 < δ) (hδn : δ < (Fintype.card ι : ℝ)⁻¹) (hδ2 : δ < 2⁻¹) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}, mu Omega ≠ ∞ →
      ∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) (Real.toNNReal (2⁻¹ - δ)⁻¹) (mu.restrict Omega) ≤
          (Real.toNNReal (K * mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - δ)) : ℝ≥0∞) *
            ‖W1p.gradient v‖ₑ := by
  set n : ℕ := Fintype.card ι
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  have hs : (s : ℝ) = (2⁻¹ - δ)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 (by linarith))
  have hs2 : (2 : ℝ≥0∞) ≤ s := by
    have : (2 : ℝ) ≤ s := by
      rw [hs, le_inv_comm₀ two_pos (by linarith)]
      linarith
    exact_mod_cast this
  set K : ℝ := (n : ℝ)⁻¹ * mu.real (Metric.ball 0 1) ^ (-(n : ℝ)⁻¹) *
    ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ)
  have hK : 0 < K := by
    have : 0 < (n : ℝ)⁻¹ - δ := sub_pos.2 hδn
    have : 0 < 1 - δ := by linarith
    have : 0 < mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos mu
        (0 : EuclideanSpace ℝ ι) one_pos).ne' measure_ball_lt_top.ne
    positivity
  refine ⟨K, hK, fun {Omega} hOmega v hv => ?_⟩
  have hsob := W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (mu := mu)
    hOmega hs2 (δ := δ) (by rw [ENNReal.toReal_ofNat, hs, inv_inv]; ring)
    (by rwa [finrank_euclideanSpace]) hv
  rw [finrank_euclideanSpace] at hsob
  refine hsob.trans_eq ?_
  rw [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_toReal hOmega,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by linarith), ← ENNReal.ofReal_mul hK.le,
    ← measureReal_def]

omit [DecidableEq ι] in
/-- **The Sobolev inequality on `W^{1,2}_0(Ω)` dual to an exponent `r > max(2, n)`.** If `Ω` has
finite measure and `max(2, n) < r`, then the exponent `q` with `1/r + 1/q = 1/2` admits a
constant `S` with `‖v‖_{L^q} ≤ S ‖∇v‖₂` for every `v ∈ W^{1,2}_0(Ω)`. The hypothesis
`n < r.toReal` already forces `r < ∞`. Hölder's inequality with the exponents `r`, `2` and `q`
then bounds `∫ |b| |∇w| |v|` for `b ∈ Lʳ(Ω)`, `w ∈ W^{1,2}(Ω)` and `v ∈ W^{1,2}_0(Ω)`. This is
the case `δ = 1/r` of `TauCeti.PDE.exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow`. -/
theorem exists_inv_add_inv_eq_and_forall_eLpNorm_value_le_of_measure_ne_top [Nonempty ι]
    {Omega : Opens (EuclideanSpace ℝ ι)} (hOmega : mu Omega ≠ ∞) {r : ℝ≥0∞} (hr2 : 2 < r)
    (hn : (Fintype.card ι : ℝ) < r.toReal) :
    ∃ q : ℝ≥0∞, r⁻¹ + q⁻¹ = 2⁻¹ ∧ ∃ S : ℝ≥0, ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ := by
  have hr : r ≠ ∞ := (ENNReal.toReal_pos_iff.1 ((Nat.cast_nonneg _).trans_lt hn)).2.ne
  have hr2' : 2 < r.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hr).2 hr2
  have hδ2 : r.toReal⁻¹ < 2⁻¹ := inv_strictAnti₀ two_pos hr2'
  obtain ⟨K, -, hK⟩ := exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow (mu := mu)
    (inv_pos.2 (by linarith)) (inv_strictAnti₀ (by exact_mod_cast Fintype.card_pos) hn) hδ2
  refine ⟨_, ?_, _, fun v hv ↦ hK hOmega v hv⟩
  -- With `δ = 1/r`, the exponent `q = (1/2 - δ)⁻¹` has `1/q = 1/2 - 1/r`; check it in `ℝ`.
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr2'
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp [hr0, hδ2]) (by simp),
    ENNReal.toReal_add (by simpa) (by simpa)]
  simp [Real.coe_toNNReal _ (inv_nonneg.2 (sub_pos.2 hδ2).le)]

/-- The Sobolev exponents used in the scale-invariant bounds: for `0 ≤ θ < min (1/n) (1/2)` there
are `δ` with `θ < δ < min (1/n) (1/2)`, and then `s = (1/2 - δ)⁻¹` satisfies `1/s = 1/2 - δ` and
`s (1/2 - θ) > 1`. -/
theorem exists_sobolev_exponent {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hθn : θ < (n : ℝ)⁻¹)
    (hθ2 : θ < 2⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (n : ℝ)⁻¹ ∧ δ < 2⁻¹ ∧
      ((Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) : ℝ)⁻¹ = 2⁻¹ - δ ∧
      1 < ((Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) : ℝ) * (2⁻¹ - θ) := by
  obtain ⟨δ, hθδ, hδmin⟩ := exists_between (lt_min hθn hθ2)
  obtain ⟨hδn, hδ2⟩ := lt_min_iff.1 hδmin
  have hs : ((Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) : ℝ)⁻¹ = 2⁻¹ - δ := by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (by linarith)), inv_inv]
  refine ⟨δ, hθ.trans_lt hθδ, hδn, hδ2, hs, ?_⟩
  have hs0 : (0 : ℝ) < (Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) := inv_pos.1 (by rw [hs]; linarith)
  rw [← div_lt_iff₀' hs0, one_div, hs]
  linarith

/-! ### Stampacchia's bound from the energy inequality of the truncations -/

omit [DecidableEq ι] in
/-- The energy estimate of Stampacchia's method with a scalar datum `g ∈ L^{q/2}` and a datum
`F ∈ L^q` in divergence form. If the truncation `w = (u - l)⁺` satisfies
`λ ‖∇w‖² ≤ ∫ g w - ∫ ⟪F, ∇w⟫`, then Hölder's inequality on `A = {u > l}`, off which `w` and `∇w`
vanish, and the Sobolev inequality `‖w‖_s ≤ S ‖∇w‖₂` give

`‖w‖_s ≤ S (S ‖g‖_{q/2} |Ω| ^ ρ + ‖F‖_q) / λ · |A| ^ (1/2 - 1/q)`, where `ρ = 1/2 - 1/q - 1/s`. -/
private theorem toReal_eLpNorm_posPartAbove_le_of_mul_norm_gradient_sq_le
    (hOmega : mu Omega ≠ ∞) {q s S : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqs : 1 < (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {lam : ℝ} (hlam : 0 < lam) {g : EuclideanSpace ℝ ι → ℝ}
    (hg : MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l)
    (henergy : lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
      ∫ x in Omega, g x * W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x ∂mu -
        ∫ x in Omega, ⟪F x, W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x⟫
          ∂mu) :
    (eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s
        (mu.restrict Omega)).toReal ≤
      S * (S * (eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
          mu.real Omega ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) +
        (eLpNorm F q (mu.restrict Omega)).toReal) / lam *
        (mu.restrict Omega).real {x | l < W1p.value u x} ^ (2⁻¹ - (q : ℝ)⁻¹) := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  have hl : 0 ≤ l := hk.trans hkl
  set w := W1p.posPartAbove (by norm_num) hl u
  have hw0 : w ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hq0 : (0 : ℝ) < q := by linarith
  have hs0 : (0 : ℝ) < s := by
    rcases (NNReal.coe_nonneg s).eq_or_lt with hs | hs
    · rw [← hs, zero_mul] at hqs
      norm_num at hqs
    · exact hs
  -- The exponents: `θ₂ = 1/2 - 1/q` and `ρ = 1/2 - 1/q - 1/s > 0`.
  have hρ : 0 < 2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹ := by
    have : (s : ℝ)⁻¹ < 2⁻¹ - (q : ℝ)⁻¹ := by
      rw [inv_lt_iff_one_lt_mul₀' hs0]
      linarith
    linarith
  have hq2 : ((q / 2 : ℝ≥0) : ℝ) = q / 2 := by simp
  have hqinv : (q : ℝ)⁻¹ < 2⁻¹ := inv_strictAnti₀ two_pos hq
  have h2q : 2 / (q : ℝ) = 2 * (q : ℝ)⁻¹ := by ring
  -- The Sobolev inequality, in real form.
  have hsob := hS w hw0
  have hwLp : MemLp (W1p.value w) s ν := lt_of_le_of_lt hsob (by finiteness)
  have hsobR : (eLpNorm (W1p.value w) s ν).toReal ≤ S * ‖W1p.gradient w‖ :=
    W1p.toReal_eLpNorm_value_le_mul_norm_gradient hsob
  -- `w` and `∇w` vanish off `A = {u > l}`.
  set A := {x | l < W1p.value u x}
  have hwA : ∀ᵐ x ∂ν, x ∉ A → W1p.value w x = 0 := by
    filter_upwards [W1p.value_posPartAbove_ae (by norm_num) hl u] with x hx hxA
    rw [hx, max_eq_right (sub_nonpos.2 (not_lt.1 hxA))]
  have hgA : ∀ᵐ x ∂ν, x ∉ A → ‖W1p.gradient w x‖ = 0 := by
    filter_upwards [W1p.gradient_posPartAbove_ae (by norm_num) hl u] with x hx hxA
    rw [hx, indicator_of_notMem hxA, norm_zero]
  -- Hölder's inequality for the scalar datum.
  have hholder₁ := (Real.le_norm_self _).trans <|
    MeasureTheory.norm_integral_smul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow
      (r := q / 2) (by rw [← NNReal.coe_pos, hq2]; linarith) (by exact_mod_cast hs0)
      (by rw [hq2, inv_div, h2q]; linarith) hg hwLp (measure_ne_top ν A) hwA
  simp only [smul_eq_mul, hq2, inv_div] at hholder₁
  -- Hölder's inequality for the datum in divergence form.
  have hq2' : (2 : ℝ≥0∞) ≤ q := by
    have : (2 : ℝ≥0) ≤ q := by exact_mod_cast hq.le
    exact_mod_cast this
  have hint : Integrable (fun x => ‖F x‖ * ‖W1p.gradient w x‖) ν :=
    (hF.mono_exponent hq2').norm.integrable_mul (Lp.memLp _).norm
  have hinner : -∫ x in Omega, ⟪F x, W1p.gradient w x⟫ ∂mu ≤
      ∫ x in Omega, ‖F x‖ * ‖W1p.gradient w x‖ ∂mu := by
    refine (neg_le_abs _).trans ?_
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hint (ae_of_all _ fun x => norm_inner_le_norm _ _)
  have hholder₂ := (Real.le_norm_self _).trans <|
    MeasureTheory.norm_integral_smul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow (s := 2)
      (by exact_mod_cast hq0) two_pos
      (by rw [NNReal.coe_ofNat]; linarith [inv_anti₀ two_pos hq.le]) hF.norm
      (by simpa using (Lp.memLp (W1p.gradient w)).norm) (measure_ne_top ν A) hgA
  simp only [smul_eq_mul] at hholder₂
  rw [eLpNorm_norm _ hF.aestronglyMeasurable, eLpNorm_norm _ (Lp.aestronglyMeasurable _),
    ENNReal.coe_ofNat, ← Lp.norm_def, NNReal.coe_ofNat] at hholder₂
  -- Collect: `λ X² ≤ X (S G |A| ^ θ₁ + Fq |A| ^ θ₂)` with `X = ‖∇w‖`.
  set X := ‖W1p.gradient w‖
  set W := (eLpNorm (W1p.value w) s ν).toReal
  set Gq := (eLpNorm g (q / 2 : ℝ≥0) ν).toReal
  set Fq := (eLpNorm F q ν).toReal
  set mA := ν.real A
  set mΩ := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  set θ := 2⁻¹ - (q : ℝ)⁻¹
  set ρ := 2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹
  have hX : 0 ≤ X := norm_nonneg _
  have hmA : 0 ≤ mA := measureReal_nonneg
  have hmAΩ : mA ≤ mΩ := by
    refine (measureReal_mono (subset_univ _)).trans_eq ?_
    simp [ν, measureReal_def, mΩ]
  have hθ : 0 ≤ θ := by simp only [θ]; linarith
  have hexp₁ : 1 - 2 / (q : ℝ) - (s : ℝ)⁻¹ = θ + ρ := by
    simp only [θ, ρ]
    ring
  have hexp₂ : 1 - (q : ℝ)⁻¹ - 2⁻¹ = θ := by
    simp only [θ]
    ring
  rw [hexp₁] at hholder₁
  rw [hexp₂] at hholder₂
  have hsplit : mA ^ (θ + ρ) ≤ mA ^ θ * mΩ ^ ρ := by
    rw [Real.rpow_add' hmA (by linarith)]
    gcongr
  have hT : lam * X ^ 2 ≤ X * ((S * Gq * mΩ ^ ρ + Fq) * mA ^ θ) := by
    calc lam * X ^ 2 ≤ Gq * W * mA ^ (θ + ρ) + Fq * X * mA ^ θ :=
          henergy.trans (by linarith)
      _ ≤ Gq * (S * X) * (mA ^ θ * mΩ ^ ρ) + Fq * X * mA ^ θ := by
          gcongr
      _ = X * ((S * Gq * mΩ ^ ρ + Fq) * mA ^ θ) := by ring
  -- Cancel one factor of `X`.
  have hXle : X ≤ (S * Gq * mΩ ^ ρ + Fq) * mA ^ θ / lam := by
    rw [le_div_iff₀ hlam]
    rcases hX.eq_or_lt with hX0 | hXpos
    · rw [← hX0, zero_mul]
      positivity
    · nlinarith
  calc W ≤ S * X := hsobR
    _ ≤ S * ((S * Gq * mΩ ^ ρ + Fq) * mA ^ θ / lam) := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
/-- **Stampacchia's bound from the energy inequality of the truncations.** Let `Ω` have finite
measure and satisfy a Sobolev inequality `‖v‖_s ≤ S ‖∇v‖₂` on `W^{1,2}_0(Ω)`, let `q > 2` with
`s (1/2 - 1/q) > 1`, and let `g ∈ L^{q/2}(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`. Let `u ∈ H¹(Ω)` with
`(u - k)⁺ ∈ H¹₀(Ω)` for a level `k ≥ 0`, and suppose that at every level `l ≥ k` the truncation
`w = (u - l)⁺` satisfies

`λ ‖∇w‖² ≤ ∫_Ω g w - ∫_Ω ⟪F, ∇w⟫`.

Then almost everywhere in `Ω`

`u ≤ k + 2 ^ (β / (β - 1)) S (S ‖g‖_{q/2} |Ω| ^ ρ + ‖F‖_q) / λ · |Ω| ^ ρ`,

where `β = s (1/2 - 1/q)` and `ρ = 1/2 - 1/q - 1/s`. For a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ g + ∂ᵢFⁱ` with uniformly elliptic `a` and `c ≥ 0` the energy inequality is
the subsolution inequality tested against `w`; with a drift it holds above a level where the
drift term can be absorbed. -/
theorem ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le
    (hOmega : mu Omega ≠ ∞) {q s S : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqs : 1 < (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {lam : ℝ} (hlam : 0 < lam) {g : EuclideanSpace ℝ ι → ℝ}
    (hg : MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (henergy : ∀ l (hkl : k ≤ l),
      lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
        ∫ x in Omega, g x * W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x⟫
            ∂mu) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) / ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) - 1)) *
        (S * (S * (eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
            mu.real Omega ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) +
          (eLpNorm F q (mu.restrict Omega)).toReal) / lam) *
        mu.real Omega ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  have hs0 : 0 < s := by
    by_contra hs
    rw [nonpos_iff_eq_zero.1 (not_lt.1 hs), NNReal.coe_zero, zero_mul] at hqs
    norm_num at hqs
  have hbound := ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le hOmega hs0
    (div_nonneg (by positivity) hlam.le) hqs hk
    (fun l hkl => ((hS _ (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl
      hboundary)).trans_lt (by finiteness)).ne)
    (fun l hkl => toReal_eLpNorm_posPartAbove_le_of_mul_norm_gradient_sq_le hOmega hq hqs hS hlam
      hg hF hk hboundary hkl (henergy l hkl))
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  congr 3

omit [DecidableEq ι] in
/-- **Stampacchia's bound from the energy inequality of the truncations, in every dimension.**
Let `n ≥ 1` be the dimension and let `q > n` with `q > 2`. There is `C > 0`, depending only on
`n`, `q` and the normalization of the additive Haar measure `mu`, with the following property. Let
`Ω` have finite measure, let `λ > 0`, `g ∈ L^{q/2}(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)`
with `(u - k)⁺ ∈ H¹₀(Ω)` for a level `k ≥ 0`. If at every level `l ≥ k` the truncation
`w = (u - l)⁺` satisfies `λ ‖∇w‖² ≤ ∫_Ω g w - ∫_Ω ⟪F, ∇w⟫`, then almost everywhere in `Ω`

`u ≤ k + C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`.

Both terms are invariant under dilations of `Ω`. -/
theorem exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le [Nonempty ι]
    {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {lam : ℝ}
      {g : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ → 0 < lam →
      MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      (∀ l (hkl : k ≤ l),
        lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
          ∫ x in Omega, g x * W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x ∂mu -
            ∫ x in Omega,
              ⟪F x, W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x⟫ ∂mu) →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (((eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
            mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) +
          (eLpNorm F q (mu.restrict Omega)).toReal *
            mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹)) / lam) := by
  set n : ℕ := Fintype.card ι
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  -- The Sobolev exponent `s = (1/2 - δ)⁻¹`, with `1/q < δ < min (1/n) (1/2)`.
  obtain ⟨δ, hδ0, hδn, hδ2, hs, hqs⟩ := exists_sobolev_exponent (θ := (q : ℝ)⁻¹)
    (inv_nonneg.2 hq0.le) ((inv_lt_inv₀ hq0 hn0).2 hqn) ((inv_lt_inv₀ hq0 two_pos).2 hq)
  obtain ⟨K, hK, hsob⟩ :=
    exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow (mu := mu) hδ0 hδn hδ2
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  set E : ℝ := (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) / ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) - 1)
  refine ⟨2 ^ E * (K ^ 2 + K), by positivity, fun {Omega lam g F u k} hk hOmega hlam hg hF
    hboundary henergy => ?_⟩
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  have hm : 0 ≤ m := measureReal_nonneg
  set S : ℝ≥0 := Real.toNNReal (K * m ^ ((n : ℝ)⁻¹ - δ))
  have hSval : (S : ℝ) = K * m ^ ((n : ℝ)⁻¹ - δ) := Real.coe_toNNReal _ (by positivity)
  have hbound := ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le hOmega hq hqs
    (hsob hOmega) hlam hg hF hk hboundary henergy
  filter_upwards [hbound] with x hx
  refine hx.trans ?_
  -- `S |Ω| ^ ρ = K |Ω| ^ (1/n - 1/q)`, since `ρ = 1/2 - 1/q - 1/s = δ - 1/q`.
  have hρ : 2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹ = δ - (q : ℝ)⁻¹ := by
    rw [hs]
    ring
  have hne : (n : ℝ)⁻¹ - (q : ℝ)⁻¹ ≠ 0 := (sub_pos.2 ((inv_lt_inv₀ hq0 hn0).2 hqn)).ne'
  have hpow : (S : ℝ) * m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) = K * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
    have hsum : (n : ℝ)⁻¹ - δ + (δ - (q : ℝ)⁻¹) = (n : ℝ)⁻¹ - (q : ℝ)⁻¹ := by ring
    rw [hSval, hρ, mul_assoc, ← Real.rpow_add' hm (by rwa [hsum]), hsum]
  have hpow2 : (m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) ^ 2 = m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) := by
    rw [← Real.rpow_mul_natCast hm]
    ring_nf
  set Gq := (eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal
  set Fq := (eLpNorm F q (mu.restrict Omega)).toReal
  set P := m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)
  have hGq : 0 ≤ Gq := ENNReal.toReal_nonneg
  have hFq : 0 ≤ Fq := ENNReal.toReal_nonneg
  have hP : 0 ≤ P := by positivity
  calc k + 2 ^ E * (S * (S * Gq * m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) + Fq) / lam) *
        m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹)
      = k + 2 ^ E * ((Gq * ((S : ℝ) * m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹)) ^ 2 +
          Fq * ((S : ℝ) * m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹))) / lam) := by ring
    _ = k + 2 ^ E * ((K ^ 2 * (Gq * P ^ 2) + K * (Fq * P)) / lam) := by
        rw [hpow]
        ring
    _ ≤ k + 2 ^ E * (((K ^ 2 + K) * (Gq * P ^ 2 + Fq * P)) / lam) := by
        gcongr
        nlinarith [mul_nonneg hGq (sq_nonneg P), mul_nonneg hFq hP]
    _ = _ := by
        rw [hpow2]
        ring

/-! ### The scale-invariant bounds for a scalar right-hand side -/

/-- **Stampacchia's global bound with a small drift, in every dimension.** Let `n ≥ 1` be the
dimension and let `r > 1` with `r > n/2`. There is `C > 0`, depending only on `n`, `r` and the
normalization of the additive Haar measure `mu`, with the following property. Let `Ω` have finite
measure, let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b` be
measurable with `‖b‖ ≤ β`, let `c` be bounded, measurable and nonnegative, and let `f ∈ Lʳ(Ω)`.
Suppose that the drift is small on `H¹₀(Ω)`, `2β ‖v‖_{L²} ≤ λ ‖∇v‖_{L²}`, as it is when `2βP ≤ λ`
for a Poincaré constant `P` of `Ω`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ f` in `Ω`

with `u ≤ k` on `∂Ω` for a level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost
everywhere in `Ω`

`u ≤ k + C ‖f‖_{Lʳ(Ω)} / λ · |Ω| ^ (2/n - 1/r)`.

The bound is invariant under dilations of `Ω`. The Sobolev inequality behind it is the one on
sets of finite measure, `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`,
which holds in every dimension; the small drift is absorbed by Gårding's inequality
(`TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sq_le_energyFormH1_self_of_small_drift`). -/
theorem exists_ae_value_le_add_mul_div_mul_rpow_drift [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v ∈ w1p0Submodule mu Omega 2, 2 * beta * ‖W1p.value v‖ ≤ lam * ‖W1p.gradient v‖) →
      MemLp f r (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹) := by
  -- This is the case `q = 2r`, `F = 0` of the bound from the energy inequality of the
  -- truncations, with the coercivity constant `λ/4` that a small drift leaves.
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le (mu := mu) (q := 2 * r)
      (by push_cast; linarith) (by push_cast; exact hrn)
  have hr2 : 2 * r / 2 = r := mul_div_cancel_left₀ r two_ne_zero
  refine ⟨4 * C, by positivity, fun {Omega a b c lam Lam beta gamma f u k} hk hOmega h
    ha hb hc hb_bound hc_bound hc_nonneg hsmall hf hu hboundary => ?_⟩
  have hlam := h.pos
  -- The energy form is coercive on `H¹₀(Ω)` with constant `λ/4`.
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  have hbound := hmain hk hOmega (by positivity : 0 < lam / 4) (F := 0) (by rwa [hr2]) MemLp.zero
    hboundary fun l hkl => by
      simpa only [Pi.zero_apply, inner_zero_left, integral_zero, sub_zero] using
        mul_norm_gradient_posPartAbove_sq_le hcoeff hc_nonneg
          (fun v hv => h.mul_norm_gradient_sq_le_energyFormH1_self_of_small_drift ha hb hc hb_bound
            hc_bound hc_nonneg (hsmall v hv)) hu hk hboundary hkl
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  rw [hr2, eLpNorm_zero, ENNReal.toReal_zero, zero_mul, add_zero, NNReal.coe_mul,
    NNReal.coe_ofNat, div_mul_cancel_left₀ two_ne_zero]
  field_simp

/-- **Global boundedness of weak Dirichlet solutions with a small drift, in every dimension.** Let
`n ≥ 1` be the dimension and let `r > 1` with `r > n/2`. There is `C > 0`, depending only on `n`,
`r` and the normalization of `mu`, such that on every `Ω` of finite measure, for measurable,
uniformly elliptic `a` with constants `0 < λ ≤ Λ`, measurable `b` with `‖b‖ ≤ β`, small on
`H¹₀(Ω)` in the sense that `2β ‖v‖_{L²} ≤ λ ‖∇v‖_{L²}`, and bounded, measurable, nonnegative `c`,
the weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` with
`f ∈ Lʳ(Ω)`, that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, satisfies, almost everywhere in
`Ω`,

`|u| ≤ C ‖f‖_{Lʳ(Ω)} / λ · |Ω| ^ (2/n - 1/r)`.

This is the two-sided form of `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow_drift` at the
level `k = 0`, applied to `u` and to `-u`. -/
theorem exists_ae_abs_value_le_mul_div_mul_rpow_drift [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p0 mu Omega 2},
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v ∈ w1p0Submodule mu Omega 2, 2 * beta * ‖W1p.value v‖ ≤ lam * ‖W1p.gradient v‖) →
      MemLp f r (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∀ᵐ x ∂mu.restrict Omega, |W1p.value (u : W1p mu Omega 2) x| ≤
        C * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹) := by
  obtain ⟨C, hC, hmain⟩ := exists_ae_value_le_add_mul_div_mul_rpow_drift (mu := mu) hr hrn
  refine ⟨C, hC, fun {Omega a b c lam Lam beta gamma f u} hOmega h ha hb hc hb_bound hc_bound
    hc_nonneg hsmall hf hsol => ?_⟩
  -- The bound from above for `u`, and for `-u`, a weak solution with forcing `-f`.
  have hup := hmain (u := (u : W1p mu Omega 2)) le_rfl hOmega h ha hb hc hb_bound hc_bound
    hc_nonneg hsmall hf (fun v _ => (hsol v).le)
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl u.property)
  have hlo := hmain (u := -(u : W1p mu Omega 2)) (f := fun x => -f x) le_rfl hOmega h ha hb hc
    hb_bound hc_bound hc_nonneg hsmall hf.neg (fun v _ => by
      rw [← neg_one_smul ℝ (u : W1p mu Omega 2), energyFormH1_smul_left, hsol v]
      simp only [neg_mul, integral_neg, one_mul, le_refl])
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl (-u).property)
  have hnorm : eLpNorm (fun x => -f x) r (mu.restrict Omega) = eLpNorm f r (mu.restrict Omega) :=
    eLpNorm_neg _ _ _
  rw [hnorm] at hlo
  simpa only [zero_add] using (W1p.ae_abs_value_le_iff subset_rfl).2 ⟨hup, hlo⟩

open Metric in
/-- **The Dirichlet problem with a small drift on a ball.** On `B = B(x₀, ρ)` with `2βρ ≤ λ`, the
Poincaré inequality `‖v‖_{L²} ≤ ρ ‖∇v‖_{L²}` on `H¹₀(B)`, taken as the hypothesis `hpoinc` and
supplied by `TauCeti.W1p.norm_value_le_mul_norm_gradient_of_eq_ball`, makes the energy form of
`-∂ᵢ(aⁱʲ ∂ⱼ·) + bⁱ ∂ᵢ` coercive on `H¹₀(B)`
(`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare`), so Lax--Milgram
gives a weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) + bⁱ ∂ᵢw = f` for every `f ∈ Lʳ(B)` with
`r > max 1 (2n/(n + 2))`. -/
private theorem exists_forall_energyFormH1_eq_setIntegral_ball_drift [Nonempty ι] {r : ℝ≥0}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {lam Lam beta : ℝ} {f : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ}
    (h : UniformlyEllipticOn (ball x₀ ρ) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict (ball x₀ ρ)))
    (hb : AEStronglyMeasurable b (mu.restrict (ball x₀ ρ)))
    (hb_bound : ∀ x ∈ ball x₀ ρ, ‖b x‖ ≤ beta) (hbeta : 0 ≤ beta)
    (hsmall : 2 * beta * ρ ≤ lam) (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) * (2 - r) < 2 * r)
    (hf : MemLp f r (mu.restrict (ball x₀ ρ))) (hρ : 0 ≤ ρ)
    (hpoinc : ∀ v ∈ w1p0Submodule mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
      ‖W1p.value v‖ ≤ ρ * ‖W1p.gradient v‖) :
    ∃ w : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
      ∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        energyFormH1 a b 0 (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2)
            (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) =
          ∫ x in ball x₀ ρ, f x * W1p.value (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x ∂mu := by
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hcoeff := memLp_energyIntegrand_of_bounds (Omega := B) (c := 0) (gamma := 0)
    h.upper_nonneg ha hb aestronglyMeasurable_const (fun x hx eta xi => h.upper_bound hx eta xi)
    hb_bound (fun _ _ => by simp)
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have hcoer : IsCoercive (energyFormH1L0 hcoeff) :=
    isCoercive_energyFormH1L0 hcoeff
      (energyFormH1_poincare_constant_pos hbeta hρ (by linarith [h.pos])) fun w =>
        h.mul_norm_sq_le_energyFormH1_self_of_poincare (Omega := B) ha hb
          aestronglyMeasurable_const hb_bound (gamma := 0) (fun _ _ => by simp)
          (fun _ _ => le_rfl) (hpoinc w w.property)
  obtain ⟨ℓ, hℓ⟩ := W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp hBfin hr
    (by rwa [finrank_euclideanSpace]) hf
  obtain ⟨w, ⟨hw0, hw⟩, -⟩ :=
    existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq hcoeff hcoer 0 ℓ
  rw [sub_zero] at hw0
  exact ⟨⟨w, hw0⟩, fun v => (hw v).trans (hℓ v)⟩

open Metric in
/-- **Stampacchia's bound on a ball with a small drift.** Let `n ≥ 1` be the dimension and let
`r > 1` with `r > n/2`. There is `K > 0`, depending only on `n`, `r` and the normalization of
`mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on
`B = B(x₀, ρ)` with constants `λ, Λ`, let `b` be measurable with `‖b‖ ≤ β` on `B` and `2βρ ≤ λ`,
and let `f ∈ Lʳ(B)`. Then there is a weak solution `w ∈ H¹₀(B)` of the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼw) + bⁱ ∂ᵢw = f` in `B`, that is `a(w, v) = ∫_B f v` for every `v ∈ H¹₀(B)`, with

`|w| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` almost everywhere on `B`.

The smallness `2βρ ≤ λ` makes the drift small against the Poincaré constant `ρ` of the ball
(`TauCeti.W1p.norm_value_le_mul_norm_gradient_of_eq_ball`), so the energy form is coercive on
`H¹₀(B)` (`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare`) and
Lax--Milgram gives `w`; the bound is
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_drift` on the ball, where
`|B|^(2/n - 1/r)` is a multiple of `ρ^(2 - n/r)`. -/
theorem exists_forall_energyFormH1_eq_setIntegral_ae_abs_le_drift [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {lam Lam beta : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (ball x₀ ρ) a lam Lam → AEStronglyMeasurable a (mu.restrict (ball x₀ ρ)) →
      AEStronglyMeasurable b (mu.restrict (ball x₀ ρ)) → (∀ x ∈ ball x₀ ρ, ‖b x‖ ≤ beta) →
      2 * beta * ρ ≤ lam → MemLp f r (mu.restrict (ball x₀ ρ)) → 0 < ρ →
      ∃ w : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a b 0 (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2)
              (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) =
            ∫ x in ball x₀ ρ, f x * W1p.value (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x ∂mu) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x| ≤
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrn' : n * (2 - r) < 2 * r := mul_two_sub_lt_two_mul_of_lt_two_mul hn.le hr1 hrn
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_drift (mu := mu) hr hrn
  set e : ℝ := 2 / n - (r : ℝ)⁻¹
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e,
    mul_pos hC (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos) _), ?_⟩
  intro a b lam Lam beta f x₀ ρ h ha hb hb_bound hsmall hf hρ
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ (mem_ball_self hρ))
  -- The Poincaré inequality `‖v‖_{L²} ≤ ρ ‖∇v‖_{L²}` on `H¹₀(B)` makes the drift small.
  have hpoinc : ∀ v ∈ w1p0Submodule mu B 2, ‖W1p.value v‖ ≤ ρ * ‖W1p.gradient v‖ :=
    fun v hv => W1p.norm_value_le_mul_norm_gradient_of_eq_ball hρ rfl hv
  have hsmallB : ∀ v ∈ w1p0Submodule mu B 2,
      2 * beta * ‖W1p.value v‖ ≤ lam * ‖W1p.gradient v‖ := fun v hv => by
    calc 2 * beta * ‖W1p.value v‖ ≤ 2 * beta * (ρ * ‖W1p.gradient v‖) := by
          gcongr
          exact hpoinc v hv
      _ = 2 * beta * ρ * ‖W1p.gradient v‖ := by ring
      _ ≤ lam * ‖W1p.gradient v‖ := by gcongr
  obtain ⟨w, hw⟩ := exists_forall_energyFormH1_eq_setIntegral_ball_drift h ha hb hb_bound hbeta
    hsmall hr hrn' hf hρ.le hpoinc
  refine ⟨w, hw, ?_⟩
  -- `|B|^e = ρ^(n e) |B(0, 1)|^e`, with `n e = 2 - n/r`.
  have hmeas : mu.real (ball x₀ ρ) ^ e =
      ρ ^ (2 - n / r) * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e := by
    rw [Measure.addHaar_real_ball_rpow _ _ hρ, finrank_euclideanSpace]
    congr 2
    simp only [e, n]
    field_simp
  filter_upwards [hstamp (Omega := B) (c := 0) (gamma := 0) hBfin h ha hb
    aestronglyMeasurable_const hb_bound (fun _ _ => by simp) (fun _ _ => le_rfl) hsmallB hf
    hw] with x hx
  refine hx.trans_eq ?_
  simp only [B, Opens.coe_mk]
  rw [hmeas]
  ring

open Metric in
/-- **Stampacchia's bound on a ball.** Let `n ≥ 1` be the dimension and let `r > 1` with
`r > n/2`. There is `K > 0`, depending only on `n`, `r` and the normalization of `mu`, such that
the following holds. Let `a` be measurable and uniformly elliptic on `B = B(x₀, ρ)` with constants
`λ, Λ`, and let `f ∈ Lʳ(B)`. Then there is a weak solution `w ∈ H¹₀(B)` of the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼw) = f` in `B`, that is `a(w, v) = ∫_B f v` for every `v ∈ H¹₀(B)`, with

`|w| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` almost everywhere on `B`.

This is the case `b = 0` of `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_ae_abs_le_drift`.
-/
theorem exists_forall_energyFormH1_eq_setIntegral_ae_abs_le [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (ball x₀ ρ) a lam Lam → AEStronglyMeasurable a (mu.restrict (ball x₀ ρ)) →
      MemLp f r (mu.restrict (ball x₀ ρ)) → 0 < ρ →
      ∃ w : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2)
              (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) =
            ∫ x in ball x₀ ρ, f x * W1p.value (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x ∂mu) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x| ≤
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  obtain ⟨K, hK, hmain⟩ :=
    exists_forall_energyFormH1_eq_setIntegral_ae_abs_le_drift (mu := mu) hr hrn
  exact ⟨K, hK, fun h ha hf hρ => hmain (b := 0) (beta := 0) h ha aestronglyMeasurable_const
    (fun _ _ => by simp) (by simpa using h.pos.le) hf hρ⟩


/-! ### A right-hand side in divergence form -/

/-- **Stampacchia's global bound for a right-hand side in divergence form.** Let `Ω` have finite
measure, let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let
`c` be bounded, measurable and nonnegative. Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev
inequality `‖v‖_{Lˢ} ≤ S ‖∇v‖_{L²}`, and let `F ∈ L^q(Ω; ℝⁿ)` with `q ≥ 2` and
`s (1/2 - 1/q) > 1`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` in `Ω`,

that is `a(u, v) ≤ -∫_Ω F · ∇v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a
level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + 2 ^ (β / (β - 1)) S ‖F‖_{L^q} / λ · |Ω| ^ (1/2 - 1/q - 1/s)`, where
`β = s (1/2 - 1/q)`.

No regularity of `∂Ω` or of the coefficients beyond measurability is needed. -/
theorem UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le_divergence
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {q s S : ℝ≥0} (hq : 2 ≤ (q : ℝ))
    (hqs : 1 < (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) / ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) - 1)) * S *
        (eLpNorm F q (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  -- This is the case `g = 0` of the bound from the energy inequality of the truncations.
  have hq' : 2 < (q : ℝ) := by
    refine hq.lt_of_ne fun hq2 => ?_
    rw [← hq2] at hqs
    norm_num at hqs
  -- Without a drift, ellipticity makes the energy form coercive with constant `λ`.
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (beta := 0) h.upper_nonneg ha
    aestronglyMeasurable_const hc (fun x hx eta xi => h.upper_bound hx eta xi)
    (fun _ _ => by simp) hc_bound
  have hκ : ∀ v ∈ w1p0Submodule mu Omega 2, lam * ‖W1p.gradient v‖ ^ 2 ≤
      energyFormH1 a 0 c v v := fun v _ =>
    h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha hc (fun _ _ => rfl) hc_bound
      hc_nonneg v
  have hbound := ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le hOmega hq' hqs hS
    h.pos (g := 0) MemLp.zero hF hk hboundary fun l hkl => by
      simpa only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] using
        mul_norm_gradient_posPartAbove_sq_le hcoeff hc_nonneg hκ hu hk hboundary hkl
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  rw [eLpNorm_zero, ENNReal.toReal_zero, mul_zero, zero_mul, zero_add]
  ring

/-- **Stampacchia's global bound for a right-hand side in divergence form, in every dimension.**
Let `n ≥ 1` be the dimension and let `q > n` with `q > 2`. There is `C > 0`, depending only on
`n`, `q` and the normalization of the additive Haar measure `mu`, with the following property.
Let `Ω` have finite measure, let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `c` be bounded, measurable and nonnegative, and let `F ∈ L^q(Ω; ℝⁿ)`. If
`u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` in `Ω`

with `u ≤ k` on `∂Ω` for a level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost
everywhere in `Ω`

`u ≤ k + C ‖F‖_{L^q(Ω)} / λ · |Ω| ^ (1/n - 1/q)`.

The bound is invariant under dilations of `Ω`; on a ball of radius `ρ` the factor
`|Ω| ^ (1/n - 1/q)` is a multiple of the Morrey gain `ρ ^ (1 - n/q)`. The condition `q > 2`
matters only for `n = 1`; it comes from the Sobolev exponents `s = (1/2 - δ)⁻¹`, `δ < 1/2`, which
the method needs to satisfy `s (1/2 - 1/q) > 1`. -/
theorem exists_ae_value_le_add_mul_div_mul_rpow_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (eLpNorm F q (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
  -- This is the case `g = 0` of the bound from the energy inequality of the truncations.
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le (mu := mu) hq hqn
  refine ⟨C, hC, fun {Omega a c lam Lam gamma F u k} hk hOmega h ha hc hc_bound hc_nonneg hF hu
    hboundary => ?_⟩
  -- Without a drift, ellipticity makes the energy form coercive with constant `λ`.
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (beta := 0) h.upper_nonneg ha
    aestronglyMeasurable_const hc (fun x hx eta xi => h.upper_bound hx eta xi)
    (fun _ _ => by simp) hc_bound
  have hκ : ∀ v ∈ w1p0Submodule mu Omega 2, lam * ‖W1p.gradient v‖ ^ 2 ≤
      energyFormH1 a 0 c v v := fun v _ =>
    h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha hc (fun _ _ => rfl) hc_bound
      hc_nonneg v
  have hbound := hmain hk hOmega h.pos (g := 0) MemLp.zero hF hboundary fun l hkl => by
    simpa only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] using
      mul_norm_gradient_posPartAbove_sq_le hcoeff hc_nonneg hκ hu hk hboundary hkl
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  rw [eLpNorm_zero, ENNReal.toReal_zero, zero_mul, zero_add]
  ring

/-- **Global boundedness of weak Dirichlet solutions with a right-hand side in divergence form,
in every dimension.** Let `n ≥ 1` be the dimension and let `q > n` with `q > 2`. There is
`C > 0`, depending only on `n`, `q` and the normalization of `mu`, such that on every `Ω` of
finite measure, for measurable, uniformly elliptic `a` with constants `0 < λ ≤ Λ` and bounded,
measurable, nonnegative `c`, the weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = ∂ᵢFⁱ` with `F ∈ L^q(Ω; ℝⁿ)`, that is `a(u, v) = -∫_Ω F · ∇v` for every
`v ∈ H¹₀(Ω)`, satisfies, almost everywhere in `Ω`,

`|u| ≤ C ‖F‖_{L^q(Ω)} / λ · |Ω| ^ (1/n - 1/q)`.

This is the two-sided form of `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow_divergence` at
the level `k = 0`, applied to `u` and to `-u`. -/
theorem exists_ae_abs_value_le_mul_div_mul_rpow_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2},
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        energyFormH1 a 0 c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      ∀ᵐ x ∂mu.restrict Omega, |W1p.value (u : W1p mu Omega 2) x| ≤
        C * (eLpNorm F q (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
  obtain ⟨C, hC, hmain⟩ := exists_ae_value_le_add_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  refine ⟨C, hC, fun {Omega a c lam Lam gamma F u} hOmega h ha hc hc_bound hc_nonneg hF hsol => ?_⟩
  -- The bound from above for `u`, and for `-u`, a weak solution with datum `-F`.
  have hup := hmain (u := (u : W1p mu Omega 2)) le_rfl hOmega h ha hc hc_bound hc_nonneg hF
    (fun v _ => (hsol v).le) (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl u.property)
  have hlo := hmain (u := -(u : W1p mu Omega 2)) (F := fun x => -F x) le_rfl hOmega h ha hc
    hc_bound hc_nonneg hF.neg (fun v _ => by
      rw [← neg_one_smul ℝ (u : W1p mu Omega 2), energyFormH1_smul_left, hsol v]
      simp only [inner_neg_left, integral_neg, neg_mul, one_mul, le_refl])
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl (-u).property)
  have hnorm : eLpNorm (fun x => -F x) q (mu.restrict Omega) = eLpNorm F q (mu.restrict Omega) :=
    eLpNorm_neg _ _ _
  rw [hnorm] at hlo
  simpa only [zero_add] using (W1p.ae_abs_value_le_iff subset_rfl).2 ⟨hup, hlo⟩

end TauCeti.PDE
