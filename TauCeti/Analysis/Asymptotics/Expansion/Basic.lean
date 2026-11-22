/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Asymptotic scales and Poincaré asymptotic expansions

This file introduces asymptotic scales (`Asymptotics.IsAsymptoticScale`) and asymptotic expansions
with respect to a scale (`Asymptotics.HasAsymptoticExpansion`), together with their basic API and
the theory of Poincaré asymptotic expansions at infinity and at finite points (NIST DLMF §2.1).

An asymptotic scale along a filter `l` is a sequence `phi : ℕ → α → 𝕜` such that
`phi (n + 1) =o[l] phi n` for every `n`. A function `f : α → E` admits the asymptotic expansion
`∑ φₙ • aₙ` along `l` when every truncated remainder `f - ∑_{n < N} φₙ • aₙ` is `O(φ_N)` along `l`.
When `phi` is an asymptotic scale, this is equivalent to each remainder after `N + 1` terms being
`o(φ_N)`, and when each `phi n` is frequently nonzero along `l`, the coefficient sequence `a` is
uniquely determined by `f`. In contrast, distinct functions can share the same asymptotic
expansion: for instance, `0`, `exp (-z)`, and `exp (-z^(1/2))` all share the zero Poincaré
expansion in `(z ^ n)⁻¹` in any closed sector `|arg z| ≤ π / 2 - δ` with `δ > 0`.

## Main definitions

* `Asymptotics.IsAsymptoticScale`: a sequence `phi : ℕ → α → 𝕜` with `phi (n + 1) =o[l] phi n`
  for all `n` (DLMF 2.1.19).
* `Asymptotics.HasAsymptoticExpansion`: `f - ∑_{n < N} φₙ • aₙ =O[l] φ_N` for all `N`
  (DLMF 2.1.13, 2.1.20).

## Main results

* `Asymptotics.hasAsymptoticExpansion_iff_isLittleO`: equivalence with `o(φ_N)` remainders after
  `N + 1` terms when `phi` is an asymptotic scale.
* `Asymptotics.hasAsymptoticExpansion_iff_tendsto`: ratio-limit characterization when `phi n` is
  eventually nonzero.
* `Asymptotics.HasAsymptoticExpansion.unique`: uniqueness of coefficients for an asymptotic scale
  whose terms are frequently nonzero along `l`.
* `Asymptotics.hasAsymptoticExpansion_inv_pow_iff`: DLMF 2.1.15 characterization of Poincaré
  expansions at infinity.
* `Asymptotics.hasAsymptoticExpansion_of_hasSum`: a series `∑ (z ^ s)⁻¹ • a s` converging outside
  a ball is the Poincaré expansion of its sum along `Bornology.cobounded`.
* `HasFPowerSeriesAt.hasAsymptoticExpansion`: a convergent power series at `c` is the
  Poincaré expansion of its sum along `𝓝 c`.
* `Asymptotics.hasAsymptoticExpansion_zero_cexp_neg_sector` and
  `Asymptotics.hasAsymptoticExpansion_zero_cexp_neg_sqrt_sector`: DLMF 2.1.17 non-uniqueness of
  the function with a given Poincaré expansion in a closed right half-plane sector.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1, <https://dlmf.nist.gov/2.1>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1.
-/

public section

open Filter Topology Finset Set
open scoped Real

namespace Asymptotics

/-! ### Definitions -/

section Defs

variable {α 𝕜 E : Type*}

/-- An asymptotic scale along a filter `l` (DLMF 2.1.19): each scale function is little-o of the
previous one. -/
def IsAsymptoticScale [Norm 𝕜] (l : Filter α) (phi : ℕ → α → 𝕜) : Prop :=
  ∀ n, phi (n + 1) =o[l] phi n

/-- Definition of `IsAsymptoticScale`. -/
theorem isAsymptoticScale_iff [Norm 𝕜] {l : Filter α} {phi : ℕ → α → 𝕜} :
    IsAsymptoticScale l phi ↔ ∀ n, phi (n + 1) =o[l] phi n :=
  .rfl

/-- The asymptotic expansion `f ~ ∑ φₙ • aₙ` along `l` (DLMF 2.1.13, 2.1.20): for every `N`, the
remainder after `N` terms is `O(φ_N)` along `l`. -/
def HasAsymptoticExpansion [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    (l : Filter α) (phi : ℕ → α → 𝕜) (a : ℕ → E) (f : α → E) : Prop :=
  ∀ N, (fun x => f x - ∑ n ∈ range N, phi n x • a n) =O[l] phi N

/-- Definition of `HasAsymptoticExpansion`. -/
theorem hasAsymptoticExpansion_iff [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E} :
    HasAsymptoticExpansion l phi a f ↔
      ∀ N, (fun x => f x - ∑ n ∈ range N, phi n x • a n) =O[l] phi N :=
  .rfl

end Defs

/-! ### API for `IsAsymptoticScale` -/

section Scale

variable {α β 𝕜 : Type*}

theorem IsAsymptoticScale.isLittleO_succ [Norm 𝕜] {l : Filter α} {phi : ℕ → α → 𝕜}
    (h : IsAsymptoticScale l phi) (n : ℕ) : phi (n + 1) =o[l] phi n :=
  h n

theorem IsAsymptoticScale.isLittleO_of_lt [Norm 𝕜] {l : Filter α} {phi : ℕ → α → 𝕜}
    (h : IsAsymptoticScale l phi) {m n : ℕ} (hmn : m < n) : phi n =o[l] phi m := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero _)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | rfl
    · exact (h.isLittleO_succ n).trans (ih hlt)
    · exact h.isLittleO_succ m

theorem IsAsymptoticScale.isBigO_of_le [Norm 𝕜] {l : Filter α} {phi : ℕ → α → 𝕜}
    (h : IsAsymptoticScale l phi) {m n : ℕ} (hmn : m ≤ n) : phi n =O[l] phi m := by
  rcases hmn.eq_or_lt with rfl | hlt
  · exact isBigO_refl _ _
  · exact (h.isLittleO_of_lt hlt).isBigO

theorem IsAsymptoticScale.mono [Norm 𝕜] {l l' : Filter α} {phi : ℕ → α → 𝕜}
    (h : IsAsymptoticScale l phi) (hle : l' ≤ l) : IsAsymptoticScale l' phi :=
  fun n => (h n).mono hle

theorem IsAsymptoticScale.comp_tendsto [Norm 𝕜] {l : Filter α} {l' : Filter β}
    {phi : ℕ → α → 𝕜} {g : β → α} (h : IsAsymptoticScale l phi) (hg : Tendsto g l' l) :
    IsAsymptoticScale l' (fun n x => phi n (g x)) :=
  fun n => (h n).comp_tendsto hg

theorem IsAsymptoticScale.congr [Norm 𝕜] {l : Filter α} {phi psi : ℕ → α → 𝕜}
    (h : IsAsymptoticScale l phi) (hfg : ∀ n, phi n =ᶠ[l] psi n) :
    IsAsymptoticScale l psi :=
  fun n => (h n).congr' (hfg (n + 1)) (hfg n)

theorem IsAsymptoticScale.mul_left [NormedRing 𝕜] [NormMulClass 𝕜] {l : Filter α}
    {phi : ℕ → α → 𝕜} (h : IsAsymptoticScale l phi) (g : α → 𝕜) :
    IsAsymptoticScale l (fun n x => g x * phi n x) :=
  fun n => (isBigO_refl g l).mul_isLittleO (h n)

theorem IsAsymptoticScale.const_mul [NormedDivisionRing 𝕜] {l : Filter α}
    {phi : ℕ → α → 𝕜} {κ : ℕ → 𝕜} (h : IsAsymptoticScale l phi) (hκ : ∀ n, κ n ≠ 0) :
    IsAsymptoticScale l (fun n x => κ n * phi n x) :=
  fun n => ((h n).const_mul_left (κ (n + 1))).const_mul_right (hκ n)

/-- Powers `w x ^ n` of a function `w` tending to `0` form an asymptotic scale. -/
theorem isAsymptoticScale_pow [NormedDivisionRing 𝕜] {l : Filter α} {w : α → 𝕜}
    (hw : Tendsto w l (𝓝 0)) : IsAsymptoticScale l (fun n x => w x ^ n) :=
  fun n => (isLittleO_pow_pow (Nat.lt_succ_self n)).comp_tendsto hw

/-- The inverse-power scale `z ↦ (z ^ n)⁻¹` at infinity in a subset `X`. -/
theorem isAsymptoticScale_inv_pow_cobounded [NormedDivisionRing 𝕜] (X : Set 𝕜) :
    IsAsymptoticScale (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) := by
  have hw : Tendsto (Inv.inv : 𝕜 → 𝕜) (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 0) :=
    (Filter.tendsto_inv₀_cobounded (α := 𝕜)).mono_left inf_le_left
  exact (isAsymptoticScale_pow hw).congr fun n =>
    Eventually.of_forall fun z => by simp [inv_pow]

/-- The inverse-power scale `x ↦ (x ^ n)⁻¹` along `atTop` on `ℝ`. -/
theorem isAsymptoticScale_inv_pow_atTop :
    IsAsymptoticScale atTop (fun n (x : ℝ) => (x ^ n)⁻¹) := by
  have hw : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  exact (isAsymptoticScale_pow hw).congr fun n =>
    Eventually.of_forall fun x => by simp [inv_pow]

/-- The power scale `z ↦ (z - c) ^ n` near a finite point `c` within a subset `X`
(DLMF 2.1.16). -/
theorem isAsymptoticScale_sub_pow_nhdsWithin [NormedDivisionRing 𝕜] (X : Set 𝕜) (c : 𝕜) :
    IsAsymptoticScale (𝓝[X] c) (fun n z => (z - c) ^ n) := by
  have hw : Tendsto (fun z : 𝕜 => z - c) (𝓝[X] c) (𝓝 0) := by
    have h : Tendsto (fun z : 𝕜 => z - c) (𝓝 c) (𝓝 0) := by
      simpa using (continuous_sub_right c).tendsto c
    exact h.mono_left nhdsWithin_le_nhds
  exact isAsymptoticScale_pow hw

end Scale

/-! ### API for `HasAsymptoticExpansion` -/

section Expansion

variable {α β 𝕜 E : Type*}

theorem HasAsymptoticExpansion.isBigO [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (N : ℕ) :
    (fun x => f x - ∑ n ∈ range N, phi n x • a n) =O[l] phi N :=
  hf N

/-- For an asymptotic scale, the remainder after `N + 1` terms is `o(φ_N)`. -/
theorem HasAsymptoticExpansion.isLittleO [SeminormedAddCommGroup 𝕜] [SeminormedAddCommGroup E]
    [SMul 𝕜 E] {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hphi : IsAsymptoticScale l phi) (N : ℕ) :
    (fun x => f x - ∑ n ∈ range (N + 1), phi n x • a n) =o[l] phi N :=
  (hf.isBigO (N + 1)).trans_isLittleO (hphi.isLittleO_succ N)

/-- For an asymptotic scale, having an asymptotic expansion is equivalent to every remainder after
`N + 1` terms being `o(φ_N)`. -/
theorem hasAsymptoticExpansion_iff_isLittleO [SeminormedRing 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hphi : IsAsymptoticScale l phi) :
    HasAsymptoticExpansion l phi a f ↔
      ∀ N, (fun x => f x - ∑ n ∈ range (N + 1), phi n x • a n) =o[l] phi N := by
  refine ⟨fun hf => hf.isLittleO hphi, fun h N => ?_⟩
  have hterm : (fun x => phi N x • a N) =O[l] phi N :=
    IsBigO.of_bound ‖a N‖ <| Eventually.of_forall fun x => by
      rw [mul_comm]
      exact norm_smul_le (phi N x) (a N)
  have hsum := (h N).isBigO.add hterm
  refine hsum.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  rw [sum_range_succ, sub_add_eq_sub_sub, sub_add_cancel]

/-- Ratio-limit characterization of an asymptotic expansion when the scale functions are eventually
nonzero along `l`. -/
theorem hasAsymptoticExpansion_iff_tendsto [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hphi : IsAsymptoticScale l phi) (hne : ∀ n, ∀ᶠ x in l, phi n x ≠ 0) :
    HasAsymptoticExpansion l phi a f ↔
      ∀ n, Tendsto (fun x => (phi n x)⁻¹ • (f x - ∑ s ∈ range n, phi s x • a s))
        l (𝓝 (a n)) := by
  rw [hasAsymptoticExpansion_iff_isLittleO hphi]
  refine forall_congr' fun n => ?_
  rw [← isLittleO_norm_left, ← isLittleO_norm_right,
    isLittleO_iff_tendsto' ((hne n).mono fun x hx h => absurd (norm_eq_zero.mp h) hx)]
  conv_rhs => rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_congr' ((hne n).mono fun x hx => ?_)
  dsimp only
  have hrew : (phi n x)⁻¹ • (f x - ∑ s ∈ range n, phi s x • a s) - a n =
      (phi n x)⁻¹ • (f x - ∑ s ∈ range (n + 1), phi s x • a s) := by
    conv_rhs => rw [sum_range_succ, sub_add_eq_sub_sub, smul_sub, inv_smul_smul₀ hx]
  rw [hrew, norm_smul, norm_inv, div_eq_inv_mul]

theorem HasAsymptoticExpansion.mono [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l l' : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hle : l' ≤ l) :
    HasAsymptoticExpansion l' phi a f :=
  fun N => (hf N).mono hle

theorem HasAsymptoticExpansion.comp_tendsto [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l : Filter α} {l' : Filter β} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E} {g : β → α}
    (hf : HasAsymptoticExpansion l phi a f) (hg : Tendsto g l' l) :
    HasAsymptoticExpansion l' (fun n x => phi n (g x)) a (f ∘ g) :=
  fun N => (hf N).comp_tendsto hg

theorem HasAsymptoticExpansion.congr_fun [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f g : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hfg : f =ᶠ[l] g) :
    HasAsymptoticExpansion l phi a g :=
  fun N => (hf N).congr' (hfg.mono fun _ hx => by dsimp only; rw [hx]) EventuallyEq.rfl

theorem HasAsymptoticExpansion.congr_coeff [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a b : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hab : ∀ n, a n = b n) :
    HasAsymptoticExpansion l phi b f := by
  have hba : b = a := funext fun n => (hab n).symm
  rwa [hba]

theorem HasAsymptoticExpansion.congr_scale [Norm 𝕜] [SeminormedAddCommGroup E] [SMul 𝕜 E]
    {l : Filter α} {phi psi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hfg : ∀ n, phi n =ᶠ[l] psi n) :
    HasAsymptoticExpansion l psi a f := by
  intro N
  have hfin : ∀ᶠ x in l, ∀ n ∈ range N, phi n x = psi n x :=
    (eventually_all_finset (range N)).mpr fun n _ => hfg n
  refine (hf N).congr' (hfin.mono fun x hx => ?_) (hfg N)
  dsimp only
  congr 1
  exact sum_congr rfl fun n hn => by rw [hx n hn]

/-- Rescaling the scale functions `φ n =ᶠ[l] κ n * ψ n` multiplies the expansion coefficients
by `κ n`. -/
theorem HasAsymptoticExpansion.rescale_scale [SeminormedCommRing 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] {l : Filter α} {phi psi : ℕ → α → 𝕜} {κ : ℕ → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f)
    (hκ : ∀ n, phi n =ᶠ[l] fun x => κ n * psi n x) :
    HasAsymptoticExpansion l psi (fun n => κ n • a n) f := by
  intro N
  have hfin : ∀ᶠ x in l, ∀ n ∈ range N, phi n x = κ n * psi n x :=
    (eventually_all_finset (range N)).mpr fun n _ => hκ n
  have h1 : (fun x => f x - ∑ n ∈ range N, psi n x • (κ n • a n)) =O[l] phi N := by
    refine (hf N).congr' (hfin.mono fun x hx => ?_) EventuallyEq.rfl
    dsimp only
    congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [hx n hn, mul_comm, mul_smul]
  have h2 : phi N =O[l] psi N :=
    IsBigO.of_bound ‖κ N‖ <| (hκ N).mono fun x hx => by
      rw [hx]
      exact norm_mul_le _ _
  exact h1.trans h2

/-- The zero function has the zero expansion in any scale. -/
@[simp]
theorem hasAsymptoticExpansion_zero [Norm 𝕜] [SeminormedAddCommGroup E]
    [SMulZeroClass 𝕜 E] (l : Filter α) (phi : ℕ → α → 𝕜) :
    HasAsymptoticExpansion l phi (0 : ℕ → E) (0 : α → E) :=
  fun N => by simp [isBigO_zero]

theorem HasAsymptoticExpansion.const_smul {𝕜' : Type*} [Norm 𝕜] [SeminormedRing 𝕜']
    [SeminormedAddCommGroup E] [SMul 𝕜 E] [Module 𝕜' E] [IsBoundedSMul 𝕜' E]
    [SMulCommClass 𝕜 𝕜' E] {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (c : 𝕜') :
    HasAsymptoticExpansion l phi (fun n => c • a n) (fun x => c • f x) := by
  intro N
  refine ((hf N).const_smul_left c).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [Pi.smul_apply, smul_sub, smul_sum, smul_comm]

theorem HasAsymptoticExpansion.add [Norm 𝕜] [SeminormedAddCommGroup E] [DistribSMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a b : ℕ → E} {f g : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hg : HasAsymptoticExpansion l phi b g) :
    HasAsymptoticExpansion l phi (a + b) (f + g) := by
  intro N
  refine ((hf N).add (hg N)).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  simp only [Pi.add_apply, smul_add, sum_add_distrib]
  abel

theorem HasAsymptoticExpansion.neg [Norm 𝕜] [SeminormedAddCommGroup E] [DistribSMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) :
    HasAsymptoticExpansion l phi (-a) (-f) := by
  intro N
  refine (hf N).neg_left.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  simp only [Pi.neg_apply, smul_neg, sum_neg_distrib]
  abel

theorem HasAsymptoticExpansion.sub [Norm 𝕜] [SeminormedAddCommGroup E] [DistribSMul 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a b : ℕ → E} {f g : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (hg : HasAsymptoticExpansion l phi b g) :
    HasAsymptoticExpansion l phi (a - b) (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Multiplying both `f` and the scale `phi` by a common scalar function `g` preserves the
coefficients of the asymptotic expansion. -/
theorem HasAsymptoticExpansion.smul [NormedRing 𝕜] [NormMulClass 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hf : HasAsymptoticExpansion l phi a f) (g : α → 𝕜) :
    HasAsymptoticExpansion l (fun n x => g x * phi n x) a (fun x => g x • f x) := by
  intro N
  obtain ⟨C, hC⟩ := (hf N).bound
  refine IsBigO.of_bound (max C 0) <| hC.mono fun x hx => ?_
  have hrew : g x • f x - ∑ n ∈ range N, (g x * phi n x) • a n =
      g x • (f x - ∑ n ∈ range N, phi n x • a n) := by
    simp only [smul_sub, smul_sum, mul_smul]
  rw [hrew, norm_mul]
  calc
    ‖g x • (f x - ∑ n ∈ range N, phi n x • a n)‖
        ≤ ‖g x‖ * ‖f x - ∑ n ∈ range N, phi n x • a n‖ := norm_smul_le _ _
    _ ≤ ‖g x‖ * (C * ‖phi N x‖) := by gcongr
    _ ≤ ‖g x‖ * (max C 0 * ‖phi N x‖) := by gcongr; exact le_max_left C 0
    _ = max C 0 * (‖g x‖ * ‖phi N x‖) := by ring

/-- Uniqueness of the coefficients of an asymptotic expansion with respect to an asymptotic scale
whose terms are frequently nonzero along `l` (DLMF §2.1(iii)). -/
theorem HasAsymptoticExpansion.unique [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {l : Filter α} {phi : ℕ → α → 𝕜} {a b : ℕ → E} {f : α → E}
    (hphi : IsAsymptoticScale l phi) (hne : ∀ n, ∃ᶠ x in l, phi n x ≠ 0)
    (ha : HasAsymptoticExpansion l phi a f) (hb : HasAsymptoticExpansion l phi b f) :
    a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hdiff : (fun x => phi n x • (a n - b n)) =o[l] phi n := by
      refine ((hb.isLittleO hphi n).sub (ha.isLittleO hphi n)).congr'
        (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
      dsimp only
      have hpre : ∑ k ∈ range n, phi k x • a k = ∑ k ∈ range n, phi k x • b k :=
        sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk)]
      rw [sum_range_succ, sum_range_succ, hpre, smul_sub]
      abel
    by_contra hab
    have hpos : 0 < ‖a n - b n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    have hbd := hdiff.bound (half_pos hpos)
    obtain ⟨x, hxne, hxbd⟩ := ((hne n).and_eventually hbd).exists
    have hnpos : 0 < ‖phi n x‖ := norm_pos_iff.mpr hxne
    rw [norm_smul] at hxbd
    nlinarith

end Expansion

/-! ### Poincaré expansions -/

section Poincare

variable {𝕜 E : Type*}

/-- Uniqueness of Poincaré expansions at infinity on an unbounded subset `X`
(`(Bornology.cobounded 𝕜 ⊓ 𝓟 X).NeBot`). -/
theorem HasAsymptoticExpansion.unique_inv_pow_cobounded [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {X : Set 𝕜}
    [hX : (Bornology.cobounded 𝕜 ⊓ 𝓟 X).NeBot] {a b : ℕ → E} {f : 𝕜 → E}
    (ha : HasAsymptoticExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) a f)
    (hb : HasAsymptoticExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) b f) :
    a = b := by
  refine ha.unique (isAsymptoticScale_inv_pow_cobounded X) (fun n => ?_) hb
  refine Filter.Eventually.frequently ?_
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono inf_le_left]
    with z hz
  exact inv_ne_zero (pow_ne_zero n (norm_pos_iff.mp hz))

/-- Uniqueness of Poincaré expansions along `atTop` on `ℝ`. -/
theorem HasAsymptoticExpansion.unique_inv_pow_atTop [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → E} {f : ℝ → E}
    (ha : HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) a f)
    (hb : HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) b f) :
    a = b := by
  refine ha.unique isAsymptoticScale_inv_pow_atTop (fun n => ?_) hb
  refine Filter.Eventually.frequently ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact inv_ne_zero (pow_ne_zero n hx.ne')

/-- Uniqueness of Poincaré expansions at an accumulation point `c` of `X`
(`(𝓝[X \ {c}] c).NeBot`, DLMF 2.1.16). -/
theorem HasAsymptoticExpansion.unique_sub_pow_nhdsWithin [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {X : Set 𝕜} {c : 𝕜}
    [hX : (𝓝[X \ {c}] c).NeBot] {a b : ℕ → E} {f : 𝕜 → E}
    (ha : HasAsymptoticExpansion (𝓝[X \ {c}] c) (fun n z => (z - c) ^ n) a f)
    (hb : HasAsymptoticExpansion (𝓝[X \ {c}] c) (fun n z => (z - c) ^ n) b f) :
    a = b := by
  refine ha.unique (isAsymptoticScale_sub_pow_nhdsWithin (X \ {c}) c) (fun n => ?_) hb
  refine Filter.Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact pow_ne_zero n (sub_ne_zero.mpr hz.2)

/-- DLMF 2.1.15: the Poincaré expansion at infinity in `X` is equivalent to the limits
`z ^ n • (f z - ∑_{s < n} (z ^ s)⁻¹ • a s) → a n`. -/
theorem hasAsymptoticExpansion_inv_pow_iff [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (X : Set 𝕜) (a : ℕ → E) (f : 𝕜 → E) :
    HasAsymptoticExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) a f ↔
      ∀ n, Tendsto (fun z => z ^ n • (f z - ∑ s ∈ range n, (z ^ s)⁻¹ • a s))
        (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 (a n)) := by
  have hne : ∀ n, ∀ᶠ z in Bornology.cobounded 𝕜 ⊓ 𝓟 X, (z ^ n)⁻¹ ≠ 0 := fun n => by
    filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono inf_le_left]
      with z hz
    exact inv_ne_zero (pow_ne_zero n (norm_pos_iff.mp hz))
  exact (hasAsymptoticExpansion_iff_tendsto (isAsymptoticScale_inv_pow_cobounded X) hne).trans
    (forall_congr' fun n => by simp only [inv_inv])

/-- A series `∑ (z ^ s)⁻¹ • a s` convergent for `‖z‖ > R` is the Poincaré asymptotic expansion
of its sum along `Bornology.cobounded 𝕜`. -/
theorem hasAsymptoticExpansion_of_hasSum [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] {R : ℝ} {a : ℕ → E} {f : 𝕜 → E}
    (hf : ∀ z : 𝕜, R < ‖z‖ → HasSum (fun s => (z ^ s)⁻¹ • a s) (f z)) :
    HasAsymptoticExpansion (Bornology.cobounded 𝕜) (fun n z => (z ^ n)⁻¹) a f := by
  intro N
  by_cases hex : ∃ z₀ : 𝕜, max R 0 < ‖z₀‖
  · obtain ⟨z₀, hz₀⟩ := hex
    have hrR : R < ‖z₀‖ := (le_max_left R 0).trans_lt hz₀
    have hr0 : 0 < ‖z₀‖ := (le_max_right R 0).trans_lt hz₀
    obtain ⟨A, hA⟩ := (hf z₀ hrR).summable.tendsto_cofinite_zero.norm.bddAbove_range_of_cofinite
    set M : ℝ := max A 0
    have hcoeff : ∀ s, ‖a s‖ ≤ M * ‖z₀‖ ^ s := fun s => by
      have h1 : ‖(z₀ ^ s)⁻¹ • a s‖ ≤ M := (hA ⟨s, rfl⟩).trans (le_max_left A 0)
      rw [norm_smul, norm_inv, norm_pow, inv_mul_eq_div, div_le_iff₀ (pow_pos hr0 s)] at h1
      exact h1
    refine IsBigO.of_bound (2 * M * ‖z₀‖ ^ N) ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (2 * ‖z₀‖)] with z hz
    have hz0 : 0 < ‖z‖ := by linarith
    have hzR : R < ‖z‖ := by linarith
    have htail : HasSum (fun k => (z ^ (k + N))⁻¹ • a (k + N))
        (f z - ∑ s ∈ range N, (z ^ s)⁻¹ • a s) :=
      (hasSum_nat_add_iff' N).mpr (hf z hzR)
    have hgeom : HasSum (fun k : ℕ => (M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * ((1 / 2 : ℝ) ^ k))
        ((M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * (1 - 1 / 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
    have hle : ‖f z - ∑ s ∈ range N, (z ^ s)⁻¹ • a s‖ ≤
        (M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * (1 - 1 / 2)⁻¹ := by
      refine le_of_tendsto_of_tendsto htail.tendsto_sum_nat.norm hgeom.tendsto_sum_nat
        (Eventually.of_forall fun m => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
      have hratio : ‖z₀‖ / ‖z‖ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hz0 (by norm_num : (0 : ℝ) < 2)]
        linarith
      calc
        ‖(z ^ (k + N))⁻¹ • a (k + N)‖
            = (‖z‖ ^ (k + N))⁻¹ * ‖a (k + N)‖ := by rw [norm_smul, norm_inv, norm_pow]
        _ ≤ (‖z‖ ^ (k + N))⁻¹ * (M * ‖z₀‖ ^ (k + N)) := by gcongr; exact hcoeff (k + N)
        _ = M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖ * (‖z₀‖ / ‖z‖) ^ k := by
          rw [norm_inv, norm_pow, pow_add, pow_add, mul_inv, div_pow]
          ring
        _ ≤ M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖ * (1 / 2 : ℝ) ^ k := by
          gcongr
    have hconst : (M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * (1 - 1 / 2 : ℝ)⁻¹ =
        2 * M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖ := by ring
    rwa [hconst] at hle
  · push Not at hex
    have hbot : Bornology.cobounded 𝕜 = ⊥ := by
      rw [Bornology.cobounded_eq_bot_iff]
      refine ⟨(Metric.isBounded_closedBall (x := (0 : 𝕜)) (r := max R 0)).subset fun z _ => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hex z
    rw [hbot]
    exact isBigO_bot _ _

/-- A convergent power series at `c` is the Poincaré asymptotic expansion of its sum along `𝓝 c`
(DLMF 2.1.8, 2.1.16). -/
theorem _root_.HasFPowerSeriesAt.hasAsymptoticExpansion [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜} (hf : HasFPowerSeriesAt f p c) :
    HasAsymptoticExpansion (𝓝 c) (fun n z => (z - c) ^ n) p.coeff f := by
  intro N
  have h0 : (fun y : 𝕜 => f (c + y) - ∑ n ∈ range N, y ^ n • p.coeff n) =O[𝓝 0]
      fun y : 𝕜 => y ^ N := by
    rw [← isBigO_norm_right]
    refine (hf.isBigO_sub_partialSum_pow N).congr'
      (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · dsimp only
      congr 1
      simp only [FormalMultilinearSeries.partialSum]
      refine sum_congr rfl fun n _ => ?_
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    · dsimp only
      rw [norm_pow]
  have hsub : Tendsto (fun z : 𝕜 => z - c) (𝓝 c) (𝓝 0) := by
    simpa using (continuous_sub_right c).tendsto c
  have hcomp := h0.comp_tendsto hsub
  refine hcomp.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
  simp only [Function.comp_apply, add_sub_cancel]

/-! ### Checks and examples -/

/-- The inverse-power sequence `x ↦ (x ^ n)⁻¹` is not an asymptotic scale along `𝓝[>] (0 : ℝ)`. -/
theorem not_isAsymptoticScale_inv_pow_nhdsGT_zero :
    ¬ IsAsymptoticScale (𝓝[>] (0 : ℝ)) (fun n x => (x ^ n)⁻¹) := by
  intro h
  have h0 := (h 0).bound zero_lt_one
  obtain ⟨x, hxpos, hbd⟩ := ((eventually_mem_nhdsWithin.and
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually
      (Iio_mem_nhds zero_lt_one))).and h0).exists
  have hx0 : 0 < x := hxpos.1
  have hx1 : x < 1 := hxpos.2
  simp only [zero_add, pow_zero, pow_one, inv_one, Real.norm_eq_abs, abs_one, mul_one,
    abs_inv, abs_of_pos hx0] at hbd
  have : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx0, hx1⟩
  linarith

-- Rescaling check: `1` has expansion `(1, 0, …)` in `x⁻ⁿ` and `(1/2, 0, …)` in `2 x⁻ⁿ`,
-- while `(1, 0, …)` does not expand `1` in `2 x⁻ⁿ`.
example :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 1) (fun _ : ℝ => (1 : ℝ)) ∧
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 2⁻¹) (fun _ : ℝ => (1 : ℝ)) ∧
    ¬ HasAsymptoticExpansion atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 1) (fun _ : ℝ => (1 : ℝ)) := by
  have h1 : HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 1) (fun _ : ℝ => (1 : ℝ)) := by
    intro N
    cases N with
    | zero =>
      simpa using (isBigO_refl (fun _ : ℝ => (1 : ℝ)) atTop)
    | succ N =>
      have hsum : ∀ x : ℝ,
          ∑ n ∈ range (N + 1), (x ^ n)⁻¹ * Pi.single (M := fun _ : ℕ => ℝ) 0 1 n = 1 :=
        fun x => by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; simp [Pi.single_eq_of_ne hb]
          · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
      simp only [smul_eq_mul, hsum, sub_self]
      exact isBigO_zero _ _
  have h2 : HasAsymptoticExpansion atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 2⁻¹) (fun _ : ℝ => (1 : ℝ)) := by
    have hr := h1.rescale_scale (psi := fun n (x : ℝ) => 2 * (x ^ n)⁻¹) (κ := fun _ => 2⁻¹)
      (fun n => Eventually.of_forall fun x => by ring)
    refine hr.congr_coeff fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [Pi.single_eq_of_ne hn]
  refine ⟨h1, h2, fun hbad => ?_⟩
  have hscale : IsAsymptoticScale atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹) :=
    isAsymptoticScale_inv_pow_atTop.const_mul (fun _ => two_ne_zero)
  have hne : ∀ n, ∃ᶠ x : ℝ in atTop, 2 * (x ^ n)⁻¹ ≠ 0 := fun n =>
    Filter.Eventually.frequently <| (eventually_gt_atTop (0 : ℝ)).mono fun x hx =>
      mul_ne_zero two_ne_zero (inv_ne_zero (pow_ne_zero n hx.ne'))
  have heq := h2.unique hscale hne hbad
  have h0 := congrFun heq 0
  norm_num at h0

-- Unpunctured singleton check: on `𝓝[{c}] c`, uniqueness fails since `(z - c) ^ n = 0`
-- for `n ≥ 1`.
example {𝕜 : Type*} [NormedField 𝕜] (c : 𝕜) (f : 𝕜 → 𝕜) (a : ℕ → 𝕜) (ha0 : a 0 = f c) :
    HasAsymptoticExpansion (𝓝[{c}] c) (fun n z => (z - c) ^ n) a f := by
  intro N
  cases N with
  | zero =>
    refine IsBigO.of_bound ‖f c‖ ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [mem_singleton_iff.mp hz]
    simp
  | succ N =>
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [mem_singleton_iff.mp hz]
    have hsum : ∑ n ∈ range (N + 1), ((c - c) ^ n) • a n = f c := by
      rw [Finset.sum_eq_single 0]
      · simp [ha0]
      · intro b _ hb; simp [zero_pow hb]
      · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
    rw [hsum, sub_self]

-- Geometric series check: `1 / (z - 1) ~ ∑_{s ≥ 1} z⁻ˢ` along `cobounded 𝕜`.
example {𝕜 : Type*} [NormedField 𝕜] :
    HasAsymptoticExpansion (Bornology.cobounded 𝕜) (fun n z => (z ^ n)⁻¹)
      (fun s => if s = 0 then (0 : 𝕜) else 1) (fun z => (z - 1)⁻¹) := by
  refine hasAsymptoticExpansion_of_hasSum (R := 1) fun z hz => ?_
  have hzne : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hz)
  have hnorm : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h; rw [h, norm_one] at hz; exact lt_irrefl _ hz)
  have h2 : (1 : 𝕜) - z⁻¹ ≠ 0 := sub_ne_zero.mpr (by
    intro h
    have := congrArg norm h
    simp only [norm_one, norm_inv] at this
    linarith [inv_lt_one_of_one_lt₀ hz])
  have hgeom : HasSum (fun k : ℕ => (z⁻¹) ^ k) (1 - z⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, ↓reduceIte, smul_zero, sub_zero]
  have hmul : HasSum (fun k : ℕ => z⁻¹ * (z⁻¹) ^ k) (z⁻¹ * (1 - z⁻¹)⁻¹) :=
    hgeom.mul_left z⁻¹
  have hval : z⁻¹ * (1 - z⁻¹)⁻¹ = (z - 1)⁻¹ := by
    field_simp [hzne, h1, h2]
  rw [hval] at hmul
  refine hmul.congr_fun fun k => ?_
  simp [smul_eq_mul, pow_succ', inv_pow, mul_comm]

end Poincare

end Asymptotics
