/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer
public import TauCeti.NumberTheory.LSeries.WienerIkehara.SharpCutoff
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.LSeries.Continuity

/-!
# Boundary data for prime-counting Dirichlet series

For a set `S` of prime ideals of a number field, the logarithmically weighted prime-power
coefficients `TauCeti.primeVonMangoldtCoeff K S` are nonnegative and have partial sums equal to
Chebyshev's function `TauCeti.primePsi K S`.  This file packages the exact analytic boundary data
that lets the Wiener--Ikehara theorem act on those coefficients.

`TauCeti.PrimeBoundaryRemainder K S δ` consists of the sum of their Dirichlet series on
`Re s > 1`, together with a continuous extension to `Re s ≥ 1` of the remainder after subtracting
the pole `δ / (s - 1)`.  The two functions are defined on these half-plane subtypes rather than on
all of `ℂ`; values outside the regions used by the hypotheses are therefore not carried as free
data.  `PrimeBoundaryRemainder.ofFunctions` constructs the package from the whole-plane functions
that naturally occur in analytic applications.

The main theorem `TauCeti.primeNumberTheoremTransfer` combines Wiener--Ikehara, removal of higher
prime powers, and Abel summation.  It gives the error-term forms of all three conclusions
`ψ(x) = δx + o(x)`, `ϑ(x) = δx + o(x)`, and `π(x) = δ Li(x) + o(x / log x)`, including `δ = 0`.
The conditional specialization `TauCeti.primeIdealTheorem_of_boundary` records the usual prime
ideal theorem once boundary data with residue one is available.

## Main results

* `TauCeti.PrimeBoundaryRemainder`: boundary data with residue `δ` for the prime Dirichlet
  series of `S`, with the constructor `TauCeti.PrimeBoundaryRemainder.ofFunctions`.
* `TauCeti.primeNumberTheoremTransfer`: boundary data give the asymptotics of `ψ`, `ϑ`, and `π`.
* `TauCeti.primeIdealTheorem_of_boundary`: the prime ideal theorem from boundary data with
  residue one.
* `TauCeti.primeCount_sub_mul_logIntegral_isLittleO_of_LSeriesSummable_sub`: comparison with a
  Dirichlet series `L(c, s)`. If `L(c, s) - δ / (s - 1)` extends continuously to `Re s ≥ 1` and the
  Dirichlet series of the coefficient difference converges absolutely at `s = 1`, then
  `π_S(x) = δ Li(x) + o(x / log x)`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 17.
* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

namespace TauCeti

open Asymptotics Filter NumberField
open scoped nonZeroDivisors NumberField Topology
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- **Boundary data for the prime Dirichlet series of `S`.**  The function `series` is the sum
of the Dirichlet series of `primeVonMangoldtCoeff K S` on `Re s > 1`.  The function `remainder`
is continuous on `Re s ≥ 1` and agrees on the open half-plane with
`series s - δ / (s - 1)`.

The functions have precisely their mathematically relevant domains, so the structure carries no
arbitrary values elsewhere. -/
@[ext]
structure PrimeBoundaryRemainder (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) where
  /-- The sum of the von Mangoldt Dirichlet series on `Re s > 1`. -/
  series : {s : ℂ // 1 < s.re} → ℂ
  /-- The continuous pole-subtracted remainder on `Re s ≥ 1`. -/
  remainder : {s : ℂ // 1 ≤ s.re} → ℂ
  /-- The named function `series` is the sum of the exact von Mangoldt coefficient series. -/
  hasSum (s : {s : ℂ // 1 < s.re}) :
    LSeriesHasSum (fun n ↦ (primeVonMangoldtCoeff K S n : ℂ)) s (series s)
  /-- The pole-subtracted remainder is continuous on the closed half-plane. -/
  continuous_remainder : Continuous remainder
  /-- On `Re s > 1`, the remainder is the series with its pole subtracted. -/
  remainder_eq (s : {s : ℂ // 1 < s.re}) :
    remainder ⟨s, s.property.le⟩ = series s - δ / (s - 1)

namespace PrimeBoundaryRemainder

attribute [simp] remainder_eq

section OfFunctions

variable (F G : ℂ → ℂ)
    (hF : ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n ↦ (primeVonMangoldtCoeff K S n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - δ / (s - 1))

/-- Construct prime boundary data from functions on the whole complex plane.  Only their
restrictions to `Re s > 1` and `Re s ≥ 1` are retained. -/
def ofFunctions : PrimeBoundaryRemainder K S δ where
  series s := F s
  remainder s := G s
  hasSum s := hF s s.property
  continuous_remainder := continuousOn_iff_continuous_domRestrict.mp hG
  remainder_eq s := hGF s s.property

@[simp]
theorem ofFunctions_series (s : {s : ℂ // 1 < s.re}) :
    (ofFunctions F G hF hG hGF).series s = F s :=
  (rfl)

@[simp]
theorem ofFunctions_remainder (s : {s : ℂ // 1 ≤ s.re}) :
    (ofFunctions F G hF hG hGF).remainder s = G s :=
  (rfl)

end OfFunctions

/-- Wiener--Ikehara applied to a prime boundary package: the normalized `ψ` function tends to
the residue `δ`. -/
theorem tendsto_inv_mul_primePsi (B : PrimeBoundaryRemainder K S δ) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * primePsi K S x) atTop (𝓝 δ) := by
  let F : ℂ → ℂ := fun s ↦ if hs : 1 < s.re then B.series ⟨s, hs⟩ else 0
  let G : ℂ → ℂ := fun s ↦ if hs : 1 ≤ s.re then B.remainder ⟨s, hs⟩ else 0
  have hF : ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n ↦ (primeVonMangoldtCoeff K S n : ℂ)) s (F s) := by
    intro s hs
    simpa [F, hs] using B.hasSum ⟨s, hs⟩
  have hG : ContinuousOn G {s : ℂ | 1 ≤ s.re} := by
    rw [continuousOn_iff_continuous_domRestrict]
    -- The restricted function has exactly the subtype carried by `B.remainder`.
    change Continuous (fun s : {s : ℂ // 1 ≤ s.re} ↦ G s)
    exact B.continuous_remainder.congr fun s ↦ by simp [G, s.property]
  have hGF : ∀ s : ℂ, 1 < s.re → G s = F s - δ / (s - 1) := by
    intro s hs
    simpa [F, G, hs, hs.le] using B.remainder_eq ⟨s, hs⟩
  have hmain := LSeries.wienerIkehara (a := primeVonMangoldtCoeff K S)
    (F := F) (G := G) (κ := δ) (primeVonMangoldtCoeff_nonneg S) hF hG hGF
  refine hmain.congr' (Eventually.of_forall fun x ↦ congrArg (x⁻¹ * ·) ?_)
  rw [primePsi_eq_sum_range, Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊), Finset.sum_insert (by simp)]
  simp

/-- Boundary data force the residue to be nonnegative; it need not be carried as a redundant
field because `ψ(x) / x` is eventually nonnegative and tends to `δ`. -/
theorem nonneg (B : PrimeBoundaryRemainder K S δ) : 0 ≤ δ := by
  refine ge_of_tendsto B.tendsto_inv_mul_primePsi ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact mul_nonneg (inv_nonneg.2 hx.le) (primePsi_nonneg S x)

end PrimeBoundaryRemainder

/-- **The Tauberian asymptotic for Chebyshev's `ψ`.**  Exact prime boundary data with residue `δ`
imply `ψ(x) = δx + o(x)`. -/
theorem primePsi_asymptotic_of_boundary (B : PrimeBoundaryRemainder K S δ) :
    (fun x ↦ primePsi K S x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
  refine (isLittleO_iff_tendsto' ((eventually_ne_atTop (0 : ℝ)).mono fun _ hx hzero ↦
    (hx hzero).elim)).2 ?_
  have h := B.tendsto_inv_mul_primePsi.sub_const δ
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp

/-- **Prime-number-theorem transfer from exact boundary data.**  The three conclusions are,
respectively, the von Mangoldt-weighted prime-power asymptotic, the logarithmically weighted prime
asymptotic after removing higher powers, and the unweighted prime-counting asymptotic after Abel
summation.  The error-term formulation includes residue zero. -/
theorem primeNumberTheoremTransfer (B : PrimeBoundaryRemainder K S δ) :
    (fun x ↦ primePsi K S x - δ * x) =o[atTop] (fun x : ℝ ↦ x) ∧
      (fun x ↦ primeTheta K S x - δ * x) =o[atTop] (fun x : ℝ ↦ x) ∧
      (fun x ↦ primeCount K S x - δ * Real.logIntegral x) =o[atTop]
        (fun x : ℝ ↦ x / Real.log x) := by
  have hψ := primePsi_asymptotic_of_boundary B
  have hθ := primeTheta_asymptotic_of_primePsi (standardPrimePowerRemoval K S) hψ
  exact ⟨hψ, hθ, primeCount_sub_mul_logIntegral_isLittleO hθ⟩

/-- **Prime counting by comparison with a Dirichlet series.** Let `c` be coefficients whose
Dirichlet series converges absolutely on `Re s > 1` and such that `L(c, s) - δ / (s - 1)` agrees
there with a function `G` continuous on `Re s ≥ 1`. If the Dirichlet series of the difference
between `primeVonMangoldtCoeff K S` and `c` converges absolutely at `s = 1`, then
`π_S(x) = δ Li(x) + o(x / log x)`. -/
theorem primeCount_sub_mul_logIntegral_isLittleO_of_LSeriesSummable_sub {c : ℕ → ℂ} {G : ℂ → ℂ}
    (hc : LSeries.abscissaOfAbsConv c ≤ 1) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hGc : Set.EqOn G (fun s ↦ LSeries c s - δ / (s - 1)) {s | 1 < s.re})
    (hd : LSeriesSummable (fun n ↦ (primeVonMangoldtCoeff K S n : ℂ) - c n) 1) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
  set d : ℕ → ℂ := fun n ↦ (primeVonMangoldtCoeff K S n : ℂ) - c n
  have hcd : (fun n ↦ (primeVonMangoldtCoeff K S n : ℂ)) = c + d := (add_sub_cancel c _).symm
  have hcs : ∀ s : ℂ, 1 < s.re → LSeriesSummable c s := fun s hs ↦
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (hc.trans_lt (mod_cast hs))
  have hds : ∀ s : ℂ, 1 < s.re → LSeriesSummable d s := fun s hs ↦
    hd.of_re_le_re (by simpa using hs.le)
  -- `G + L(d)` is a continuous extension of the pole-subtracted series of `S` to `Re s ≥ 1`
  exact (primeNumberTheoremTransfer <| .ofFunctions
    (LSeries fun n ↦ (primeVonMangoldtCoeff K S n : ℂ)) (fun s ↦ G s + LSeries d s)
    (fun s hs ↦ (hcd ▸ (hcs s hs).add (hds s hs)).LSeriesHasSum)
    (hG.add ((TauCeti.LSeries.continuousOn_LSeries hd).mono fun s hs ↦ by simpa using hs))
    fun s hs ↦ by rw [hGc hs, hcd, LSeries_add (hcs s hs) (hds s hs), sub_add_eq_add_sub]).2.2

/-- **The conditional prime ideal theorem.**  Boundary data for all prime ideals with residue one
give the standard asymptotic equivalences for `ψ`, `ϑ`, and `π`. -/
theorem primeIdealTheorem_of_boundary
    (B : PrimeBoundaryRemainder K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1) :
    primePsi K Set.univ ~[atTop] (fun x : ℝ ↦ x) ∧
      primeTheta K Set.univ ~[atTop] (fun x : ℝ ↦ x) ∧
      primeCount K Set.univ ~[atTop] Real.logIntegral := by
  obtain ⟨hψ, hθ, hπ⟩ := primeNumberTheoremTransfer B
  have hψ' : primePsi K Set.univ ~[atTop] (fun x : ℝ ↦ x) := by
    rw [Asymptotics.IsEquivalent]
    exact hψ.congr' (Eventually.of_forall fun x ↦ by simp) EventuallyEq.rfl
  have hθ' : primeTheta K Set.univ ~[atTop] (fun x : ℝ ↦ x) := by
    rw [Asymptotics.IsEquivalent]
    exact hθ.congr' (Eventually.of_forall fun x ↦ by simp) EventuallyEq.rfl
  replace hπ := hπ.trans_isBigO Real.logIntegral_isEquivalent_div_log.isBigO_symm
  have hπ' : primeCount K Set.univ ~[atTop] Real.logIntegral := by
    rw [Asymptotics.IsEquivalent]
    exact hπ.congr' (Eventually.of_forall fun x ↦ by simp) EventuallyEq.rfl
  exact ⟨hψ', hθ', hπ'⟩

end TauCeti
