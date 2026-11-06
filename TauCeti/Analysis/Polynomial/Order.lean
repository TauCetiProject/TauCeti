/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Polynomial.Reverse
import Mathlib.Topology.Algebra.Polynomial

/-!
# Analytic order of polynomial evaluation

At zero, the analytic order of polynomial evaluation equals its trailing degree, including
infinite order for the zero polynomial. This connects coefficient calculations for polynomial
slices to the analytic order used in preparation theorems. At an arbitrary point, the analytic
order of a nonzero polynomial function is the root multiplicity of the polynomial there.
Consequently, an analytic unit does not change the multiplicities of the roots, and over an
algebraically closed field a monic polynomial is determined, up to such units, by its germs at its
roots.

Dividing a power by the evaluation of the reversal of a nonzero polynomial gives a function
analytic at zero, since the reversal takes the nonzero leading coefficient there. This is the
reciprocal-coordinate form of a polynomial near infinity.
-/

public section

open Filter Topology

namespace Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The analytic order at zero of a polynomial function is its trailing degree. -/
@[simp]
theorem analyticOrderAt_eval_zero (p : Polynomial 𝕜) :
    analyticOrderAt (fun t ↦ p.eval t) 0 = p.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp]
    simpa only [eval_zero, Pi.zero_def, trailingDegree_zero] using
      (analyticOrderAt_zero (𝕜 := 𝕜) (E := 𝕜) (z₀ := 0))
  rw [trailingDegree_eq_natTrailingDegree hp]
  have ha : AnalyticAt 𝕜 (fun t ↦ p.eval t) 0 :=
    (AnalyticOnNhd.eval_polynomial p) 0 (Set.mem_univ _)
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.2
    (fun k hk ↦ coeff_eq_zero_of_lt_natTrailingDegree hk :
      ∀ k < p.natTrailingDegree, p.coeff k = 0)
  have hq0 : q.eval 0 ≠ 0 := by
    have hc := coeff_natTrailingDegree_ne_zero.2 hp
    have hcoeff : (X ^ p.natTrailingDegree * q).coeff p.natTrailingDegree = q.coeff 0 := by
      simpa only [zero_add] using coeff_X_pow_mul q p.natTrailingDegree 0
    have heq := congrArg (fun r : Polynomial 𝕜 ↦ r.coeff p.natTrailingDegree) hq
    rw [hcoeff] at heq
    simpa only [← coeff_zero_eq_eval_zero, ← heq] using hc
  refine ha.analyticOrderAt_eq_natCast.2 ⟨fun t ↦ q.eval t,
    (AnalyticOnNhd.eval_polynomial q) 0 (Set.mem_univ _), hq0, ?_⟩
  exact Eventually.of_forall fun t ↦ by
    conv_lhs => rw [hq]
    simp only [eval_mul, eval_pow, eval_X, sub_zero, smul_eq_mul]

/-- The analytic order of a nonzero polynomial function at a point is the multiplicity of that
point as a root of the polynomial. -/
theorem analyticOrderAt_eval {p : Polynomial 𝕜} (hp : p ≠ 0) (a : 𝕜) :
    analyticOrderAt (fun t ↦ p.eval t) a = p.rootMultiplicity a := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  refine ((AnalyticOnNhd.eval_polynomial p) a (Set.mem_univ _)).analyticOrderAt_eq_natCast.2
    ⟨fun t ↦ q.eval t, (AnalyticOnNhd.eval_polynomial q) a (Set.mem_univ _),
      fun h ↦ hq (dvd_iff_isRoot.2 h), .of_forall fun t ↦ ?_⟩
  conv_lhs => rw [hpq]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]

/-- For a nonzero polynomial `p`, the function `w ↦ w ^ n / p.reverse.eval w` is analytic at `0`:
the reversal does not vanish at `0`, where it takes the leading coefficient of `p`. -/
theorem analyticAt_pow_div_eval_reverse {p : Polynomial 𝕜} (hp : p ≠ 0) (n : ℕ) :
    AnalyticAt 𝕜 (fun w : 𝕜 ↦ w ^ n / p.reverse.eval w) 0 :=
  ((analyticAt_id (𝕜 := 𝕜)).pow _).div ((AnalyticOnNhd.eval_polynomial _) 0 (Set.mem_univ _))
    (eval_zero_reverse_ne_zero hp)

/-- Polynomials which agree near `ζ` up to analytic units have the same multiplicity at `ζ`. -/
theorem rootMultiplicity_eq_of_mul_eval_eventuallyEq {p q : Polynomial 𝕜} (hp : p ≠ 0) (hq : q ≠ 0)
    {v₁ v₂ : 𝕜 → 𝕜} {ζ : 𝕜} (hv₁ : AnalyticAt 𝕜 v₁ ζ) (hv₂ : AnalyticAt 𝕜 v₂ ζ)
    (h₁ : v₁ ζ ≠ 0) (h₂ : v₂ ζ ≠ 0)
    (h : (v₁ * fun w ↦ p.eval w) =ᶠ[𝓝 ζ] v₂ * fun w ↦ q.eval w) :
    p.rootMultiplicity ζ = q.rootMultiplicity ζ := by
  have hord₁ := analyticOrderAt_mul hv₁ (AnalyticOnNhd.eval_polynomial p ζ (Set.mem_univ ζ))
  have hord₂ := analyticOrderAt_mul hv₂ (AnalyticOnNhd.eval_polynomial q ζ (Set.mem_univ ζ))
  rw [hv₁.analyticOrderAt_eq_zero.2 h₁, zero_add, analyticOrderAt_eval hp] at hord₁
  rw [hv₂.analyticOrderAt_eq_zero.2 h₂, zero_add, analyticOrderAt_eval hq] at hord₂
  exact_mod_cast hord₁.symm.trans ((analyticOrderAt_congr h).trans hord₂)

/-- Two functions continuous at `w` which agree near `w` after multiplication by a nonzero
polynomial agree at `w`. -/
theorem eq_of_eventually_mul_eval_eq {p : Polynomial 𝕜} (hp : p ≠ 0) {v₁ v₂ : 𝕜 → 𝕜} {w : 𝕜}
    (h₁ : ContinuousAt v₁ w) (h₂ : ContinuousAt v₂ w)
    (h : ∀ᶠ t in 𝓝 w, v₁ t * p.eval t = v₂ t * p.eval t) : v₁ w = v₂ w := by
  have hne : ∀ᶠ t in 𝓝[≠] w, p.eval t ≠ 0 :=
    (eventually_eval_ne_zero_codiscrete hp).filter_mono (nhdsNE_le_codiscrete w)
  exact tendsto_nhds_unique_of_eventuallyEq (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)
    (((h.filter_mono nhdsWithin_le_nhds).and hne).mono fun _ ht ↦ mul_right_cancel₀ ht.2 ht.1)

section IsAlgClosed

variable [IsAlgClosed 𝕜]

/-- If `g = p * h` with `p` monic with no root but `a` and `h` a unit at `a`, and `g` has order `d`
at `a`, then `p = (X - C a) ^ d`. -/
theorem Monic.eq_X_sub_C_pow_of_analyticOrderAt_eq {g h : 𝕜 → 𝕜} {p : Polynomial 𝕜} {a : 𝕜} {d : ℕ}
    (hp : p.Monic) (hroot : ∀ ζ, p.IsRoot ζ → ζ = a) (hh : AnalyticAt 𝕜 h a) (hh0 : h a ≠ 0)
    (hg : ∀ w, g w = p.eval w * h w) (hd : analyticOrderAt g a = d) : p = (X - C a) ^ d := by
  classical
  have hgfun : (fun w ↦ p.eval w) * h = g := _root_.funext fun w ↦ (hg w).symm
  have hord := analyticOrderAt_mul (AnalyticOnNhd.eval_polynomial p a (Set.mem_univ a)) hh
  rw [hgfun, hd, hh.analyticOrderAt_eq_zero.2 hh0, add_zero,
    analyticOrderAt_eval hp.ne_zero] at hord
  have hmul : p.rootMultiplicity a = d := by exact_mod_cast hord.symm
  have hroots : p.roots = Multiset.replicate d a := by
    refine Multiset.eq_replicate.2 ⟨?_, fun b hb ↦ hroot b (isRoot_of_mem_roots hb)⟩
    rw [← hmul, ← count_roots]
    exact (Multiset.count_eq_card.2 fun x hx ↦ (hroot x (isRoot_of_mem_roots hx)).symm).symm
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp, hroots]
  simp

/-- Two monic polynomials with all their roots in an open set, agreeing there up to analytic units,
are equal. -/
theorem Monic.eq_of_forall_mem_mul_eval_eq {p q : Polynomial 𝕜} (hp : p.Monic) (hq : q.Monic)
    {v₁ v₂ : 𝕜 → 𝕜} {U : Set 𝕜} (hU : IsOpen U) (hroot₁ : ∀ ζ, p.IsRoot ζ → ζ ∈ U)
    (hroot₂ : ∀ ζ, q.IsRoot ζ → ζ ∈ U) (hv₁ : ∀ w ∈ U, AnalyticAt 𝕜 v₁ w ∧ v₁ w ≠ 0)
    (hv₂ : ∀ w ∈ U, AnalyticAt 𝕜 v₂ w ∧ v₂ w ≠ 0)
    (h : ∀ w ∈ U, v₁ w * p.eval w = v₂ w * q.eval w) : p = q := by
  classical
  have hroots : p.roots = q.roots := Multiset.ext.2 fun ζ ↦ by
    rw [count_roots, count_roots]
    by_cases hζ : ζ ∈ U
    · exact rootMultiplicity_eq_of_mul_eval_eventuallyEq hp.ne_zero hq.ne_zero (hv₁ ζ hζ).1
        (hv₂ ζ hζ).1 (hv₁ ζ hζ).2 (hv₂ ζ hζ).2 (eventually_of_mem (hU.mem_nhds hζ) h)
    · rw [rootMultiplicity_eq_zero (mt (hroot₁ ζ) hζ), rootMultiplicity_eq_zero (mt (hroot₂ ζ) hζ)]
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp,
    (IsAlgClosed.splits q).eq_prod_roots_of_monic hq, hroots]

end IsAlgClosed

end Polynomial
