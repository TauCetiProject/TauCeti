/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.FactorOrder
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Differences of analytic polynomial roots

Suppose a polynomial family splits locally into analytic linear factors and its discriminant
is a power of one distinguished variable times an analytic unit. Every difference of two
distinctly labelled roots is then a power of that variable times an analytic unit as well.
Roots may coincide on the distinguished hyperplane; their differences have constant finite
order along it.

The discriminant identity used here is `Polynomial.discr_prod_X_sub_C`. Each root difference
occurs twice in that product. The analytic factor-order theorem extracts its power-times-unit
form without assuming that its slice order is already constant.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4.
-/

public section

open Filter Topology
open Polynomial

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For an analytic splitting whose discriminant is a centered power times an analytic unit,
every difference of roots with distinct labels is locally a centered power times an analytic
unit. The roots need not be distinct on the distinguished hyperplane. -/
theorem exists_root_sub_eq_pow_mul_unit {n : ℕ} {r : Fin n → E × 𝕜 → 𝕜}
    {P : E × 𝕜 → Polynomial 𝕜} {x₀ : E} {y₀ : 𝕜}
    (hr : ∀ i, AnalyticAt 𝕜 (r i) (x₀, y₀))
    (hP : ∀ᶠ p in 𝓝 (x₀, y₀), P p = ∏ i, (X - C (r i p)))
    {a : ℕ} {u : E × 𝕜 → 𝕜} (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).discr = (p.2 - y₀) ^ a * u p)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ b : ℕ, ∃ v : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 v (x₀, y₀) ∧ v (x₀, y₀) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), r i p - r j p = (p.2 - y₀) ^ b * v p := by
  classical
  -- Repeat each unordered pair twice, so the discriminant is a product of the
  -- differences themselves, rather than of their squares.
  let s := (Finset.univ : Finset (Fin n)).sigma fun k ↦
    (Finset.Ioi k).sigma fun _ ↦ (Finset.univ : Finset (Fin 2))
  let G : (Σ _ : Fin n, Σ _ : Fin n, Fin 2) → E × 𝕜 → 𝕜 :=
    fun k p ↦ r k.1 p - r k.2.1 p
  have hG : ∀ k ∈ s, AnalyticAt 𝕜 (G k) (x₀, y₀) :=
    fun k _ ↦ (hr k.1).sub (hr k.2.1)
  have hprod : ∀ᶠ p in 𝓝 (x₀, y₀), ∏ k ∈ s, G k p = (p.2 - y₀) ^ a * u p := by
    filter_upwards [hP, hdiscr] with p hPp hdp
    rw [hPp, Polynomial.discr_prod_X_sub_C] at hdp
    simpa only [s, G, Finset.prod_sigma, Fin.prod_univ_two, pow_two] using hdp
  have ha : AnalyticAt 𝕜 (fun p ↦ ∏ k ∈ s, G k p) (x₀, y₀) := by
    simpa only [Finset.prod_fn] using Finset.analyticAt_prod _ hG
  have horder : ∀ᶠ x in 𝓝 x₀,
      analyticOrderAt (fun y ↦ ∏ k ∈ s, G k (x, y)) y₀ = a :=
    ha.eventually_analyticOrderAt_eq_natCast_iff.2
      ⟨u, hu, hu0, by simpa only [smul_eq_mul] using hprod⟩
  have hfactor := exists_factor_eq_pow_mul_unit hG horder
  have hlt (k l : Fin n) (hkl : k < l) :
      ∃ b : ℕ, ∃ v : E × 𝕜 → 𝕜,
        AnalyticAt 𝕜 v (x₀, y₀) ∧ v (x₀, y₀) ≠ 0 ∧
          ∀ᶠ p in 𝓝 (x₀, y₀), r k p - r l p = (p.2 - y₀) ^ b * v p :=
    hfactor ⟨k, l, 0⟩ (by simp [s, hkl])
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · obtain ⟨b, v, hv, hv0, heq⟩ := hlt j i h
    refine ⟨b, -v, hv.neg, neg_ne_zero.2 hv0, ?_⟩
    filter_upwards [heq] with p hp
    simpa only [Pi.neg_apply, mul_neg, neg_sub] using congrArg Neg.neg hp

end TauCeti
