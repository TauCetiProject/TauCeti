/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Polynomial
public import TauCeti.RingTheory.DiscreteValuationRing.RootBall
import TauCeti.NumberTheory.LocalField.Different.Monogenic
import TauCeti.NumberTheory.LocalField.Monogenic
import TauCeti.NumberTheory.LocalField.Henselian
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Roots in small balls at a uniformizer

Let `ξ` be a uniformizer of a totally ramified separable extension `L/K` of degree `n`, and let
`d` be its discriminant exponent. For a monic polynomial `g` of degree `n` over `𝒪[K]`, and
`d + n ≤ n * ρ`, the ball `v_L(y - ξ) ≥ n * ρ` contains a root of `g` if and only if
`v_L(g(ξ)) ≥ n * ρ + d`, and then contains exactly one root.

The theorems `IsTotallyRamified.exists_isRoot_le_addVal_iff` and
`IsTotallyRamified.existsUnique_isRoot_le_addVal_iff` allow any radius order `r ≥ d + n`,
not just multiples of `n`.

This is the local fibre count used to integrate the number of roots of Eisenstein polynomials.
Its essential point is that no coefficient-closeness hypothesis on `g` is needed: orthogonality
of the powers of `ξ` forces the derivative order to equal `d` whenever either condition holds.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Lemma 1.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsSeparable K L]

private theorem derivative_order_eq (h : IsTotallyRamified K L) {ξ : 𝒪[L]}
    (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L + ramificationIndex K L ≤ r)
    (hclose : (∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ∨
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) :
    addVal 𝒪[L] (aeval ξ g.derivative) = discriminantExponent K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  -- Compare with the minimal polynomial, whose derivative order is the discriminant exponent.
  let f := minpoly 𝒪[K] ξ
  have hf : f.Monic := minpoly.monic (IsIntegral.of_finite 𝒪[K] ξ)
  have hfdeg : f.natDegree = ramificationIndex K L := by
    simpa only [IsTotallyRamified.integralPowerBasis_gen,
      IsTotallyRamified.integralPowerBasis_dim] using (h.integralPowerBasis hξ).natDegree_minpoly
  have hd : addVal 𝒪[L] (aeval ξ f.derivative) = discriminantExponent K L := by
    rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, h.inertiaDegree_eq_one,
      one_mul]
    exact (natCast_differentExponent_eq_addVal_aeval_derivative_minpoly K L
      (h.adjoin_eq_top_of_irreducible hξ)).symm
  have hfroot : aeval ξ f = 0 := minpoly.aeval 𝒪[K] ξ
  have hsub : (g - f).natDegree < ramificationIndex K L :=
    (⟨hdeg, hg⟩ : g.IsMonicOfDegree _).natDegree_sub_lt ramificationIndex_pos.ne'
      ⟨hfdeg, hf⟩
  -- In degree one the difference is constant, so the derivatives agree without an estimate.
  by_cases he : ramificationIndex K L = 1
  · have hzero : (g - f).derivative = 0 := by
      rw [eq_C_of_natDegree_eq_zero (p := g - f) (by omega), derivative_C]
    rw [derivative_sub, sub_eq_zero] at hzero
    rw [hzero, hd]
  have hr2 : 1 < r := by
    have := ramificationIndex_pos (K := K) (L := L)
    omega
  have hdr : (discriminantExponent K L : ℕ∞) ≤ r := by
    exact_mod_cast (Nat.le_add_right _ _).trans hr
  -- Orthogonality bounds evaluation in terms of the difference of derivatives.
  have hbound : addVal 𝒪[L] (aeval ξ g) ≤
      addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ f.derivative) + 1 := by
    simpa only [derivative_sub, map_sub, hfroot, sub_zero] using
      addVal_aeval_le_addVal_aeval_derivative_add_one hξ hsub
  rcases hclose with ⟨z, hz, hball⟩ | hval
  · -- A root in the ball forces the Taylor terms to have larger order than this bound
    -- unless the two derivatives have the same order.
    by_contra hne
    have hdiff : addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ f.derivative) =
        min (addVal 𝒪[L] (aeval ξ g.derivative)) (discriminantExponent K L) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [(addVal 𝒪[L]).map_sub_eq_of_lt_left (hd ▸ hlt), min_eq_left hlt.le]
      · rw [(addVal 𝒪[L]).map_sub_eq_of_lt_right (hd ▸ hgt), hd, min_eq_right hgt.le]
    rw [hdiff] at hbound
    let a := min (addVal 𝒪[L] (aeval ξ g.derivative)) (discriminantExponent K L : ℕ∞)
    have ha : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    have hval : (r : ℕ∞) + a ≤ addVal 𝒪[L] (aeval ξ g) := by
      simpa only [eval_map_algebraMap] using
        Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L]))
          (by simpa only [derivative_map, eval_map_algebraMap] using
            (min_le_left (addVal 𝒪[L] (aeval ξ g.derivative))
              (discriminantExponent K L : ℕ∞)))
          ((min_le_right _ _).trans hdr)
          (by simpa only [IsRoot, eval_map_algebraMap] using hz) hball
    have hlt : a + 1 < (r : ℕ∞) + a := by
      rw [add_comm (r : ℕ∞)]
      exact (ENat.add_lt_add_iff_left ha).2 (by exact_mod_cast hr2)
    exact (hlt.trans_le hval).not_ge hbound
  · -- A sufficiently small value forces the difference of derivatives to have order > d.
    have hlt : (discriminantExponent K L : ℕ∞) + 1 <
        addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ f.derivative) + 1 := by
      apply lt_of_lt_of_le _ (hval.trans hbound)
      exact_mod_cast (by omega : discriminantExponent K L + 1 < r + discriminantExponent K L)
    have hdiff : addVal 𝒪[L] (aeval ξ f.derivative) <
        addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ f.derivative) := by
      rw [hd]
      exact (ENat.add_lt_add_iff_right (by simp)).1 hlt
    rw [← sub_add_cancel (aeval ξ g.derivative) (aeval ξ f.derivative)]
    exact ((addVal 𝒪[L]).map_add_eq_of_lt_right hdiff).trans hd

/-- **The local fibre count.** A monic polynomial of degree `[L : K]` has exactly one root
in a sufficiently small uniformizer ball precisely when its value at the center has the extra
order given by the discriminant exponent. The radius order `r` need not be divisible by the
ramification index. -/
theorem IsTotallyRamified.existsUnique_isRoot_le_addVal_iff (h : IsTotallyRamified K L)
    {ξ : 𝒪[L]} (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L + ramificationIndex K L ≤ r) :
    (∃! z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g) := by
  have hdr : (discriminantExponent K L : ℕ∞) < r := by
    have := ramificationIndex_pos (K := K) (L := L)
    exact_mod_cast (by omega : discriminantExponent K L < r)
  constructor
  · rintro ⟨z, hz, -⟩
    have hd := derivative_order_eq h hξ hg hdeg hr (.inl ⟨z, hz⟩)
    simpa only [eval_map_algebraMap, Nat.cast_add] using
      Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L])) (by
        simpa only [derivative_map, eval_map_algebraMap] using hd.ge) hdr.le
        (by simpa only [IsRoot, eval_map_algebraMap] using hz.1) hz.2
  · intro hval
    have hd := derivative_order_eq h hξ hg hdeg hr (.inr hval)
    have hroot := ((g.map (algebraMap 𝒪[K] 𝒪[L])).existsUnique_isRoot_le_addVal_iff ξ
      (r := (r : ℕ∞)) (by
        simpa only [derivative_map, eval_map_algebraMap, hd] using hdr)).2
      (by simpa only [derivative_map, eval_map_algebraMap, hd, Nat.cast_add] using hval)
    simpa only [IsRoot, eval_map_algebraMap] using hroot

/-- The existence form of the local fibre criterion. Whenever a root exists in this ball,
it is unique by `IsTotallyRamified.existsUnique_isRoot_le_addVal_iff`. -/
theorem IsTotallyRamified.exists_isRoot_le_addVal_iff (h : IsTotallyRamified K L)
    {ξ : 𝒪[L]} (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L + ramificationIndex K L ≤ r) :
    (∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g) := by
  constructor
  · intro hz
    have hd := derivative_order_eq h hξ hg hdeg hr (.inl hz)
    obtain ⟨z, hz, hball⟩ := hz
    have hdr : (discriminantExponent K L : ℕ∞) ≤ r := by
      exact_mod_cast (Nat.le_add_right _ _).trans hr
    simpa only [eval_map_algebraMap, Nat.cast_add] using
      Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L])) (by
        simpa only [derivative_map, eval_map_algebraMap] using hd.ge) hdr
        (by simpa only [IsRoot, eval_map_algebraMap] using hz) hball
  · intro hval
    exact ((h.existsUnique_isRoot_le_addVal_iff hξ hg hdeg hr).2 hval).exists

end TauCeti
