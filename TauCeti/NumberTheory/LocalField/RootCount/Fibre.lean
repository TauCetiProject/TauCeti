/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.DiscreteValuationRing.Hensel
import TauCeti.NumberTheory.LocalField.Monogenic
import TauCeti.NumberTheory.LocalField.Henselian
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Roots in small balls at a uniformizer

Let `ξ` be a uniformizer of a totally ramified separable extension `L/K` of degree `n`, and let
`d` be its discriminant exponent. For a monic polynomial `g` of degree `n` over `𝒪[K]`, and
`d < r`, the ball `v_L(y - ξ) ≥ r` contains a root of `g` if and only if
`v_L(g(ξ)) ≥ r + d`, and then contains exactly one root.

This is the local fibre count used to integrate the number of roots of Eisenstein polynomials.
No coefficient-closeness hypothesis on `g` is needed: orthogonality of the powers of `ξ` forces
the derivative order to equal `d` whenever either condition holds. The radius order need not
be divisible by the ramification index.

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

private theorem natDegree_sub_minpoly_lt (h : IsTotallyRamified K L) {ξ : 𝒪[L]}
    (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) :
    (g - minpoly 𝒪[K] ξ).natDegree < ramificationIndex K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hfdeg : (minpoly 𝒪[K] ξ).natDegree = ramificationIndex K L := by
    simpa only [IsTotallyRamified.integralPowerBasis_gen,
      IsTotallyRamified.integralPowerBasis_dim] using (h.integralPowerBasis hξ).natDegree_minpoly
  exact (⟨hdeg, hg⟩ : g.IsMonicOfDegree _).natDegree_sub_lt ramificationIndex_pos.ne'
    ⟨hfdeg, minpoly.monic (IsIntegral.of_finite 𝒪[K] ξ)⟩

-- In degree one the difference is constant, so the derivatives agree without an estimate.
private theorem derivative_eq_minpoly_of_ramificationIndex_eq_one
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ)
    {g : 𝒪[K][X]} (hg : g.Monic) (hdeg : g.natDegree = ramificationIndex K L)
    (he : ramificationIndex K L = 1) : g.derivative = (minpoly 𝒪[K] ξ).derivative := by
  have hsub := natDegree_sub_minpoly_lt h hξ hg hdeg
  have hzero : (g - minpoly 𝒪[K] ξ).derivative = 0 := by
    rw [eq_C_of_natDegree_eq_zero (p := g - minpoly 𝒪[K] ξ) (by omega), derivative_C]
  simpa only [derivative_sub, sub_eq_zero] using hzero

-- Orthogonality bounds evaluation in terms of the difference of derivatives.
private theorem addVal_aeval_le_derivative_sub_minpoly_add_one
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ)
    {g : 𝒪[K][X]} (hg : g.Monic) (hdeg : g.natDegree = ramificationIndex K L) :
    addVal 𝒪[L] (aeval ξ g) ≤
      addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ (minpoly 𝒪[K] ξ).derivative) + 1 := by
  simpa only [derivative_sub, map_sub, minpoly.aeval, sub_zero] using
    addVal_aeval_le_addVal_aeval_derivative_add_one hξ (natDegree_sub_minpoly_lt h hξ hg hdeg)

variable [Algebra.IsSeparable K L]

private theorem derivative_order_eq_of_isRoot (h : IsTotallyRamified K L) {ξ : 𝒪[L]}
    (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L < r) {z : 𝒪[L]}
    (hz : aeval z g = 0) (hball : (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) :
    addVal 𝒪[L] (aeval ξ g.derivative) = discriminantExponent K L := by
  have hd := h.addVal_aeval_derivative_minpoly_eq_discriminantExponent hξ
  by_cases he : ramificationIndex K L = 1
  · rw [derivative_eq_minpoly_of_ramificationIndex_eq_one h hξ hg hdeg he, hd]
  have hr2 : 1 < r := by
    have := ramificationIndex_pos (K := K) (L := L)
    have := ramificationIndex_sub_one_le_discriminantExponent (K := K) (L := L)
    omega
  have hdr : (discriminantExponent K L : ℕ∞) ≤ r := by exact_mod_cast hr.le
  have hbound := addVal_aeval_le_derivative_sub_minpoly_add_one h hξ hg hdeg
  -- Taylor terms at a root in the ball have larger order than the orthogonality bound
  -- unless the two derivatives have the same order.
  by_contra hne
  have hdiff : addVal 𝒪[L]
      (aeval ξ g.derivative - aeval ξ (minpoly 𝒪[K] ξ).derivative) =
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

private theorem derivative_order_eq_of_le_addVal (h : IsTotallyRamified K L) {ξ : 𝒪[L]}
    (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L < r)
    (hval : ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) :
    addVal 𝒪[L] (aeval ξ g.derivative) = discriminantExponent K L := by
  have hd := h.addVal_aeval_derivative_minpoly_eq_discriminantExponent hξ
  by_cases he : ramificationIndex K L = 1
  · rw [derivative_eq_minpoly_of_ramificationIndex_eq_one h hξ hg hdeg he, hd]
  have hr2 : 1 < r := by
    have := ramificationIndex_pos (K := K) (L := L)
    have := ramificationIndex_sub_one_le_discriminantExponent (K := K) (L := L)
    omega
  have hbound := addVal_aeval_le_derivative_sub_minpoly_add_one h hξ hg hdeg
  -- A sufficiently small value forces the difference of derivatives to have order > d.
  have hlt : (discriminantExponent K L : ℕ∞) + 1 <
      addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ (minpoly 𝒪[K] ξ).derivative) + 1 := by
    apply lt_of_lt_of_le _ (hval.trans hbound)
    exact_mod_cast (by omega : discriminantExponent K L + 1 < r + discriminantExponent K L)
  have hdiff : addVal 𝒪[L] (aeval ξ (minpoly 𝒪[K] ξ).derivative) <
      addVal 𝒪[L] (aeval ξ g.derivative - aeval ξ (minpoly 𝒪[K] ξ).derivative) := by
    rw [hd]
    exact (ENat.add_lt_add_iff_right (by simp)).1 hlt
  rw [← sub_add_cancel (aeval ξ g.derivative) (aeval ξ (minpoly 𝒪[K] ξ).derivative)]
  exact ((addVal 𝒪[L]).map_add_eq_of_lt_right hdiff).trans hd

private theorem le_addVal_aeval_of_isRoot (h : IsTotallyRamified K L)
    {ξ : 𝒪[L]} (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L < r) {z : 𝒪[L]}
    (hz : aeval z g = 0) (hball : (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) :
    ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g) := by
  have hd := derivative_order_eq_of_isRoot h hξ hg hdeg hr hz hball
  have hdr : (discriminantExponent K L : ℕ∞) ≤ r := by exact_mod_cast hr.le
  simpa only [eval_map_algebraMap, Nat.cast_add] using
    Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L])) (by
      simpa only [derivative_map, eval_map_algebraMap] using hd.ge) hdr
      (by simpa only [IsRoot, eval_map_algebraMap] using hz) hball

/-- **The local fibre count.** A monic polynomial of degree `[L : K]` has exactly one root
in a sufficiently small uniformizer ball precisely when its value at the center has the extra
order given by the discriminant exponent. -/
theorem IsTotallyRamified.existsUnique_isRoot_le_addVal_iff (h : IsTotallyRamified K L)
    {ξ : 𝒪[L]} (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L < r) :
    (∃! z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g) := by
  have hdr : (discriminantExponent K L : ℕ∞) < r := by exact_mod_cast hr
  constructor
  · rintro ⟨z, hz, -⟩
    exact le_addVal_aeval_of_isRoot h hξ hg hdeg hr hz.1 hz.2
  · intro hval
    have hd := derivative_order_eq_of_le_addVal h hξ hg hdeg hr hval
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
    (hr : discriminantExponent K L < r) :
    (∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g) := by
  constructor
  · rintro ⟨z, hz, hball⟩
    exact le_addVal_aeval_of_isRoot h hξ hg hdeg hr hz hball
  · intro hval
    exact ((h.existsUnique_isRoot_le_addVal_iff hξ hg hdeg hr).2 hval).exists

end TauCeti
