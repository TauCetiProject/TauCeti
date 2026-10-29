/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Hensel
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import TauCeti.NumberTheory.LocalField.Different.Monogenic
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.NumberTheory.LocalField.Monogenic

/-!
# Roots in small balls around a uniformizer: the local fibre count

Let `L / K` be a totally ramified separable extension of nonarchimedean local fields of degree
`n`, let `ξ` be a uniformizer of `L` (equivalently, a root of an Eisenstein polynomial generating
`L`), and let `d` be the discriminant exponent of `L / K`. Since `𝒪[L] = 𝒪[K][ξ]`, the derivative
of the minimal polynomial `f` of `ξ` has order `v_L(f'(ξ)) = d`.

For a monic polynomial `g` of degree `n` over `𝒪[K]` and a radius order `r ≥ d + n`, the closed
ball `v_L(z - ξ) ≥ r` contains a root of `g` if and only if `v_L(g(ξ)) ≥ r + d`, and it then
contains exactly one root. At a radius `r = n ρ` the ball is the cube `ξ + π ^ ρ 𝒪[L]` for a
uniformizer `π` of `K`. This is Serre's local fibre count: it describes the polynomials with a
root near `ξ` by a single valuation condition at `ξ`, which in power-basis coordinates is a box.

## Main results

* `TauCeti.IsTotallyRamified.addVal_aeval_derivative_minpoly_eq_discriminantExponent`: the order
  of `f'(ξ)` is the discriminant exponent.
* `TauCeti.IsTotallyRamified.existsUnique_isRoot_le_addVal_iff`: the local fibre count, a unique
  root in the ball exactly when `v_L(g(ξ)) ≥ r + d`.
* `TauCeti.IsTotallyRamified.exists_isRoot_le_addVal_iff`: its existence form.

## Implementation notes

No closeness of the coefficients of `g` to those of `f` is assumed. Either condition forces
`v_L(g'(ξ)) = d`: the difference `g - f` has degree less than `n`, so by orthogonality of the
powers of `ξ` the order of `(g - f)'(ξ)` is at least `v_L(g(ξ)) - 1`, and a root of `g` close to
`ξ` makes `v_L(g(ξ))` large by the Taylor expansion of `g` at `ξ`. Hensel's lemma in closed balls,
`Polynomial.existsUnique_isRoot_le_addVal_iff`, then applies at `ξ`. Some lower bound on `r` is
necessary for uniqueness: for `K = ℚ₂` and `ξ = √2`, where `d = 3`, the ball `v_L(z - ξ) ≥ 2`
contains both roots of `X ^ 2 - 2`.

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

/-- In a totally ramified extension, the derivative of the minimal polynomial over `𝒪[K]` of a
uniformizer `ξ` of `L` has order the discriminant exponent at `ξ`. -/
theorem IsTotallyRamified.addVal_aeval_derivative_minpoly_eq_discriminantExponent
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) :
    addVal 𝒪[L] (aeval ξ (derivative (minpoly 𝒪[K] ξ))) = discriminantExponent K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, h.inertiaDegree_eq_one,
    one_mul]
  exact (natCast_differentExponent_eq_addVal_aeval_derivative_minpoly K L
    (h.adjoin_eq_top_of_irreducible hξ)).symm

/-- A monic `g` of degree `e(L/K)` that has a root in the ball `v_L(z - ξ) ≥ r`, or whose value
at `ξ` has order at least `r + d`, has derivative of order exactly `d` at `ξ`, for `r ≥ d + e`. -/
private theorem IsTotallyRamified.addVal_aeval_derivative_eq_discriminantExponent
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L + ramificationIndex K L ≤ r)
    (hclose : (∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ∨
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) :
    addVal 𝒪[L] (aeval ξ (derivative g)) = discriminantExponent K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  -- Compare with the minimal polynomial `f` of `ξ`, whose derivative has order `d` at `ξ`.
  let f := minpoly 𝒪[K] ξ
  have hf : f.Monic := minpoly.monic (IsIntegral.of_finite 𝒪[K] ξ)
  have hfdeg : f.natDegree = ramificationIndex K L := by
    simpa only [IsTotallyRamified.integralPowerBasis_gen,
      IsTotallyRamified.integralPowerBasis_dim] using (h.integralPowerBasis hξ).natDegree_minpoly
  have hd : addVal 𝒪[L] (aeval ξ (derivative f)) = discriminantExponent K L :=
    h.addVal_aeval_derivative_minpoly_eq_discriminantExponent hξ
  have hfroot : aeval ξ f = 0 := minpoly.aeval 𝒪[K] ξ
  have hsub : (g - f).natDegree < ramificationIndex K L :=
    (⟨hdeg, hg⟩ : g.IsMonicOfDegree _).natDegree_sub_lt ramificationIndex_pos.ne' ⟨hfdeg, hf⟩
  -- In degree one the difference `g - f` is constant, so the derivatives agree.
  by_cases he : ramificationIndex K L = 1
  · have hzero : derivative (g - f) = 0 := by
      rw [eq_C_of_natDegree_eq_zero (p := g - f) (by omega), derivative_C]
    rw [derivative_sub, sub_eq_zero] at hzero
    rw [hzero, hd]
  have hr2 : 1 < r := by
    have := ramificationIndex_pos (K := K) (L := L)
    omega
  have hdr : (discriminantExponent K L : ℕ∞) ≤ r := by
    exact_mod_cast (Nat.le_add_right _ _).trans hr
  -- Orthogonality bounds the order of `g(ξ) = (g - f)(ξ)` by that of `(g - f)'(ξ)`, plus one.
  have hbound : addVal 𝒪[L] (aeval ξ g) ≤
      addVal 𝒪[L] (aeval ξ (derivative g) - aeval ξ (derivative f)) + 1 := by
    simpa only [derivative_sub, map_sub, hfroot, sub_zero] using
      addVal_aeval_le_addVal_aeval_derivative_add_one_of_irreducible hξ hsub
  rcases hclose with ⟨z, hz, hball⟩ | hval
  · -- If the orders of `g'(ξ)` and `f'(ξ)` differed, the order `a` of their difference would be
    -- their minimum, and the root `z` would force `v_L(g(ξ)) ≥ r + a > a + 1`.
    by_contra hne
    have hdiff : addVal 𝒪[L] (aeval ξ (derivative g) - aeval ξ (derivative f)) =
        min (addVal 𝒪[L] (aeval ξ (derivative g))) (discriminantExponent K L) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [(addVal 𝒪[L]).map_sub_eq_of_lt_left (hd ▸ hlt), min_eq_left hlt.le]
      · rw [(addVal 𝒪[L]).map_sub_eq_of_lt_right (hd ▸ hgt), hd, min_eq_right hgt.le]
    rw [hdiff] at hbound
    let a := min (addVal 𝒪[L] (aeval ξ (derivative g))) (discriminantExponent K L : ℕ∞)
    have ha : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    have hval : (r : ℕ∞) + a ≤ addVal 𝒪[L] (aeval ξ g) := by
      simpa only [eval_map_algebraMap] using
        Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L]))
          (by simpa only [derivative_map, eval_map_algebraMap] using min_le_left _ _)
          ((min_le_right _ _).trans hdr)
          (by simpa only [IsRoot, eval_map_algebraMap] using hz) hball
    have hlt : a + 1 < (r : ℕ∞) + a := by
      rw [add_comm (r : ℕ∞)]
      exact (ENat.add_lt_add_iff_left ha).2 (by exact_mod_cast hr2)
    exact (hlt.trans_le hval).not_ge hbound
  · -- A small value at `ξ` forces `(g - f)'(ξ)` to have order larger than `d`.
    have hlt : (discriminantExponent K L : ℕ∞) + 1 <
        addVal 𝒪[L] (aeval ξ (derivative g) - aeval ξ (derivative f)) + 1 := by
      refine lt_of_lt_of_le ?_ (hval.trans hbound)
      exact_mod_cast (by omega : discriminantExponent K L + 1 < r + discriminantExponent K L)
    have hdiff : addVal 𝒪[L] (aeval ξ (derivative f)) <
        addVal 𝒪[L] (aeval ξ (derivative g) - aeval ξ (derivative f)) := by
      rw [hd]
      exact (ENat.add_lt_add_iff_right (by simp)).1 hlt
    rw [← sub_add_cancel (aeval ξ (derivative g)) (aeval ξ (derivative f))]
    exact ((addVal 𝒪[L]).map_add_eq_of_lt_right hdiff).trans hd

/-- **The local fibre count** (Serre's Lemma 1). Let `ξ` be a uniformizer of a totally ramified
extension `L / K` of degree `e(L/K)` and discriminant exponent `d`. For a monic `g` of degree
`e(L/K)` over `𝒪[K]` and `r ≥ d + e(L/K)`, the ball `v_L(z - ξ) ≥ r` contains exactly one root of
`g` if and only if `v_L(g(ξ)) ≥ r + d`. -/
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
    have hd := h.addVal_aeval_derivative_eq_discriminantExponent hξ hg hdeg hr (.inl ⟨z, hz⟩)
    simpa only [eval_map_algebraMap, Nat.cast_add] using
      Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L]))
        (by simpa only [derivative_map, eval_map_algebraMap] using hd.ge) hdr.le
        (by simpa only [IsRoot, eval_map_algebraMap] using hz.1) hz.2
  · intro hval
    have hd := h.addVal_aeval_derivative_eq_discriminantExponent hξ hg hdeg hr (.inr hval)
    have hroot := ((g.map (algebraMap 𝒪[K] 𝒪[L])).existsUnique_isRoot_le_addVal_iff ξ
      (r := (r : ℕ∞)) (by
        simpa only [derivative_map, eval_map_algebraMap, hd] using hdr)).2
      (by simpa only [derivative_map, eval_map_algebraMap, hd, Nat.cast_add] using hval)
    simpa only [IsRoot, eval_map_algebraMap] using hroot

/-- **The local fibre count, existence form.** Under the hypotheses of
`TauCeti.IsTotallyRamified.existsUnique_isRoot_le_addVal_iff`, the ball `v_L(z - ξ) ≥ r` contains
a root of `g` if and only if `v_L(g(ξ)) ≥ r + d`; that root is then unique. -/
theorem IsTotallyRamified.exists_isRoot_le_addVal_iff (h : IsTotallyRamified K L)
    {ξ : 𝒪[L]} (hξ : Irreducible ξ) {g : 𝒪[K][X]} (hg : g.Monic)
    (hdeg : g.natDegree = ramificationIndex K L) {r : ℕ}
    (hr : discriminantExponent K L + ramificationIndex K L ≤ r) :
    (∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
      ((r + discriminantExponent K L : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g) := by
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun hval ↦
    ((h.existsUnique_isRoot_le_addVal_iff hξ hg hdeg hr).2 hval).exists⟩
  have hd := h.addVal_aeval_derivative_eq_discriminantExponent hξ hg hdeg hr (.inl ⟨z, hz⟩)
  have hdr : (discriminantExponent K L : ℕ∞) ≤ r := by
    exact_mod_cast (Nat.le_add_right _ _).trans hr
  simpa only [eval_map_algebraMap, Nat.cast_add] using
    Polynomial.le_addVal_eval_of_isRoot (F := g.map (algebraMap 𝒪[K] 𝒪[L]))
      (by simpa only [derivative_map, eval_map_algebraMap] using hd.ge) hdr
      (by simpa only [IsRoot, eval_map_algebraMap] using hz.1) hz.2

end TauCeti
