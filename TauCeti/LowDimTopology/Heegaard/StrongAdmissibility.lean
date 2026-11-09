/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.SpincAdmissibility

/-!
# Strong admissibility

Strong admissibility restricts periodic domains using the Maslov index of a chosen generator.
For a nonzero periodic domain of nonnegative index `2m`, some region must have multiplicity
greater than `m`. We use the rational half-index because the abstract region system accepts
an arbitrary Euler-characteristic function; on a geometric Heegaard diagram this is the usual
integer-valued condition. In particular, an index-zero periodic domain has both positive and
negative coefficients, so strong admissibility at `x` implies weak admissibility at `x`
(`TauCeti.HeegaardRegionSystem.WeaklyAdmissibleAt`).

Through weak admissibility at the terminal generator `y`, this makes nonnegative domains from
`x` to `y` with fixed basepoint multiplicities and fixed Maslov index finite
(`HeegaardRegionSystem.WeaklyAdmissibleAt.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index`).
That suffices for the hat differential, which only counts domains avoiding the basepoint. The
differentials of the minus and infinity complexes count domains with every basepoint
multiplicity, and strong admissibility gives the finiteness they need: in a diagram with a single
basepoint whose region Euler characteristics are those of a closed surface, only finitely many
nonnegative domains from `x` to `y` have a given Maslov index, whatever their basepoint
multiplicity (Ozsváth–Szabó, Lemma 4.14). Equivalently
(`TauCeti.HeegaardRegionSystem.forall_finite_setOf_isDomainBetween_nonneg_index_iff`), the only
nonnegative domain from `y` to itself of Maslov index zero is zero, even among those covering the
basepoint. Conversely, this finiteness characterizes strong admissibility: clearing the
denominator of a rational index `q`, a periodic domain `P` with no coefficient above `q / 2`
gives the nonnegative index-zero domain `q.num Σ - 2 q.den P`.

## Main definitions

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible`: every nonzero periodic domain of nonnegative
  Maslov index has a coefficient greater than half its index.

## Main results

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.weaklyAdmissibleAt`: strong admissibility at
  a generator implies weak admissibility there.
* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.finite_setOf_isDomainBetween_nonneg_index`:
  in a strongly admissible diagram, only finitely many nonnegative domains from `x` to `y` have a
  given Maslov index.
* `TauCeti.HeegaardRegionSystem.stronglyAdmissible_iff_forall_finite`: in such a diagram, strong
  admissibility is equivalent to this finiteness.

## References

P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Ann. of Math. **159** (2004),
[arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.2: Definition 4.10 (strong
admissibility) and Lemma 4.14 (finiteness of positive domains of a given Maslov index).
-/

public section

namespace TauCeti.HeegaardRegionSystem

variable {n : ℕ} {Point Region Basepoint : Type*}
  {H : HeegaardRegionSystem n Point Region Basepoint}
  [Fintype Point] [Fintype Region] [DecidableEq Region]

variable (H) in
/-- Strong admissibility at a generator `x`: every nonzero periodic domain `P` of nonnegative
Maslov index has a coefficient strictly greater than half its index. The Euler characteristics
of the regions are supplied by `χ`. -/
def StronglyAdmissible (χ : Region → ℤ) (x : H.Generator) : Prop :=
  ∀ P ∈ H.periodicDomains, P ≠ 0 → 0 ≤ H.maslovIndex χ x x P →
    ∃ r, H.maslovIndex χ x x P / 2 < (P r : ℚ)

/-- Strong admissibility at `x` means every nonzero periodic domain of nonnegative Maslov
index has a coefficient strictly greater than half its index. -/
theorem stronglyAdmissible_iff {χ : Region → ℤ} {x : H.Generator} :
    H.StronglyAdmissible χ x ↔
      ∀ P ∈ H.periodicDomains, P ≠ 0 → 0 ≤ H.maslovIndex χ x x P →
        ∃ r, H.maslovIndex χ x x P / 2 < (P r : ℚ) := Iff.rfl

/-- Strong admissibility has the same value at generators joined by a domain: the Maslov
index of a periodic domain is independent of the generator within that class. -/
theorem stronglyAdmissible_iff_of_isDomainBetween {χ : Region → ℤ} {x y : H.Generator}
    {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    H.StronglyAdmissible χ x ↔ H.StronglyAdmissible χ y := by
  constructor
  · intro h P hP hne hidx
    have hμ := hD.maslovIndex_self_eq χ (H.isDomainBetween_self_iff.mpr hP).1
    rw [← hμ] at hidx ⊢
    exact h P hP hne hidx
  · intro h P hP hne hidx
    have hμ := hD.maslovIndex_self_eq χ (H.isDomainBetween_self_iff.mpr hP).1
    rw [hμ] at hidx ⊢
    exact h P hP hne hidx

/-- A strongly admissible diagram at `x` is weakly admissible at `x`: an index-zero periodic
domain `P` must have a coefficient greater than zero, and so must `-P`. -/
theorem StronglyAdmissible.weaklyAdmissibleAt {χ : Region → ℤ} {x : H.Generator}
    (hH : H.StronglyAdmissible χ x) : H.WeaklyAdmissibleAt χ x := by
  refine weaklyAdmissibleAt_def.mpr fun P hP hindex hne => ?_
  obtain ⟨r, hr⟩ := hH P hP hne (by simp [hindex])
  have hnegindex : H.maslovIndex χ x x (-P) = 0 := by
    rw [map_neg, hindex]
    exact neg_zero
  obtain ⟨s, hs⟩ := hH (-P) (H.periodicDomains.neg_mem hP)
    (by simpa using hne) (hnegindex ▸ le_refl _)
  simp only [hindex, zero_div] at hr
  simp only [hnegindex, zero_div] at hs
  refine ⟨⟨r, by exact_mod_cast hr⟩, ⟨s, ?_⟩⟩
  have hsInt : (0 : ℤ) < -P s := by exact_mod_cast hs
  exact neg_pos.mp hsInt

section Finite

variable {χ : Region → ℤ} {x y : H.Generator}

/-- In a diagram with at most one basepoint whose region Euler characteristics `χ` are those of a
closed surface of genus `n`, strong admissibility at `y` rules out nonzero nonnegative domains
from `y` to itself of Maslov index zero, even those covering the basepoint. -/
theorem StronglyAdmissible.eq_zero_of_isDomainBetween_of_nonneg [Subsingleton Basepoint]
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) (hH : H.StronglyAdmissible χ y)
    {Q : Region → ℤ} (hQ : H.IsDomainBetween y y Q) (hQ₀ : 0 ≤ Q)
    (hμ : H.maslovIndex χ y y Q = 0) : Q = 0 := by
  obtain ⟨k, hk₀, hk⟩ : ∃ k : ℤ, 0 ≤ k ∧ ∀ z, Q (H.basepoint z) = k := by
    rcases isEmpty_or_nonempty Basepoint with hB | ⟨⟨z⟩⟩
    · exact ⟨0, le_rfl, fun z => isEmptyElim z⟩
    · exact ⟨Q (H.basepoint z), hQ₀ _, fun z' => by rw [Subsingleton.elim z' z]⟩
  -- With `k` the basepoint multiplicity of `Q`, `k Σ - Q` is a periodic domain of Maslov index
  -- `2 k` with no coefficient greater than `k`, which strong admissibility forbids unless it is
  -- zero.
  have hP : k • 1 - Q ∈ H.periodicDomains :=
    isDomainBetween_self_iff.mp ⟨by simpa only [sub_eq_add_neg] using
      ((H.isDomainBetween_one y).zsmul k).add hQ.neg, fun z => by simp [hk z]⟩
  have hPμ : H.maslovIndex χ y y (k • 1 - Q) = 2 * k := by
    rw [map_sub, map_zsmul, maslovIndex_one_eq_two hχ, hμ, sub_zero, zsmul_eq_mul, mul_comm]
  by_contra hne
  by_cases hP₀ : k • 1 - Q = 0
  · -- Then `Q = k Σ` has Maslov index `2 k`, so `k = 0` and `Q = 0`.
    rw [hP₀, map_zero, eq_comm, mul_eq_zero, Int.cast_eq_zero] at hPμ
    rw [sub_eq_zero, (hPμ.resolve_left two_ne_zero), zero_smul] at hP₀
    exact hne hP₀.symm
  obtain ⟨r, hr⟩ := hH _ hP hP₀ (by rw [hPμ]; positivity)
  rw [hPμ, mul_div_cancel_left₀ _ two_ne_zero] at hr
  have : Q r < 0 := by
    have : (k : ℚ) < k - Q r := by simpa using hr
    exact_mod_cast (by linarith : (Q r : ℚ) < 0)
  exact (hQ₀ r).not_gt this

/-- In a diagram with at most one basepoint whose region Euler characteristics `χ` are those of a
closed surface of genus `n`, strong admissibility at `y` leaves only finitely many nonnegative
domains from any generator `x` to `y` with a prescribed Maslov index, whatever their basepoint
multiplicity. This is the finiteness behind the differentials of the minus and infinity
Heegaard Floer complexes, which count domains with every basepoint multiplicity. -/
theorem StronglyAdmissible.finite_setOf_isDomainBetween_nonneg_index [Subsingleton Basepoint]
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) (hH : H.StronglyAdmissible χ y)
    (x : H.Generator) (m : ℚ) :
    {D : Region → ℤ | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite :=
  forall_finite_setOf_isDomainBetween_nonneg_index_iff.mpr
    (fun _ hQ hQ₀ hμ => hH.eq_zero_of_isDomainBetween_of_nonneg hχ hQ hQ₀ hμ) x m

/-- In a diagram with a single basepoint whose region Euler characteristics `χ` are those of a
closed surface of genus `n`, strong admissibility at `y` is exactly the finiteness of the
nonnegative domains from each generator to `y` with each prescribed Maslov index. -/
theorem stronglyAdmissible_iff_forall_finite [Subsingleton Basepoint] (z : Basepoint)
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) :
    H.StronglyAdmissible χ y ↔ ∀ (x : H.Generator) (m : ℚ),
      {D : Region → ℤ | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  refine ⟨fun hH => hH.finite_setOf_isDomainBetween_nonneg_index hχ, fun hfin P hP hne _ => ?_⟩
  set q := H.maslovIndex χ y y P with hq
  by_contra! hle
  -- Clearing the denominator of the index `q`, `q.num Σ - 2 q.den P` is a nonnegative domain from
  -- `y` to itself of Maslov index zero.
  have hQ := forall_finite_setOf_isDomainBetween_nonneg_index_iff.mp hfin
    (q.num • 1 - (2 * q.den : ℤ) • P)
    (by
      simpa only [sub_eq_add_neg] using ((H.isDomainBetween_one y).zsmul q.num).add
        ((isDomainBetween_self_iff.mpr hP).1.zsmul _).neg)
    (fun r => by
      have hr : (2 * q.den : ℚ) * P r ≤ q.num :=
        calc (2 * q.den : ℚ) * P r ≤ 2 * q.den * (q / 2) :=
              mul_le_mul_of_nonneg_left (hle r) (by positivity)
          _ = q.num := by rw [← Rat.mul_den_eq_num]; ring
      simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      exact sub_nonneg.mpr (by exact_mod_cast hr))
    (by
      rw [map_sub, map_zsmul, map_zsmul, maslovIndex_one_eq_two hχ, ← hq, zsmul_eq_mul,
        zsmul_eq_mul, ← Rat.mul_den_eq_num]
      push_cast
      ring)
  -- So `2 q.den P = q.num Σ`, and `P` vanishes at the basepoint, so `q.num = 0` and `P = 0`.
  rw [sub_eq_zero] at hQ
  have hnum : q.num = 0 := by
    simpa [(H.mem_periodicDomains_iff.mp hP).1 z] using congrFun hQ (H.basepoint z)
  rw [hnum, zero_smul, eq_comm, smul_eq_zero] at hQ
  exact hne (hQ.resolve_left (by positivity))

end Finite

end TauCeti.HeegaardRegionSystem
