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
multiplicity (Ozsváth–Szabó, Lemma 4.14). Equivalently, the only nonnegative domain from `y` to
itself of Maslov index zero is zero, even among those covering the basepoint. When the periodic
domains have even integer Maslov indices, as on a geometric diagram, this finiteness
characterizes strong admissibility.

## Main definitions

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible`: every nonzero periodic domain of nonnegative
  Maslov index has a coefficient greater than half its index.

## Main results

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.weaklyAdmissibleAt`: strong admissibility at
  a generator implies weak admissibility there.
* `TauCeti.HeegaardRegionSystem.forall_finite_setOf_isDomainBetween_nonneg_index_iff`: the
  nonnegative domains ending at `y` with each prescribed Maslov index are finite in number
  exactly when the only nonnegative domain from `y` to itself of Maslov index zero is zero.
* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.finite_setOf_isDomainBetween_nonneg_index`:
  in a strongly admissible diagram, only finitely many nonnegative domains from `x` to `y` have a
  given Maslov index.
* `TauCeti.HeegaardRegionSystem.stronglyAdmissible_iff_forall_finite`: when periodic domains
  have even integer Maslov indices, strong admissibility is equivalent to this finiteness.

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

variable (H) in
/-- The domains from `y` to itself of Maslov index zero at `y`. Unlike periodic domains, they may
cover the basepoints. -/
private def selfDomainsIndexZero (χ : Region → ℤ) (y : H.Generator) :
    AddSubgroup (Region → ℤ) :=
  (H.alphaArcBoundary.comp H.alphaBoundary).ker ⊓ (H.betaArcBoundary.comp H.betaBoundary).ker ⊓
    (H.maslovIndex χ y y).ker

private theorem mem_selfDomainsIndexZero_iff {Q : Region → ℤ} :
    Q ∈ H.selfDomainsIndexZero χ y ↔
      H.IsDomainBetween y y Q ∧ H.maslovIndex χ y y Q = 0 := by
  simp [selfDomainsIndexZero, and_assoc]

/-- Only finitely many nonnegative domains connect each generator `x` to `y` with each prescribed
Maslov index, whatever their basepoint multiplicities, exactly when the only nonnegative domain
from `y` to itself of Maslov index zero is zero. Such a domain may cover the basepoints, so this
is stronger than weak admissibility at `y`
(`TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_iff_forall_finite`). -/
theorem forall_finite_setOf_isDomainBetween_nonneg_index_iff :
    (∀ (x : H.Generator) (m : ℚ),
      {D : Region → ℤ | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite) ↔
      ∀ Q : Region → ℤ, H.IsDomainBetween y y Q → 0 ≤ Q → H.maslovIndex χ y y Q = 0 → Q = 0 := by
  constructor
  · intro hfin Q hQ hQ₀ hμ
    refine (H.selfDomainsIndexZero χ y).finite_setOf_mem_nonneg_iff.mp
      ((hfin y 0).subset fun Q hQ => ?_) Q (mem_selfDomainsIndexZero_iff.mpr ⟨hQ, hμ⟩) hQ₀
    obtain ⟨hQ, hQ₀⟩ := hQ
    obtain ⟨hdom, hμ⟩ := mem_selfDomainsIndexZero_iff.mp hQ
    exact ⟨hdom, hQ₀, hμ⟩
  · intro h x m
    -- Any two of these domains differ by a domain from `y` to itself of Maslov index zero.
    refine AddSubgroup.finite_of_forall_sub_mem (P := H.selfDomainsIndexZero χ y)
      (fun Q hQ hQ₀ => ?_) (fun _ hD => hD.2.1) fun D ⟨hD, _, hDm⟩ D' ⟨hD', _, hD'm⟩ => ?_
    · obtain ⟨hdom, hμ⟩ := mem_selfDomainsIndexZero_iff.mp hQ
      exact h Q hdom hQ₀ hμ
    · refine mem_selfDomainsIndexZero_iff.mpr ⟨?_, ?_⟩
      · simpa [neg_add_eq_sub] using hD.neg.add hD'
      · rw [← neg_add_eq_sub, hD.neg.maslovIndex_add χ hD', maslovIndex_neg, hDm, hD'm,
          neg_add_cancel]

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
closed surface of genus `n`, and whose periodic domains have even integer Maslov indices at `y`,
as on a geometric Heegaard diagram, strong admissibility at `y` is exactly the finiteness of the
nonnegative domains from each generator to `y` with each prescribed Maslov index. -/
theorem stronglyAdmissible_iff_forall_finite [Subsingleton Basepoint] (z : Basepoint)
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ))
    (heven : ∀ P ∈ H.periodicDomains, ∃ k : ℤ, H.maslovIndex χ y y P = 2 * k) :
    H.StronglyAdmissible χ y ↔ ∀ (x : H.Generator) (m : ℚ),
      {D : Region → ℤ | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  refine ⟨fun hH => hH.finite_setOf_isDomainBetween_nonneg_index hχ, fun hfin P hP hne hμ => ?_⟩
  obtain ⟨k, hk⟩ := heven P hP
  rw [hk, mul_div_cancel_left₀ _ two_ne_zero]
  by_contra! hle
  -- Then `k Σ - P` is a nonnegative domain from `y` to itself of Maslov index zero.
  have hQ := forall_finite_setOf_isDomainBetween_nonneg_index_iff.mp hfin (k • 1 - P)
    (by simpa only [sub_eq_add_neg] using
      ((H.isDomainBetween_one y).zsmul k).add (isDomainBetween_self_iff.mpr hP).1.neg)
    (fun r => by simpa using (show P r ≤ k by exact_mod_cast hle r))
    (by rw [map_sub, map_zsmul, maslovIndex_one_eq_two hχ, hk, zsmul_eq_mul, mul_comm, sub_self])
  -- So `P = k Σ`, and `P` vanishes at the basepoint, so `P = 0`.
  rw [sub_eq_zero] at hQ
  have hk₀ : k = 0 := by simpa [← hQ] using (H.mem_periodicDomains_iff.mp hP).1 z
  exact hne (by rw [← hQ, hk₀, zero_smul])

end Finite

end TauCeti.HeegaardRegionSystem
