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
In a singly pointed diagram of a closed surface, strong admissibility at `y` gives more: the
nonnegative domains from `x` to `y` with fixed Maslov index are finite whatever their basepoint
multiplicity. A domain from `y` to itself is a periodic domain plus `n_z` copies of the whole
surface `Σ`, which has Maslov index two, so strong admissibility at `y` is the statement that
no nonzero nonnegative domain from `y` to itself has Maslov index zero, and Dickson's lemma turns
this into finiteness. This is the finiteness needed for differentials that count holomorphic
disks of every basepoint multiplicity, recording `n_z` as a power of a formal variable `U`.

## Main definitions

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible`: every nonzero periodic domain of
  nonnegative Maslov index `2m` has a coefficient greater than `m`.

## Main results

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.weaklyAdmissibleAt`: strong admissibility
  at a generator implies weak admissibility there.
* `TauCeti.HeegaardRegionSystem.stronglyAdmissible_iff_forall_isDomainBetween_self`: in a singly
  pointed diagram, strong admissibility at `y` says that the only nonnegative domain from `y` to
  itself of Maslov index zero is zero.
* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.finite_setOf_isDomainBetween_nonneg_index`:
  strong admissibility at `y` makes the nonnegative domains from `x` to `y` of each Maslov index
  finite.
* `TauCeti.HeegaardRegionSystem.stronglyAdmissible_iff_forall_finite`: conversely, this
  finiteness characterizes strong admissibility at `y`.

## References

P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Ann. of Math. **159** (2004),
[arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.2: Definition 4.10 (strong
admissibility for a spin^c structure) and Lemmas 4.13–4.14 (finiteness of nonnegative classes
in admissible diagrams).
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

section Finiteness

variable {χ : Region → ℤ} {x y : H.Generator} {E : Region → ℤ}

variable (H) in
/-- The domains from `y` to itself of Maslov index zero at `y`; any two nonnegative domains from
`x` to `y` of the same Maslov index differ by one of them. -/
private def selfDomainsIndexZero (χ : Region → ℤ) (y : H.Generator) :
    AddSubgroup (Region → ℤ) where
  carrier := {E | H.IsDomainBetween y y E ∧ H.maslovIndex χ y y E = 0}
  add_mem' {E F} hE hF :=
    ⟨hE.1.add hF.1, by rw [hE.1.maslovIndex_add χ hF.1, hE.2, hF.2, add_zero]⟩
  zero_mem' := ⟨isDomainBetween_zero y, map_zero _⟩
  neg_mem' {E} hE := ⟨hE.1.neg, by rw [maslovIndex_neg, hE.2, neg_zero]⟩

private theorem mem_selfDomainsIndexZero :
    E ∈ H.selfDomainsIndexZero χ y ↔ H.IsDomainBetween y y E ∧ H.maslovIndex χ y y E = 0 :=
  Iff.rfl

variable [Subsingleton Basepoint] (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ))
include hχ

/-- In a singly pointed diagram of a closed surface of genus `n` that is strongly admissible at
`y`, the only nonnegative domain from `y` to itself of Maslov index zero is zero. Unlike weak
admissibility at `y`, which only excludes such domains with multiplicity zero at the basepoint,
this excludes them for every basepoint multiplicity. -/
theorem StronglyAdmissible.eq_zero_of_isDomainBetween_self (hH : H.StronglyAdmissible χ y)
    (hE : H.IsDomainBetween y y E) (hE₀ : 0 ≤ E) (hμ : H.maslovIndex χ y y E = 0) : E = 0 := by
  -- Write `E = Q + m Σ` with `Q` periodic and `m ≥ 0`; then `μ(-Q) = 2m` and `-Q ≤ m`.
  obtain ⟨m, hm, hQ⟩ := hE.exists_nonneg_sub_smul_one_mem_periodicDomains hE₀
  have hμQ : H.maslovIndex χ y y (-(E - m • 1)) = 2 * m := by
    rw [map_neg, map_sub, map_zsmul, maslovIndex_one_eq_two hχ, hμ, zsmul_eq_mul]
    ring
  have hQ₀ : E - m • 1 = 0 := by
    by_contra hne
    obtain ⟨r, hr⟩ := hH _ (neg_mem hQ) (neg_ne_zero.mpr hne) (by rw [hμQ]; positivity)
    rw [hμQ] at hr
    have hEr : (0 : ℚ) ≤ E r := by exact_mod_cast hE₀ r
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      neg_sub, Int.cast_sub] at hr
    linarith
  -- So `-Q = 0` has Maslov index `2m = 0`, and `E = Q + m Σ = 0`.
  have hm₀ : m = 0 := by
    rw [hQ₀, neg_zero, map_zero] at hμQ
    exact_mod_cast (mul_eq_zero.mp hμQ.symm).resolve_left two_ne_zero
  simpa [hm₀] using hQ₀

/-- A singly pointed diagram of a closed surface of genus `n` is strongly admissible at `y`
exactly when its only nonnegative domain from `y` to itself of Maslov index zero is zero. If a
nonzero periodic domain `P` of index `2m ≥ 0` has every coefficient at most `m`, then a multiple
of `m Σ - P` is a nonzero nonnegative domain of index zero from `y` to itself. -/
theorem stronglyAdmissible_iff_forall_isDomainBetween_self [Nonempty Basepoint] :
    H.StronglyAdmissible χ y ↔ ∀ E, H.IsDomainBetween y y E → 0 ≤ E →
      H.maslovIndex χ y y E = 0 → E = 0 := by
  refine ⟨fun hH E => hH.eq_zero_of_isDomainBetween_self hχ, fun h P hP hne hidx => ?_⟩
  obtain ⟨z⟩ := ‹Nonempty Basepoint›
  by_contra hcon
  push Not at hcon
  -- The index of `P` is `k / 4`, so `E = k Σ - 8 P` is nonnegative of index zero.
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (H.maslovIndex_mem_zmultiples_inv_four χ y y P)
  rw [zsmul_eq_mul] at hk
  have hE : H.IsDomainBetween y y (k • 1 - (8 : ℤ) • P) := by
    obtain ⟨-, hα, hβ⟩ := mem_periodicDomains_iff.mp hP
    simp only [isDomainBetween_iff, sub_self, map_sub, map_zsmul, alphaBoundary_one,
      betaBoundary_one, hα, hβ, smul_zero, map_zero, and_self]
  have hE₀ : 0 ≤ k • (1 : Region → ℤ) - (8 : ℤ) • P := fun r => by
    have hr : (8 * P r : ℚ) ≤ k := by linarith [hcon r]
    simpa using (by exact_mod_cast hr : 8 * P r ≤ k)
  have hμ : H.maslovIndex χ y y (k • 1 - (8 : ℤ) • P) = 0 := by
    rw [map_sub, map_zsmul, map_zsmul, maslovIndex_one_eq_two hχ, ← hk, zsmul_eq_mul,
      zsmul_eq_mul]
    push_cast
    ring
  -- Evaluating `E = 0` at the basepoint gives `k = 0`, and then `8 P = 0`.
  have h0 := h _ hE hE₀ hμ
  have hk₀ : k = 0 := by
    simpa [(mem_periodicDomains_iff.mp hP).1 z] using congr_fun h0 (H.basepoint z)
  exact hne (funext fun r => by simpa [hk₀] using congr_fun h0 r)

/-- In a singly pointed diagram of a closed surface of genus `n` that is strongly admissible at
`y`, only finitely many nonnegative domains connect `x` to `y` with prescribed Maslov index `m`.
Their basepoint multiplicities are not prescribed, in contrast to the finiteness given by weak
admissibility at `y`
(`WeaklyAdmissibleAt.finite_setOf_isDomainBetween_basepoint_eq_nonneg_index`);
this is the finiteness behind differentials that record every basepoint multiplicity by a power
of a formal variable. -/
theorem StronglyAdmissible.finite_setOf_isDomainBetween_nonneg_index
    (hH : H.StronglyAdmissible χ y) (x : H.Generator) (m : ℚ) :
    {D : Region → ℤ | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite :=
  -- Any two of these domains differ by a domain from `y` to itself of Maslov index zero.
  AddSubgroup.finite_of_forall_sub_mem (P := H.selfDomainsIndexZero χ y)
    (fun E hE hE₀ => hH.eq_zero_of_isDomainBetween_self hχ (mem_selfDomainsIndexZero.mp hE).1 hE₀
      (mem_selfDomainsIndexZero.mp hE).2)
    (fun _ hD => hD.2.1) fun D ⟨hD, _, hDm⟩ D' ⟨hD', _, hD'm⟩ => by
      rw [mem_selfDomainsIndexZero, sub_eq_neg_add]
      refine ⟨hD.neg.add hD', ?_⟩
      rw [hD.neg.maslovIndex_add χ hD', maslovIndex_neg, hDm, hD'm, neg_add_cancel]

/-- A singly pointed diagram of a closed surface of genus `n` is strongly admissible at `y`
exactly when, for every generator `x` and Maslov index `m`, only finitely many nonnegative
domains connect `x` to `y` with this Maslov index. Without strong admissibility at `y`, the
multiples of a nonzero nonnegative domain of index zero from `y` to itself are infinitely many
such domains. -/
theorem stronglyAdmissible_iff_forall_finite [Nonempty Basepoint] :
    H.StronglyAdmissible χ y ↔ ∀ (x : H.Generator) (m : ℚ),
      {D : Region → ℤ | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = m}.Finite := by
  refine ⟨fun hH => hH.finite_setOf_isDomainBetween_nonneg_index hχ,
    fun hfin => (stronglyAdmissible_iff_forall_isDomainBetween_self hχ).mpr fun E hE hE₀ hμ =>
      (H.selfDomainsIndexZero χ y).finite_setOf_mem_nonneg_iff.mp ((hfin y 0).subset ?_) E
        (mem_selfDomainsIndexZero.mpr ⟨hE, hμ⟩) hE₀⟩
  rintro F ⟨hF, hF₀⟩
  exact ⟨(mem_selfDomainsIndexZero.mp hF).1, hF₀, (mem_selfDomainsIndexZero.mp hF).2⟩

end Finiteness

end TauCeti.HeegaardRegionSystem
