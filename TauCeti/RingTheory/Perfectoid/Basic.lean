/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.RingTheory.Huber.Frobenius
public import TauCeti.RingTheory.Huber.Normed

/-!
# Perfectoid Tate rings

Fix a natural number `p` (a prime in all results about Frobenius). A complete Hausdorff Tate ring
`R` with power-bounded subring `R°` is a *perfectoid Tate ring* if

* `R` is uniform, that is, `R°` is bounded, and
* some pseudo-uniformizer `ϖ ∈ R°` has `ϖ ^ p ∣ p` in `R°` and makes the Frobenius
  `Φ : R° ⧸ ϖ → R° ⧸ ϖ ^ p`, `[x] ↦ [x ^ p]`, bijective.

The definition fixes no perfectoid base field: characteristic `0` and characteristic `p` are both
allowed, and the zero ring is perfectoid. The divisibility `ϖ ^ p ∣ p` is asked in `R°`, which
excludes `ℚ_p`, although Frobenius on `ℤ_p ⧸ p` is bijective.

The class `IsPerfectoidTateRing p R` states the Frobenius condition elementwise. Injectivity of
`Φ` is automatic: `R°` is integrally closed in `R`, so `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`
(`TauCeti.Huber.quotientFrobenius_powerBoundedSubring_injective`). Hence a perfectoid Tate ring
may be produced from surjectivity of `Φ` alone (`IsPerfectoidTateRing.of_surjective`).

## Main definitions

* `TauCeti.Perfectoid.IsPerfectoidTateRing p R`: `R` is a perfectoid Tate ring.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_iff`: the definition in terms of the ring homomorphism
  `Φ = Ideal.quotientFrobenius`: `R` is uniform and `Φ` is bijective for some pseudo-uniformizer
  `ϖ ∈ R°` with `ϖ ^ p ∣ p`.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`: surjectivity of `Φ` suffices.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.isUniform`, `IsPerfectoidTateRing.isReduced`: a
  perfectoid Tate ring is uniform, hence reduced.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_ringEquiv`: the condition transports along a ring
  isomorphism that is a homeomorphism.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed`: a complete algebraically closed
  nontrivially normed ultrametric field with `‖p‖ < 1` is perfectoid; in particular `ℂ_p` is
  (`TauCeti.Perfectoid.isPerfectoidTateRing_padicComplex`).
* `TauCeti.Perfectoid.not_isPerfectoidTateRing_padic`: `ℚ_p` is not perfectoid, although
  Frobenius on `ℤ_p ⧸ p` is bijective.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1 and Remarks 3.2–3.3.
* P. Scholze, J. Weinstein, *Berkeley lectures on p-adic geometry*, Definition 6.1.1 and
  Remark 6.1.3.
* K. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Definition 3.3.1.
-/

public section

open Ideal TauCeti.Huber

namespace TauCeti.Perfectoid

/-- A complete Hausdorff Tate ring `R` is a *perfectoid Tate ring* (Scholze, *Étale cohomology of
diamonds*, Definition 3.1) if its power-bounded subring `R°` is bounded and some
pseudo-uniformizer `ϖ ∈ R°` satisfies `ϖ ^ p ∣ p` in `R°` and makes the Frobenius
`R° ⧸ ϖ → R° ⧸ ϖ ^ p`, `[x] ↦ [x ^ p]`, bijective.

Bijectivity is stated elementwise: every `x ∈ R°` is a `p`-th power modulo `ϖ ^ p`
(surjectivity), and `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y` (injectivity, which is automatic, see
`IsPerfectoidTateRing.of_surjective`). `isPerfectoidTateRing_iff` restates it with the ring
homomorphism `Ideal.quotientFrobenius`. -/
class IsPerfectoidTateRing (p : ℕ) (R : Type*) [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] :
    Prop where
  /-- A perfectoid Tate ring is uniform: its power-bounded subring is bounded. -/
  isBounded_powerBoundedSubring : IsBounded (powerBoundedSubring R : Set R)
  /-- Some pseudo-uniformizer `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°` makes the Frobenius
  `R° ⧸ ϖ → R° ⧸ ϖ ^ p` surjective and injective. -/
  exists_pseudoUniformizer : ∃ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) ∧
    ϖ ^ p ∣ (p : powerBoundedSubring R) ∧ (∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) ∧
    ∀ y : powerBoundedSubring R, ϖ ^ p ∣ y ^ p → ϖ ∣ y

section TateRing

variable (p : ℕ) {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]

namespace IsPerfectoidTateRing

/-- **A perfectoid Tate ring is uniform.** -/
theorem isUniform [IsPerfectoidTateRing p R] : IsUniform R :=
  isUniform_iff_isBounded_powerBoundedSubring.mpr (isBounded_powerBoundedSubring (p := p))

/-- **A perfectoid Tate ring is reduced**, being a Hausdorff uniform Tate ring. -/
theorem isReduced [IsPerfectoidTateRing p R] : IsReduced R :=
  have := isUniform p (R := R)
  IsUniform.isReduced

variable {p}

/-- **Surjectivity of the Frobenius suffices.** If `R°` is bounded and some pseudo-uniformizer
`ϖ ∈ R°` with `ϖ ^ p ∣ p` makes every element of `R°` a `p`-th power modulo `ϖ ^ p`, then `R` is
perfectoid; injectivity of `R° ⧸ ϖ → R° ⧸ ϖ ^ p` is automatic. -/
theorem of_surjective (hp : p ≠ 0) (hR : IsBounded (powerBoundedSubring R : Set R))
    {ϖ : powerBoundedSubring R} (hϖ : IsPseudoUniformizer (ϖ : R))
    (hdvd : ϖ ^ p ∣ (p : powerBoundedSubring R))
    (hsurj : ∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) : IsPerfectoidTateRing p R :=
  ⟨hR, ϖ, hϖ, hdvd, hsurj, fun _ ↦ (IsIntegrallyClosedIn.pow_dvd_pow_iff hp hϖ.isUnit).mp⟩

/-- The zero ring is a perfectoid Tate ring: `0` is a topologically nilpotent unit, and every
quotient of `R°` vanishes. -/
instance (priority := 100) of_subsingleton [Subsingleton R] : IsPerfectoidTateRing p R :=
  ⟨isBounded_of_discreteTopology _, 0,
    isPseudoUniformizer_iff.mpr ⟨isUnit_of_subsingleton _, .zero⟩,
    by simp [Subsingleton.elim (p : powerBoundedSubring R) 0], fun x ↦ ⟨0, by
      simp [Subsingleton.elim (x - 0 ^ p) 0]⟩, fun y _ ↦ by simp [Subsingleton.elim y 0]⟩

section Transport

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsTateRing S] [CompleteSpace S] [T2Space S]

/-- **Perfectoidness transports along a ring isomorphism that is a homeomorphism.** -/
theorem of_ringEquiv [IsPerfectoidTateRing p R] (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) : IsPerfectoidTateRing p S := by
  obtain ⟨ϖ, hϖ, hdvd, hsurj, hinj⟩ := exists_pseudoUniformizer (p := p) (R := R)
  set f := powerBoundedSubringEquiv e he he'
  refine ⟨?_, f ϖ, ?_, ?_, fun x ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← map_powerBoundedSubring e he he', Subring.coe_map, RingEquiv.coe_toRingHom,
      isBounded_image_ringEquiv_iff e he he']
    exact isBounded_powerBoundedSubring (p := p)
  · rw [powerBoundedSubringEquiv_apply]
    exact hϖ.map he
  · simpa only [map_pow, map_natCast] using map_dvd f hdvd
  · obtain ⟨y, hy⟩ := hsurj (f.symm x)
    exact ⟨f y, by simpa only [map_sub, map_pow, RingEquiv.apply_symm_apply] using map_dvd f hy⟩
  · have hy' := map_dvd f.symm hy
    rw [map_pow, map_pow, RingEquiv.symm_apply_apply] at hy'
    simpa only [RingEquiv.apply_symm_apply] using map_dvd f (hinj _ hy')

end Transport

end IsPerfectoidTateRing

/-- **A perfectoid Tate ring is a uniform Tate ring with a bijective Frobenius**
`R° ⧸ ϖ → R° ⧸ ϖ ^ p` for some pseudo-uniformizer `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°`. This is the
form of Scholze's definition with the ring homomorphism `Ideal.quotientFrobenius`. -/
theorem isPerfectoidTateRing_iff [Fact p.Prime] :
    IsPerfectoidTateRing p R ↔ IsUniform R ∧
      ∃ (ϖ : powerBoundedSubring R) (hp : (p : powerBoundedSubring R) ∈ span {ϖ ^ p}),
        IsPseudoUniformizer (ϖ : R) ∧
        Function.Bijective (quotientFrobenius (span {ϖ}) (span {ϖ ^ p}) p hp
          fun _ hx ↦ mem_span_singleton.mpr (pow_dvd_pow_of_dvd (mem_span_singleton.mp hx) p)) := by
  refine ⟨fun h ↦ ⟨IsPerfectoidTateRing.isUniform p, ?_⟩, fun ⟨hR, ϖ, hp, hϖ, hbij⟩ ↦ ?_⟩
  · obtain ⟨ϖ, hϖ, hdvd, hsurj, -⟩ := h.exists_pseudoUniformizer
    refine ⟨ϖ, mem_span_singleton.mpr hdvd, hϖ,
      quotientFrobenius_powerBoundedSubring_injective p hϖ.isUnit _ _, ?_⟩
    rw [quotientFrobenius_surjective_iff]
    simpa only [mem_span_singleton] using hsurj
  · have hsurj := (quotientFrobenius_surjective_iff _ _).mp hbij.2
    simp only [mem_span_singleton] at hp hsurj
    exact .of_surjective (Fact.out : p.Prime).ne_zero hR.isBounded_powerBoundedSubring hϖ hp hsurj

end TateRing

section Examples

/-- **A complete algebraically closed nonarchimedean field with `‖p‖ < 1` is perfectoid.** If
`K` is a complete algebraically closed ultrametric nontrivially normed field and `p ≠ 0` is a
natural number with `‖(p : K)‖ < 1`, then `K` is a perfectoid Tate ring at `p`. -/
theorem isPerfectoidTateRing_of_isAlgClosed {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] {p : ℕ} (hp : p ≠ 0)
    (hpK : ‖(p : K)‖ < 1) : IsPerfectoidTateRing p K := by
  -- an element `c` with `0 < ‖c‖ < 1` and `‖p‖ ≤ ‖c‖`
  obtain ⟨c, hc0, hc1, hpc⟩ : ∃ c : K, c ≠ 0 ∧ ‖c‖ < 1 ∧ ‖(p : K)‖ ≤ ‖c‖ := by
    by_cases h : (p : K) = 0
    · obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
      exact ⟨c, norm_pos_iff.mp hc0, hc1, by simp [h]⟩
    · exact ⟨p, h, hpK, le_rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hp)
  have hϖ1 : ‖ϖ‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg ϖ) hp, ← norm_pow, hϖ]
    exact hc1
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hc0 (by rw [← hϖ, zero_pow hp])
  have hmem {x : K} (hx : ‖x‖ ≤ 1) : x ∈ powerBoundedSubring K :=
    mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr hx)
  refine .of_surjective hp
    (IsUniform.isBounded_powerBoundedSubring (A := K)) (ϖ := ⟨ϖ, hmem hϖ1.le⟩)
    (isPseudoUniformizer_iff_norm_lt_one.mpr ⟨hϖ0, hϖ1⟩) ⟨⟨p / c, hmem ?_⟩, ?_⟩ fun x ↦ ?_
  · rw [norm_div]
    exact div_le_one_of_le₀ hpc (norm_nonneg c)
  · ext
    simp [hϖ, mul_div_cancel₀ _ hc0]
  · obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) (Nat.pos_of_ne_zero hp)
    have hy1 : ‖y‖ ≤ 1 := by
      rw [← pow_le_one_iff_of_nonneg (norm_nonneg y) hp, ← norm_pow, hy]
      exact isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.2)
    refine ⟨⟨y, hmem hy1⟩, ⟨0, ?_⟩⟩
    ext
    simp [hy]

/-- **`ℂ_p` is a perfectoid Tate ring.** -/
instance isPerfectoidTateRing_padicComplex (p : ℕ) [Fact p.Prime] :
    IsPerfectoidTateRing p ℂ_[p] :=
  isPerfectoidTateRing_of_isAlgClosed (Fact.out : p.Prime).ne_zero (by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt))

/-- **`ℚ_p` is not a perfectoid Tate ring** (Scholze, *Étale cohomology of diamonds*,
Remark 3.3). A pseudo-uniformizer `ϖ` of `ℚ_p` has `‖ϖ‖ ≤ p⁻¹`, so `‖ϖ ^ p‖ < ‖p‖` and `ϖ ^ p`
does not divide `p` in `ℤ_p`, although Frobenius on `ℤ_p ⧸ p = 𝔽_p` is bijective. -/
theorem not_isPerfectoidTateRing_padic (p : ℕ) [hp : Fact p.Prime] :
    ¬ IsPerfectoidTateRing p ℚ_[p] := by
  intro h
  obtain ⟨ϖ, hϖ, ⟨c, hc⟩, -⟩ := h.exists_pseudoUniformizer
  obtain ⟨hϖ0, hϖ1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp hϖ
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  -- `‖ϖ‖ < 1` forces `‖ϖ‖ ≤ p⁻¹`, the norms of `ℚ_p` being integer powers of `p`
  have hϖp : ‖(ϖ : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    simpa using (Padic.norm_le_pow_iff_norm_lt_pow_add_one (ϖ : ℚ_[p]) (-1)).mpr (by simpa)
  have hc1 : ‖(c : ℚ_[p])‖ ≤ 1 := isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.2)
  have hnorm : (p : ℝ)⁻¹ = ‖(ϖ : ℚ_[p])‖ ^ p * ‖(c : ℚ_[p])‖ := by
    rw [← Padic.norm_p, ← norm_pow, ← norm_mul]
    exact congrArg (‖·‖) (congrArg Subtype.val hc)
  have hlt : ‖(ϖ : ℚ_[p])‖ ^ p < (p : ℝ)⁻¹ :=
    calc ‖(ϖ : ℚ_[p])‖ ^ p ≤ (p : ℝ)⁻¹ ^ p := by gcongr
      _ < (p : ℝ)⁻¹ := pow_lt_self_of_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1)
          hp.out.one_lt
  have : ‖(ϖ : ℚ_[p])‖ ^ p * ‖(c : ℚ_[p])‖ < (p : ℝ)⁻¹ :=
    (mul_le_of_le_one_right (by positivity) hc1).trans_lt hlt
  exact this.ne hnorm.symm

end Examples

end TauCeti.Perfectoid
