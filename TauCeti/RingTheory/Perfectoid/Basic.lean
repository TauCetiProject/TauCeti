/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Perfectoid Tate rings

Fix a prime `p`. A complete Hausdorff Tate ring `R`, with power-bounded subring `R°`, is a
*perfectoid Tate ring* if

* `R` is uniform, that is, `R°` is bounded; and
* some pseudouniformiser `ϖ ∈ R°` satisfies `ϖ ^ p ∣ p` in `R°`, and Frobenius
  `Φ : R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)`, `[x] ↦ [x ^ p]`, is bijective.

No perfectoid base field is fixed, and both characteristic `0` and characteristic `p` are allowed.
Uniformity is not implied by the second condition, and the divisibility `ϖ ^ p ∣ p` must hold in
`R°`, not merely in `R`, where it is automatic since `ϖ` is a unit of `R`. It makes `[x] ↦ [x ^ p]`
a ring homomorphism `R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)` (`TauCeti.frobeniusModPow`). Bijectivity of Frobenius
on `R° ⧸ (p)` alone is not enough: it holds on `ℤ_p ⧸ p = 𝔽_p`, yet `ℚ_p` is not perfectoid, as the
definition asks for the different map modulo `ϖ ^ p`.

The class `TauCeti.Perfectoid.IsPerfectoidTateRing` states the second condition elementwise, and
`TauCeti.Perfectoid.isPerfectoidTateRing_iff` recovers the bijectivity of
`TauCeti.frobeniusModPow`. Injectivity of `Φ` is automatic, because `R°` is integrally closed in
`R` and `ϖ` is a unit of `R` (`TauCeti.frobeniusModPow_injective`). So only
surjectivity of `Φ` has to be checked (`TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`).

## Main definitions

* `TauCeti.Perfectoid.IsPerfectoidTateRing p R`: `R` is a perfectoid Tate ring.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_iff`: the definition in terms of bijectivity of
  `Φ : R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)`.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`: surjectivity of `Φ` suffices.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.isUniform`,
  `TauCeti.Perfectoid.IsPerfectoidTateRing.isReduced`: perfectoid Tate rings are uniform, hence
  reduced.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_ringEquiv`: the notion is invariant under
  isomorphisms of topological rings.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_perfectRing`: a uniform perfect Tate ring of
  characteristic `p` is perfectoid.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_subsingleton`: the zero ring is.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1 and Remarks 3.2–3.3.
* P. Scholze, *Perfectoid spaces*, Definition 5.1 and Proposition 5.8.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, §3.2.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

section Definition

/-- A complete Hausdorff Tate ring `R` is a *perfectoid Tate ring* if (a) `R` is uniform, i.e.
the power-bounded subring `R°` is bounded, and (b) some pseudouniformiser `ϖ ∈ R°` has
`ϖ ^ p ∣ p` in `R°` and Frobenius `R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)`, `[x] ↦ [x ^ p]`, is bijective
(Scholze, *Étale cohomology of diamonds*, Definition 3.1). Condition (b) is stated elementwise:
every `x ∈ R°` is a `p`-th power modulo `ϖ ^ p`, and `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`; see
`isPerfectoidTateRing_iff` for the form with `frobeniusModPow`. -/
class IsPerfectoidTateRing (p : ℕ) (R : Type*) [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] :
    Prop where
  /-- (a) `R` is uniform: the power-bounded subring `R°` is bounded. -/
  isBounded_powerBoundedSubring : IsBounded (powerBoundedSubring R : Set R)
  /-- (b) a pseudouniformiser `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°` for which Frobenius
  `R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)` is surjective and injective. -/
  exists_pseudoUniformizer : ∃ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) ∧
    ϖ ^ p ∣ (p : powerBoundedSubring R) ∧
    (∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) ∧
    ∀ y : powerBoundedSubring R, ϖ ^ p ∣ y ^ p → ϖ ∣ y

variable (p : ℕ) {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]

/-- A perfectoid Tate ring is uniform. -/
theorem IsPerfectoidTateRing.isUniform [IsPerfectoidTateRing p R] : IsUniform R :=
  isUniform_iff_isBounded_powerBoundedSubring.mpr
    (IsPerfectoidTateRing.isBounded_powerBoundedSubring (p := p))

/-- A perfectoid Tate ring is reduced, being a Hausdorff uniform Tate ring (Scholze,
*Perfectoid spaces*, proof of Proposition 5.8). -/
theorem IsPerfectoidTateRing.isReduced [IsPerfectoidTateRing p R] : IsReduced R :=
  have := IsPerfectoidTateRing.isUniform p (R := R)
  IsUniform.isReduced

variable {p}

/-- **Surjectivity of Frobenius suffices**: a uniform complete Hausdorff Tate ring with a
pseudouniformiser `ϖ ∈ R°` such that `ϖ ^ p ∣ p` in `R°` and every element of `R°` is a `p`-th
power modulo `ϖ ^ p` is perfectoid; injectivity of Frobenius is automatic (Scholze, *Étale
cohomology of diamonds*, Remark 3.2). -/
theorem IsPerfectoidTateRing.of_surjective [NeZero p] [IsUniform R] (ϖ : powerBoundedSubring R)
    (hϖ : IsPseudoUniformizer (ϖ : R)) (h : ϖ ^ p ∣ (p : powerBoundedSubring R))
    (hs : ∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) : IsPerfectoidTateRing p R where
  isBounded_powerBoundedSubring := IsUniform.isBounded_powerBoundedSubring
  exists_pseudoUniformizer := ⟨ϖ, hϖ, h, hs, fun _ ↦
    (IsIntegrallyClosedIn.pow_dvd_pow_iff (A := R) (NeZero.ne p) hϖ.isUnit).mp⟩

/-- **Perfectoid Tate rings via Frobenius**: `R` is perfectoid exactly when it is uniform and
some pseudouniformiser `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°` makes Frobenius
`R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)` bijective. -/
theorem isPerfectoidTateRing_iff [Fact p.Prime] :
    IsPerfectoidTateRing p R ↔ IsUniform R ∧ ∃ ϖ : powerBoundedSubring R,
      IsPseudoUniformizer (ϖ : R) ∧ ∃ h : ϖ ^ p ∣ (p : powerBoundedSubring R),
        Function.Bijective (frobeniusModPow p h) := by
  refine ⟨fun hR ↦ ⟨hR.isUniform p, ?_⟩, fun ⟨_, ϖ, hϖ, h, hbij⟩ ↦ ?_⟩
  · obtain ⟨ϖ, hϖ, h, hs, hi⟩ := hR.exists_pseudoUniformizer
    exact ⟨ϖ, hϖ, h, (frobeniusModPow_injective_iff h).mpr hi,
      (frobeniusModPow_surjective_iff h).mpr hs⟩
  · exact .of_surjective ϖ hϖ h ((frobeniusModPow_surjective_iff h).mp hbij.2)

/-- A uniform complete Hausdorff Tate ring with a pseudouniformiser `ϖ ∈ R°` such that
`ϖ ^ p ∣ p` in `R°`, and in which every element of `R°` has a `p`-th root in `R`, is perfectoid:
the roots are power-bounded because `R°` is integrally closed in `R`. -/
theorem IsPerfectoidTateRing.of_forall_exists_pow_eq [NeZero p] [IsUniform R]
    (ϖ : powerBoundedSubring R) (hϖ : IsPseudoUniformizer (ϖ : R))
    (h : ϖ ^ p ∣ (p : powerBoundedSubring R))
    (hroot : ∀ x : powerBoundedSubring R, ∃ y : R, y ^ p = x) : IsPerfectoidTateRing p R := by
  refine .of_surjective ϖ hϖ h fun x ↦ ?_
  obtain ⟨y, hy⟩ := hroot x
  obtain ⟨z, rfl⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := powerBoundedSubring R) (x := y) (NeZero.pos p) (hy ▸ isIntegral_algebraMap)
  have hx : x = z ^ p := Subtype.ext hy.symm
  refine ⟨z, ?_⟩
  rw [hx, sub_self]
  exact dvd_zero _

/-- **A uniform perfect Tate ring of characteristic `p` is perfectoid** (Scholze, *Étale cohomology
of diamonds*, Proposition 3.5): every pseudouniformiser works, `ϖ ^ p ∣ p = 0` being automatic,
and Frobenius is bijective. -/
theorem IsPerfectoidTateRing.of_perfectRing [Fact p.Prime] [CharP R p] [PerfectRing R p]
    [IsUniform R] : IsPerfectoidTateRing p R := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := R)
  have hp : (p : powerBoundedSubring R) = 0 := Subtype.ext (CharP.cast_eq_zero R p)
  exact .of_forall_exists_pow_eq ⟨ϖ, mem_powerBoundedSubring.mpr
    (IsPowerBounded.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent)⟩ hϖ
    (hp ▸ dvd_zero _) fun x ↦
      (surjective_frobenius R p x).imp fun _ h ↦ by rwa [frobenius_def] at h

/-- **Perfectoid Tate rings transport along isomorphisms of topological rings.** -/
theorem IsPerfectoidTateRing.of_ringEquiv {S : Type*} [CommRing S] [UniformSpace S]
    [IsUniformAddGroup S] [IsTopologicalRing S] [IsTateRing S] [CompleteSpace S] [T2Space S]
    [IsPerfectoidTateRing p R] (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) :
    IsPerfectoidTateRing p S := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  have := IsUniform.of_ringEquiv e he he'
  obtain ⟨ϖ, hϖ, h, hs, hi⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  set f := powerBoundedSubringEquiv e he he'
  refine ⟨IsUniform.isBounded_powerBoundedSubring, f ϖ, ?_, ?_, fun x ↦ ?_, fun y hy ↦ ?_⟩
  · rw [powerBoundedSubringEquiv_apply]
    exact hϖ.map he
  · simpa using map_dvd f h
  · obtain ⟨y, hy⟩ := hs (f.symm x)
    exact ⟨f y, by simpa using map_dvd f hy⟩
  · simpa using map_dvd f (hi (f.symm y) (by simpa using map_dvd f.symm hy))

end Definition

section Examples

variable (p : ℕ)

/-- **The zero ring is a perfectoid Tate ring**: `0` is a topologically nilpotent unit, and all
the quotients in the definition vanish. -/
theorem isPerfectoidTateRing_of_subsingleton (R : Type*) [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]
    [Subsingleton R] : IsPerfectoidTateRing p R where
  isBounded_powerBoundedSubring := isBounded_iff.mpr fun _ hU ↦ ⟨Set.univ, Filter.univ_mem,
    fun x _ ↦ Subsingleton.elim (0 : R) x ▸ mem_of_mem_nhds hU⟩
  exists_pseudoUniformizer := ⟨0, isPseudoUniformizer_iff.mpr ⟨isUnit_of_subsingleton _, .zero⟩,
    ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ ⟨0, ⟨0, Subsingleton.elim _ _⟩⟩,
    fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end Examples

end TauCeti.Perfectoid
