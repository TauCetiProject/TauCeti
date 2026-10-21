/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Perfectoid Tate rings

Fix a prime `p`. A complete Hausdorff Tate ring `R`, with ring `R°` of power-bounded elements, is a
*perfectoid Tate ring* if

* `R` is uniform, that is, `R°` is bounded, and
* some pseudouniformiser `ϖ ∈ R°` satisfies `ϖ ^ p ∣ p` in `R°` (not merely in `R`), and
  Frobenius `R° ⧸ ϖ →+* R° ⧸ ϖ ^ p`, `[x] ↦ [x ^ p]`, is bijective.

No perfectoid base field is fixed. Both characteristic `0` and characteristic `p` are allowed (if
`p = 0` in `R` the divisibility is automatic), and `p` may be a nonzero nonunit, as in a product of
a perfectoid field of characteristic `0` with one of characteristic `p`. The zero ring is
perfectoid. These are the local models of perfectoid spaces.

The class `TauCeti.Perfectoid.IsPerfectoidTateRing` states the Frobenius condition elementwise:
every element of `R°` is a `p`-th power modulo `ϖ ^ p`, and `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`. The
second clause is in fact automatic for every `ϖ ∈ R°` invertible in `R`, because `R°` is integrally
closed in `R` (`TauCeti.Perfectoid.injective_frobeniusModPow`); so a uniform Tate ring is
perfectoid as soon as Frobenius is surjective for one such `ϖ`
(`TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`). Uniformity cannot be dropped, and is not
implied by the Frobenius condition; it makes a perfectoid Tate ring reduced.

## Main definitions

* `TauCeti.Perfectoid.IsPerfectoidTateRing p R`: `R` is a perfectoid Tate ring.

## Main results

* `TauCeti.Perfectoid.injective_frobeniusModPow`: Frobenius `R° ⧸ ϖ →+* R° ⧸ ϖ ^ p` is injective
  for every `ϖ ∈ R°` that is a unit of `R` and satisfies `ϖ ^ p ∣ p` in `R°`.
* `TauCeti.Perfectoid.isPerfectoidTateRing_iff`: `R` is perfectoid iff it is uniform and Frobenius
  is surjective for some pseudouniformiser `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°`.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`: the corresponding constructor.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.exists_bijective_frobeniusModPow`: a perfectoid Tate
  ring has a pseudouniformiser for which Frobenius is bijective.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.isUniform` and
  `TauCeti.Perfectoid.IsPerfectoidTateRing.isReduced`: perfectoid Tate rings are uniform, hence
  reduced.
* `TauCeti.Perfectoid.isPerfectoidTateRing_iff_of_ringEquiv`: the notion transports along
  isomorphisms of topological rings.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_subsingleton`: the zero ring is perfectoid.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Definition 3.1 and Remark 3.2.
* P. Scholze, J. Weinstein, *Berkeley lectures on p-adic geometry*, Definition 6.1.1 and
  Remark 6.1.3.
* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Definition 3.3.1.
* P. Scholze, *Perfectoid spaces*, Proposition 5.8 (perfectoid rings are reduced).
-/

public section

open Function

namespace TauCeti.Perfectoid

open Huber

section Nonarchimedean

variable {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanAddGroup R]
  [SeparatelyContinuousMul R] {p : ℕ} [hp : Fact p.Prime]

/-- **Frobenius modulo a unit is injective on power-bounded elements.** If `ϖ ∈ R°` is a unit of
`R` with `ϖ ^ p ∣ p` in `R°`, then `R° ⧸ ϖ →+* R° ⧸ ϖ ^ p` is injective: if `ϖ ^ p ∣ y ^ p` in
`R°`, then `y / ϖ ∈ R` has `p`-th power in `R°`, so it is integral over `R°` and lies in `R°`. -/
theorem injective_frobeniusModPow {ϖ : powerBoundedSubring R} (hϖ : IsUnit (ϖ : R))
    (h : ϖ ^ p ∣ (p : powerBoundedSubring R)) : Injective (frobeniusModPow ϖ p h) :=
  (injective_frobeniusModPow_iff ϖ p h).mpr fun _ ↦
    (IsIntegrallyClosedIn.pow_dvd_pow_iff (A := R) hp.out.ne_zero hϖ).mp

end Nonarchimedean

/-- **Perfectoid Tate rings** (Scholze, *Étale cohomology of diamonds*, Definition 3.1). A complete
Hausdorff Tate ring `R` is perfectoid if its ring `R°` of power-bounded elements is bounded and
some pseudouniformiser `ϖ ∈ R°` has `ϖ ^ p ∣ p` in `R°` and Frobenius
`R° ⧸ ϖ →+* R° ⧸ ϖ ^ p` bijective. The bijectivity is stated elementwise; see
`TauCeti.Perfectoid.isPerfectoidTateRing_iff` for the formulation with
`TauCeti.frobeniusModPow`. -/
class IsPerfectoidTateRing (p : ℕ) (R : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] : Prop where
  /-- A perfectoid Tate ring is uniform: its ring `R°` of power-bounded elements is bounded. -/
  isUniform : IsUniform R
  /-- Some pseudouniformiser `ϖ ∈ R°` has `ϖ ^ p ∣ p` in `R°`, every element of `R°` is a `p`-th
  power modulo `ϖ ^ p`, and `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y` in `R°`. -/
  exists_pseudoUniformizer : ∃ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) ∧
    ϖ ^ p ∣ (p : powerBoundedSubring R) ∧ (∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) ∧
    ∀ y : powerBoundedSubring R, ϖ ^ p ∣ y ^ p → ϖ ∣ y

variable {p : ℕ} {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]

namespace IsPerfectoidTateRing

variable (p) in
/-- **A perfectoid Tate ring is reduced**, being a Hausdorff uniform Tate ring
(Scholze, *Perfectoid spaces*, Proposition 5.8). -/
theorem isReduced [IsPerfectoidTateRing p R] : IsReduced R :=
  have := isUniform (p := p) (R := R)
  IsUniform.isReduced

variable [Fact p.Prime]

/-- **A perfectoid Tate ring has a pseudouniformiser for which Frobenius is bijective**: some
pseudouniformiser `ϖ ∈ R°` has `ϖ ^ p ∣ p` in `R°` and `R° ⧸ ϖ →+* R° ⧸ ϖ ^ p` bijective. -/
theorem exists_bijective_frobeniusModPow [IsPerfectoidTateRing p R] :
    ∃ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) ∧
      ∃ h : ϖ ^ p ∣ (p : powerBoundedSubring R), Bijective (frobeniusModPow ϖ p h) := by
  obtain ⟨ϖ, hϖ, h, hs, hi⟩ := exists_pseudoUniformizer (p := p) (R := R)
  exact ⟨ϖ, hϖ, h, (injective_frobeniusModPow_iff ϖ p h).mpr hi,
    (surjective_frobeniusModPow_iff ϖ p h).mpr hs⟩

/-- **Surjectivity of Frobenius suffices** (Scholze, *Étale cohomology of diamonds*, Remark 3.2):
a uniform Tate ring with a pseudouniformiser `ϖ ∈ R°` such that `ϖ ^ p ∣ p` in `R°` and
`R° ⧸ ϖ →+* R° ⧸ ϖ ^ p` is surjective is perfectoid. Injectivity is automatic, by
`TauCeti.Perfectoid.injective_frobeniusModPow`. -/
theorem of_surjective [IsUniform R] (ϖ : powerBoundedSubring R) (hϖ : IsPseudoUniformizer (ϖ : R))
    (h : ϖ ^ p ∣ (p : powerBoundedSubring R)) (hs : Surjective (frobeniusModPow ϖ p h)) :
    IsPerfectoidTateRing p R where
  isUniform := ‹_›
  exists_pseudoUniformizer := ⟨ϖ, hϖ, h, (surjective_frobeniusModPow_iff ϖ p h).mp hs,
    (injective_frobeniusModPow_iff ϖ p h).mp (injective_frobeniusModPow hϖ.isUnit h)⟩

end IsPerfectoidTateRing

/-- **Characterisation of perfectoid Tate rings.** `R` is perfectoid exactly when it is uniform and
some pseudouniformiser `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°` makes Frobenius
`R° ⧸ ϖ →+* R° ⧸ ϖ ^ p` surjective. -/
theorem isPerfectoidTateRing_iff [Fact p.Prime] :
    IsPerfectoidTateRing p R ↔ IsUniform R ∧ ∃ ϖ : powerBoundedSubring R,
      IsPseudoUniformizer (ϖ : R) ∧
        ∃ h : ϖ ^ p ∣ (p : powerBoundedSubring R), Surjective (frobeniusModPow ϖ p h) := by
  refine ⟨fun hR ↦ ⟨IsPerfectoidTateRing.isUniform (p := p), ?_⟩, fun ⟨_, ϖ, hϖ, h, hs⟩ ↦
    IsPerfectoidTateRing.of_surjective ϖ hϖ h hs⟩
  obtain ⟨ϖ, hϖ, h, hb⟩ := IsPerfectoidTateRing.exists_bijective_frobeniusModPow (p := p) (R := R)
  exact ⟨ϖ, hϖ, h, hb.surjective⟩

variable (p) in
/-- **The zero ring is a perfectoid Tate ring**: `0` is a topologically nilpotent unit, and all
quotients vanish. -/
theorem isPerfectoidTateRing_of_subsingleton [Subsingleton R] : IsPerfectoidTateRing p R where
  isUniform := inferInstance
  exists_pseudoUniformizer :=
    ⟨0, isPseudoUniformizer_iff.mpr ⟨isUnit_of_subsingleton _, .zero⟩,
      ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ ⟨0, ⟨0, Subsingleton.elim _ _⟩⟩,
      fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

section Transport

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsTateRing S] [CompleteSpace S] [T2Space S]

/-- **Perfectoidness transports along isomorphisms of topological rings**: the isomorphism
restricts to `R° ≃+* S°` and carries a pseudouniformiser to a pseudouniformiser. -/
theorem IsPerfectoidTateRing.of_ringEquiv [IsPerfectoidTateRing p R] (e : R ≃+* S)
    (he : Continuous e) (he' : Continuous e.symm) : IsPerfectoidTateRing p S where
  isUniform := (IsPerfectoidTateRing.isUniform (p := p) (R := R)).of_ringEquiv e he he'
  exists_pseudoUniformizer := by
    obtain ⟨ϖ, hϖ, h, hs, hi⟩ := exists_pseudoUniformizer (p := p) (R := R)
    set f := powerBoundedSubringEquiv e he he'
    refine ⟨f ϖ, by simpa [f] using hϖ.map he, by simpa using map_dvd f h, fun x ↦ ?_,
      fun y hy ↦ ?_⟩
    · obtain ⟨y, hy⟩ := hs (f.symm x)
      exact ⟨f y, by simpa using map_dvd f hy⟩
    · simpa using map_dvd (f : powerBoundedSubring R ≃+* powerBoundedSubring S)
        (hi (f.symm y) (by simpa using map_dvd (f.symm : _ ≃+* _) hy))

/-- **Perfectoidness is invariant under isomorphisms of topological rings.** -/
theorem isPerfectoidTateRing_iff_of_ringEquiv (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) : IsPerfectoidTateRing p R ↔ IsPerfectoidTateRing p S :=
  ⟨fun _ ↦ .of_ringEquiv e he he', fun _ ↦ .of_ringEquiv e.symm he' he⟩

end Transport

end TauCeti.Perfectoid
