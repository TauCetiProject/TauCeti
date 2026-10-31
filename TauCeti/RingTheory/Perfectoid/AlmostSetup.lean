/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.BasicSetup
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.RootIdeal

/-!
# The almost setup of a perfectoid Tate ring

Let `R` be a Huber ring admitting a pseudouniformiser with compatible `p`-power roots, for
instance a perfectoid Tate ring (`TauCeti.Perfectoid.PseudoUniformizerRoots.nonempty`). Then the
ideal `R°°` of topologically nilpotent elements of `R°` is the root ideal of any such system of
roots, by
`TauCeti.Perfectoid.PseudoUniformizerRoots.topologicallyNilpotentIdeal_eq_span_range_rootPB`, so
it is idempotent and flat, and `(R°, R°°)` is a basic setup for almost mathematics.
The same holds for `(R⁺, R°°)` with `R⁺` any ring of integral elements, the ideal now being the
topologically nilpotent elements of `R⁺`. This is the setup in which almost-vanishing statements
about a perfectoid Tate ring, such as the almost acyclicity of `O⁺` on affinoid perfectoid
spaces, are made.

An `R°`-module is almost zero for this setup exactly when it is killed by every
pseudouniformiser of `R` lying in `R°`, or, equivalently, by every root `ϖ ^ (1 / p ^ n)` of one
fixed pseudouniformiser `ϖ` with compatible `p`-power roots. The setup itself does not depend on
any choice of `ϖ`.

## Main definitions

* `TauCeti.Perfectoid.almostSetup`: the basic setup `(R°, R°°)`.
* `TauCeti.Perfectoid.almostSetupPlus`: the basic setup `(R⁺, R°° ∩ R⁺)` for a ring of integral
  elements `R⁺`; its ideal consists of the topologically nilpotent elements of `R⁺`.

## Main results

* `TauCeti.Perfectoid.almostSetup_isAlmostZero_iff`: an `R°`-module is almost zero iff every
  pseudouniformiser in `R°` kills it.
* `TauCeti.Perfectoid.almostSetup_isAlmostZero_iff_rootPB`: an `R°`-module is almost zero iff
  every root `ϖ ^ (1 / p ^ n)` kills it.
* `TauCeti.Perfectoid.almostSetupPlus_isAlmostZero_iff`: an `R⁺`-module is almost zero iff every
  pseudouniformiser in `R⁺` kills it.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Definition 3.21 and Example 3.22.
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and Definition 4.3.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Example 4.1.3.
* O. Gabber, L. Ramero, *Almost ring theory*, §2.1.
-/

public section

open TauCeti.Huber TauCeti.Almost

namespace TauCeti.Perfectoid

variable (p : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
  [Fact (1 < p)] [Nonempty (PseudoUniformizerRoots p R)]

section PowerBounded

variable [IsHuberRing R]

/-- **The almost setup `(R°, R°°)`** of a Huber ring `R` admitting a pseudouniformiser with
compatible `p`-power roots, for instance of a perfectoid Tate ring: the ideal `R°°` of
topologically nilpotent elements of `R°` is idempotent and `R°° ⊗[R°] R°°` is flat. The setup
depends only on `R`, not on a choice of roots. -/
noncomputable def almostSetup : BasicSetup (powerBoundedSubring R) where
  ideal := topologicallyNilpotentIdeal R
  isIdempotentElem :=
    let ϖ : PseudoUniformizerRoots p R := Classical.arbitrary _
    isIdempotentElem_topologicallyNilpotentIdeal (Fact.out : 1 < p) ϖ.rootsPB
      (ϖ.isPseudoUniformizer_coeffMonoidHom_rootsPB 0)
  flat_tilde :=
    let ϖ : PseudoUniformizerRoots p R := Classical.arbitrary _
    have := flat_topologicallyNilpotentIdeal (Fact.out : 1 < p) ϖ.rootsPB
      (ϖ.isPseudoUniformizer_coeffMonoidHom_rootsPB 0)
    inferInstance

@[simp]
theorem almostSetup_ideal : (almostSetup p R).ideal = topologicallyNilpotentIdeal R :=
  (rfl)

variable {p R}

/-- An `R°`-module is almost zero for `(R°, R°°)` iff it is killed by every root
`ϖ ^ (1 / p ^ n)` of one pseudouniformiser `ϖ` with compatible `p`-power roots. -/
theorem almostSetup_isAlmostZero_iff_rootPB (ϖ : PseudoUniformizerRoots p R) {M : Type*}
    [AddCommGroup M] [Module (powerBoundedSubring R) M] :
    (almostSetup p R).IsAlmostZero M ↔ ∀ (n : ℕ) (x : M), ϖ.rootPB n • x = 0 := by
  rw [BasicSetup.isAlmostZero_iff_isTorsionBySet, almostSetup_ideal,
    ϖ.topologicallyNilpotentIdeal_eq_span_range_rootPB (Fact.out : 1 < p),
    ← Module.isTorsionBySet_iff_is_torsion_by_span]
  exact ⟨fun h n x ↦ @h x ⟨_, n, rfl⟩, by rintro h x ⟨_, n, rfl⟩; exact h n x⟩

/-- An `R°`-module is almost zero for `(R°, R°°)` iff it is killed by every pseudouniformiser of
`R` lying in `R°`. -/
theorem almostSetup_isAlmostZero_iff {M : Type*} [AddCommGroup M]
    [Module (powerBoundedSubring R) M] :
    (almostSetup p R).IsAlmostZero M ↔
      ∀ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) → ∀ x : M, ϖ • x = 0 := by
  refine ⟨fun h ϖ hϖ ↦ h.smul_eq_zero (by
    rw [almostSetup_ideal, mem_topologicallyNilpotentIdeal]
    exact hϖ.isTopologicallyNilpotent), fun h ↦ ?_⟩
  let ϖ : PseudoUniformizerRoots p R := Classical.arbitrary _
  refine (almostSetup_isAlmostZero_iff_rootPB ϖ).mpr fun n ↦ h _ ?_
  rw [PseudoUniformizerRoots.coe_rootPB]
  exact ϖ.isPseudoUniformizer_root n

end PowerBounded

section Plus

variable {Rplus : Subring R} (h : IsRingOfIntegralElements Rplus)

/-- **The almost setup `(R⁺, R°°)`** of a ring of integral elements `R⁺` in a ring `R` admitting
a pseudouniformiser with compatible `p`-power roots: the ideal of topologically nilpotent elements
of `R⁺`, which is `R°°` since `R°° ⊆ R⁺`, is idempotent and its tensor square over `R⁺` is
flat. -/
noncomputable def almostSetupPlus : BasicSetup Rplus where
  ideal := (topologicallyNilpotentIdeal R).comap (Rplus.inclusion h.le_powerBoundedSubring)
  isIdempotentElem :=
    let ϖ : PseudoUniformizerRoots p R := Classical.arbitrary _
    h.isIdempotentElem_comap_topologicallyNilpotentIdeal (Fact.out : 1 < p) (ϖ.rootsIn h)
      (ϖ.isPseudoUniformizer_coeffMonoidHom_rootsIn h 0)
  flat_tilde :=
    let ϖ : PseudoUniformizerRoots p R := Classical.arbitrary _
    have := h.flat_comap_topologicallyNilpotentIdeal (Fact.out : 1 < p) (ϖ.rootsIn h)
      (ϖ.isPseudoUniformizer_coeffMonoidHom_rootsIn h 0)
    inferInstance

/-- The ideal of `(R⁺, R°°)` is the pullback of `R°°` along the inclusion `R⁺ ⊆ R°`. -/
theorem almostSetupPlus_ideal :
    (almostSetupPlus p R h).ideal =
      (topologicallyNilpotentIdeal R).comap (Rplus.inclusion h.le_powerBoundedSubring) :=
  (rfl)

/-- The ideal of `(R⁺, R°°)` consists of the elements of `R⁺` that are topologically nilpotent
in `R`. -/
@[simp]
theorem mem_almostSetupPlus_ideal {x : Rplus} :
    x ∈ (almostSetupPlus p R h).ideal ↔ IsTopologicallyNilpotent (x : R) := by
  rw [almostSetupPlus_ideal, Ideal.mem_comap, mem_topologicallyNilpotentIdeal,
    Subring.coe_inclusion]

variable {p R}

/-- An `R⁺`-module is almost zero for `(R⁺, R°°)` iff it is killed by every pseudouniformiser of
`R` lying in `R⁺`. -/
theorem almostSetupPlus_isAlmostZero_iff {M : Type*} [AddCommGroup M] [Module Rplus M] :
    (almostSetupPlus p R h).IsAlmostZero M ↔
      ∀ ϖ : Rplus, IsPseudoUniformizer (ϖ : R) → ∀ x : M, ϖ • x = 0 := by
  refine ⟨fun hM ϖ hϖ ↦ hM.smul_eq_zero ((mem_almostSetupPlus_ideal p R h).mpr
    hϖ.isTopologicallyNilpotent), fun hM ↦ ?_⟩
  let ϖ : PseudoUniformizerRoots p R := Classical.arbitrary _
  rw [BasicSetup.isAlmostZero_iff_isTorsionBySet, almostSetupPlus_ideal,
    h.comap_topologicallyNilpotentIdeal_eq_span_range (Fact.out : 1 < p) (ϖ.rootsIn h)
      (ϖ.isPseudoUniformizer_coeffMonoidHom_rootsIn h 0),
    ← Module.isTorsionBySet_iff_is_torsion_by_span]
  rintro x ⟨_, n, rfl⟩
  exact hM _ (ϖ.isPseudoUniformizer_coeffMonoidHom_rootsIn h n) x

end Plus

end TauCeti.Perfectoid
