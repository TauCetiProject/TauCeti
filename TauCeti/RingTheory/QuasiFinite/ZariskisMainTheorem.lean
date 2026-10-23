/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# A global form of Zariski's main theorem

Mathlib's algebraic Zariski main theorem
(`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) is local: at a prime
`p` of a finite type `R`-algebra `A` that is quasi-finite at `p`, it produces a module-finite
subalgebra `A'` and some `r ∉ p` in `A'` with `A'[1/r] = A[1/r]`. When `A` is quasi-finite at every
prime, finitely many such basic opens cover `Spec A`, and the subalgebras can be merged into one.
This file records the resulting statement, in the form in which it is used to reduce questions
about quasi-finite algebras to finite ones: a single module-finite subalgebra `A'` and finitely
many elements `r ∈ A'` generating the unit ideal of `A`, such that every element of `A` is moved
into `A'` by a large enough power of each `r`.

## Main results

* `Algebra.QuasiFinite.exists_fg_subalgebra_and_span_eq_top`: the global form of Zariski's main
  theorem for a quasi-finite algebra of finite type.

## References

* [Stacks Project, Tag 00Q9](https://stacks.math.columbia.edu/tag/00Q9), Zariski's main theorem.
-/

public section

open Filter

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra.QuasiFinite

/-- **Zariski's main theorem, global form.** A quasi-finite algebra `A` of finite type over `R`
has a module-finite subalgebra `A'` and finitely many elements `r ∈ A'` generating the unit ideal
of `A`, such that for every `x ∈ A` and every such `r`, all large enough powers of `r` move `x`
into `A'`. Geometrically, `Spec A` is covered by finitely many basic opens `D(r)` on which it
agrees with the finite `R`-scheme `Spec A'`. -/
theorem exists_fg_subalgebra_and_span_eq_top [Algebra.FiniteType R A] [Algebra.QuasiFinite R A] :
    ∃ (A' : Subalgebra R A) (s : Finset A), A'.toSubmodule.FG ∧ (s : Set A) ⊆ A' ∧
      Ideal.span (s : Set A) = ⊤ ∧ ∀ r ∈ s, ∀ x : A, ∀ᶠ m in atTop, r ^ m * x ∈ A' := by
  classical
  -- Apply the local form at every prime.
  have hloc (P : PrimeSpectrum A) : ∃ B : Subalgebra R A, B.toSubmodule.FG ∧ ∃ r : B,
      (r : A) ∉ P.asIdeal ∧ Function.Bijective (Localization.awayMap B.val.toRingHom r) :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective P.asIdeal
  choose B hB r hr hbij using hloc
  -- The chosen elements generate the unit ideal, hence finitely many of them do.
  have hspan : Ideal.span (Set.range fun P ↦ (r P : A)) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  choose P hP using fun x : s ↦ hs x.2
  replace hP (x : s) : (r (P x) : A) = x := hP x
  -- Merge the finitely many module-finite subalgebras.
  choose t ht using fun x : s ↦ hB (P x)
  let A' := Algebra.adjoin R (⋃ x : s, (t x : Set A))
  have hle (x : s) : B (P x) ≤ A' := by
    intro y hy
    have : y ∈ Submodule.span R (t x : Set A) := by rwa [ht x]
    exact Algebra.span_le_adjoin R _ (Submodule.span_mono (Set.subset_iUnion _ x) this)
  have hsA' : (s : Set A) ⊆ A' := fun y hy ↦ by
    simpa [hP ⟨y, hy⟩] using hle _ (r (P ⟨y, hy⟩)).2
  refine ⟨A', s, fg_adjoin_of_finite (Set.finite_iUnion fun x ↦ (t x).finite_toSet) ?_, hsA',
    hspan, fun y hy z ↦ ?_⟩
  · simp only [Set.mem_iUnion]
    rintro y ⟨x, hy⟩
    have : y ∈ Submodule.span R (t x : Set A) := Submodule.subset_span hy
    rw [ht x] at this
    exact IsIntegral.of_mem_of_fg (B (P x)) (hB (P x)) y this
  -- `A'[1/y] → A[1/y]` is surjective, so `y ^ m * z ∈ A'` for some `m`.
  obtain ⟨b, m, hb⟩ := Localization.awayMap_surjective_iff.mp (hbij (P ⟨y, hy⟩)).2 z
  have hb' : (b : A) = y ^ m * z := by simpa [hP ⟨y, hy⟩] using hb
  refine eventually_atTop.mpr ⟨m, fun n hn ↦ ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_assoc, ← hb']
  exact A'.mul_mem (A'.pow_mem (hsA' hy) _) (hle _ b.2)

end Algebra.QuasiFinite
