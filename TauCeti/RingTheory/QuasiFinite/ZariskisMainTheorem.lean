/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Consequences of Zariski's main theorem

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
    ∃ (A' : Subalgebra R A) (s : Finset A), Module.Finite R A' ∧ (s : Set A) ⊆ A' ∧
      Ideal.span (s : Set A) = ⊤ ∧ ∀ r ∈ s, ∀ x : A, ∀ᶠ m in atTop, r ^ m * x ∈ A' := by
  classical
  -- Apply the local form at every prime.
  choose B hB r hr hbij using fun P : PrimeSpectrum A ↦
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) P.asIdeal
  -- The basic opens `D(r P)` cover `Spec A`, hence finitely many of the `r P` generate `⊤`.
  have hspan : Ideal.span (Set.range fun P ↦ (r P : A)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp <| top_unique fun P _ ↦
      TopologicalSpace.Opens.mem_iSup.mpr ⟨P, hr P⟩
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  choose P hP using fun x : s ↦ Set.mem_range.mp (hs x.property)
  -- Merge the finitely many module-finite subalgebras.
  choose t ht using fun x : s ↦ hB (P x)
  let A' := Algebra.adjoin R (⋃ x : s, (t x : Set A))
  have hle (x : s) : B (P x) ≤ A' := fun y hy ↦
    Algebra.span_le_adjoin R _ (Submodule.span_mono (Set.subset_iUnion _ x) ((ht x).ge hy))
  have hsA' : (s : Set A) ⊆ A' := fun y hy ↦ by
    simpa [hP ⟨y, hy⟩] using hle _ (r (P ⟨y, hy⟩)).property
  refine ⟨A', s, Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.finite_iUnion fun x ↦ (t x).finite_toSet) (Set.forall_mem_iUnion.mpr fun x y hy ↦
      IsIntegral.of_mem_of_fg _ (hB (P x)) y ((ht x).le (Submodule.subset_span hy))),
    hsA', hspan, fun y hy z ↦ ?_⟩
  -- `A'[1/y] → A[1/y]` is surjective, so `y ^ m * z ∈ A'` for some `m`.
  obtain ⟨b, m, hb⟩ := Localization.awayMap_surjective_iff.mp (hbij (P ⟨y, hy⟩)).2 z
  have hb' : (b : A) = y ^ m * z := by simpa [hP ⟨y, hy⟩] using hb
  refine eventually_atTop.mpr ⟨m, fun n hn ↦ ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_assoc, ← hb']
  exact A'.mul_mem (A'.pow_mem (hsA' hy) _) (hle _ b.property)

end Algebra.QuasiFinite
