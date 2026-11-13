/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Quotient.BoundedTorsion
public import TauCeti.RingTheory.AdicCompletion.Exactness
import TauCeti.LinearAlgebra.Exact

/-!
# Principal-adic completion and bounded torsion obstructions

Completion for a principal ideal preserves an inclusion if the parameter-power torsion of
its cokernel is killed by a fixed power. Consequently, if parameter-power torsion is bounded
in both `range g` and `coker g`, completion preserves the kernel of a map `g : M →ₗ[R] N`.
No regularity, Noetherianity or finite generation is assumed.

For a complex `M → N → P`, bounds on parameter-power torsion in the second map's range and
in first cohomology give a bound in the first map's cokernel. In particular, an annihilating
power for first cohomology supplies its torsion bound. This
supplies the algebraic kernel step in comparing completed sections with compatible sections on
infinitesimal neighbourhoods via a Čech complex. The sheaf comparison and the separate
completeness of the section module are not asserted here.

## Main results

* `AdicCompletion.map_span_singleton_exact_of_annihilates_homology`: middle exactness after
  completion, with an annihilating power for the next cohomology group.
* `AdicCompletion.map_span_singleton_exact_of_bounded_torsion_homology`: the version
  requiring only a bound on the power torsion of the next cohomology group.

Together with `AdicCompletion.map_span_singleton_injective_of_bounded_torsion_range`, these
supply the hypotheses for `LinearMap.kerAdicCompletionEquiv` and its two simp formulas.

## References

* [Stacks Project, Lemma 52.12.7](https://stacks.math.columbia.edu/tag/0EII),
  the bounded-torsion argument in formal-section comparison.

The completion and its residue evaluations are Mathlib's construction of Kenny Lau,
refactored by Judith Ludwig and Christian Merten, who supplied its completed-ring module
structure and functorial map `AdicCompletion.map`.
-/

public section

open scoped Pointwise

namespace AdicCompletion

variable {R : Type*} [CommRing R] {r : R} {k l m : ℕ}
  {L M N P : Type*} [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- An inclusion remains injective after principal-adic completion if the parameter-power
torsion of its cokernel is killed by a fixed power. No finiteness assumptions are needed. -/
theorem map_span_singleton_injective_of_bounded_torsion {f : M →ₗ[R] N}
    (hf : Function.Injective f)
    (hbound : ∀ x : N ⧸ f.range, (∃ n : ℕ, r ^ n • x = 0) → r ^ k • x = 0) :
    Function.Injective (map (Ideal.span {r}) f) :=
  map_injective_of_comap_pow_smul_le
    (f.comap_span_singleton_pow_smul_le_of_bounded_torsion hf hbound)

/-- An inclusion in an exact pair remains injective after principal-adic completion when
parameter-power torsion in the last map's range is bounded. -/
theorem map_span_singleton_injective_of_bounded_torsion_range {f : L →ₗ[R] M}
    {g : M →ₗ[R] N} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hrange : ∀ y ∈ g.range, (∃ n : ℕ, r ^ n • y = 0) → r ^ l • y = 0) :
    Function.Injective (map (Ideal.span {r}) f) := by
  apply map_span_singleton_injective_of_bounded_torsion hf (k := l)
  have hb := g.pow_smul_eq_zero_quotient_ker_of_bounded_torsion_range hrange
  rwa [hfg.linearMap_ker_eq] at hb

/-- Completion preserves middle exactness when parameter-power torsion is bounded in both
the last map's range and its cokernel. The last map need not be surjective. -/
theorem map_span_singleton_exact_of_bounded_torsion {f : L →ₗ[R] M} {g : M →ₗ[R] N}
    (hfg : Function.Exact f g)
    (hrange : ∀ y ∈ g.range, (∃ n : ℕ, r ^ n • y = 0) → r ^ l • y = 0)
    (hbound : ∀ x : N ⧸ g.range, (∃ n : ℕ, r ^ n • x = 0) → r ^ k • x = 0) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) := by
  have hi := map_span_singleton_injective_of_bounded_torsion
    (f := g.range.subtype) g.range.injective_subtype (k := k) (r := r) (by
      rw [Submodule.range_subtype]
      exact hbound)
  have hb := g.pow_smul_eq_zero_quotient_ker_of_bounded_torsion_range hrange
  rw [hfg.linearMap_ker_eq] at hb
  have hc := map_exact_of_comap_pow_smul_le hfg.range_subtype.rangeRestrict
    g.surjective_rangeRestrict
    (f.range.subtype.comap_span_singleton_pow_smul_le_of_bounded_torsion (r := r) (k := l)
      f.range.injective_subtype (by rw [Submodule.range_subtype]; exact hb))
  apply hi.comp_exact_iff_exact.mpr at hc
  rw [← f.subtype_comp_rangeRestrict, ← map_comp]
  apply (map_surjective _ f.surjective_rangeRestrict).comp_exact_iff_exact.mpr
  simpa only [map_comp, LinearMap.subtype_comp_rangeRestrict] using hc

/-- For an exact sequence extending to a complex, bounds on parameter-power torsion in
both ranges and in the next homology group ensure middle exactness after completion. -/
theorem map_span_singleton_exact_of_bounded_torsion_homology
    {f : L →ₗ[R] M} {g : M →ₗ[R] N} {h : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hgh : h ∘ₗ g = 0)
    (hrange : ∀ y ∈ g.range, (∃ n : ℕ, r ^ n • y = 0) → r ^ l • y = 0)
    (hrangeP : ∀ z ∈ h.range, (∃ n : ℕ, r ^ n • z = 0) → r ^ m • z = 0)
    (hH : ∀ y ∈ h.ker, (∃ n : ℕ, r ^ n • y ∈ g.range) → r ^ k • y ∈ g.range) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) :=
  map_span_singleton_exact_of_bounded_torsion hfg hrange
    (g.pow_smul_eq_zero_coker_of_bounded_torsion_homology hgh hrangeP hH)

/-- In an exact sequence `L → M → N` extending to a complex `M → N → P`, completion
preserves exactness at `M` if power torsion is bounded in both ranges and a fixed power kills
`ker h / range g`. In a Čech complex the latter is the first-cohomology obstruction. -/
theorem map_span_singleton_exact_of_annihilates_homology
    {f : L →ₗ[R] M} {g : M →ₗ[R] N} {h : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hgh : h ∘ₗ g = 0)
    (hrange : ∀ y ∈ g.range, (∃ n : ℕ, r ^ n • y = 0) → r ^ l • y = 0)
    (hrangeP : ∀ z ∈ h.range, (∃ n : ℕ, r ^ n • z = 0) → r ^ m • z = 0)
    (hkill : ∀ y ∈ h.ker, r ^ k • y ∈ g.range) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) :=
  map_span_singleton_exact_of_bounded_torsion_homology hfg hgh hrange hrangeP
    (fun y hy _ ↦ hkill y hy)

end AdicCompletion
