/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.UniformVanishing
import Mathlib.FieldTheory.Galois.Profinite
import TauCeti.NumberTheory.NumberField.RestrictedRamification.Cohomology
import TauCeti.Topology.Algebra.Group.OpenSubgroup.BoundedIndex
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Uniform vanishing of cocycles of bounded exponent on `G_{K,S}`

Let `K` be a number field, `Ω` a normal extension of `K`, such as a separable closure, and `S` a
finite set of finite places of `K`. For an open subgroup `U` of `G_{K,S}` and `m ≠ 0` there is one
open normal subgroup `N ≤ U` of `G_{K,S}` such that, for every discrete `G_{K,S}`-module `B` killed
by `m` on which `U` acts trivially, every continuous `1`-cocycle `G_{K,S} → B` vanishes on `N`, and
is therefore constant on the cosets of `N`
(`TauCeti.RestrictedRamification.exists_openNormalSubgroup_forall_mem_Z1`).

The finiteness input is Hermite's theorem in the form
`TauCeti.RestrictedRamification.finite_setOf_isOpen_index_le`: `G_{K,S}` has finitely many open
subgroups of bounded index, so the open subgroup `U` has only finitely many continuous
homomorphisms to `ℤ/m`. The uniformity argument is the abstract one of
`TauCeti.ContCohomology.exists_openNormalSubgroup_forall_mem_Z1`.

This is the step that lets one count cocycles of `G_{K,S}` with values in all modules killed by
`m` at once, as functions on one finite quotient `G_{K,S} ⧸ N`.

## Main results

* `TauCeti.RestrictedRamification.finite_continuousZModDual`: an open subgroup of `G_{K,S}` has
  finitely many continuous homomorphisms to `ℤ/m`.
* `TauCeti.RestrictedRamification.exists_openNormalSubgroup_forall_mem_Z1`: one open normal
  subgroup `N ≤ U` on which every continuous `1`-cocycle with values in a discrete module killed
  by `m` and fixed by `U` vanishes.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/New/Congruences/Selmer/OneSystem.lean`, declaration
`New.Selmer.exists_openNormalSubgroup_forall_eq_zero`, which works on `Gal(Ω/E)` with cocycles
unramified outside `S` and takes its finiteness input from ideles; here the group is `G_{K,S}` and
the input is Hermite's theorem.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4, Lemma 4.9.
-/

public section

open IsDedekindDomain

open scoped NumberField

namespace TauCeti.RestrictedRamification

universe u v

variable {K : Type*} {Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- **Finitely many characters of order dividing `m`.** An open subgroup `U` of `G_{K,S}` has only
finitely many continuous homomorphisms to `ℤ/m`, by Hermite's theorem. -/
theorem finite_continuousZModDual (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (U : OpenSubgroup (galoisGroupS K Ω S)) (m : ℕ) [NeZero m] :
    Finite (continuousZModDual m U) :=
  have : Finite (U →ₜ* Multiplicative (ZMod m)) :=
    finite_continuousMonoidHom_of_finite_setOf_isOpen_index_le
      (finite_setOf_isOpen_index_le_of_isOpen U.isOpen _
        ((finite_setOf_isOpen_index_le S hS _).subset fun _ hW ↦ ⟨hW.1, hW.2.2⟩))
  inferInstanceAs (Finite (Additive _))

/-- **Uniform vanishing of cocycles of bounded exponent on `G_{K,S}`.** For an open subgroup `U` of
`G_{K,S}` and `m ≠ 0`, there is one open normal subgroup `N ≤ U` of `G_{K,S}` such that, for every
discrete `G_{K,S}`-module `B` killed by `m` on which `U` acts trivially, every continuous
`1`-cocycle `f : G_{K,S} → B` vanishes on `N` and satisfies `f (g * n) = f g` for `n ∈ N`. -/
theorem exists_openNormalSubgroup_forall_mem_Z1 (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) (U : OpenSubgroup (galoisGroupS K Ω S)) (m : ℕ) [NeZero m] :
    ∃ N : OpenNormalSubgroup (galoisGroupS K Ω S), N.toSubgroup ≤ U ∧
      ∀ (B : Type v) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
        [DistribMulAction (galoisGroupS K Ω S) B], (∀ b : B, m • b = 0) →
          (∀ u ∈ U, ∀ b : B, u • b = b) →
          ∀ f ∈ ContCohomology.Z1 (galoisGroupS K Ω S) B, ∀ n ∈ N, f n = 0 ∧ ∀ g, f (g * n) = f g :=
  have := finite_continuousZModDual S hS U m
  ContCohomology.exists_openNormalSubgroup_forall_mem_Z1 (U := U.toSubgroup) U.isOpen m

end TauCeti.RestrictedRamification
