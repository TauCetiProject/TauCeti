/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Compression
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Singular homology of a pair below its connectivity, with coefficients in a module

Let `A` be a subspace of `X` such that every point of `X` is joined by a path to `A` and the
relative homotopy sets `πₖ(X, A, a)` are trivial for `0 < k < n` and every `a ∈ A`. For every
module `M` over a ring `R`, the inclusion of `A` induces a surjection `Hₘ(A; M) ⟶ Hₘ(X; M)` on
singular homology for `m < n` (`TauCeti.epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup`)
and a bijection for `m + 1 < n`
(`TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`), and the
relative singular homology `Hₘ(X, A; M)` vanishes for `m < n`
(`TauCeti.isZero_singularHomology_ofSubset_of_relHomotopyGroup`). This is the vanishing half of
the relative Hurewicz theorem; unlike the isomorphism in degree `n`, it needs no assumption on the
fundamental groups of `X` and `A`.

Singular homology with coefficients in `M` is homology with local coefficients in the constant
system at `M` (`TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso`), compatibly with maps
of spaces (`TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso_hom_space_naturality`). So
the two statements about the inclusion are the case of a constant system of the compression of
singular chains with local coefficients
(`TauCeti.epi_twistedHomologyMap_subtypeVal_of_relHomotopyGroup`,
`TauCeti.isIso_twistedHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`), Eilenberg's
deformation of the singular cubes of `X` into `A`. The vanishing of relative homology follows from
the long exact sequence of the pair.

## Main results

* `TauCeti.epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup`,
  `TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`: the inclusion
  of the subspace is surjective on homology below the connectivity of the pair, and bijective one
  degree lower.
* `TauCeti.isZero_singularHomology_ofSubset_of_relHomotopyGroup`: relative singular homology
  vanishes below the connectivity of the pair.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of the singular chains of a pair into those of the subspace.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1, Lemma 4.6 (the
  compression lemma), and Section 4.2, Theorem 4.32 (the relative Hurewicz theorem).
-/

public section

open CategoryTheory Limits AlgebraicTopology

universe u v

namespace TauCeti

open LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} {A : Set X} {n : ℕ}

/-- **The inclusion of a subspace induces surjections on homology below the connectivity of the
pair.** If every point of `X` is joined by a path to a point of `A`, and the relative homotopy set
`π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every `a ∈ A`, then the inclusion of `A`
into `X` induces an epimorphism `Hₘ(A; M) ⟶ Hₘ(X; M)` for every `m < n` and every module `M`. -/
theorem epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup
    (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (M : ModuleCat.{v} R) {m : ℕ} (hm : m < n) :
    Epi (((singularHomologyFunctor (ModuleCat.{v} R) m).obj M).map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) := by
  have := epi_twistedHomologyMap_subtypeVal_of_relHomotopyGroup h₀ h
    ((constantFunctor X).obj M) hm
  have : Epi (twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal A))
      ((constantFunctor X).obj M) m ≫ (twistedHomologyConstantIso X M m).hom) := inferInstance
  rwa [twistedHomologyConstantIso_hom_space_naturality, epi_comp_iff_of_epi,
    epi_comp_iff_of_epi] at this

/-- **The inclusion of a subspace induces isomorphisms on homology one degree below the
connectivity of the pair.** If every point of `X` is joined by a path to a point of `A`, and the
relative homotopy set `π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every `a ∈ A`, then
the inclusion of `A` into `X` induces an isomorphism `Hₘ(A; M) ≅ Hₘ(X; M)` for every `m + 1 < n`
and every module `M`. Together with `TauCeti.epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup`
in degree `m = n - 1`, this is the range given by the long exact sequence of the pair. -/
theorem isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt
    (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (M : ModuleCat.{v} R) {m : ℕ} (hm : m + 1 < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{v} R) m).obj M).map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) := by
  have := isIso_twistedHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt h₀ h
    ((constantFunctor X).obj M) hm
  have : IsIso (twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal A))
      ((constantFunctor X).obj M) m ≫ (twistedHomologyConstantIso X M m).hom) := inferInstance
  rwa [twistedHomologyConstantIso_hom_space_naturality, isIso_comp_left_iff,
    isIso_comp_left_iff] at this

/-- **Relative singular homology vanishes below the connectivity of the pair.** If every point of
`X` is joined by a path to a point of `A`, and the relative homotopy set `π_{k+1}(X, A, a)` is
trivial for every `k + 1 < n` and every `a ∈ A`, then `Hₘ(X, A; M) = 0` for every `m < n` and
every module `M`. -/
theorem isZero_singularHomology_ofSubset_of_relHomotopyGroup
    (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (M : ModuleCat.{v} R) {m : ℕ} (hm : m < n) :
    IsZero ((TopPair.ofSubset A).singularHomology M m) := by
  -- The map induced on singular homology is `SSet.homologyMap (TopCat.toSSet.map P.map)` for the
  -- pair `P = TopPair.ofSubset A`, whose subspace inclusion is `Subtype.val`, by definition.
  have he := epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup h₀ h M hm
  cases m with
  | zero => exact (TopPair.ofSubset A).isZero_singularHomology_zero_of_epi M he
  | succ m =>
    have := isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt h₀ h M hm
    have hmono : Mono (((singularHomologyFunctor (ModuleCat.{v} R) m).obj M).map
        (TopCat.ofHom (ContinuousMap.subtypeVal A))) := inferInstance
    exact (TopPair.ofSubset A).isZero_singularHomology_of_epi_of_mono M rfl he hmono

end TauCeti
