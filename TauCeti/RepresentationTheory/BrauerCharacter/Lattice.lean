/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.RepresentationTheory.BrauerCharacter.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import TauCeti.LinearAlgebra.End.FiniteOrder

/-!
# Brauer characters of reductions of lattices

Let `O` be a domain with a ring homomorphism `O → k` to a field (for a `p`-modular system,
the residue map of the valuation ring), and `σ` a representation of `G` on a finite free
`O`-module `M` (a `G`-stable lattice). Its reduction is the scalar extension `k ⊗[O] M`. If the
characteristic polynomial of `σ g` splits over `O`, the Brauer character of the reduction at a
`p`-regular `g` is the sum, over the roots `λ ∈ O` of that polynomial counted with multiplicity,
of the lift of the reduction of `λ`.

When `O` contains a primitive `m`-th root of unity and the order of `g` divides `m`, the
characteristic polynomial does split over `O` (`Module.End.splits_charpoly_of_pow_eq_one`). If
moreover `ι : O → L` agrees with the lifted reduction on the `m`-th roots of unity of `O`, the
Brauer character of the reduction at `g` is `ι` of the ordinary character `tr (σ g)`. For a
`p`-modular system `(K, O, k)` and `ι` the inclusion of `O` into `ℂ` this says that the Brauer
character of the reduction of a lattice agrees with the ordinary character on the `p`-regular
elements.

## Main results

* `Representation.brauerCharacter_baseChange_of_splits`: the Brauer character of the reduction,
  through the roots over `O`.
* `Representation.brauerCharacter_baseChange_eq_character`: the Brauer character of the reduction
  is the image of the ordinary character.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, 2016, §10.1, p. 170, and
  Proposition 10.1.3, pp. 170–171.
* J. M. Martínez, *Modular representation theory of finite groups*, course notes, Firenze 2024,
  Lecture 1.
-/

public section

open Module Polynomial

namespace Representation

open TauCeti

variable {O k L G M : Type*} [CommRing O] [IsDomain O] [Field k] [Algebra O k] [CommRing L]
  {m : ℕ} [NeZero m] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
  [Monoid G] (p : ℕ) (τ : rootsOfUnity m k ≃* rootsOfUnity m L) (σ : Representation O G M)

/-- **The Brauer character of a reduction.** If the characteristic polynomial of `σ g` splits over
`O`, the Brauer character of the reduction `k ⊗[O] M` at a `p`-regular `g` is the sum of the lifts
of the reductions of its roots, counted with multiplicity. -/
theorem brauerCharacter_baseChange_of_splits {g : G} (hg : p.Coprime (orderOf g))
    (hs : (σ g).charpoly.Splits) :
    (σ.baseChange k).brauerCharacter p τ g =
      ((σ g).charpoly.roots.map fun x ↦ rootsOfUnityLift τ (algebraMap O k x)).sum := by
  rw [brauerCharacter_of_coprime p τ _ hg, baseChange_apply, LinearMap.charpoly_baseChange,
    hs.roots_map_of_ne_zero ((LinearMap.charpoly_monic _).map _).ne_zero, Multiset.map_map,
    Function.comp_def]

/-- **Agreement with ordinary characters.** Let `O` contain a primitive `m`-th root of unity and
let `ι : O →+* L` agree with the lifted reduction on the `m`-th roots of unity of `O`. At a
`p`-regular `g` whose order divides `m`, the Brauer character of the reduction `k ⊗[O] M` is the
image under `ι` of the ordinary character `tr (σ g)`. -/
theorem brauerCharacter_baseChange_eq_character [HasEnoughRootsOfUnity O m] (ι : O →+* L)
    (hι : ∀ x : O, x ^ m = 1 → rootsOfUnityLift τ (algebraMap O k x) = ι x) {g : G}
    (hg : p.Coprime (orderOf g)) (hgm : orderOf g ∣ m) :
    (σ.baseChange k).brauerCharacter p τ g = ι (LinearMap.trace O M (σ g)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot O m
  have hpow : σ g ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 ((orderOf_map_dvd σ g).trans hgm)
  have hs := Module.End.splits_charpoly_of_pow_eq_one hζ hpow
  -- The trace is the sum of the roots of the split characteristic polynomial.
  have htr : LinearMap.trace O M (σ g) = (σ g).charpoly.roots.sum := by
    let b := Module.Free.chooseBasis O M
    rw [LinearMap.trace_eq_matrix_trace O b, Matrix.trace_eq_sum_roots_charpoly_of_splits
      (by rwa [LinearMap.charpoly_toMatrix]), LinearMap.charpoly_toMatrix]
  rw [brauerCharacter_baseChange_of_splits p τ σ hg hs, htr, map_multiset_sum]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun x hx ↦
    hι x (Module.End.pow_eq_one_of_isRoot_charpoly hpow (isRoot_of_mem_roots hx)))

end Representation
