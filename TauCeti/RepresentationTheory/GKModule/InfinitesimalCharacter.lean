/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.RepresentationTheory.GKModule.Schur

/-!
# Adjoint covariance of the enveloping-algebra action on `(𝔤, K)`-modules

Let `M` be a `(𝔤, K)`-module, so that `ρ g ⁅x, v⁆ = ⁅Ad g x, ρ g v⁆` for `g ∈ K` and `x ∈ 𝔤`. Each
`Ad g` is a Lie algebra endomorphism of `𝔤` and induces an algebra endomorphism `Ad g` of `U(𝔤)`.
The covariance extends from `𝔤` to the whole enveloping algebra: `ρ g (u v) = (Ad g u) (ρ g v)`.

Consequently a central element of `U(𝔤)` fixed by `Ad g` acts by an operator commuting with `ρ g`.
When `Ad(K)` fixes the centre `Z(U(𝔤))` pointwise, the action of `Z(U(𝔤))` commutes with `K`, and
Schur's lemma gives the infinitesimal character of an irreducible admissible `(𝔤, K)`-module from
the adjoint action alone.

## Main statements

* `TauCeti.GKModule.map_representation`: the action of `K` is covariant for the actions of `K` and
  of `U(𝔤)`.
* `TauCeti.GKModule.map_centralAction_of_map_eq`: a central element of `U(𝔤)` fixed by `Ad g`
  acts by an operator commuting with `ρ g`.
* `TauCeti.GKModule.IsIrreducible.exists_hasInfinitesimalCharacter_of_map_eq`: an irreducible
  admissible `(𝔤, K)`-module has an infinitesimal character when `Ad(K)` fixes `Z(U(𝔤))`.
* `TauCeti.GKModule.IsIrreducible.exists_hasInfinitesimalCharacter_of_trivial`: in particular when
  `K` acts trivially on `𝔤`.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
-/

public section

namespace TauCeti.GKModule

open Representation _root_.TauCeti.UniversalEnvelopingAlgebra

variable {k 𝔤 K : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Monoid K]
  {Ad : Representation k K 𝔤} [IsLieAction Ad] {V : Type*} [AddCommGroup V] [Module k V]
  [LieRingModule 𝔤 V] [LieModule k 𝔤 V]

/-- **Adjoint covariance of the `U(𝔤)`-action.** The action of `g ∈ K` on a `(𝔤, K)`-module
intertwines the action of `u ∈ U(𝔤)` with that of its image under the algebra endomorphism of
`U(𝔤)` induced by `Ad g`. -/
theorem map_representation (M : GKModule Ad V) (g : K) (u : UniversalEnvelopingAlgebra k 𝔤)
    (v : V) :
    M.ρ g (representation k 𝔤 V u v) =
      representation k 𝔤 V (map k (Ad.toLieHom g) u) (M.ρ g v) :=
  map_representation_of_map_lie _ (M.ρ g)
    (fun x w ↦ by rw [toLieHom_apply]; exact M.map_lie g x w) u v

/-- A central element of `U(𝔤)` fixed by the algebra endomorphism induced by `Ad g` acts on a
`(𝔤, K)`-module by an operator commuting with `ρ g`. -/
theorem map_centralAction_of_map_eq (M : GKModule Ad V) {g : K}
    {z : Subalgebra.center k (UniversalEnvelopingAlgebra k 𝔤)}
    (hz : map k (Ad.toLieHom g) (z : UniversalEnvelopingAlgebra k 𝔤) = z) (v : V) :
    M.ρ g (centralAction k 𝔤 V z v) = centralAction k 𝔤 V z (M.ρ g v) := by
  rw [centralAction_apply, centralAction_apply, map_representation, hz]

/-- **An irreducible admissible `(𝔤, K)`-module has an infinitesimal character** when the algebra
endomorphisms of `U(𝔤)` induced by `Ad(K)` fix the centre `Z(U(𝔤))` pointwise. The centre then
commutes with `K` by `TauCeti.GKModule.map_centralAction_of_map_eq`, and
`TauCeti.GKModule.IsIrreducible.exists_hasInfinitesimalCharacter` applies. -/
theorem IsIrreducible.exists_hasInfinitesimalCharacter_of_map_eq [IsAlgClosed k]
    {M : GKModule Ad V} (hM : M.IsIrreducible) (hadm : M.ρ.HasFiniteMultiplicities)
    (hZ : ∀ (g : K) (z : Subalgebra.center k (UniversalEnvelopingAlgebra k 𝔤)),
      map k (Ad.toLieHom g) (z : UniversalEnvelopingAlgebra k 𝔤) = z) :
    ∃ χ : Subalgebra.center k (UniversalEnvelopingAlgebra k 𝔤) →ₐ[k] k,
      HasInfinitesimalCharacter k 𝔤 V χ :=
  hM.exists_hasInfinitesimalCharacter hadm fun g z ↦ M.map_centralAction_of_map_eq (hZ g z)

/-- **An irreducible admissible `(𝔤, K)`-module for the trivial action of `K` on `𝔤` has an
infinitesimal character**: `Ad g` induces the identity of `U(𝔤)`. -/
theorem IsIrreducible.exists_hasInfinitesimalCharacter_of_trivial [IsAlgClosed k]
    {M : GKModule (Representation.trivial k K 𝔤) V} (hM : M.IsIrreducible)
    (hadm : M.ρ.HasFiniteMultiplicities) :
    ∃ χ : Subalgebra.center k (UniversalEnvelopingAlgebra k 𝔤) →ₐ[k] k,
      HasInfinitesimalCharacter k 𝔤 V χ := by
  refine hM.exists_hasInfinitesimalCharacter_of_map_eq hadm fun g z ↦ ?_
  have : (Representation.trivial k K 𝔤).toLieHom g = LieHom.id :=
    LieHom.ext fun _ ↦ by simp
  rw [this, map_id, AlgHom.id_apply]

end TauCeti.GKModule
